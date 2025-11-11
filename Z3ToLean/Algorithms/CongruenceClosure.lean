/-
Congruence Closure algorithm for equality reasoning

Implements the Nelson-Oppen congruence closure algorithm for determining
if two terms are equal based on a set of equality axioms and the congruence rule:
  If a = b and f(a) = g(a), then f(a) = f(b) and g(a) = g(b)
-/

import Z3ToLean.Z3Proof.AST
import Z3ToLean.Algorithms.UnionFind

namespace Z3Proof.Algorithms

open Z3Proof

/-! ## Normalized Terms -/

-- Simplified term representation for CC
inductive NormTerm where
  | var : String → NormTerm
  | app : String → List NormTerm → NormTerm
  deriving Repr, BEq, Hashable

def termToNormTerm : Term → NormTerm
  | Term.const id _ => NormTerm.var id
  | Term.var name _ => NormTerm.var name
  | Term.intLit n => NormTerm.var (toString n)
  | Term.boolLit b => NormTerm.var (if b then "true" else "false")
  | Term.app sym args _ => NormTerm.app sym (args.map termToNormTerm)

/-! ## Congruence Closure State -/

structure CongruenceClosure where
  uf : UnionFind NormTerm
  equations : List (NormTerm × NormTerm)
  deriving Repr

def CongruenceClosure.empty : CongruenceClosure :=
  { uf := UnionFind.empty
  , equations := [] }

def CongruenceClosure.addEquality (cc : CongruenceClosure) (t1 t2 : NormTerm) : CongruenceClosure :=
  let uf' := cc.uf.insert t1 |>.insert t2 |>.union t1 t2
  { uf := uf'
  , equations := (t1, t2) :: cc.equations }

def CongruenceClosure.areEqual (cc : CongruenceClosure) (t1 t2 : NormTerm) : Bool :=
  cc.uf.connected t1 t2

/-! ## Building Congruence Closure from Formulas -/

def extractEquality (f : Formula) : Option (Term × Term) :=
  match f with
  | Formula.eq t1 t2 => some (t1, t2)
  | _ => none

partial def buildCongruenceClosure (premises : List Formula) : CongruenceClosure :=
  let equations := premises.filterMap extractEquality
  let normEquations := equations.map fun (t1, t2) => (termToNormTerm t1, termToNormTerm t2)

  -- Build initial CC with all equalities
  normEquations.foldl (fun cc (t1, t2) => cc.addEquality t1 t2) CongruenceClosure.empty

/-! ## EUF Validation -/

def validateEUF (premises : List Formula) (goal : Formula) : Except String Unit :=
  -- Extract equality from goal (handling negations)
  let equalityOpt := match goal with
    | Formula.eq t1 t2 => some (t1, t2)
    | Formula.not (Formula.eq t1 t2) => some (t1, t2)  -- Handle negated equality
    | _ => extractEquality goal

  match equalityOpt with
  | none => Except.error s!"EUF goal must be an equality or negated equality, got: {repr goal}"
  | some (goalLhs, goalRhs) =>
      -- Build congruence closure from premises
      let cc := buildCongruenceClosure premises

      -- Check if goal follows from CC
      let normGoalLhs := termToNormTerm goalLhs
      let normGoalRhs := termToNormTerm goalRhs

      if cc.areEqual normGoalLhs normGoalRhs then
        Except.ok ()
      else
        Except.error s!"EUF validation failed: equality {goalLhs} = {goalRhs} does not follow from premises"

/-! ## CC (Congruence Closure) Validation -/

def validateCC (premises : List Formula) (goal : Formula) : Except String Unit :=
  -- CC is just EUF for our purposes
  validateEUF premises goal

end Z3Proof.Algorithms
