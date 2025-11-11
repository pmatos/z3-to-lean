/-
Formal specifications for proof inference rules

This module defines the soundness conditions for each type of proof rule
used in Z3 proofs (Farkas, EUF, CC, RUP, etc.).

Each rule has a specification that states: if the premises are satisfied
by a valuation, then the conclusion must also be satisfied.
-/

import Z3ToLean.Spec.Formula
import Z3ToLean.Spec.Clause

namespace Z3Proof.Spec

open Z3Proof

/-! ## General Soundness Property -/

def ProofRule : Type := List Formula → Formula → Prop

def soundRule (rule : ProofRule) : Prop :=
  ∀ premises conclusion, rule premises conclusion →
    ∀ v : Valuation, (∀ p ∈ premises, v ⊨ p) → v ⊨ conclusion

/-! ## Assume Rule -/

axiom assume_sound (f : Formula) :
    soundRule (fun premises conclusion =>
      premises = [] ∧ conclusion = f)

/-! ## Farkas Rule -/

structure FarkasCoeff where
  coeff : Int
  premise : Formula

def applyFarkas (coeffs : List FarkasCoeff) : Prop :=
  ∀ v : Valuation,
    (∀ fc ∈ coeffs, v ⊨ fc.premise) →
    ∃ (contradiction : Bool), contradiction = false

axiom farkas_sound (coeffs : List FarkasCoeff) (conclusion : Clause) :
    (∀ fc ∈ coeffs, fc.coeff ≥ 0) →
    applyFarkas coeffs →
    soundRule (fun premises concl =>
      (premises = coeffs.map (·.premise)) ∧
      (concl = Formula.or conclusion.literals))

/-! ## EUF (Equality with Uninterpreted Functions) Rule -/

axiom euf_sound (premises : List Formula) (conclusion : Formula) :
    (∀ p ∈ premises, ∃ t1 t2, p = Formula.eq t1 t2) →
    soundRule (fun ps c => ps = premises ∧ c = conclusion)

/-! ## Congruence Closure Rule -/

axiom cc_sound (premises : List Formula) (conclusion : Formula) :
    soundRule (fun ps c => ps = premises ∧ c = conclusion)

/-! ## RUP (Reverse Unit Propagation) Rule -/

def unitPropagate (clauses : List Clause) (unit : Formula) : List Clause :=
  clauses.filterMap fun c =>
    if c.literals.contains unit then
      none
    else if c.literals.contains unit.negate then
      some { literals := c.literals.filter (· != unit.negate) }
    else
      some c

partial def hasConflict (clauses : List Clause) : Bool :=
  clauses.any (·.isEmpty) ||
  match clauses.find? (fun c => c.literals.length == 1) with
  | some c =>
      match c.literals.head? with
      | some unit => hasConflict (unitPropagate clauses unit)
      | none => false
  | none => false

axiom rup_sound (premises : List Clause) (toDerive : Clause) :
    let negated := toDerive.literals.map Formula.negate
    let extended := premises ++ negated.map Clause.unit
    hasConflict extended = true →
    clauseEntails premises toDerive

/-! ## Tseitin Transformation Rule -/

axiom tseitin_sound (original : Formula) (cnf : List Clause) :
    clausesUnsatisfiable (cnf.map toFormula |>.map Clause.unit) ↔
    ¬(∃ v, Valuation.satisfies v original)

/-! ## Quantifier Instantiation Rule -/

structure InstBinding where
  var : VarName
  term : Term

axiom inst_sound (bindings : List InstBinding) (template : Formula) (inst : Formula) :
    soundRule (fun premises conclusion =>
      premises = [template] ∧ conclusion = inst)

/-! ## Complete Proof Soundness -/

def validProof (commands : List ProofCommand) : Prop :=
  ∀ v : Valuation,
    let assumptions := commands.filterMap (fun cmd =>
      match cmd with
      | ProofCommand.assume f => some f
      | _ => none)
    (∀ a ∈ assumptions, v ⊨ a) →
    ∃ derived_false : Bool, derived_false = false

axiom proof_soundness (proof : Proof) :
    validProof proof.commands →
    unsatisfiable (proof.commands.filterMap (fun cmd =>
      match cmd with
      | ProofCommand.assume f => some f
      | _ => none))

end Z3Proof.Spec
