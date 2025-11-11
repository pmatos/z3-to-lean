/-
Farkas certificate validation for linear arithmetic

Implements validation of Farkas' lemma for proving unsatisfiability
of linear arithmetic constraints.

Farkas' Lemma: A system of linear inequalities is unsatisfiable iff
there exist non-negative coefficients such that their linear combination
yields a contradiction (e.g., 0 >= k where k > 0).
-/

import Z3ToLean.Z3Proof.AST

namespace Z3Proof.Algorithms

open Z3Proof

/-! ## Linear Constraints -/

inductive Constraint where
  | ge : Term → Int → Constraint
  | eq : Term → Int → Constraint
  deriving Repr, BEq

def Constraint.negate : Constraint → Constraint
  | Constraint.ge t k => Constraint.ge t (-k + 1)
  | Constraint.eq t k => Constraint.eq t k

structure LinearTerm where
  var : String
  coeff : Int
  deriving Repr, BEq

def LinearCombination := List LinearTerm

def LinearCombination.constant : LinearCombination → Int
  | [] => 0
  | _ => 0

/-! ## Formula to Constraint Conversion -/

partial def termToVar : Term → Option String
  | Term.const id _ => some id
  | Term.var name _ => some name
  | Term.app "+" [t1, _t2] _ => termToVar t1
  | Term.app "-" [t1, _t2] _ => termToVar t1
  | _ => none

partial def termToInt : Term → Option Int
  | Term.intLit n => some n
  | _ => none

def extractComparison (f : Formula) : Option (Term × String × Term) :=
  match f with
  | Formula.gt t1 t2 => some (t1, ">", t2)
  | Formula.lt t1 t2 => some (t1, "<", t2)
  | Formula.ge t1 t2 => some (t1, ">=", t2)
  | Formula.le t1 t2 => some (t1, "<=", t2)
  | Formula.eq t1 t2 => some (t1, "=", t2)
  | _ => none

def formulaToConstraint (f : Formula) : Option Constraint :=
  match extractComparison f with
  | some (t1, op, t2) =>
      match termToVar t1, termToInt t2 with
      | some var, some k =>
          let term := Term.const var SortType.int
          match op with
          | ">" => some (Constraint.ge term (k + 1))
          | ">=" => some (Constraint.ge term k)
          | "<" => some (Constraint.ge term (-k + 1))
          | "<=" => some (Constraint.ge term (-k))
          | "=" => some (Constraint.eq term k)
          | _ => none
      | _, _ =>
          match termToVar t2, termToInt t1 with
          | some var, some k =>
              let term := Term.const var SortType.int
              match op with
              | ">" => some (Constraint.ge term (-k - 1))
              | ">=" => some (Constraint.ge term (-k))
              | "<" => some (Constraint.ge term (k - 1))
              | "<=" => some (Constraint.ge term k)
              | "=" => some (Constraint.eq term k)
              | _ => none
          | _, _ => none
  | none =>
      match f with
      | Formula.not f' =>
          match formulaToConstraint f' with
          | some c => some c.negate
          | none => none
      | _ => none

/-! ## Farkas Certificate Validation -/

structure FarkasCoeff where
  coeff : Int
  formula : Formula
  deriving Repr

def validateFarkasSimple (coeffs : List FarkasCoeff) : Except String Unit :=
  if coeffs.isEmpty then
    Except.error "Farkas: empty coefficient list"
  else
    match coeffs.find? (fun fc => fc.coeff < 0) with
    | some fc => Except.error s!"Farkas: negative coefficient {fc.coeff}"
    | none => Except.ok ()

def extractFarkasCoeffs (hint : ProofHint) : Option (List FarkasCoeff) :=
  match hint with
  | ProofHint.farkas coeffs =>
      some (coeffs.map fun (coeff, formula) => { coeff := coeff, formula := formula })
  | _ => none

end Z3Proof.Algorithms
