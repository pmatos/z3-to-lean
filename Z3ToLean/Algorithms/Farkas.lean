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

-- Simplified Farkas validation - only checks non-negative coefficients
def validateFarkasSimple (coeffs : List FarkasCoeff) : Except String Unit :=
  if coeffs.isEmpty then
    Except.error "Farkas: empty coefficient list"
  else
    match coeffs.find? (fun fc => fc.coeff < 0) with
    | some fc => Except.error s!"Farkas: negative coefficient {fc.coeff}"
    | none => Except.ok ()

-- Full Farkas validation - checks arithmetic correctness
def validateFarkasFull (coeffs : List FarkasCoeff) : Except String Unit := do
  -- Step 1: Check coefficients are non-negative
  validateFarkasSimple coeffs

  -- Step 2: Extract constraints from formulas
  let constraints ← coeffs.mapM fun fc => do
    let constraintOpt := formulaToConstraint fc.formula
    match constraintOpt with
    | some c =>
        -- Debug: print formula and extracted constraint
        -- dbg_trace s!"Formula: {repr fc.formula} -> Constraint: {repr c}"
        Except.ok (fc.coeff, c)
    | none => Except.error s!"Farkas: formula is not a linear constraint: {repr fc.formula}"

  -- Step 3: Compute the linear combination
  -- Constraints are in the form: var >= k
  -- When we multiply by farkasCoeff, we get: farkasCoeff * var >= farkasCoeff * k
  -- Rearranging: farkasCoeff * var - farkasCoeff * k >= 0
  -- When we sum all: Σ(coeff_i * var_i) - Σ(coeff_i * k_i) >= 0
  let rec combineConstraints (remaining : List (Int × Constraint)) (varMap : List (String × Int)) (constantTerm : Int) : Except String (List (String × Int) × Int) :=
    match remaining with
    | [] => Except.ok (varMap, constantTerm)
    | (farkasCoeff, constraint) :: rest =>
        match constraint with
        | Constraint.ge (Term.const var _) k =>
            -- Constraint: var >= k
            -- Rewritten: var - k >= 0
            -- Multiplied: farkasCoeff * var - farkasCoeff * k >= 0
            let currentCoeff := varMap.lookup var |>.getD 0
            let newCoeff := currentCoeff + farkasCoeff
            let newVarMap := (var, newCoeff) :: varMap.filter (fun (v, _) => v != var)
            let newConstant := constantTerm - farkasCoeff * k
            combineConstraints rest newVarMap newConstant
        | Constraint.eq (Term.const var _) k =>
            -- Equality: var = k
            -- Rewritten: var - k >= 0 (treating as inequality for Farkas)
            let currentCoeff := varMap.lookup var |>.getD 0
            let newCoeff := currentCoeff + farkasCoeff
            let newVarMap := (var, newCoeff) :: varMap.filter (fun (v, _) => v != var)
            let newConstant := constantTerm - farkasCoeff * k
            combineConstraints rest newVarMap newConstant
        | _ => Except.error "Farkas: constraint has unexpected structure"

  let (varCoeffs, constantTerm) ← combineConstraints constraints [] 0

  -- Step 4: Check for contradiction
  -- After linear combination, we have: Σ(coeff_i * var_i) + constantTerm >= 0
  -- A contradiction occurs when:
  -- - All variable coefficients are 0 (they cancel out)
  -- - But constantTerm is negative (e.g., -1 >= 0, which is 0 >= 1)
  let allVarsCancelled := varCoeffs.all fun (_, c) => c == 0
  if allVarsCancelled && constantTerm < 0 then
    Except.ok ()  -- Valid contradiction: constantTerm >= 0 where constantTerm < 0
  else if !allVarsCancelled then
    Except.error s!"Farkas: variables don't cancel out: {repr varCoeffs}"
  else
    Except.error s!"Farkas: no contradiction derived (constant term = {constantTerm})"

def extractFarkasCoeffs (hint : ProofHint) : Option (List FarkasCoeff) :=
  match hint with
  | ProofHint.farkas coeffs =>
      some (coeffs.map fun (coeff, formula) => { coeff := coeff, formula := formula })
  | _ => none

end Z3Proof.Algorithms
