/-
RUP (Reverse Unit Propagation) validation for SAT reasoning

Implements Boolean Constraint Propagation (BCP) and RUP checking.

RUP validation: A clause C is derivable via RUP from clauses Γ if:
  Γ ∪ {¬l₁, ¬l₂, ..., ¬lₙ} ⊢ ⊥  (where C = l₁ ∨ l₂ ∨ ... ∨ lₙ)

In other words, adding the negations of C's literals leads to a conflict
via unit propagation.
-/

import Z3ToLean.Z3Proof.AST

namespace Z3Proof.Algorithms

open Z3Proof

/-! ## Assignment and Clause State -/

inductive Assignment where
  | unassigned
  | true
  | false
  deriving Repr, BEq, DecidableEq

structure VarAssignment where
  assignments : List (Id × Assignment)
  deriving Repr

def VarAssignment.empty : VarAssignment :=
  { assignments := [] }

def VarAssignment.lookup (va : VarAssignment) (id : Id) : Assignment :=
  match va.assignments.lookup id with
  | some a => a
  | none => Assignment.unassigned

def VarAssignment.set (va : VarAssignment) (id : Id) (a : Assignment) : VarAssignment :=
  { assignments := (id, a) :: va.assignments.filter (fun (i, _) => i != id) }

/-! ## Formula Evaluation under Assignment -/

partial def evaluateFormulaUnderAssignment (va : VarAssignment) (f : Formula) : Option Bool :=
  match f with
  | Formula.atom id =>
      match va.lookup id with
      | Assignment.true => some true
      | Assignment.false => some false
      | Assignment.unassigned => none
  | Formula.not f' =>
      match evaluateFormulaUnderAssignment va f' with
      | some b => some (!b)
      | none => none
  | Formula.and fs =>
      -- AND is true if all sub-formulas are true, false if any is false, none if any is unknown
      let evals := fs.map (evaluateFormulaUnderAssignment va)
      if evals.any (· == some false) then
        some false
      else if evals.all (· == some true) then
        some true
      else
        none
  | Formula.or fs =>
      -- OR is true if any sub-formula is true, false if all are false, none if any is unknown
      let evals := fs.map (evaluateFormulaUnderAssignment va)
      if evals.any (· == some true) then
        some true
      else if evals.all (· == some false) then
        some false
      else
        none
  | Formula.implies f1 f2 =>
      -- IMPLIES: (not f1) or f2
      match evaluateFormulaUnderAssignment va f1, evaluateFormulaUnderAssignment va f2 with
      | some false, _ => some true    -- false => anything is true
      | _, some true => some true     -- anything => true is true
      | some true, some false => some false   -- true => false is false
      | none, _ => none               -- unknown antecedent
      | _, none => none               -- unknown consequent
  | _ => none  -- eq, lt, gt, le, ge require term evaluation (not implemented for SAT)

def clauseIsSatisfied (va : VarAssignment) (c : Clause) : Bool :=
  c.literals.any fun f => evaluateFormulaUnderAssignment va f == some true

def clauseIsUnit (va : VarAssignment) (c : Clause) : Option Formula :=
  -- A clause is unit if exactly one literal is unassigned and others are false
  let unassignedLits := c.literals.filter fun f =>
    evaluateFormulaUnderAssignment va f == none
  let falseLits := c.literals.filter fun f =>
    evaluateFormulaUnderAssignment va f == some false

  if unassignedLits.length == 1 &&
     falseLits.length == c.literals.length - 1 then
    unassignedLits.head?
  else
    none

def clauseIsConflicting (va : VarAssignment) (c : Clause) : Bool :=
  c.literals.all fun f => evaluateFormulaUnderAssignment va f == some false

/-! ## Unit Propagation -/

partial def findUnitClause (va : VarAssignment) (clauses : List Clause) : Option Clause :=
  clauses.find? fun c =>
    !clauseIsSatisfied va c && (clauseIsUnit va c).isSome

partial def propagateUnit (va : VarAssignment) (unitLit : Formula) : VarAssignment :=
  match unitLit with
  | Formula.atom id => va.set id Assignment.true
  | Formula.not (Formula.atom id) => va.set id Assignment.false
  | _ => va

partial def unitPropagate (va : VarAssignment) (clauses : List Clause) (fuel : Nat := 1000) : VarAssignment :=
  if fuel == 0 then va
  else
    -- Check for conflict first (might occur after previous propagation)
    if clauses.any (clauseIsConflicting va) then
      va  -- Stop propagation, conflict found
    else
      match findUnitClause va clauses with
      | none => va
      | some unitClause =>
          match clauseIsUnit va unitClause with
          | none => va
          | some unitLit =>
              let va' := propagateUnit va unitLit
              unitPropagate va' clauses (fuel - 1)

def hasConflict (va : VarAssignment) (clauses : List Clause) : Bool :=
  clauses.any (clauseIsConflicting va)

/-! ## RUP Verification -/

def validateRUP (existingClauses : List Clause) (toDerive : Clause) : Except String Unit :=
  -- Special case: empty clause (contradiction)
  -- Just check if existing clauses already lead to conflict
  if toDerive.isEmpty then
    let finalAssignment := unitPropagate VarAssignment.empty existingClauses
    if hasConflict finalAssignment existingClauses then
      Except.ok ()
    else
      Except.error "RUP validation failed: empty clause not derivable (no conflict in existing clauses)"
  else
    -- RUP: negate the clause to derive, run unit propagation, check for conflict
    let negatedLiterals := toDerive.literals.map Formula.negate
    let negatedClauses := negatedLiterals.map Clause.unit
    let allClauses := existingClauses ++ negatedClauses

    -- Run unit propagation starting from empty assignment
    let finalAssignment := unitPropagate VarAssignment.empty allClauses

    -- Check if we reached a conflict
    if hasConflict finalAssignment allClauses then
      Except.ok ()
    else
      Except.error "RUP validation failed: no conflict after unit propagation"

end Z3Proof.Algorithms
