/-
Formal semantic specification for clauses

Clauses are disjunctions of literals (formulas or their negations).
This module defines what it means for a clause to be satisfied and
provides the foundation for reasoning about clause-based proof systems.
-/

import Z3ToLean.Spec.Formula

namespace Z3Proof.Spec

open Z3Proof

/-! ## Clause Semantics -/

def Clause.eval (v : Valuation) (c : Clause) : Bool :=
  c.literals.any (evalFormula v)

def Valuation.satisfiesClause (v : Valuation) (c : Clause) : Prop :=
  Clause.eval v c = true

notation:50 v:50 " ⊨ᶜ " c:50 => Valuation.satisfiesClause v c

def clauseEntails (premises : List Clause) (conclusion : Clause) : Prop :=
  ∀ v : Valuation, (∀ p ∈ premises, v ⊨ᶜ p) → v ⊨ᶜ conclusion

notation:40 premises:40 " ⊨ᶜ " conclusion:40 => clauseEntails premises conclusion

def clausesUnsatisfiable (cs : List Clause) : Prop :=
  ¬∃ v : Valuation, ∀ c ∈ cs, v ⊨ᶜ c

/-! ## Empty Clause -/

theorem empty_clause_false (v : Valuation) :
    ¬(v ⊨ᶜ Clause.empty) := by
  intro h
  simp [Valuation.satisfiesClause, Clause.eval, Clause.empty] at h

theorem empty_clause_unsatisfiable :
    clausesUnsatisfiable [Clause.empty] := by
  intro ⟨v, h⟩
  have : v ⊨ᶜ Clause.empty := h Clause.empty (List.mem_singleton.mpr rfl)
  exact empty_clause_false v this

/-! ## Unit Clauses -/

def Clause.isUnit (c : Clause) : Bool :=
  c.literals.length == 1

axiom unit_clause_iff_formula (v : Valuation) (f : Formula) :
    v ⊨ᶜ (Clause.unit f) ↔ v ⊨ f

/-! ## Clause Properties -/

axiom clause_weakening (v : Valuation) (c : Clause) (f : Formula) :
    v ⊨ᶜ c → v ⊨ᶜ { literals := f :: c.literals }

axiom clause_from_formulas (v : Valuation) (fs : List Formula) :
    (∃ f ∈ fs, v ⊨ f) → v ⊨ᶜ { literals := fs }

/-! ## Resolution -/

def resolves (c1 c2 : Clause) (pivot : Formula) : Option Clause :=
  if c1.literals.contains pivot && c2.literals.contains pivot.negate then
    let lits1 := c1.literals.filter (· != pivot)
    let lits2 := c2.literals.filter (· != pivot.negate)
    some { literals := lits1 ++ lits2 }
  else
    none

axiom resolution_sound (v : Valuation) (c1 c2 c : Clause) (pivot : Formula) :
    resolves c1 c2 pivot = some c → v ⊨ᶜ c1 → v ⊨ᶜ c2 → v ⊨ᶜ c

/-! ## Clause to Formula Conversion -/

def toFormula (c : Clause) : Formula :=
  Formula.or c.literals

axiom clause_equiv_formula (v : Valuation) (c : Clause) :
    v ⊨ᶜ c ↔ Valuation.satisfies v (toFormula c)

end Z3Proof.Spec
