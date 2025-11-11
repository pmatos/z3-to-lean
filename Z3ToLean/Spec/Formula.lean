/-
Formal semantic specification for Z3 proof formulas

This module defines the mathematical meaning of formulas and terms,
providing the foundation for proving soundness of the proof checker.

Key concepts:
- Valuation: Assignment of values to variables and constants
- Evaluation: Computing the semantic value of a term or formula
- Entailment (⊨): Logical consequence relation
- Soundness: Inference rules preserve truth
-/

import Z3ToLean.Z3Proof.AST

namespace Z3Proof.Spec

open Z3Proof

/-! ## Semantic Domains -/

inductive Value where
  | int : Int → Value
  | bool : Bool → Value
  deriving Repr, BEq, Inhabited, DecidableEq

def Value.toInt : Value → Option Int
  | Value.int n => some n
  | _ => none

def Value.toBool : Value → Option Bool
  | Value.bool b => some b
  | _ => none

/-! ## Valuations -/

structure Valuation where
  constants : Id → Value
  functions : Symbol → List Value → Value
  deriving Inhabited

def Valuation.empty : Valuation :=
  { constants := fun _ => Value.int 0
  , functions := fun _ _ => Value.int 0 }

def Valuation.setConst (v : Valuation) (id : Id) (val : Value) : Valuation :=
  { v with constants := fun i => if i == id then val else v.constants i }

/-! ## Term Evaluation -/

def evalTerm (v : Valuation) : Term → Value
  | Term.const id _ => v.constants id
  | Term.var name _ => v.constants name
  | Term.intLit n => Value.int n
  | Term.boolLit b => Value.bool b
  | Term.app sym args _ =>
      let argVals := args.map (evalTerm v)
      v.functions sym argVals

/-! ## Formula Evaluation -/

partial def evalFormula (v : Valuation) : Formula → Bool
  | Formula.atom id =>
      match v.constants id with
      | Value.bool b => b
      | _ => false
  | Formula.eq t1 t2 =>
      evalTerm v t1 == evalTerm v t2
  | Formula.lt t1 t2 =>
      match evalTerm v t1, evalTerm v t2 with
      | Value.int n1, Value.int n2 => n1 < n2
      | _, _ => false
  | Formula.gt t1 t2 =>
      match evalTerm v t1, evalTerm v t2 with
      | Value.int n1, Value.int n2 => n1 > n2
      | _, _ => false
  | Formula.le t1 t2 =>
      match evalTerm v t1, evalTerm v t2 with
      | Value.int n1, Value.int n2 => n1 ≤ n2
      | _, _ => false
  | Formula.ge t1 t2 =>
      match evalTerm v t1, evalTerm v t2 with
      | Value.int n1, Value.int n2 => n1 ≥ n2
      | _, _ => false
  | Formula.not f => !(evalFormula v f)
  | Formula.and fs => fs.all (evalFormula v)
  | Formula.or fs => fs.any (evalFormula v)
  | Formula.implies f1 f2 =>
      !(evalFormula v f1) || evalFormula v f2

/-! ## Logical Consequence -/

def Valuation.satisfies (v : Valuation) (f : Formula) : Prop :=
  evalFormula v f = true

notation:50 v:50 " ⊨ " f:50 => Valuation.satisfies v f

def entails (premises : List Formula) (conclusion : Formula) : Prop :=
  ∀ v : Valuation, (∀ p ∈ premises, v ⊨ p) → v ⊨ conclusion

notation:40 premises:40 " ⊨ " conclusion:40 => entails premises conclusion

def valid (f : Formula) : Prop :=
  ∀ v : Valuation, v ⊨ f

def unsatisfiable (fs : List Formula) : Prop :=
  ¬∃ v : Valuation, ∀ f ∈ fs, v ⊨ f

/-! ## Basic Properties -/

axiom not_soundness (v : Valuation) (f : Formula) :
    v ⊨ Formula.not f ↔ ¬(v ⊨ f)

axiom eq_refl (v : Valuation) (t : Term) :
    v ⊨ Formula.eq t t

axiom eq_symm (v : Valuation) (t1 t2 : Term) :
    v ⊨ Formula.eq t1 t2 → v ⊨ Formula.eq t2 t1

axiom eq_trans (v : Valuation) (t1 t2 t3 : Term) :
    v ⊨ Formula.eq t1 t2 → v ⊨ Formula.eq t2 t3 → v ⊨ Formula.eq t1 t3

/-! ## Derived Properties -/

theorem entails_reflexive (f : Formula) : [f] ⊨ f := by
  intro v h
  exact h f (List.mem_singleton.mpr rfl)

theorem unsatisfiable_from_false (fs : List Formula) :
    (∃ f ∈ fs, ∀ v, ¬(Valuation.satisfies v f)) → unsatisfiable fs := by
  intro ⟨f, hf, hnot⟩ ⟨v, hall⟩
  exact hnot v (hall f hf)

end Z3Proof.Spec
