/-
AST representation for Z3 sat.euf proof format

This module defines the data structures for representing Z3 proofs in the sat.euf format.
The format is based on SMTLIB2 syntax with extensions for proof terms.

Core proof commands:
- `assume`: Introduce an assumption
- `infer`: Derive a new clause with justification
- `del`: Remove a clause (garbage collection)

Proof hints provide justification:
- `farkas`: Linear arithmetic via Farkas' lemma
- `euf`: Equality reasoning
- `cc`: Congruence closure
- `rup`: Reverse unit propagation
-/

namespace Z3Proof

-- Unique identifiers for terms and formulas
abbrev Id := String

-- Variable names
abbrev VarName := String

-- Function and predicate symbols
abbrev Symbol := String

-- Sort (type) representation
inductive SortType where
  | bool : SortType
  | int : SortType
  | proof : SortType  -- Proof sort for proof terms
  | func : List SortType → SortType → SortType
  deriving Repr, BEq, Inhabited

-- Terms in the logic
inductive Term where
  | const : Id → SortType → Term
  | var : VarName → SortType → Term
  | intLit : Int → Term
  | boolLit : Bool → Term
  | app : Symbol → List Term → SortType → Term
  deriving Repr, BEq, Inhabited

-- Formulas (Boolean terms)
inductive Formula where
  | atom : Id → Formula
  | eq : Term → Term → Formula
  | lt : Term → Term → Formula
  | gt : Term → Term → Formula
  | le : Term → Term → Formula
  | ge : Term → Term → Formula
  | not : Formula → Formula
  | and : List Formula → Formula
  | or : List Formula → Formula
  | implies : Formula → Formula → Formula
  deriving Repr, BEq, Inhabited

-- Clause: disjunction of literals (formulas or negations)
structure Clause where
  literals : List Formula
  deriving Repr, BEq, Inhabited

-- Proof hints for inference steps
inductive ProofHint where
  -- Farkas' lemma: coefficients and corresponding formulas
  | farkas : List (Int × Formula) → ProofHint

  -- Equality reasoning: derived formula with premises and optional sub-proof
  | euf : Formula → List Formula → Option Id → ProofHint

  -- Congruence closure: equality derivation
  | cc : Formula → ProofHint

  -- Reverse unit propagation (SAT reasoning)
  | rup : ProofHint

  -- Tseitin transformation
  | tseitin : ProofHint

  -- Quantifier instantiation with bindings
  | inst : List (VarName × Term) → ProofHint

  -- Unresolved proof term reference (to be resolved during verification)
  | ref : Id → ProofHint

  deriving Repr, BEq, Inhabited

-- Proof commands
inductive ProofCommand where
  -- Declaration commands
  | declareFun : Symbol → List SortType → SortType → ProofCommand
  | declareConst : Id → SortType → ProofCommand

  -- Definition commands
  | defineConst : Id → SortType → Term → ProofCommand
  | defineFun : Symbol → List (VarName × SortType) → SortType → Term → ProofCommand

  -- Proof rule declarations (type signatures for proof constructors)
  | declareProofRule : Symbol → List SortType → ProofCommand

  -- Core proof commands
  | assume : Formula → ProofCommand
  | infer : Clause → ProofHint → ProofCommand
  | del : Clause → ProofCommand

  deriving Repr, BEq, Inhabited

-- Complete proof: sequence of commands
structure Proof where
  commands : List ProofCommand
  deriving Repr, BEq, Inhabited

-- Helper functions for working with formulas

def Formula.negate : Formula → Formula
  | Formula.not f => f
  | f => Formula.not f

def Clause.empty : Clause :=
  { literals := [] }

def Clause.isEmpty (c : Clause) : Bool :=
  c.literals.isEmpty

def Clause.unit (f : Formula) : Clause :=
  { literals := [f] }

-- Pretty printing utilities (for debugging)

def SortType.toString : SortType → String
  | SortType.bool => "Bool"
  | SortType.int => "Int"
  | SortType.proof => "Proof"
  | SortType.func args ret => s!"({String.intercalate " " (args.map toString)} -> {ret.toString})"

def Term.toString : Term → String
  | Term.const id _ => id
  | Term.var name _ => name
  | Term.intLit n => reprStr n
  | Term.boolLit b => if b then "true" else "false"
  | Term.app sym args _ => s!"({sym} {String.intercalate " " (args.map toString)})"

def Formula.toString : Formula → String
  | Formula.atom id => id
  | Formula.eq t1 t2 => s!"(= {t1.toString} {t2.toString})"
  | Formula.lt t1 t2 => s!"(< {t1.toString} {t2.toString})"
  | Formula.gt t1 t2 => s!"(> {t1.toString} {t2.toString})"
  | Formula.le t1 t2 => s!"(<= {t1.toString} {t2.toString})"
  | Formula.ge t1 t2 => s!"(>= {t1.toString} {t2.toString})"
  | Formula.not f => s!"(not {f.toString})"
  | Formula.and fs => s!"(and {String.intercalate " " (fs.map toString)})"
  | Formula.or fs => s!"(or {String.intercalate " " (fs.map toString)})"
  | Formula.implies f1 f2 => s!"(=> {f1.toString} {f2.toString})"

def Clause.toString (c : Clause) : String :=
  s!"(cl {String.intercalate " " (c.literals.map Formula.toString)})"

def ProofHint.toString : ProofHint → String
  | ProofHint.farkas coeffs =>
      let pairs := coeffs.map fun (n, f) => s!"({n} {f.toString})"
      s!"farkas {String.intercalate " " pairs}"
  | ProofHint.euf goal premises _ =>
      s!"euf {goal.toString} [{String.intercalate ", " (premises.map Formula.toString)}]"
  | ProofHint.cc f => s!"cc {f.toString}"
  | ProofHint.rup => "rup"
  | ProofHint.tseitin => "tseitin"
  | ProofHint.inst bindings =>
      let pairs := bindings.map fun (v, t) => s!"({v} {t.toString})"
      s!"inst {String.intercalate " " pairs}"
  | ProofHint.ref id => s!"ref {id}"

def ProofCommand.toString : ProofCommand → String
  | ProofCommand.declareFun sym args ret =>
      s!"(declare-fun {sym} ({String.intercalate " " (args.map SortType.toString)}) {ret.toString})"
  | ProofCommand.declareConst id sort =>
      s!"(declare-const {id} {sort.toString})"
  | ProofCommand.defineConst id sort term =>
      s!"(define-const {id} {sort.toString} {term.toString})"
  | ProofCommand.defineFun sym params ret body =>
      let paramStr := params.map fun (v, s) => s!"({v} {s.toString})"
      s!"(define-fun {sym} ({String.intercalate " " paramStr}) {ret.toString} {body.toString})"
  | ProofCommand.declareProofRule sym sorts =>
      s!"(declare-proof-rule {sym} ({String.intercalate " " (sorts.map SortType.toString)}))"
  | ProofCommand.assume f =>
      s!"(assume {f.toString})"
  | ProofCommand.infer clause hint =>
      s!"(infer {clause.toString} {hint.toString})"
  | ProofCommand.del clause =>
      s!"(del {clause.toString})"

instance : ToString SortType where
  toString := SortType.toString

instance : ToString Term where
  toString := Term.toString

instance : ToString Formula where
  toString := Formula.toString

instance : ToString Clause where
  toString := Clause.toString

instance : ToString ProofHint where
  toString := ProofHint.toString

instance : ToString ProofCommand where
  toString := ProofCommand.toString

end Z3Proof
