/-
Proof checking context

Maintains the state during proof verification including:
- Function and constant declarations
- Defined constants and their values
- Current assumptions
- Derived clauses
-/

import Z3ToLean.Z3Proof.AST

namespace Z3Proof.Checker

open Z3Proof

-- Verification result
inductive VerifyResult where
  | ok : String → VerifyResult  -- Success with message
  | error : String → VerifyResult  -- Failure with error message
  deriving Repr

def VerifyResult.isOk : VerifyResult → Bool
  | VerifyResult.ok _ => true
  | VerifyResult.error _ => false

-- Proof checking context
structure Context where
  -- Function declarations: name → (arg sorts, return sort)
  functions : List (Symbol × (List SortType × SortType))
  -- Function definitions: name → (params, return sort, body)
  functionDefs : List (Symbol × (List (VarName × SortType) × SortType × Term))
  -- Constant declarations: name → sort
  constants : List (Id × SortType)
  -- Defined constants: name → (sort, term)
  definitions : List (Id × (SortType × Term))
  -- Current assumptions (formulas assumed to be true)
  assumptions : List Formula
  -- Derived clauses
  derived : List Clause
  deriving Repr

-- Empty context
def Context.empty : Context :=
  { functions := []
  , functionDefs := []
  , constants := []
  , definitions := []
  , assumptions := []
  , derived := []
  }

-- Add function declaration
def Context.declareFunction (ctx : Context) (sym : Symbol) (args : List SortType) (ret : SortType) : Context :=
  { ctx with functions := (sym, (args, ret)) :: ctx.functions }

-- Add constant declaration
def Context.declareConst (ctx : Context) (id : Id) (sort : SortType) : Context :=
  { ctx with constants := (id, sort) :: ctx.constants }

-- Add constant definition
def Context.defineConst (ctx : Context) (id : Id) (sort : SortType) (term : Term) : Context :=
  { ctx with definitions := (id, (sort, term)) :: ctx.definitions }

-- Add function definition
def Context.defineFunction (ctx : Context) (sym : Symbol) (params : List (VarName × SortType)) (ret : SortType) (body : Term) : Context :=
  { ctx with functionDefs := (sym, (params, ret, body)) :: ctx.functionDefs }

-- Add assumption
def Context.assume (ctx : Context) (f : Formula) : Context :=
  { ctx with assumptions := f :: ctx.assumptions }

-- Add derived clause
def Context.addDerived (ctx : Context) (c : Clause) : Context :=
  { ctx with derived := c :: ctx.derived }

-- Lookup functions
def Context.lookupFunction (ctx : Context) (sym : Symbol) : Option (List SortType × SortType) :=
  ctx.functions.lookup sym

def Context.lookupConst (ctx : Context) (id : Id) : Option SortType :=
  ctx.constants.lookup id

def Context.lookupDefinition (ctx : Context) (id : Id) : Option (SortType × Term) :=
  ctx.definitions.lookup id

def Context.lookupFunctionDef (ctx : Context) (sym : Symbol) : Option (List (VarName × SortType) × SortType × Term) :=
  ctx.functionDefs.lookup sym

-- Check if formula is in assumptions
def Context.hasAssumption (ctx : Context) (f : Formula) : Bool :=
  ctx.assumptions.contains f

-- Statistics
def Context.numAssumptions (ctx : Context) : Nat :=
  ctx.assumptions.length

def Context.numDerived (ctx : Context) : Nat :=
  ctx.derived.length

/-! ## Reference Validation -/

def Context.isConstDefined (ctx : Context) (id : Id) : Bool :=
  match ctx.lookupConst id, ctx.lookupDefinition id, ctx.lookupFunction id with
  | some _, _, _ => true
  | _, some _, _ => true
  | _, _, some ([], _) => true
  | none, none, _ => false

def Context.isBuiltinFunction (sym : Symbol) : Bool :=
  match sym with
  | ">" | "<" | ">=" | "<=" | "=" | "not" | "and" | "or" | "=>" | "ite"
  | "+" | "-" | "*" | "div" | "mod" | "abs"
  | "distinct" | "iff" | "xor"
  => true
  | _ => false

def Context.isFunctionDefined (ctx : Context) (sym : Symbol) : Bool :=
  if Context.isBuiltinFunction sym then true
  else ctx.lookupFunction sym |>.isSome

-- Validate term with additional valid variable names (for function parameters)
partial def Context.validateTermWithVars (ctx : Context) (validVars : List VarName) (t : Term) : Except String Unit :=
  match t with
  | Term.const id _ =>
      if validVars.contains id || ctx.isConstDefined id then
        Except.ok ()
      else
        Except.error s!"Undefined constant: {id}"
  | Term.var name _ =>
      if validVars.contains name || ctx.isConstDefined name then
        Except.ok ()
      else
        Except.error s!"Undefined variable: {name}"
  | Term.intLit _ => Except.ok ()
  | Term.boolLit _ => Except.ok ()
  | Term.app sym args _ =>
      if !ctx.isFunctionDefined sym then
        Except.error s!"Undefined function: {sym}"
      else
        args.foldlM (fun _ arg => ctx.validateTermWithVars validVars arg) ()

-- Validate term (no additional variables)
partial def Context.validateTerm (ctx : Context) (t : Term) : Except String Unit :=
  ctx.validateTermWithVars [] t

partial def Context.validateFormula (ctx : Context) (f : Formula) : Except String Unit :=
  match f with
  | Formula.atom id =>
      if ctx.isConstDefined id then
        Except.ok ()
      else
        Except.error s!"Undefined atom: {id}"
  | Formula.eq t1 t2 => do
      ctx.validateTerm t1
      ctx.validateTerm t2
  | Formula.lt t1 t2 => do
      ctx.validateTerm t1
      ctx.validateTerm t2
  | Formula.gt t1 t2 => do
      ctx.validateTerm t1
      ctx.validateTerm t2
  | Formula.le t1 t2 => do
      ctx.validateTerm t1
      ctx.validateTerm t2
  | Formula.ge t1 t2 => do
      ctx.validateTerm t1
      ctx.validateTerm t2
  | Formula.not f' =>
      ctx.validateFormula f'
  | Formula.and fs =>
      fs.foldlM (fun _ f' => ctx.validateFormula f') ()
  | Formula.or fs =>
      fs.foldlM (fun _ f' => ctx.validateFormula f') ()
  | Formula.implies f1 f2 => do
      ctx.validateFormula f1
      ctx.validateFormula f2

def Context.validateClause (ctx : Context) (c : Clause) : Except String Unit :=
  c.literals.foldlM (fun _ f => ctx.validateFormula f) ()

/-! ## Term to Formula Conversion -/

mutual
  partial def Context.termToFormula (ctx : Context) (term : Term) : Except String Formula :=
  match term with
  | Term.const id _ =>
      -- Recursively resolve if this is a defined constant
      match ctx.lookupDefinition id with
      | some (SortType.bool, defTerm) => ctx.termToFormula defTerm
      | _ => Except.ok (Formula.atom id)
  | Term.boolLit true => Except.error "Cannot convert boolean literal 'true' to formula"
  | Term.boolLit false => Except.error "Cannot convert boolean literal 'false' to formula"
  | Term.app "=" [t1, t2] _ => Except.ok (Formula.eq t1 t2)
  | Term.app "<" [t1, t2] _ => Except.ok (Formula.lt t1 t2)
  | Term.app ">" [t1, t2] _ => Except.ok (Formula.gt t1 t2)
  | Term.app "<=" [t1, t2] _ => Except.ok (Formula.le t1 t2)
  | Term.app ">=" [t1, t2] _ => Except.ok (Formula.ge t1 t2)
  | Term.app "not" [arg] _ => do
      let f ← ctx.termToFormula arg
      Except.ok (Formula.not f)
  | Term.app "and" args _ => do
      let fs ← args.mapM (ctx.termToFormula ·)
      Except.ok (Formula.and fs)
  | Term.app "or" args _ => do
      let fs ← args.mapM (ctx.termToFormula ·)
      Except.ok (Formula.or fs)
  | Term.app "=>" [t1, t2] _ => do
      let f1 ← ctx.termToFormula t1
      let f2 ← ctx.termToFormula t2
      Except.ok (Formula.implies f1 f2)
  | _ => Except.error s!"Cannot convert term to formula: {repr term}"

  -- Resolve a formula by expanding any formula references (atoms that are defined constants)
  partial def Context.resolveFormula (ctx : Context) (f : Formula) : Formula :=
    match f with
    | Formula.atom id =>
        -- Check if this atom refers to a defined boolean constant
        match ctx.lookupDefinition id with
        | some (SortType.bool, term) =>
            -- Try to convert the term to a formula and resolve recursively
            match ctx.termToFormula term with
            | Except.ok resolvedFormula => ctx.resolveFormula resolvedFormula
            | Except.error _ => f  -- Keep as atom if conversion fails
        | _ => f  -- Keep as atom if not a defined constant
    | Formula.not f' => Formula.not (ctx.resolveFormula f')
    | Formula.and fs => Formula.and (fs.map ctx.resolveFormula)
    | Formula.or fs => Formula.or (fs.map ctx.resolveFormula)
    | Formula.implies f1 f2 => Formula.implies (ctx.resolveFormula f1) (ctx.resolveFormula f2)
    | _ => f  -- Other formulas (eq, lt, gt, etc.) don't have sub-formulas to resolve
end

end Z3Proof.Checker
