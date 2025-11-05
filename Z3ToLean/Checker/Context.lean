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

-- Check if formula is in assumptions
def Context.hasAssumption (ctx : Context) (f : Formula) : Bool :=
  ctx.assumptions.contains f

-- Statistics
def Context.numAssumptions (ctx : Context) : Nat :=
  ctx.assumptions.length

def Context.numDerived (ctx : Context) : Nat :=
  ctx.derived.length

end Z3Proof.Checker
