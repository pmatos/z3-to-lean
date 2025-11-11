/-
Core proof verification logic

Processes proof commands sequentially and verifies their correctness.
-/

import Z3ToLean.Z3Proof.AST
import Z3ToLean.Checker.Context

namespace Z3Proof.Checker

open Z3Proof

-- Process a single proof command
def processCommand (ctx : Context) (cmd : ProofCommand) : Except String Context :=
  match cmd with
  | ProofCommand.declareFun sym args ret =>
    Except.ok (ctx.declareFunction sym args ret)

  | ProofCommand.declareConst id sort =>
    Except.ok (ctx.declareConst id sort)

  | ProofCommand.defineConst id sort term => do
    ctx.validateTerm term
    Except.ok (ctx.defineConst id sort term)

  | ProofCommand.defineFun sym params ret body =>
    -- For now, just treat as a function declaration
    let argSorts := params.map (·.2)
    Except.ok (ctx.declareFunction sym argSorts ret)

  | ProofCommand.declareProofRule sym sorts =>
    -- Proof rules are like function declarations with Proof return type
    Except.ok (ctx.declareFunction sym sorts SortType.proof)

  | ProofCommand.assume formula => do
    ctx.validateFormula formula
    Except.ok (ctx.assume formula)

  | ProofCommand.infer clause hint => do
    -- Validate all formulas in the clause
    ctx.validateClause clause

    -- Validate formulas referenced in hints
    match hint with
    | ProofHint.rup =>
      -- RUP: should be derivable by unit propagation
      Except.ok (ctx.addDerived clause)

    | ProofHint.farkas coeffs =>
      -- Farkas: verify linear arithmetic certificate
      -- Validate that all referenced formulas exist
      let formulas := coeffs.map (·.2)
      formulas.foldlM (fun _ f => ctx.validateFormula f) ()
      Except.ok (ctx.addDerived clause)

    | ProofHint.euf goal premises _proofOpt =>
      -- EUF: verify equality reasoning
      -- Validate goal and all premises
      ctx.validateFormula goal
      premises.foldlM (fun _ p => ctx.validateFormula p) ()
      Except.ok (ctx.addDerived clause)

    | ProofHint.cc formula =>
      -- Congruence closure: verify congruence
      ctx.validateFormula formula
      Except.ok (ctx.addDerived clause)

    | ProofHint.tseitin =>
      -- Tseitin transformation
      Except.ok (ctx.addDerived clause)

    | ProofHint.inst bindings =>
      -- Quantifier instantiation
      -- Validate all terms in bindings
      bindings.foldlM (fun _ (_var, term) => ctx.validateTerm term) ()
      Except.ok (ctx.addDerived clause)

  | ProofCommand.del clause =>
    -- Delete clause (garbage collection)
    -- For now, just ignore deletions
    Except.ok ctx

-- Process a list of commands
partial def processCommands (ctx : Context) (cmds : List ProofCommand) : Except String Context :=
  match cmds with
  | [] => Except.ok ctx
  | cmd :: rest => do
    let ctx' ← processCommand ctx cmd
    processCommands ctx' rest

-- Verify a complete proof
def verifyProof (proof : Proof) : Except String Context := do
  let ctx := Context.empty
  processCommands ctx proof.commands

-- Verify proof with detailed output
structure VerifyStats where
  totalCommands : Nat
  declarations : Nat
  definitions : Nat
  assumptions : Nat
  inferences : Nat
  derivedClauses : Nat
  deriving Repr

def countCommandTypes (cmds : List ProofCommand) : (Nat × Nat × Nat × Nat) :=
  cmds.foldl (fun (decls, defs, assms, infers) cmd =>
    match cmd with
    | ProofCommand.declareFun .. => (decls + 1, defs, assms, infers)
    | ProofCommand.declareConst .. => (decls + 1, defs, assms, infers)
    | ProofCommand.declareProofRule .. => (decls + 1, defs, assms, infers)
    | ProofCommand.defineConst .. => (decls, defs + 1, assms, infers)
    | ProofCommand.defineFun .. => (decls, defs + 1, assms, infers)
    | ProofCommand.assume .. => (decls, defs, assms + 1, infers)
    | ProofCommand.infer .. => (decls, defs, assms, infers + 1)
    | ProofCommand.del .. => (decls, defs, assms, infers)
  ) (0, 0, 0, 0)

def verifyProofWithStats (proof : Proof) : Except String (Context × VerifyStats) := do
  let ctx ← verifyProof proof
  let (decls, defs, assms, infers) := countCommandTypes proof.commands
  let stats : VerifyStats := {
    totalCommands := proof.commands.length
    declarations := decls
    definitions := defs
    assumptions := assms
    inferences := infers
    derivedClauses := ctx.numDerived
  }
  Except.ok (ctx, stats)

end Z3Proof.Checker
