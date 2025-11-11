/-
Core proof verification logic

Processes proof commands sequentially and verifies their correctness.
-/

import Z3ToLean.Z3Proof.AST
import Z3ToLean.Checker.Context
import Z3ToLean.Algorithms.Farkas
import Z3ToLean.Algorithms.RUP
import Z3ToLean.Algorithms.CongruenceClosure

namespace Z3Proof.Checker

open Z3Proof
open Z3Proof.Algorithms

-- Extract proof hint from a proof term
-- Resolves formula references to their actual formula structures
partial def extractProofHintFromTerm (ctx : Context) (term : Term) : Except String ProofHint :=
  -- Helper to resolve a formula or proof reference to a formula
  let rec resolveToFormula (id : Id) : Except String Formula := do
    match ctx.lookupDefinition id with
    | some (SortType.bool, formulaTerm) => ctx.termToFormula formulaTerm
    | some (SortType.proof, proofTerm) =>
        -- Extract conclusion from nested proof term
        match proofTerm with
        | Term.app "cc" [Term.const fid _] _ =>
            -- CC proof's conclusion is its argument
            resolveToFormula fid
        | Term.app "euf" (Term.const goalId _ :: _) _ =>
            -- EUF proof's conclusion is its goal (might be negated)
            resolveToFormula goalId
        | _ => Except.error s!"Cannot extract conclusion from proof term: {repr proofTerm}"
    | some (sort, _) => Except.error s!"Reference {id} has sort {sort}, expected Bool or Proof"
    | none => Except.error s!"Undefined reference: {id}"

  match term with
  | Term.app "euf" args _ => do
      -- euf takes: goal premise1 premise2 ...
      -- Arguments can be formula or proof references
      if args.isEmpty then
        Except.error "EUF proof term needs at least a goal"
      let goal ← match args.head? with
        | some (Term.const id _) => resolveToFormula id
        | some t => Except.error s!"EUF goal must be a const reference, got {repr t}"
        | none => Except.error "EUF missing goal"
      let premises ← args.tail.mapM fun arg => do
        match arg with
        | Term.const id _ => resolveToFormula id
        | _ => Except.error "EUF premises must be const references"
      Except.ok (ProofHint.euf goal premises none)

  | Term.app "farkas" args _ => do
      -- farkas takes alternating coeff formula coeff formula ...
      let rec extractPairs (remaining : List Term) : Except String (List (Int × Formula)) :=
        match remaining with
        | [] => Except.ok []
        | Term.intLit n :: Term.const fid _ :: rest => do
            let formula ← resolveToFormula fid
            let rest' ← extractPairs rest
            Except.ok ((n, formula) :: rest')
        | _ => Except.error "Farkas proof term must alternate between int coefficients and formula references"
      extractPairs args >>= fun pairs => Except.ok (ProofHint.farkas pairs)

  | Term.app "cc" [Term.const fid _] _ => do
      let formula ← resolveToFormula fid
      Except.ok (ProofHint.cc formula)

  | Term.app sym _ _ =>
      Except.error s!"Unknown proof constructor: {sym}"

  | _ =>
      Except.error s!"Invalid proof term: {repr term}"

-- Process a single proof command
def processCommand (ctx : Context) (cmd : ProofCommand) : Except String Context :=
  match cmd with
  | ProofCommand.declareFun sym args ret =>
    Except.ok (ctx.declareFunction sym args ret)

  | ProofCommand.declareConst id sort =>
    Except.ok (ctx.declareConst id sort)

  | ProofCommand.defineConst id sort term => do
    ctx.validateTerm term

    -- If this is a proof term (Proof sort), validate Farkas coefficients
    if sort == SortType.proof then
      match term with
      | Term.app "farkas" args _ =>
          -- farkas takes alternating (coeff, formula) arguments
          -- Validate coefficients are non-negative
          let rec checkCoeffs (remaining : List Term) (idx : Nat) : Except String Unit :=
            match remaining with
            | [] => Except.ok ()
            | t :: ts =>
                if idx % 2 == 0 then  -- Even index = coefficient
                  match t with
                  | Term.intLit n =>
                      if n < 0 then
                        Except.error s!"Farkas: negative coefficient {n} in proof term {id}"
                      else
                        checkCoeffs ts (idx + 1)
                  | _ => checkCoeffs ts (idx + 1)
                else  -- Odd index = formula reference
                  checkCoeffs ts (idx + 1)
          checkCoeffs args 0
      | _ => Except.ok ()

    Except.ok (ctx.defineConst id sort term)

  | ProofCommand.defineFun sym params ret body => do
    -- Validate function body with parameters as valid variables
    let paramNames := params.map (·.1)
    ctx.validateTermWithVars paramNames body

    -- Store function definition (also declares it)
    let argSorts := params.map (·.2)
    let ctx' := ctx.declareFunction sym argSorts ret
    Except.ok (ctx'.defineFunction sym params ret body)

  | ProofCommand.declareProofRule sym sorts =>
    -- Proof rules are like function declarations with Proof return type
    Except.ok (ctx.declareFunction sym sorts SortType.proof)

  | ProofCommand.assume formula => do
    ctx.validateFormula formula
    -- Store formula as-is (don't resolve for SAT-level reasoning)
    Except.ok (ctx.assume formula)

  | ProofCommand.infer clause hint => do
    -- Validate all formulas in the clause
    ctx.validateClause clause

    -- Resolve proof term references
    let resolvedHint ← match hint with
      | ProofHint.ref id =>
          -- Look up the proof term definition
          match ctx.lookupDefinition id with
          | some (SortType.proof, term) =>
              -- Extract proof hint from the term
              extractProofHintFromTerm ctx term
          | some (sort, _) =>
              Except.error s!"Reference {id} has sort {sort}, expected Proof"
          | none =>
              Except.error s!"Undefined proof term reference: {id}"
      | _ => Except.ok hint

    -- Validate formulas referenced in hints
    match resolvedHint with
    | ProofHint.rup =>
      -- RUP: validate using unit propagation (currently simplified)
      -- TODO: Fix RUP validation to properly handle all cases
      -- For now, just accept RUP inferences
      -- Convert assumptions to unit clauses
      let assumptionClauses := ctx.assumptions.map Clause.unit
      -- Combine with previously derived clauses
      let allClauses := assumptionClauses ++ ctx.derived
      -- Validate RUP (uses Boolean abstraction, no formula resolution needed)
      validateRUP allClauses clause
      Except.ok (ctx.addDerived clause)

    | ProofHint.farkas coeffs =>
      -- Farkas: verify linear arithmetic certificate
      -- Step 1: Validate that all referenced formulas exist
      let formulas := coeffs.map (·.2)
      formulas.foldlM (fun _ f => ctx.validateFormula f) ()

      -- Step 2: Validate Farkas certificate
      -- TODO: Implement full arithmetic validation (validateFarkasFull)
      -- Currently only checks non-negative coefficients
      let farkasCoeffs := coeffs.map fun (coeff, formula) =>
        { coeff := coeff, formula := formula : FarkasCoeff }
      validateFarkasSimple farkasCoeffs

      Except.ok (ctx.addDerived clause)

    | ProofHint.euf goal premises _proofOpt =>
      -- EUF: verify equality reasoning using congruence closure
      -- Step 1: Validate formulas exist
      ctx.validateFormula goal
      premises.foldlM (fun _ p => ctx.validateFormula p) ()

      -- Step 2: Validate using congruence closure
      -- Combine premises with assumptions
      let allPremises := ctx.assumptions ++ premises
      validateEUF allPremises goal

      Except.ok (ctx.addDerived clause)

    | ProofHint.cc formula =>
      -- Congruence closure: verify congruence
      -- Step 1: Validate formula exists
      ctx.validateFormula formula

      -- Step 2: Validate using congruence closure
      -- CC uses all assumptions as premises
      validateCC ctx.assumptions formula

      Except.ok (ctx.addDerived clause)

    | ProofHint.tseitin =>
      -- Tseitin transformation: CNF conversion preserving equisatisfiability
      -- TODO: Implement full Tseitin validation
      -- Should verify that the clause is a valid Tseitin encoding step
      -- For now, accept all Tseitin-tagged inferences
      Except.ok (ctx.addDerived clause)

    | ProofHint.inst bindings =>
      -- Quantifier instantiation
      -- TODO: Implement full quantifier instantiation validation
      -- Should verify that:
      -- 1. The clause is derived from a quantified formula
      -- 2. The bindings are valid substitutions
      -- 3. The resulting clause follows from the instantiation
      -- For now, just validate that all terms in bindings are well-formed
      bindings.foldlM (fun _ (_var, term) => ctx.validateTerm term) ()
      Except.ok (ctx.addDerived clause)

    | ProofHint.ref id =>
      -- Should never reach here - references are resolved above
      Except.error s!"Unresolved proof term reference: {id}"

  | ProofCommand.del _clause =>
    -- TODO: Track deleted clauses for memory management
    -- For now, just ignore deletions (no impact on soundness)
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
