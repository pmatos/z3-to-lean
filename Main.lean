import Z3ToLean

open Z3Proof.Parser
open Z3Proof.Checker

def main (args : List String) : IO Unit := do
  IO.println "Z3-to-Lean Proof Checker"
  IO.println "========================"
  IO.println ""

  if args.isEmpty then
    IO.println "Usage: z3-to-lean <proof-file.smt2>"
    IO.println ""
    IO.println "Example:"
    IO.println "  z3-to-lean Examples/proof_clean_simple.smt2"
  else
    let filename := args[0]!
    IO.println s!"Reading proof file: {filename}"
    IO.println ""

    -- Read file
    let contents ← IO.FS.readFile filename

    -- Parse proof
    match parseProofFile contents with
    | Except.error msg => do
      IO.println s!"✗ Parse error: {msg}"
      IO.Process.exit 1
    | Except.ok proof => do
      IO.println s!"✓ Parsed {proof.commands.length} commands"

      -- Verify proof
      match verifyProofWithStats proof with
      | Except.error msg => do
        IO.println s!"✗ Verification failed: {msg}"
        IO.Process.exit 1
      | Except.ok (_ctx, stats) => do
        IO.println s!"✓ Verification succeeded!"
        IO.println ""
        IO.println "Statistics:"
        IO.println s!"  Total commands:    {stats.totalCommands}"
        IO.println s!"  Declarations:      {stats.declarations}"
        IO.println s!"  Definitions:       {stats.definitions}"
        IO.println s!"  Assumptions:       {stats.assumptions}"
        IO.println s!"  Inferences:        {stats.inferences}"
        IO.println s!"  Derived clauses:   {stats.derivedClauses}"
        IO.println ""
        IO.println "✓ Proof correct"
