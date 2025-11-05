import Z3ToLean

open Z3Proof.Parser

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

    -- Read file
    let contents ← IO.FS.readFile filename

    -- Parse proof
    match parseProofFile contents with
    | Except.error msg => do
      IO.println s!"Error: {msg}"
      IO.Process.exit 1
    | Except.ok proof => do
      IO.println s!"✓ Successfully parsed {proof.commands.length} commands"
      IO.println ""
      IO.println "Proof commands:"
      for cmd in proof.commands do
        IO.println s!"  - {cmd}"
      IO.println ""
      IO.println "(Verification not yet implemented)"
