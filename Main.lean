import Z3ToLean

def main (args : List String) : IO Unit := do
  IO.println "Z3-to-Lean Proof Checker"
  IO.println "========================"
  if args.isEmpty then
    IO.println "Usage: z3-to-lean <proof-file.smt2>"
    IO.println ""
    IO.println "Example:"
    IO.println "  z3-to-lean Examples/proof_clean_simple.smt2"
  else
    IO.println s!"Would check proof file: {args[0]!}"
    IO.println "(Parser not yet implemented)"
