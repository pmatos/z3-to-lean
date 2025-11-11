# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Z3-to-Lean is a demonstration system for Z3 proof generation and Lean proof verification. It parses Z3's `sat.euf` proof format and verifies proofs using a minimal proof checker kernel in Lean 4. The project follows the **De Bruijn criterion**: proofs are checked by a small, auditable kernel separate from the proof generator.

**Current Status**: Working end-to-end demonstration with simplified verification. The checker validates proof structure and command sequencing but does not perform deep validity checking of inference steps (Farkas certificates, congruence closure, RUP).

## Build Commands

```bash
# Build the project
lake build

# Clean build artifacts
lake clean

# Run the proof checker
.lake/build/bin/z3-to-lean <proof-file.smt2>

# Run demo (tests all examples + generates new proof)
./demo.sh
```

## Testing

```bash
# Test all example proofs
for f in Examples/proof_*.smt2; do
  echo "Testing: $f"
  .lake/build/bin/z3-to-lean "$f"
done

# Test a specific example
.lake/build/bin/z3-to-lean Examples/proof_clean_simple.smt2
```

## Generating Z3 Proofs

To generate a proof that can be verified by this tool:

```bash
# Create an SMT2 problem file
cat > problem.smt2 << 'EOF'
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
EOF

# Generate proof using Z3 (must use sat.euf format)
z3 problem.smt2 sat.euf=true tactic.default_tactic=smt \
   solver.proof.log=problem_proof.smt2

# Verify the generated proof
.lake/build/bin/z3-to-lean problem_proof.smt2
```

**Critical**: The Z3 options `sat.euf=true` and `tactic.default_tactic=smt` are required to generate proofs in the correct format.

## Code Architecture

### Module Structure

- **Z3ToLean.lean**: Root module, imports Z3Proof and Checker
- **Main.lean**: CLI entry point, orchestrates parsing and verification
- **Z3ToLean/Z3Proof/**: Proof representation
  - `AST.lean`: Data structures for Z3 proof format (SortType, Term, Formula, Clause, ProofHint, ProofCommand)
  - `Parser.lean`: Parses sat.euf format into AST
- **Z3ToLean/Checker/**: Proof verification
  - `Context.lean`: Tracks declarations, definitions, assumptions, derived clauses
  - `Core.lean`: Processes commands and verifies proofs

### Key Data Structures

**AST Types** (Z3ToLean/Z3Proof/AST.lean):
- `SortType`: Type system (Bool, Int, Proof, function types)
- `Term`: Constants, variables, literals, function applications
- `Formula`: Equality, comparisons, logical operators (not, and, or, implies)
- `Clause`: Disjunction of literals
- `ProofHint`: Justification for inferences (farkas, euf, cc, rup, tseitin, inst)
- `ProofCommand`: Declarations, definitions, assumes, infers, deletes

**Verification State** (Z3ToLean/Checker/Context.lean):
- `Context`: Maintains functions, constants, definitions, assumptions, and derived clauses during verification

### Proof Verification Flow

1. **Parse** (Z3ToLean/Z3Proof/Parser.lean): S-expression parser converts sat.euf format to AST
2. **Process Commands** (Z3ToLean/Checker/Core.lean): Sequential processing of ProofCommands
   - Declarations: Add to symbol table
   - Definitions: Store term/function definitions
   - Assumes: Add formulas to assumption set
   - Infers: Validate structure and add to derived clauses (simplified - no deep checking)
   - Deletes: Ignored (garbage collection)
3. **Output Statistics**: Report counts of different command types

### Supported Proof Hints

The parser handles these proof justifications:
- `farkas`: Linear arithmetic via Farkas' lemma (coefficients + formulas)
- `euf`: Equality with uninterpreted functions
- `cc`: Congruence closure
- `rup`: Reverse unit propagation (SAT)
- `tseitin`: Boolean encoding transformations
- `inst`: Quantifier instantiation with variable bindings

**Note**: Currently these hints are parsed but not deeply verified. The checker accepts them structurally without validating the mathematical correctness of the inference.

## Development Notes

### Prerequisites

- **Z3**: version 4.15.1 or later
- **Lean 4**: version 4.24.0 or later (includes Lake)

### Example Proofs

The `Examples/` directory contains:
- `proof_clean_simple.smt2`: Arithmetic contradiction (x > 5 AND x < 3)
- `proof_clean_no_number.smt2`: Equality contradiction (n = 0 AND n > 10)
- `proof_transitivity.smt2`: Equality transitivity (a = b, b = c ⊢ a = c)
- `proof_congruence.smt2`: Function congruence (x = y ⊢ f(x) = f(y))
- `invalid_*.smt2`: Test cases for error detection

All `proof_*.smt2` files should verify successfully. The `invalid_*.smt2` files are designed to fail verification.

### Future Enhancement Areas

The current system provides a working demonstration. To make it production-ready:

**Short Term**:
- Implement Farkas certificate validation for arithmetic reasoning
- Add congruence closure algorithm for equality checking
- Implement RUP verification for SAT reasoning
- Enhance error messages with detailed failure information

**Long Term**:
- Formally verify the checker kernel in Lean
- Support extended theories (bit-vectors, arrays, non-linear arithmetic)
- Generate Lean proof terms from Z3 proofs for full proof reconstruction
- Optimize for larger proofs (currently handles small examples)

### Lean-Specific Patterns

- **Except monad**: Used throughout for error handling (`Except String T`)
- **do notation**: Parser and checker use monadic style
- **Partial functions**: `processCommands` is marked partial for recursion
- **Namespaces**: Code organized under `Z3Proof`, `Z3Proof.Parser`, `Z3Proof.Checker`
- **Deriving**: AST types derive `Repr`, `BEq`, `Inhabited` for convenience

## Related Documentation

- `README.md`: User-facing documentation, quick start guide, usage examples
- `RESEARCH_REPORT.md`: 42-page comprehensive report with academic background, related work, and 32 references
- `demo.sh`: Automated demonstration script that tests all examples and generates a new proof
