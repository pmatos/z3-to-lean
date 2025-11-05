#!/bin/bash
# Demo script for Z3-to-Lean proof checker

set -e

echo "╔════════════════════════════════════════════════════════╗"
echo "║   Z3-to-Lean Proof Checker Demonstration              ║"
echo "╚════════════════════════════════════════════════════════╝"
echo ""

# Check prerequisites
echo "Checking prerequisites..."
if ! command -v z3 &> /dev/null; then
    echo "Error: z3 not found. Please install Z3."
    exit 1
fi
if ! command -v lake &> /dev/null; then
    echo "Error: lake not found. Please install Lean 4."
    exit 1
fi
echo "✓ Z3 and Lean 4 found"
echo ""

# Build the project
echo "Building z3-to-lean..."
lake build
echo "✓ Build complete"
echo ""

# Test all example proofs
echo "═══════════════════════════════════════════════════════"
echo "Testing Example Proofs"
echo "═══════════════════════════════════════════════════════"
echo ""

for proof in Examples/proof_*.smt2; do
    name=$(basename "$proof" .smt2)
    echo "Testing: $name"
    echo "────────────────────────────────────────────────────"
    .lake/build/bin/z3-to-lean "$proof"
    echo ""
done

# Generate and verify a new proof
echo "═══════════════════════════════════════════════════════"
echo "Complete Workflow Demo: Generate & Verify New Proof"
echo "═══════════════════════════════════════════════════════"
echo ""

# Create a simple SMT2 problem
cat > /tmp/demo_proof.smt2 << 'EOF'
(declare-const a Int)
(declare-const b Int)
(assert (= a 5))
(assert (= b 10))
(assert (not (= (+ a b) 15)))
(check-sat)
EOF

echo "1. Created SMT2 problem:"
echo "   (declare-const a Int)"
echo "   (declare-const b Int)"
echo "   (assert (= a 5))"
echo "   (assert (= b 10))"
echo "   (assert (not (= (+ a b) 15)))"
echo "   (check-sat)"
echo ""

echo "2. Generating Z3 proof..."
z3 /tmp/demo_proof.smt2 sat.euf=true tactic.default_tactic=smt \
   solver.proof.log=/tmp/demo_proof_proof.smt2
echo "✓ Proof generated"
echo ""

echo "3. Verifying proof in Lean..."
echo "────────────────────────────────────────────────────────"
.lake/build/bin/z3-to-lean /tmp/demo_proof_proof.smt2
echo ""

echo "═══════════════════════════════════════════════════════"
echo "Demo Complete!"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "Summary:"
echo "  • All example proofs verified ✓"
echo "  • New proof generated and verified ✓"
echo "  • Z3-to-Lean pipeline working end-to-end ✓"
echo ""
echo "For more information, see README.md and RESEARCH_REPORT.md"
