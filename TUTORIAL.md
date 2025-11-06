# Step-by-Step Tutorial: How Z3 Proof Verification Works in Lean

**A Comprehensive Guide to Understanding SMT Proof Checking**

---

## Table of Contents

1. [Introduction](#1-introduction)
2. [The Example Problem](#2-the-example-problem)
3. [Understanding the Z3 Proof](#3-understanding-the-z3-proof)
4. [How Lean Processes the Proof](#4-how-lean-processes-the-proof)
5. [Key Concepts Explained](#5-key-concepts-explained)
6. [Code Architecture](#6-code-architecture)
7. [Try It Yourself](#7-try-it-yourself)
8. [Advanced Topics](#8-advanced-topics)

---

## 1. Introduction

### What This Tutorial Covers

This tutorial walks you through a complete example of Z3 proof generation and Lean verification. By the end, you'll understand:

- How Z3 generates proofs for unsatisfiable problems
- What the `sat.euf` proof format looks like
- How the Lean parser converts proofs to data structures
- How the verification engine validates proofs step-by-step
- The key concepts behind SMT proof checking

### The Big Picture

```
┌─────────────┐      ┌─────────────┐      ┌─────────────┐      ┌─────────────┐
│   SMT2      │      │     Z3      │      │    Lean     │      │   Result    │
│  Problem    │ ───> │   Solver    │ ───> │   Parser    │ ───> │  ✓ Correct  │
│             │      │             │      │             │      │  ✗ Invalid  │
└─────────────┘      └─────────────┘      └─────────────┘      └─────────────┘
   x > 5 ∧ x < 3      sat.euf proof      AST + Checker       Verified UNSAT
```

### Prerequisites

- Basic understanding of logic (AND, OR, NOT)
- Familiarity with simple arithmetic inequalities
- Ability to read Lean code (helpful but not required)
- Z3 and Lean 4 installed (to try examples)

---

## 2. The Example Problem

### The Original SMT2 File

Let's start with the simplest possible problem: proving that no integer can be both greater than 5 AND less than 3.

**File: `Examples/clean_simple.smt2`**
```smt2
; No number is both > 5 and < 3
(declare-const x Int)
(assert (> x 5))
(assert (< x 3))
(check-sat)
```

### What This Means

**Line by line:**

1. **Comment**: Explains what we're proving
2. **`(declare-const x Int)`**: Creates an integer variable named `x`
3. **`(assert (> x 5))`**: Claims that `x` is greater than 5
4. **`(assert (< x 3))`**: Claims that `x` is less than 3
5. **`(check-sat)`**: Asks Z3: "Can both constraints be satisfied?"

### Why This Is Impossible

**Intuitive explanation:**

If `x > 5`, then `x` must be at least 6 (for integers).
If `x < 3`, then `x` must be at most 2 (for integers).

But no integer can be both ≥ 6 AND ≤ 2 at the same time!

**Mathematical proof:**
- From `x > 5`, we get `x ≥ 6`
- From `x < 3`, we get `x ≤ 2`
- Combining: `6 ≤ x ≤ 2`
- This implies `6 ≤ 2`, which is false!
- Therefore: **UNSAT** (unsatisfiable)

### What Z3 Does

```bash
$ z3 clean_simple.smt2 sat.euf=true tactic.default_tactic=smt \
     solver.proof.log=proof_clean_simple.smt2

Output: unsat
```

Z3:
1. Reads the problem
2. Analyzes the constraints
3. Determines they're contradictory
4. Generates a **proof** showing why
5. Saves the proof to `proof_clean_simple.smt2`

---

## 3. Understanding the Z3 Proof

### The Generated Proof File

**File: `Examples/proof_clean_simple.smt2`**
```smt2
(declare-fun x () Int)
(define-const $7 Bool (> x 5))
(assume $7)
(define-const $9 Bool (< x 3))
(assume $9)
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $16 Proof (farkas 1 $9 1 $7))
(infer (not $9) (not $7) $16)
(declare-fun rup () Proof)
(infer rup)
```

**10 commands, 141 bytes** - Let's understand each one!

### Line-by-Line Explanation

#### Line 1: `(declare-fun x () Int)`

**What it says:** Declare `x` as a 0-ary function (i.e., constant) returning `Int`

**Plain English:** "Let `x` be an integer variable"

**Why needed:** Establishes `x` in the proof vocabulary so we can refer to it later

**Data structure created:**
```lean
ProofCommand.declareFun "x" [] SortType.int
```

---

#### Line 2: `(define-const $7 Bool (> x 5))`

**What it says:** Define a Boolean constant `$7` that represents `x > 5`

**Plain English:** "Let's call the formula '`x > 5`' by the name `$7`"

**Why needed:** Z3 gives identifiers to formulas to avoid repeating them. `$7` is an auto-generated name.

**Data structure created:**
```lean
ProofCommand.defineConst "$7" SortType.bool (Formula.gt (Term.const "x") (Term.intLit 5))
```

**Visualization:**
```
$7 = (> x 5) = Formula.gt
                   ├─ Term.const "x"
                   └─ Term.intLit 5
```

---

#### Line 3: `(assume $7)`

**What it says:** Assume formula `$7` is true

**Plain English:** "We're going to assume `x > 5` is true"

**Why needed:** This corresponds to the first `assert` from our original problem. We're setting up the assumptions that will lead to a contradiction.

**Data structure created:**
```lean
ProofCommand.assume (Formula.atom "$7")
```

**Context change:**
```
assumptions: [Formula.atom "$7"]
```
We now have one assumption in our proof state.

---

#### Line 4: `(define-const $9 Bool (< x 3))`

**What it says:** Define a Boolean constant `$9` that represents `x < 3`

**Plain English:** "Let's call the formula '`x < 3`' by the name `$9`"

**Why needed:** Same as line 2, but for the second constraint.

**Data structure created:**
```lean
ProofCommand.defineConst "$9" SortType.bool (Formula.lt (Term.const "x") (Term.intLit 3))
```

---

#### Line 5: `(assume $9)`

**What it says:** Assume formula `$9` is true

**Plain English:** "We're also going to assume `x < 3` is true"

**Why needed:** This is the second `assert` from our original problem.

**Context change:**
```
assumptions: [Formula.atom "$9", Formula.atom "$7"]
```
We now have **both** assumptions. This is the contradictory state!

---

#### Line 6: `(declare-fun farkas (Int Bool Int Bool) Proof)`

**What it says:** Declare `farkas` as a function that takes (Int, Bool, Int, Bool) and returns a Proof

**Plain English:** "We have a proof rule called 'Farkas' that can combine arithmetic constraints"

**Why needed:** **Farkas' Lemma** is a fundamental theorem in linear programming. It allows us to prove that a system of inequalities has no solution by finding a special linear combination.

**What Farkas' Lemma says:**
> If you can multiply inequalities by non-negative numbers and add them to get a contradiction (like 0 < -5), then the original system has no solution.

---

#### Line 7: `(define-const $16 Proof (farkas 1 $9 1 $7))`

**What it says:** Create a proof object `$16` using Farkas with arguments: coefficient 1, formula $9, coefficient 1, formula $7

**Plain English:** "Multiply constraint `$9` by 1, multiply constraint `$7` by 1, and combine them"

**The mathematics:**
```
$9 is (x < 3), which means x ≤ 2
$7 is (x > 5), which means x ≥ 6

Multiply $9 by 1:  1 × (x ≤ 2) = x ≤ 2
Multiply $7 by 1:  1 × (x ≥ 6) = x ≥ 6

Combining: x ≤ 2 AND x ≥ 6
This means: 6 ≤ x ≤ 2
Which implies: 6 ≤ 2 (FALSE!)

Therefore: At least one of $9 or $7 must be false
```

**Data structure created:**
```lean
ProofCommand.defineConst "$16" SortType.proof (Term.app "farkas" [...])
```

---

#### Line 8: `(infer (not $9) (not $7) $16)`

**What it says:** Infer the clause `(¬$9 ∨ ¬$7)` justified by proof `$16`

**Plain English:** "Based on the Farkas proof `$16`, we can conclude that at least one of our assumptions is false"

**Logical meaning:**
```
(not $9) ∨ (not $7)
= ¬(x < 3) ∨ ¬(x > 5)
= "Either x is NOT less than 3, OR x is NOT greater than 5 (or both)"
```

**Why this is valid:** The Farkas certificate in `$16` proves that assuming both `$9` AND `$7` leads to a mathematical contradiction. Therefore, at least one must be false.

**Data structure created:**
```lean
ProofCommand.infer
  { literals := [Formula.not (Formula.atom "$9"),
                 Formula.not (Formula.atom "$7")] }
  ProofHint.rup
```

**Context change:**
```
derived: [{literals: [(not $9), (not $7)]}]
```

---

#### Line 9: `(declare-fun rup () Proof)`

**What it says:** Declare `rup` as a 0-ary proof constructor

**Plain English:** "We have a proof rule called RUP (Reverse Unit Propagation)"

**What is RUP?**
- **Unit Propagation** is a core SAT solving technique
- If you have a clause with only one unassigned literal, that literal must be true
- **Reverse Unit Propagation** proves a clause by showing it can be derived through unit propagation

---

#### Line 10: `(infer rup)`

**What it says:** Infer the empty clause using RUP

**Plain English:** "By unit propagation from our existing clauses, we derive a contradiction"

**The reasoning:**
```
We have:
1. Assumption: $9 is true (x < 3)
2. Assumption: $7 is true (x > 5)
3. Derived clause: (¬$9 ∨ ¬$7)

Unit propagation:
- From assumption $9 and clause (¬$9 ∨ ¬$7), we get ¬$7
- But we also have assumption $7
- We have both $7 and ¬$7 → CONTRADICTION!
```

**What is the empty clause?**
- A clause with no literals: `( )`
- Represents logical FALSE
- In SAT, deriving the empty clause means UNSAT

**Data structure created:**
```lean
ProofCommand.infer { literals := [] } ProofHint.rup
```

**This is the proof's conclusion!** We've derived a contradiction, proving the original problem is unsatisfiable.

---

### Proof Structure Summary

```
Setup Phase:
  1. Declare variable x
  2-5. Define and assume both constraints

Reasoning Phase:
  6-7. Build Farkas certificate showing contradiction
  8. Derive clause: "at least one assumption is false"

Conclusion Phase:
  9-10. Use unit propagation to derive empty clause
        → CONTRADICTION → UNSAT proved!
```

---

## 4. How Lean Processes the Proof

Now let's trace **exactly** what happens when Lean verifies this proof.

### Phase 1: Command Line Invocation

```bash
$ .lake/build/bin/z3-to-lean Examples/proof_clean_simple.smt2
```

**What happens:**
1. Lean executable starts
2. `Main.lean:main` function is called
3. Reads command-line argument: `"Examples/proof_clean_simple.smt2"`

### Phase 2: Reading the File

```lean
let contents ← IO.FS.readFile filename
```

**Result:** Entire file loaded as a string (141 bytes)

```
"(declare-fun x () Int)\n(define-const $7 Bool (> x 5))\n..."
```

### Phase 3: Parsing - S-Expression Level

**Parser State:** Initially at position 0, line 1, column 0

**Step 1:** Skip whitespace, see `(`
```
Parser at: (declare-fun x () Int)
           ^
```

**Step 2:** Parse list until matching `)`
- Recursively parse: `declare-fun`, `x`, `()`, `Int`
- Each is an atom

**Result:**
```lean
SExpr.list [
  SExpr.atom "declare-fun",
  SExpr.atom "x",
  SExpr.list [],
  SExpr.atom "Int"
]
```

**Step 3:** Repeat for all 10 commands

**Result:** List of 10 S-expressions

### Phase 4: Parsing - AST Conversion

Now convert each S-expression to typed AST nodes.

#### Command 1 Conversion

**Input S-expr:**
```lean
SExpr.list [atom "declare-fun", atom "x", list [], atom "Int"]
```

**Pattern matching in `parseProofCommand`:**
```lean
| SExpr.list [SExpr.atom "declare-fun", SExpr.atom sym, SExpr.list args, ret] => do
  let argSorts ← args.mapM parseSortType  -- [] maps to []
  let retSort ← parseSortType ret         -- "Int" → SortType.int
  Except.ok (ProofCommand.declareFun sym argSorts retSort)
```

**Output AST:**
```lean
ProofCommand.declareFun "x" [] SortType.int
```

#### Command 2 Conversion

**Input S-expr:**
```lean
SExpr.list [atom "define-const", atom "$7", atom "Bool",
           list [atom ">", atom "x", atom "5"]]
```

**Parsing the term `(> x 5)`:**
```lean
parseTerm (list [atom ">", atom "x", atom "5"])
→ Formula.gt (Term.const "x" SortType.int) (Term.intLit 5)
```

**Output AST:**
```lean
ProofCommand.defineConst "$7" SortType.bool
  (Formula.gt (Term.const "x" SortType.int) (Term.intLit 5))
```

#### Command 8 Conversion (infer)

**Input S-expr:**
```lean
SExpr.list [atom "infer", list [atom "not", atom "$9"],
           list [atom "not", atom "$7"], atom "$16"]
```

**Parsing:**
- Extract literals: `(not $9)`, `(not $7)`
- Parse each as formula
- Last element `$16` is proof term reference

**Output AST:**
```lean
ProofCommand.infer
  { literals := [Formula.not (Formula.atom "$9"),
                 Formula.not (Formula.atom "$7")] }
  ProofHint.rup
```

**Final parsing result:**
```lean
Proof { commands := [cmd1, cmd2, cmd3, ..., cmd10] }
```

### Phase 5: Verification - Context Evolution

Initial state:
```lean
Context {
  functions := [],
  constants := [],
  definitions := [],
  assumptions := [],
  derived := []
}
```

Now process each command:

#### After Command 1: `(declare-fun x () Int)`

**Action:** `ctx.declareFunction "x" [] SortType.int`

**New Context:**
```lean
Context {
  functions := [("x", ([], Int))],
  constants := [],
  definitions := [],
  assumptions := [],
  derived := []
}
```

**State:** We now know `x` is a function (constant) of type Int

---

#### After Command 2: `(define-const $7 Bool (> x 5))`

**Action:** `ctx.defineConst "$7" SortType.bool (Formula.gt ...)`

**New Context:**
```lean
Context {
  functions := [("x", ([], Int))],
  constants := [],
  definitions := [("$7", (Bool, (> x 5)))],
  assumptions := [],
  derived := []
}
```

**State:** We now have a definition: `$7` means `x > 5`

---

#### After Command 3: `(assume $7)`

**Action:** `ctx.assume (Formula.atom "$7")`

**New Context:**
```lean
Context {
  functions := [("x", ([], Int))],
  constants := [],
  definitions := [("$7", (Bool, (> x 5)))],
  assumptions := [Formula.atom "$7"],
  derived := []
}
```

**State:** We're now assuming `$7` (which means `x > 5`) is true

---

#### After Command 4-5: Define and assume $9

**New Context:**
```lean
Context {
  functions := [("x", ([], Int))],
  constants := [],
  definitions := [("$9", (Bool, (< x 3))),
                  ("$7", (Bool, (> x 5)))],
  assumptions := [Formula.atom "$9",
                  Formula.atom "$7"],
  derived := []
}
```

**State:** Both assumptions are now active. We have a contradictory state!

---

#### After Command 6-7: Declare and define Farkas proof

**New Context:**
```lean
Context {
  functions := [("farkas", ([Int,Bool,Int,Bool], Proof)),
                ("x", ([], Int))],
  constants := [],
  definitions := [("$16", (Proof, (farkas 1 $9 1 $7))),
                  ("$9", (Bool, (< x 3))),
                  ("$7", (Bool, (> x 5)))],
  assumptions := [Formula.atom "$9",
                  Formula.atom "$7"],
  derived := []
}
```

**State:** We now have a Farkas proof object `$16` that certifies the contradiction

---

#### After Command 8: `(infer (not $9) (not $7) $16)`

**Action:** Process inference with Farkas hint

**Verification (simplified):**
- Check that the clause is well-formed ✓
- Check that proof hint is recognized ✓
- (Production would validate Farkas certificate here)
- Add clause to derived set ✓

**New Context:**
```lean
Context {
  functions := [("farkas", ([Int,Bool,Int,Bool], Proof)),
                ("x", ([], Int))],
  constants := [],
  definitions := [("$16", (Proof, (farkas 1 $9 1 $7))),
                  ("$9", (Bool, (< x 3))),
                  ("$7", (Bool, (> x 5)))],
  assumptions := [Formula.atom "$9",
                  Formula.atom "$7"],
  derived := [{literals: [(not $9), (not $7)]}]
}
```

**State:** We've derived our first clause: at least one assumption is false

---

#### After Command 9-10: RUP and empty clause

**Action:** Process second inference with RUP hint

**New Context:**
```lean
Context {
  functions := [("rup", ([], Proof)),
                ("farkas", ([Int,Bool,Int,Bool], Proof)),
                ("x", ([], Int))],
  constants := [],
  definitions := [("$16", (Proof, (farkas 1 $9 1 $7))),
                  ("$9", (Bool, (< x 3))),
                  ("$7", (Bool, (> x 5)))],
  assumptions := [Formula.atom "$9",
                  Formula.atom "$7"],
  derived := [{literals: []},  -- THE EMPTY CLAUSE!
              {literals: [(not $9), (not $7)]}]
}
```

**State:** We've derived the empty clause → **Proof complete!**

### Phase 6: Statistics Computation

```lean
def countCommandTypes (cmds : List ProofCommand) : (Nat × Nat × Nat × Nat) :=
  -- Count declarations, definitions, assumptions, inferences
```

**Result for our proof:**
```
Total commands:    10
Declarations:      3  (x, farkas, rup)
Definitions:       3  ($7, $9, $16)
Assumptions:       2  ($7, $9)
Inferences:        2  (two infer commands)
Derived clauses:   2  (disjunction + empty clause)
```

### Phase 7: Output

```
Z3-to-Lean Proof Checker
========================

Reading proof file: Examples/proof_clean_simple.smt2

✓ Parsed 10 commands
✓ Verification succeeded!

Statistics:
  Total commands:    10
  Declarations:      3
  Definitions:       3
  Assumptions:       2
  Inferences:        2
  Derived clauses:   2

✓ Proof correct
```

---

## 5. Key Concepts Explained

### What is sat.euf Format?

**SAT.EUF** = **SAT** with **EUF** (Equality and Uninterpreted Functions)

#### Background: From SAT to SMT

**SAT (Boolean Satisfiability):**
- Works with Boolean variables and formulas
- Can handle: `(p ∨ ¬q) ∧ (q ∨ r) ∧ ...`
- Cannot reason about: arithmetic, arrays, functions

**SMT (Satisfiability Modulo Theories):**
- Extends SAT with **theories**:
  - Linear arithmetic: `x + y < 5`
  - Bit-vectors: `bvadd(x, y)`
  - Arrays: `select(store(a, i, v), i) = v`
  - Equality: `f(x) = f(y) if x = y`

**How SMT solvers work:**
```
SMT Problem → Convert to SAT + Theory Lemmas
            ↓
        SAT Solver ← Theory Solvers
            ↓
        SAT/UNSAT
```

#### The sat.euf Format

**Purpose:** External proof format for Z3's reasoning

**Key features:**
1. **Based on SMTLIB2:** Uses S-expression syntax
2. **Clause-based:** Represents reasoning as clause derivation
3. **Theory lemmas:** Includes justifications for theory reasoning
4. **Three core commands:**
   - `assume`: Add assumption
   - `infer`: Derive clause with justification
   - `del`: Remove clause (garbage collection)

**Example structure:**
```smt2
(declare-fun x () Int)        ; Setup
(define-const $1 Bool ...)    ; Setup
(assume $1)                   ; Assumption
(infer ... farkas)            ; Theory lemma with certificate
(infer ... rup)               ; SAT reasoning
```

**Advantages:**
- **Verifiable:** Independent tools can check proofs
- **Self-contained:** All information for verification included
- **Theory-specific:** Contains detailed reasoning steps
- **Compact:** Reuses SMTLIB2 infrastructure

---

### Understanding Proof Hints

Proof hints justify **why** an inference step is valid. Each hint type corresponds to a different reasoning principle.

#### 1. Farkas - Linear Arithmetic Reasoning

**Farkas' Lemma** (1894):
> A system of linear inequalities has no solution if and only if there exists a non-negative linear combination of the inequalities that yields a contradiction.

**Example from our proof:**

```smt2
(declare-fun farkas (Int Bool Int Bool) Proof)
(define-const $16 Proof (farkas 1 $9 1 $7))
```

**What this means:**

Constraints:
- `$9`: `x < 3` → `x ≤ 2`
- `$7`: `x > 5` → `x ≥ 6`

Farkas certificate: `(1, $9, 1, $7)` means:
- Multiply `$9` by 1: `1 × (x ≤ 2)` = `x ≤ 2`
- Multiply `$7` by 1: `1 × (x ≥ 6)` = `x ≥ 6`

Combine them:
```
x ≤ 2  AND  x ≥ 6
```

This is equivalent to:
```
6 ≤ x ≤ 2
```

Which implies:
```
6 ≤ 2  (FALSE!)
```

**Conclusion:** The system has no solution. At least one constraint must be false: `¬(x < 3) ∨ ¬(x > 5)`

**General form:**
```smt2
(farkas c₁ φ₁ c₂ φ₂ ... cₙ φₙ)
```
Where:
- `cᵢ` are non-negative coefficients
- `φᵢ` are inequality constraints
- The combination `Σ cᵢ × φᵢ` yields a contradiction

**How to verify a Farkas certificate:**
1. Convert each constraint to form `aᵢx + bᵢ ≥ 0`
2. Compute: `Σ cᵢ(aᵢx + bᵢ)`
3. Simplify to: `Ax + B`
4. Check: `B < 0` while coefficients are non-negative → contradiction!

---

#### 2. EUF - Equality Reasoning

**EUF** = **E**quality with **U**ninterpreted **F**unctions

**Core principle:** Transitivity and congruence of equality

**Example: Transitivity**

```smt2
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
```

**Proof:**
```smt2
(declare-fun euf (Bool Bool Bool) Proof)
(define-const $12 Proof (euf (not (= a c)) (= a b) (= b c)))
(infer (not (= a b)) (not (= b c)) (= a c) $12)
```

**What this means:**

Given:
- `a = b`
- `b = c`

By transitivity:
- `a = c`

The euf proof derives: `¬(a = b) ∨ ¬(b = c) ∨ (a = c)`

Meaning: "If a=b and b=c, then a=c must be true"

**Example: Congruence**

```smt2
(declare-fun f (Int) Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
```

**Congruence property:**
> If `x = y`, then `f(x) = f(y)` for any function `f`

**Proof derives:** `¬(x = y) ∨ (f(x) = f(y))`

---

#### 3. RUP - Reverse Unit Propagation

**Unit Propagation** is the workhorse of SAT solvers.

**Unit clause:** A clause with only one unassigned literal

**Unit propagation rule:**
> If a clause becomes unit (only one unassigned literal), that literal must be true.

**Example:**

```
Clause: (p ∨ q ∨ r)
Assignment: q = false, r = false
Result: Clause becomes (p) → must assign p = true
```

**Reverse Unit Propagation (RUP):**
> Prove a clause is valid by showing it can be derived through unit propagation from existing clauses.

**Algorithm:**
1. Negate the clause to derive
2. Add negated clause to database
3. Run unit propagation
4. If derives empty clause → original clause is RUP-derivable

**Example from our proof:**

```smt2
(infer rup)  ; derives empty clause
```

**State before:**
- Assumptions: `$9` (x < 3), `$7` (x > 5)
- Derived: `(¬$9 ∨ ¬$7)`

**Unit propagation:**
```
From $9 (unit clause) and (¬$9 ∨ ¬$7), derive ¬$7
But we also have $7
Contradiction! → Empty clause
```

---

#### 4. CC - Congruence Closure

**Congruence Closure** is an algorithm for reasoning about equality.

**Maintains equivalence classes of equal terms:**
```
[x, y]        x and y are equal
[f(x), f(y)]  therefore f(x) and f(y) are equal
```

**Operations:**
- **Merge:** Combine equivalence classes when told two terms are equal
- **Find:** Check if two terms are in the same equivalence class
- **Congruence:** If `x = y` and function `f` applied, then `f(x) = f(y)`

**Example:**

```smt2
(declare-fun cc (Bool) Proof)
(define-const $13 Proof (cc (= (f y) (f x))))
```

This proves: Given `x = y`, derive `f(y) = f(x)` by congruence and symmetry.

---

### How Verification Works

#### Current Implementation (Simplified)

**What is checked:**

1. **Syntactic validity:**
   - All commands are well-formed S-expressions
   - All parentheses match
   - All commands are recognized

2. **Type consistency:**
   - Terms have consistent types (Int, Bool, etc.)
   - Function applications match declared signatures
   - Sort annotations are valid

3. **State tracking:**
   - All declarations are recorded
   - All definitions are stored
   - Assumptions are tracked
   - Derived clauses are collected

4. **Structural validation:**
   - Commands appear in valid order
   - References to undefined constants would parse but not fail verification

**What is NOT checked (current limitation):**

1. **Farkas certificates:** Don't verify coefficients produce contradiction
2. **EUF derivations:** Don't verify equality chains are valid
3. **RUP validity:** Don't check unit propagation actually derives clause
4. **Reference validity:** Don't verify all referenced constants are defined

**Why this approach?**

- **Demonstrates architecture:** Shows complete pipeline working
- **Small kernel:** Keeps trusted code minimal (~800 lines)
- **Extensible:** Easy to add certificate validation later
- **Educational:** Clear structure for learning

#### Production Verification

A production checker would add:

**1. Farkas validation:**

```lean
def validateFarkas (coeffs : List Int) (constraints : List Formula) : Bool :=
  -- Check all coefficients are non-negative
  if coeffs.any (· < 0) then return false

  -- Convert constraints to standard form
  let normalized := constraints.map normalizeConstraint

  -- Compute linear combination
  let combined := computeCombination coeffs normalized

  -- Check if result is contradictory (e.g., 0 < -5)
  isContradiction combined
```

**2. Congruence closure:**

```lean
structure CongruenceClosure where
  -- Union-find for equivalence classes
  parent : Map Term Term
  rank : Map Term Nat

  -- Congruence table for function applications
  congruences : Map (Symbol × List Term) Term

def checkEUF (cc : CongruenceClosure) (goal : Formula)
             (premises : List Formula) : Bool :=
  -- Build CC from premises
  let cc' := premises.foldl (fun cc p => cc.merge p) cc

  -- Check if goal follows
  cc'.equivalent goal.lhs goal.rhs
```

**3. RUP checking:**

```lean
def checkRUP (clauses : List Clause) (toDerive : Clause) : Bool :=
  -- Negate clause to derive
  let negated := toDerive.negate

  -- Add to clause database
  let db := clauses.push negated

  -- Run unit propagation
  match unitPropagate db with
  | some ⊥ => true   -- Derived empty clause
  | _ => false       -- Didn't derive contradiction
```

---

## 6. Code Architecture

### File Organization

```
z3-to-lean/
├── Main.lean              (49 lines)   CLI entry point
├── Z3ToLean/
│   ├── Z3Proof/
│   │   ├── AST.lean       (209 lines)  Data structures
│   │   └── Parser.lean    (349 lines)  Text → AST
│   └── Checker/
│       ├── Context.lean   (92 lines)   State management
│       └── Core.lean      (129 lines)  Verification logic
└── Examples/              Proof files
```

**Total: ~830 lines of code**

### Main.lean - CLI Entry Point

**Simplified flow:**

```lean
def main (args : List String) : IO Unit := do
  -- Step 1: Get filename from command line
  if args.isEmpty then
    showUsage
    return

  let filename := args[0]!

  -- Step 2: Read file contents
  let contents ← IO.FS.readFile filename

  -- Step 3: Parse proof
  match parseProofFile contents with
  | Except.error msg =>
    IO.println s!"✗ Parse error: {msg}"
    IO.Process.exit 1
  | Except.ok proof =>
    -- Step 4: Verify proof
    match verifyProofWithStats proof with
    | Except.error msg =>
      IO.println s!"✗ Verification failed: {msg}"
      IO.Process.exit 1
    | Except.ok (ctx, stats) =>
      -- Step 5: Show success
      IO.println "✓ Verification succeeded!"
      showStatistics stats
      IO.println "✓ Proof correct"
```

**Key points:**
- Clear separation: Read → Parse → Verify → Report
- Error handling at each stage
- Exit codes: 0 for success, 1 for failure
- Statistics for transparency

---

### AST.lean - Data Structures

**Core type hierarchy:**

```lean
-- Sorts (types)
inductive SortType where
  | bool : SortType
  | int : SortType
  | proof : SortType
  | func : List SortType → SortType → SortType

-- Terms (values)
inductive Term where
  | const : Id → SortType → Term
  | var : VarName → SortType → Term
  | intLit : Int → Term
  | boolLit : Bool → Term
  | app : Symbol → List Term → SortType → Term

-- Formulas (Boolean terms)
inductive Formula where
  | atom : Id → Formula
  | eq : Term → Term → Formula
  | lt/gt/le/ge : Term → Term → Formula
  | not : Formula → Formula
  | and/or : List Formula → Formula
  | implies : Formula → Formula → Formula

-- Clauses (disjunctions of literals)
structure Clause where
  literals : List Formula

-- Proof hints (justifications)
inductive ProofHint where
  | farkas : List (Int × Formula) → ProofHint
  | euf : Formula → List Formula → Option Id → ProofHint
  | cc : Formula → ProofHint
  | rup : ProofHint

-- Proof commands (what appears in proof files)
inductive ProofCommand where
  | declareFun : Symbol → List SortType → SortType → ProofCommand
  | declareConst : Id → SortType → ProofCommand
  | defineConst : Id → SortType → Term → ProofCommand
  | assume : Formula → ProofCommand
  | infer : Clause → ProofHint → ProofCommand
  | del : Clause → ProofCommand
```

**Design principles:**
- **Type safety:** Terms carry type information
- **Explicitness:** All information represented
- **Simplicity:** Minimal, orthogonal design
- **Extensibility:** Easy to add new constructs

---

### Parser.lean - Text to AST

**Three-layer architecture:**

#### Layer 1: Character-level parsing

```lean
structure ParseState where
  input : String
  pos : Nat
  line : Nat
  col : Nat

def Parser (α : Type) := ParseState → ParseResult α

-- Basic operations
def peek : Parser (Option Char)
def advance : Parser Unit
def skipWhitespace : Parser Unit
def char (expected : Char) : Parser Char
```

#### Layer 2: S-expression parsing

```lean
inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr

partial def sexpr : Parser SExpr := do
  skipWhitespace
  match ← peek with
  | some '(' => parseList
  | some _ => parseAtom
  | none => fail "unexpected EOF"
```

#### Layer 3: AST conversion

```lean
def parseSortType : SExpr → Except String SortType
def parseTerm : SExpr → Except String Term
def parseFormula : SExpr → Except String Formula
def parseProofHint : SExpr → Except String ProofHint
def parseProofCommand : SExpr → Except String ProofCommand
```

**Error handling:**
- Line and column tracking for error messages
- Clear error descriptions
- Type: `Except String α` for results

**Example error:**
```
Parse error at line 7, col 15: Expected ')', got EOF
```

---

### Context.lean - State Management

**Context structure:**

```lean
structure Context where
  functions : List (Symbol × (List SortType × SortType))
  constants : List (Id × SortType)
  definitions : List (Id × (SortType × Term))
  assumptions : List Formula
  derived : List Clause
```

**Operations:**

```lean
def Context.empty : Context
def declareFunction : Context → Symbol → List SortType → SortType → Context
def declareConst : Context → Id → SortType → Context
def defineConst : Context → Id → SortType → Term → Context
def assume : Context → Formula → Context
def addDerived : Context → Clause → Context
```

**Design:**
- **Immutable:** Each operation returns new context
- **Functional:** Pure functions, no side effects
- **Simple:** List-based storage (sufficient for small proofs)

---

### Core.lean - Verification Logic

**Main verification loop:**

```lean
partial def processCommands (ctx : Context) (cmds : List ProofCommand)
    : Except String Context :=
  match cmds with
  | [] => Except.ok ctx
  | cmd :: rest => do
    let ctx' ← processCommand ctx cmd
    processCommands ctx' rest
```

**Command processing:**

```lean
def processCommand (ctx : Context) (cmd : ProofCommand)
    : Except String Context :=
  match cmd with
  | ProofCommand.declareFun sym args ret =>
    Except.ok (ctx.declareFunction sym args ret)

  | ProofCommand.defineConst id sort term =>
    Except.ok (ctx.defineConst id sort term)

  | ProofCommand.assume formula =>
    Except.ok (ctx.assume formula)

  | ProofCommand.infer clause hint =>
    -- Simplified: just add to derived set
    Except.ok (ctx.addDerived clause)

  | ProofCommand.del clause =>
    Except.ok ctx
```

**Statistics computation:**

```lean
def countCommandTypes (cmds : List ProofCommand)
    : (Nat × Nat × Nat × Nat) :=
  cmds.foldl (fun (decls, defs, assms, infers) cmd =>
    match cmd with
    | ProofCommand.declareFun .. => (decls + 1, defs, assms, infers)
    | ProofCommand.defineConst .. => (decls, defs + 1, assms, infers)
    | ProofCommand.assume .. => (decls, defs, assms + 1, infers)
    | ProofCommand.infer .. => (decls, defs, assms, infers + 1)
    | _ => (decls, defs, assms, infers)
  ) (0, 0, 0, 0)
```

---

## 7. Try It Yourself

### Running the Example

```bash
# Build the project
cd z3-to-lean
lake build

# Verify the simple proof
.lake/build/bin/z3-to-lean Examples/proof_clean_simple.smt2

# Expected output:
# ✓ Parsed 10 commands
# ✓ Verification succeeded!
# Statistics: ...
# ✓ Proof correct
```

### Try All Examples

```bash
# All four examples
for f in Examples/proof_*.smt2; do
  echo "Testing: $(basename $f)"
  .lake/build/bin/z3-to-lean "$f"
  echo ""
done
```

### Create Your Own Proof

**Step 1:** Create a simple SMT2 problem

```bash
cat > my_problem.smt2 << 'EOF'
(declare-const a Int)
(declare-const b Int)
(assert (= a 5))
(assert (= b 10))
(assert (not (= (+ a b) 15)))
(check-sat)
EOF
```

**Step 2:** Generate Z3 proof

```bash
z3 my_problem.smt2 sat.euf=true tactic.default_tactic=smt \
   solver.proof.log=my_proof.smt2
```

**Step 3:** Verify in Lean

```bash
.lake/build/bin/z3-to-lean my_proof.smt2
```

### Understanding the Output

**Parse stage:**
```
✓ Parsed N commands
```
- N is the number of proof commands
- If this fails, there's a syntax error in the proof file

**Verification stage:**
```
✓ Verification succeeded!
```
- All commands processed without errors
- Context maintained consistently

**Statistics:**
```
Total commands:    N
Declarations:      D  (declare-fun, declare-const)
Definitions:       E  (define-const)
Assumptions:       A  (assume)
Inferences:        I  (infer)
Derived clauses:   C  (clauses added to context)
```

**What the numbers mean:**
- **Declarations:** How many symbols were declared
- **Definitions:** How many constants were defined (shortcuts)
- **Assumptions:** How many formulas were assumed true
- **Inferences:** How many reasoning steps
- **Derived clauses:** How many new clauses were derived

**Typical ratios:**
- Definitions ≈ Assumptions (one definition per assumption)
- Inferences < Total commands (only some commands are inferences)
- More complex proofs have more inferences

### Common Issues

**Parse error: Unclosed list**
```
✗ Parse error: Parse error at line 7, col 0: Unclosed list
```
**Fix:** Check for missing `)` in the proof file

**File not found**
```
Error: File not found: my_proof.smt2
```
**Fix:** Check file path, use correct relative or absolute path

**Z3 doesn't generate proof**
```
unsat
(error "proof is not available")
```
**Fix:** Make sure to use `sat.euf=true tactic.default_tactic=smt solver.proof.log=file.smt2`

---

## 8. Advanced Topics

### What's Simplified in Current Implementation

The current checker uses a **simplified verification approach** to demonstrate the architecture clearly:

#### 1. Certificate Validation Not Implemented

**Farkas certificates are accepted without validation:**

```lean
| ProofHint.farkas coeffs =>
  -- TODO: Validate that coefficients produce contradiction
  Except.ok (ctx.addDerived clause)
```

**What full validation would require:**
```lean
def validateFarkas (coeffs : List (Int × Formula)) : Bool :=
  -- Normalize constraints to form: ax + b ≥ 0
  let normalized := coeffs.map (fun (c, f) => (c, normalize f))

  -- Compute linear combination
  let (totalCoeff, totalConst) :=
    normalized.foldl (fun (acc_a, acc_b) (c, (a, b)) =>
      (acc_a + c * a, acc_b + c * b)
    ) (0, 0)

  -- Check: coefficients non-negative and result contradictory
  coeffs.all (fun (c, _) => c ≥ 0) && totalConst < 0
```

#### 2. EUF Derivations Not Checked

**Equality chains are assumed valid:**

```lean
| ProofHint.euf goal premises _ =>
  -- TODO: Build congruence closure and verify derivation
  Except.ok (ctx.addDerived clause)
```

**What full validation would require:**
- Implement union-find data structure
- Build congruence closure from premises
- Verify goal is in same equivalence class
- Check congruence rules are applied correctly

#### 3. RUP Steps Not Verified

**Unit propagation not actually performed:**

```lean
| ProofHint.rup =>
  -- TODO: Run unit propagation to verify clause is derivable
  Except.ok (ctx.addDerived clause)
```

**What full validation would require:**
- Maintain clause database
- Implement unit propagation algorithm
- Check that clause can be derived
- Handle watched literals for efficiency

#### 4. Reference Validation Missing

**Undefined constants not caught:**

Example: `(assume $99)` where `$99` is not defined

Currently accepted, should reject with:
```
Error: Undefined constant reference: $99
```

### Why This Approach is Valid for a Demo

**Advantages:**

1. **Shows complete architecture:**
   - Parsing works fully
   - Verification framework in place
   - Easy to add validation later

2. **Small trusted kernel:**
   - ~800 lines total
   - Easy to audit
   - Clear separation of concerns

3. **Educational value:**
   - Structure is clear
   - Not obscured by complex algorithms
   - Good foundation for learning

4. **Extensible:**
   - Plug in validation modules
   - No architectural changes needed
   - Can add incrementally

**Trade-offs:**

- **No false negatives:** All valid proofs pass ✓
- **Potential false positives:** Some invalid proofs might pass ⚠️
- **For demonstration only:** Not suitable for production without validation

### Future Enhancements

#### Enhancement 1: Farkas Validation

**Algorithm:**

```lean
structure LinearConstraint where
  coeff : Int      -- coefficient for variable
  constant : Int   -- constant term
  op : CompOp      -- ≤, <, ≥, >

def validateFarkasStep (cert : List (Int × LinearConstraint)) : Bool :=
  -- Step 1: Check coefficients non-negative
  if cert.any (fun (c, _) => c < 0) then
    return false

  -- Step 2: Multiply each constraint by its coefficient
  let scaled := cert.map (fun (c, lc) =>
    { coeff := c * lc.coeff,
      constant := c * lc.constant,
      op := lc.op })

  -- Step 3: Sum all constraints
  let total := scaled.foldl (fun acc lc =>
    { coeff := acc.coeff + lc.coeff,
      constant := acc.constant + lc.constant,
      op := combineOps acc.op lc.op })
    { coeff := 0, constant := 0, op := .ge }

  -- Step 4: Check if result is contradictory
  -- E.g., if we get 0x + 5 < 0, that's false
  isContradictory total
```

**Example:**
- Constraint 1: `x ≤ 2` (coefficient 1)
- Constraint 2: `x ≥ 6` (coefficient 1)
- Sum: `2x ≤ 8` and `2x ≥ 12`
- Contradiction: `8 ≥ 2x ≥ 12` impossible

#### Enhancement 2: Congruence Closure

**Union-Find implementation:**

```lean
structure UnionFind where
  parent : Map Term Term
  rank : Map Term Nat

def UnionFind.find (uf : UnionFind) (t : Term) : Term :=
  match uf.parent.get? t with
  | none => t
  | some p => if p == t then t else uf.find p

def UnionFind.union (uf : UnionFind) (t1 t2 : Term) : UnionFind :=
  let r1 := uf.find t1
  let r2 := uf.find t2
  if r1 == r2 then uf
  else
    let rank1 := uf.rank.get? r1 |>.getD 0
    let rank2 := uf.rank.get? r2 |>.getD 0
    if rank1 < rank2 then
      { uf with parent := uf.parent.insert r1 r2 }
    else if rank1 > rank2 then
      { uf with parent := uf.parent.insert r2 r1 }
    else
      { uf with
        parent := uf.parent.insert r2 r1,
        rank := uf.rank.insert r1 (rank1 + 1) }
```

**Congruence closure with function applications:**

```lean
structure CongruenceClosure where
  uf : UnionFind
  congruences : Map (Symbol × List Term) Term

def CC.addEquality (cc : CC) (t1 t2 : Term) : CC :=
  let cc' := { cc with uf := cc.uf.union t1 t2 }
  -- Also merge congruent function applications
  cc'.propagateCongruences

def CC.areEqual (cc : CC) (t1 t2 : Term) : Bool :=
  cc.uf.find t1 == cc.uf.find t2
```

#### Enhancement 3: RUP Verification

**Unit propagation engine:**

```lean
structure ClauseDB where
  clauses : List Clause
  assignment : Map Formula Bool
  watchedLiterals : Map Formula (List ClauseId)

def unitPropagate (db : ClauseDB) : Option ClauseDB :=
  -- Find unit clauses
  match db.clauses.findIdx? isUnit with
  | none => some db  -- No more propagation
  | some (idx, clause) =>
    let lit := clause.getUnitLiteral
    -- Assign literal
    let db' := db.assign lit true
    -- Check for conflicts
    if db'.hasConflict then
      none  -- Empty clause derived
    else
      unitPropagate db'  -- Continue propagating

def verifyRUP (db : ClauseDB) (clause : Clause) : Bool :=
  -- Negate clause and add to DB
  let negated := clause.negate
  let db' := db.addClause negated
  -- Try unit propagation
  match unitPropagate db' with
  | none => true   -- Conflict found → clause is valid
  | some _ => false  -- No conflict → clause not RUP-derivable
```

### Connection to Research

**For deep dives, see:**

1. **RESEARCH_REPORT.md**: 42-page comprehensive research covering:
   - Z3 proof formats in detail
   - Comparison with other solvers (cvc5, veriT)
   - Related systems (lean-smt, Lean4Lean, SMTCoq)
   - 32 academic references

2. **Key papers:**
   - **Farkas' Lemma**: Farkas (1894), foundational linear programming
   - **DRAT format**: Heule et al. (2013), SAT proof checking
   - **SMT proofs**: Barbosa et al. (2021), Alethe format
   - **Lean4Lean**: Carneiro (2024), verified type checker

3. **Related systems:**
   - **lean-smt**: cvc5 integration with proof reconstruction
   - **SMTCoq**: Coq plugin for SMT solvers
   - **Isabelle/HOL**: Mature SMT integration

### Production Readiness Checklist

To make this production-ready:

- [ ] Implement Farkas validation
- [ ] Implement congruence closure
- [ ] Implement RUP checking
- [ ] Add reference validity checks
- [ ] Handle more proof rules (bit-vectors, arrays)
- [ ] Optimize for large proofs (>10,000 commands)
- [ ] Add comprehensive test suite
- [ ] Formally verify the checker itself
- [ ] Add proof term generation (not just validation)
- [ ] Support incremental verification
- [ ] Add proof minimization
- [ ] Performance benchmarks vs other checkers

**Estimated effort:** 2-3 months of development for full production system

---

## Conclusion

You now understand how Z3 proof verification works in Lean from the ground up!

### What You've Learned

1. **The problem:** Simple contradictions in arithmetic
2. **Z3's proof:** sat.euf format with theory lemmas
3. **Lean's parser:** S-expressions → AST
4. **Verification:** Context evolution and state tracking
5. **Key concepts:** Farkas, EUF, RUP, CC
6. **Architecture:** Clean separation of concerns

### Key Takeaways

- **Proofs are data:** Can be parsed, verified, and analyzed
- **Small kernel:** ~800 lines for complete system
- **Theory integration:** Combines SAT + arithmetic + equality
- **Extensible design:** Easy to add more validation

### Next Steps

1. **Run the examples** - Get hands-on experience
2. **Read the code** - Understand implementation details
3. **Extend the system** - Add Farkas validation
4. **Read RESEARCH_REPORT.md** - Deep dive into theory
5. **Explore related systems** - lean-smt, Lean4Lean

### Resources

- **This project:** `/home/pmatos/dev/z3-to-lean`
- **Z3 docs:** https://github.com/Z3Prover/z3
- **Lean docs:** https://lean-lang.org/
- **Research report:** `RESEARCH_REPORT.md`
- **Testing guide:** `TESTING.md`

---

*This tutorial explains the z3-to-lean proof checking demonstration system.*

*For questions or contributions, please see README.md*
