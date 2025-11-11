/-
Parser for Z3 sat.euf proof format

This module implements a parser for Z3's sat.euf proof format, which is based on
SMTLIB2 syntax with extensions for proof terms.
-/

import Z3ToLean.Z3Proof.AST

namespace Z3Proof.Parser

open Z3Proof

-- S-expression representation (intermediate format)
inductive SExpr where
  | atom : String → SExpr
  | list : List SExpr → SExpr
  deriving Repr, BEq, Inhabited

-- Parser state with position tracking
structure ParseState where
  input : String
  pos : Nat
  line : Nat
  col : Nat
  deriving Repr

-- Parser result
inductive ParseResult (α : Type) where
  | ok : α → ParseState → ParseResult α
  | error : String → Nat → Nat → ParseResult α
  deriving Repr

-- Parser monad
def Parser (α : Type) := ParseState → ParseResult α

-- Basic parser combinators
def Parser.pure (a : α) : Parser α :=
  fun s => ParseResult.ok a s

def Parser.bind {α β : Type} (p : Parser α) (f : α → Parser β) : Parser β :=
  fun s => match p s with
    | ParseResult.ok a s' => f a s'
    | ParseResult.error msg line col => ParseResult.error msg line col

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

def Parser.fail {α : Type} (msg : String) : Parser α :=
  fun s => ParseResult.error msg s.line s.col

-- Character-level operations
def Parser.peek : Parser (Option Char) :=
  fun s =>
    if s.pos < s.input.length then
      ParseResult.ok (some (s.input.get ⟨s.pos⟩)) s
    else
      ParseResult.ok none s

def Parser.advance : Parser Unit :=
  fun s =>
    if s.pos < s.input.length then
      let c := s.input.get ⟨s.pos⟩
      let s' := if c == '\n' then
        { s with pos := s.pos + 1, line := s.line + 1, col := 0 }
      else
        { s with pos := s.pos + 1, col := s.col + 1 }
      ParseResult.ok () s'
    else
      ParseResult.ok () s

-- Skip whitespace and comments
partial def Parser.skipWhitespace : Parser Unit := do
  match ← Parser.peek with
  | none => return ()
  | some c =>
    if c.isWhitespace then
      _ ← Parser.advance
      Parser.skipWhitespace
    else if c == ';' then
      -- Skip comment until end of line
      _ ← Parser.advance
      let rec skipToNewline : Parser Unit := do
        match ← Parser.peek with
        | none => return ()
        | some '\n' => Parser.advance
        | some _ => do
          _ ← Parser.advance
          skipToNewline
      _ ← skipToNewline
      Parser.skipWhitespace
    else
      return ()

-- Parse a specific character
def Parser.char (expected : Char) : Parser Char := do
  _ ← Parser.skipWhitespace
  match ← Parser.peek with
  | none => Parser.fail s!"Expected '{expected}', got end of input"
  | some c =>
    if c == expected then
      _ ← Parser.advance
      return c
    else
      Parser.fail s!"Expected '{expected}', got '{c}'"

-- Parse an atom (symbol or literal)
partial def Parser.atom : Parser String := do
  _ ← Parser.skipWhitespace
  let rec collectChars (acc : String) : Parser String := do
    match ← Parser.peek with
    | none => return acc
    | some c =>
      if c.isWhitespace || c == '(' || c == ')' then
        return acc
      else
        _ ← Parser.advance
        collectChars (acc.push c)

  match ← Parser.peek with
  | none => Parser.fail "Expected atom, got end of input"
  | some c =>
    if c == '(' || c == ')' then
      Parser.fail s!"Expected atom, got '{c}'"
    else
      collectChars ""

-- Parse S-expression
partial def Parser.sexpr : Parser SExpr := do
  _ ← Parser.skipWhitespace
  match ← Parser.peek with
  | none => Parser.fail "Expected s-expression, got end of input"
  | some '(' => do
    _ ← Parser.char '('
    let rec parseList (acc : List SExpr) : Parser (List SExpr) := do
      _ ← Parser.skipWhitespace
      match ← Parser.peek with
      | none => Parser.fail "Unclosed list"
      | some ')' => return acc.reverse
      | some _ => do
        let elem ← Parser.sexpr
        parseList (elem :: acc)
    let elems ← parseList []
    _ ← Parser.char ')'
    return SExpr.list elems
  | some _ => do
    let a ← Parser.atom
    return SExpr.atom a

-- Parse multiple S-expressions
partial def Parser.many (p : Parser α) : Parser (List α) := do
  _ ← Parser.skipWhitespace
  match ← Parser.peek with
  | none => return []
  | some _ => do
    let x ← p
    let xs ← Parser.many p
    return x :: xs

-- Run parser
def runParser {α : Type} (p : Parser α) (input : String) : Except String α :=
  let state : ParseState := { input := input, pos := 0, line := 1, col := 0 }
  match p state with
  | ParseResult.ok result _ => Except.ok result
  | ParseResult.error msg line col => Except.error s!"Parse error at line {line}, col {col}: {msg}"

-- Convert S-expression to AST

-- Helper to get list from SExpr
def SExpr.asList : SExpr → Except String (List SExpr)
  | SExpr.list xs => Except.ok xs
  | SExpr.atom a => Except.error s!"Expected list, got atom '{a}'"

-- Helper to get atom from SExpr
def SExpr.asAtom : SExpr → Except String String
  | SExpr.atom a => Except.ok a
  | SExpr.list _ => Except.error "Expected atom, got list"

-- Parse integer from string
def parseIntLit (s : String) : Except String Int :=
  match s.toInt? with
  | some n => Except.ok n
  | none => Except.error s!"Invalid integer literal: {s}"

-- Parse boolean from string
def parseBoolLit (s : String) : Except String Bool :=
  if s == "true" then Except.ok true
  else if s == "false" then Except.ok false
  else Except.error s!"Invalid boolean literal: {s}"

-- Parse sort type
partial def parseSortType : SExpr → Except String SortType
  | SExpr.atom "Bool" => Except.ok SortType.bool
  | SExpr.atom "Int" => Except.ok SortType.int
  | SExpr.atom "Proof" => Except.ok SortType.proof
  | SExpr.list (SExpr.atom "→" :: args) => do
    if args.length < 2 then
      Except.error "Function type needs at least 2 arguments"
    let argSorts ← (args.dropLast).mapM parseSortType
    match args.getLast? with
    | some retSexpr => do
      let retSort ← parseSortType retSexpr
      Except.ok (SortType.func argSorts retSort)
    | none => Except.error "Function type missing return type"
  | other => Except.error s!"Invalid sort type: {repr other}"

-- Infer sort type for common operators
def inferOperatorSort (sym : Symbol) : SortType :=
  match sym with
  -- Comparison operators return Bool
  | "=" | "<" | ">" | "<=" | ">=" | "distinct" => SortType.bool
  -- Logical operators return Bool
  | "not" | "and" | "or" | "=>" | "iff" | "xor" | "ite" => SortType.bool
  -- Arithmetic operators return Int
  | "+" | "-" | "*" | "div" | "mod" | "abs" => SortType.int
  -- Proof constructors return Proof
  | "farkas" | "cc" | "euf" | "rup" => SortType.proof
  -- Default to Int for unknown operators
  | _ => SortType.int

-- Parse term
partial def parseTerm : SExpr → Except String Term
  | SExpr.atom a =>
    -- Try to parse as integer literal
    match parseIntLit a with
    | Except.ok n => Except.ok (Term.intLit n)
    | Except.error _ =>
      -- Try to parse as boolean literal
      match parseBoolLit a with
      | Except.ok b => Except.ok (Term.boolLit b)
      | Except.error _ =>
        -- Treat as variable or constant reference
        -- Use Bool as default since most constants in proofs are boolean
        Except.ok (Term.const a SortType.bool)
  | SExpr.list [] => Except.error "Empty list is not a valid term"
  | SExpr.list (SExpr.atom sym :: args) => do
    let termArgs ← args.mapM parseTerm
    -- Infer sort from operator
    let sort := inferOperatorSort sym
    Except.ok (Term.app sym termArgs sort)
  | SExpr.list _ => Except.error "Invalid term: list must start with symbol"

-- Parse formula
partial def parseFormula : SExpr → Except String Formula
  | SExpr.atom a => Except.ok (Formula.atom a)
  | SExpr.list [SExpr.atom "=", t1, t2] => do
    let term1 ← parseTerm t1
    let term2 ← parseTerm t2
    Except.ok (Formula.eq term1 term2)
  | SExpr.list [SExpr.atom ">", t1, t2] => do
    let term1 ← parseTerm t1
    let term2 ← parseTerm t2
    Except.ok (Formula.gt term1 term2)
  | SExpr.list [SExpr.atom "<", t1, t2] => do
    let term1 ← parseTerm t1
    let term2 ← parseTerm t2
    Except.ok (Formula.lt term1 term2)
  | SExpr.list [SExpr.atom ">=", t1, t2] => do
    let term1 ← parseTerm t1
    let term2 ← parseTerm t2
    Except.ok (Formula.ge term1 term2)
  | SExpr.list [SExpr.atom "<=", t1, t2] => do
    let term1 ← parseTerm t1
    let term2 ← parseTerm t2
    Except.ok (Formula.le term1 term2)
  | SExpr.list [SExpr.atom "not", f] => do
    let formula ← parseFormula f
    Except.ok (Formula.not formula)
  | SExpr.list (SExpr.atom "and" :: fs) => do
    let formulas ← fs.mapM parseFormula
    Except.ok (Formula.and formulas)
  | SExpr.list (SExpr.atom "or" :: fs) => do
    let formulas ← fs.mapM parseFormula
    Except.ok (Formula.or formulas)
  | SExpr.list [SExpr.atom "=>", f1, f2] => do
    let formula1 ← parseFormula f1
    let formula2 ← parseFormula f2
    Except.ok (Formula.implies formula1 formula2)
  | other => Except.error s!"Invalid formula: {repr other}"

-- Parse clause (currently just wraps formula)
def parseClause (sexpr : SExpr) : Except String Clause := do
  match sexpr with
  | SExpr.list (SExpr.atom "cl" :: lits) => do
    let formulas ← lits.mapM parseFormula
    Except.ok { literals := formulas }
  | _ => do
    -- Single formula becomes single-literal clause
    let f ← parseFormula sexpr
    Except.ok { literals := [f] }

-- Parse proof hint
partial def parseProofHint : SExpr → Except String ProofHint
  | SExpr.atom "rup" => Except.ok ProofHint.rup
  | SExpr.list [SExpr.atom "farkas", coeffsAndFormulas] => do
    -- farkas takes pairs of (coeff, formula)
    match coeffsAndFormulas with
    | SExpr.list pairs => do
      let parsePair := fun sexpr => match sexpr with
        | SExpr.list [coeff, formula] => do
          let c ← coeff.asAtom
          let n ← parseIntLit c
          let f ← parseFormula formula
          Except.ok (n, f)
        | _ => Except.error "Farkas pair must be (coeff formula)"
      pairs.mapM parsePair >>= fun ps => Except.ok (ProofHint.farkas ps)
    | _ => Except.error "Farkas must have list of pairs"
  | SExpr.list (SExpr.atom "euf" :: args) => do
    if args.length < 2 then
      Except.error "EUF needs at least goal and premises"
    match args.head? with
    | none => Except.error "EUF missing goal"
    | some goalSexpr => do
      let goal ← parseFormula goalSexpr
      let premises ← args.tail.mapM parseFormula
      Except.ok (ProofHint.euf goal premises none)
  | SExpr.list [SExpr.atom "cc", f] => do
    let formula ← parseFormula f
    Except.ok (ProofHint.cc formula)
  | other => Except.error s!"Invalid proof hint: {repr other}"

-- Parse proof command
partial def parseProofCommand : SExpr → Except String ProofCommand
  | SExpr.list [SExpr.atom "declare-fun", SExpr.atom sym, SExpr.list args, ret] => do
    let argSorts ← args.mapM parseSortType
    let retSort ← parseSortType ret
    Except.ok (ProofCommand.declareFun sym argSorts retSort)
  | SExpr.list [SExpr.atom "declare-const", SExpr.atom id, sort] => do
    let sortType ← parseSortType sort
    Except.ok (ProofCommand.declareConst id sortType)
  | SExpr.list [SExpr.atom "define-const", SExpr.atom id, sort, term] => do
    let sortType ← parseSortType sort
    let termVal ← parseTerm term
    Except.ok (ProofCommand.defineConst id sortType termVal)
  | SExpr.list [SExpr.atom "define-fun", SExpr.atom sym, SExpr.list params, ret, body] => do
    -- Parse parameters: each is (name sort)
    let parseParam : SExpr → Except String (VarName × SortType) := fun sexpr =>
      match sexpr with
      | SExpr.list [SExpr.atom name, sort] => do
          let sortType ← parseSortType sort
          Except.ok (name, sortType)
      | _ => Except.error s!"Invalid parameter format: {repr sexpr}"
    let paramList ← params.mapM parseParam
    let retSort ← parseSortType ret
    let bodyTerm ← parseTerm body
    Except.ok (ProofCommand.defineFun sym paramList retSort bodyTerm)
  | SExpr.list [SExpr.atom "assume", formula] => do
    let f ← parseFormula formula
    Except.ok (ProofCommand.assume f)
  | SExpr.list (SExpr.atom "infer" :: rest) => do
    -- infer can have multiple formulas followed by a proof term
    -- The last element is the proof term (can be an atom like "rup" or a reference like "$16")
    if rest.isEmpty then
      Except.error "infer needs at least a proof term"
    -- For now, treat all non-last elements as clause literals, last as proof hint
    let literals := rest.dropLast
    let proofTerm := rest.getLast!
    -- Try to parse as proof hint, or treat as reference
    let hint ← match proofTerm with
      | SExpr.atom "rup" => Except.ok ProofHint.rup
      | SExpr.atom ref => Except.ok (ProofHint.ref ref)  -- Proof term reference
      | _ => parseProofHint proofTerm
    let formulas ← literals.mapM parseFormula
    Except.ok (ProofCommand.infer { literals := formulas } hint)
  | SExpr.list [SExpr.atom "del", clause] => do
    let c ← parseClause clause
    Except.ok (ProofCommand.del c)
  | other => Except.error s!"Invalid proof command: {repr other}"

-- Parse complete proof file
def parseProofFile (input : String) : Except String Proof := do
  let sexprs ← runParser (Parser.many Parser.sexpr) input
  let commands ← sexprs.mapM parseProofCommand
  Except.ok { commands := commands }

end Z3Proof.Parser
