import GobraCompat.Contract

/-!
# Ring-0 annotation parser (spike stage 1.5)

Parses the text of Gobra `//@` clauses into the `Contract.lean` fragment —
the automation of the transcription step, so the contract appearing in
theorems is DERIVED from the annotation strings rather than hand-written.
Authority-in-Lean per the gobra-json-schema precedent: the frontend will
ship raw clause strings (stage-2 `"specs"` wire key); everything from
text to meaning happens here, fail-closed.

Grammar (ring 0; anything outside it is a parse error, never a guess):

    clause    := 'requires' assertion | 'ensures' assertion
               | 'invariant' assertion | 'decreases' expr?
    assertion := conj ('==>' assertion)?          -- right-assoc
    conj      := cmp ('&&' conj)?                 -- right-assoc
    cmp       := expr ('<=' | '<' | '==') expr
    expr      := term (('+' | '-') term)*         -- left-assoc
    term      := factor (('*' | '/') factor)*     -- left-assoc
    factor    := intLit | ident | '(' expr ')'

Recorded ring-0 limitations (fail closed, lift in ring 1): no
parenthesized assertions, no quantifiers/`old()`/pure-function calls, no
`%`, single-token identifiers only.

Totality: explicit fuel everywhere (initialized to input length) — no
`partial`, no well-founded-recursion obligations.
-/

namespace GobraCompat

inductive Tok where
  | int (v : Int)
  | ident (s : String)
  | plus | minus | star | slash
  | lparen | rparen
  | le | lt | eqeq | andand | implies
deriving Repr, DecidableEq

namespace Parser

def isIdentChar (c : Char) : Bool := c.isAlphanum || c = '_'

/-- Digit-list to `Nat` by plain fold (NOT `String.toNat?`, whose
byte-level extern internals do not kernel-reduce — the round-trip
theorem is checked by `decide +kernel`). -/
def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Tokenizer. Longest-match on operators (`==>` before `==`, `<=`
before `<`). Fuel-total: fuel bounds the input length. -/
def tokenizeAux : Nat → List Char → Except String (List Tok)
  | 0, [] => .ok []
  | 0, _ => .error "tokenizer out of fuel"
  | _ + 1, [] => .ok []
  | fuel + 1, c :: cs =>
    if c = ' ' || c = '\t' then tokenizeAux fuel cs
    else if c = '(' then (Tok.lparen :: ·) <$> tokenizeAux fuel cs
    else if c = ')' then (Tok.rparen :: ·) <$> tokenizeAux fuel cs
    else if c = '+' then (Tok.plus :: ·) <$> tokenizeAux fuel cs
    else if c = '-' then (Tok.minus :: ·) <$> tokenizeAux fuel cs
    else if c = '*' then (Tok.star :: ·) <$> tokenizeAux fuel cs
    else if c = '/' then (Tok.slash :: ·) <$> tokenizeAux fuel cs
    else if c = '<' then
      match cs with
      | '=' :: rest => (Tok.le :: ·) <$> tokenizeAux fuel rest
      | rest => (Tok.lt :: ·) <$> tokenizeAux fuel rest
    else if c = '=' then
      match cs with
      | '=' :: '>' :: rest => (Tok.implies :: ·) <$> tokenizeAux fuel rest
      | '=' :: rest => (Tok.eqeq :: ·) <$> tokenizeAux fuel rest
      | _ => .error "lone '='"
    else if c = '&' then
      match cs with
      | '&' :: rest => (Tok.andand :: ·) <$> tokenizeAux fuel rest
      | _ => .error "lone '&'"
    else if c.isDigit then
      let ds := c :: cs.takeWhile Char.isDigit
      let rest := cs.dropWhile Char.isDigit
      (Tok.int (Int.ofNat (digitsToNat ds)) :: ·) <$> tokenizeAux fuel rest
    else if c.isAlpha || c = '_' then
      let id := c :: cs.takeWhile isIdentChar
      let rest := cs.dropWhile isIdentChar
      (Tok.ident (String.mk id) :: ·) <$> tokenizeAux fuel rest
    else .error s!"unexpected character '{c}'"

def tokenize (s : String) : Except String (List Tok) :=
  tokenizeAux s.length s.toList

abbrev ParserM (α : Type) := List Tok → Except String (α × List Tok)

mutual
  def parseFactor : Nat → ParserM GExpr
    | 0, _ => .error "out of fuel"
    | _ + 1, .int v :: rest => .ok (.lit v, rest)
    | _ + 1, .ident s :: rest => .ok (.evar s, rest)
    | fuel + 1, .lparen :: rest => do
      let (e, rest) ← parseExpr fuel rest
      match rest with
      | .rparen :: rest => .ok (e, rest)
      | _ => .error "expected ')'"
    | _ + 1, _ => .error "expected integer, identifier, or '('"

  /-- `term := factor (('*'|'/') factor)*`, left-assoc via accumulator. -/
  def parseTermLoop : Nat → GExpr → ParserM GExpr
    | 0, _, _ => .error "out of fuel"
    | fuel + 1, acc, .star :: rest => do
      let (r, rest) ← parseFactor fuel rest
      parseTermLoop fuel (.mul acc r) rest
    | fuel + 1, acc, .slash :: rest => do
      let (r, rest) ← parseFactor fuel rest
      parseTermLoop fuel (.div acc r) rest
    | _ + 1, acc, toks => .ok (acc, toks)

  def parseTerm : Nat → ParserM GExpr
    | 0, _ => .error "out of fuel"
    | fuel + 1, toks => do
      let (l, rest) ← parseFactor fuel toks
      parseTermLoop fuel l rest

  /-- `expr := term (('+'|'-') term)*`, left-assoc via accumulator. -/
  def parseExprLoop : Nat → GExpr → ParserM GExpr
    | 0, _, _ => .error "out of fuel"
    | fuel + 1, acc, .plus :: rest => do
      let (r, rest) ← parseTerm fuel rest
      parseExprLoop fuel (.add acc r) rest
    | fuel + 1, acc, .minus :: rest => do
      let (r, rest) ← parseTerm fuel rest
      parseExprLoop fuel (.sub acc r) rest
    | _ + 1, acc, toks => .ok (acc, toks)

  def parseExpr : Nat → ParserM GExpr
    | 0, _ => .error "out of fuel"
    | fuel + 1, toks => do
      let (l, rest) ← parseTerm fuel toks
      parseExprLoop fuel l rest
end

def parseCmp : Nat → ParserM GAssertion
  | 0, _ => .error "out of fuel"
  | fuel + 1, toks => do
    let (l, rest) ← parseExpr fuel toks
    match rest with
    | .le :: rest => do
      let (r, rest) ← parseExpr fuel rest
      .ok (.le l r, rest)
    | .lt :: rest => do
      let (r, rest) ← parseExpr fuel rest
      .ok (.lt l r, rest)
    | .eqeq :: rest => do
      let (r, rest) ← parseExpr fuel rest
      .ok (.eq l r, rest)
    | _ => .error "expected comparison operator"

mutual
  /-- `conj := cmp ('&&' conj)?`, right-assoc. -/
  def parseConj : Nat → ParserM GAssertion
    | 0, _ => .error "out of fuel"
    | fuel + 1, toks => do
      let (l, rest) ← parseCmp fuel toks
      match rest with
      | .andand :: rest => do
        let (r, rest) ← parseConj fuel rest
        .ok (.conj l r, rest)
      | _ => .ok (l, rest)

  /-- `assertion := conj ('==>' assertion)?`, right-assoc. -/
  def parseAssertion : Nat → ParserM GAssertion
    | 0, _ => .error "out of fuel"
    | fuel + 1, toks => do
      let (l, rest) ← parseConj fuel toks
      match rest with
      | .implies :: rest => do
        let (r, rest) ← parseAssertion fuel rest
        .ok (.impl l r, rest)
      | _ => .ok (l, rest)
end

end Parser

/-- A parsed clause. -/
inductive SpecClause where
  | requiresC (a : GAssertion)
  | ensuresC (a : GAssertion)
  | invariantC (a : GAssertion)
  | decreasesC (measure : Option GExpr)
deriving Repr, DecidableEq

/-- Parse one clause's text (the content of one `//@` comment). -/
def parseClause (s : String) : Except String SpecClause := do
  let toks ← Parser.tokenize s
  let fuel := toks.length + 1
  match toks with
  | .ident "requires" :: rest => do
    let (a, rest) ← Parser.parseAssertion fuel rest
    if rest.isEmpty then .ok (.requiresC a) else .error "trailing tokens"
  | .ident "ensures" :: rest => do
    let (a, rest) ← Parser.parseAssertion fuel rest
    if rest.isEmpty then .ok (.ensuresC a) else .error "trailing tokens"
  | .ident "invariant" :: rest => do
    let (a, rest) ← Parser.parseAssertion fuel rest
    if rest.isEmpty then .ok (.invariantC a) else .error "trailing tokens"
  | [.ident "decreases"] => .ok (.decreasesC none)
  | .ident "decreases" :: rest => do
    let (e, rest) ← Parser.parseExpr fuel rest
    if rest.isEmpty then .ok (.decreasesC (some e)) else .error "trailing tokens"
  | _ => .error "expected requires/ensures/invariant/decreases"

/-- Assemble clauses into a contract (clause order preserved per kind). -/
def parseContract (clauses : List String) : Except String GobraContract := do
  let parsed ← clauses.mapM parseClause
  .ok <| parsed.foldl (init := (⟨[], [], [], false⟩ : GobraContract))
    fun ct c =>
      match c with
      | .requiresC a => { ct with requires := ct.requires ++ [a] }
      | .ensuresC a => { ct with ensures := ct.ensures ++ [a] }
      | .invariantC a => { ct with loopInvariants := ct.loopInvariants ++ [a] }
      | .decreasesC _ => { ct with terminates := true }

end GobraCompat
