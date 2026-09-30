import GoLean.NativeDeclaration
import GoLean.StrictJson
import GoLean.GoCore.Syntax
import GoLean.GoCore.Unseq
import GoLean.GoCore.Locals

/-!
# Native frontend lowering

Decodes the native wire schema (`golean-native-v2` since G-P S2, 2026-09-28 — a
`golean-native-v1` wire refuses by name; emitted by
`tools/nativefrontend`) directly into a clean `GoCore.Program`, failing closed
on anything not yet modeled. This is the native analogue of `GobraToIR`, but
because `go/types` resolved names and types up front, the lowering is a direct
structural map with no recovery heuristics.

The wire is a typed Go AST (Go's grammar with resolved types attached). The
GoCore-specific desugaring lives here and is inspectable:

- `x := e` / `var x T = e`  →  `initialization` then `assign`
- `return e`                →  assign the result local, then `returnStmt`
- `for init; c; post {..}`  →  `block[init; while c (block[body; post])]`
- `if init; c {..} else ..` →  `block[init; ifThenElse c ..]`
- `x += e` / `x++`          →  `assign x (op x e)`

This module is intentionally incremental: each new Go construct adds one wire
tag and one lowering case. Unmodeled constructs are explicit adapter errors.
-/

namespace GoLean.NativeToIR

open Lean GoLean GoLean.GoCore
open GoLean.StrictJson

/-- One in-scope declaration of the R1 environment (B6, 2026-09-30): the
lowering's spelling (the wire's `id`/`name` — a shadow rename or capture pointer
where the frontend renamed), its numeric declaration id, and its declared type. -/
private structure LocalDecl where
  name : String
  id : VarId
  typ : Ty
  deriving Repr, BEq, Inhabited

private def LocalDecl.param (d : LocalDecl) : Param := { id := d.id, typ := d.typ }

/-- The lowering monad: failure plus a reader carrying the PROGRAM's
package-level-variable count (audit response 2026-08-05, C1): every
`globaladdr` gid must be strictly below it, checked AT THE DECODE
BOUNDARY — the one-boundary-constructor collision-check rule. Without
the check a malformed wire's dangling gid did NOT go stuck as
originally claimed: `storeLoc` at an unseeded location used to
MATERIALIZE a cell, so an out-of-range gid aliased onto whatever the
allocator handed out next (e.g. the subject's result cell) and
produced a silent wrong answer. Since BUG-085 (2026-09-03) `storeLoc`
refuses `.internal` there, so the core now fails closed on its own;
this check and the driver-level `StateWf` assert after seeding
(`runProgramM`/`enumSetup`) remain as the earlier, louder nets.

The decode context: the global count (arms the `globaladdr` bound
check) and the type-name → table-index map (C2: `Ty.defined` is an INDEX
into the dependency-ordered type table; `named` wire references resolve
through this map, built from the wire's `types` names — plus the two
machine-reserved entries — BEFORE any body decodes). -/
private structure LowerCtx where
  nGlobals : Nat
  typeIdx : Std.HashMap String TypeIdx
  /-- B6 (2026-09-30): the enclosing function's WIRE name table — the frontend's
  source entries, indexed by the `local` indices its nodes carry; the decoder's
  `$`-temporaries are interned after them (`LowerSt`). Empty outside a function. -/
  table : Array LocalName := #[]
  /-- Stage E6a R1 (2026-09-24): the locals IN SCOPE at the statement being decoded — the
  enclosing function's params and results, then every `declare` target / `var` declaration /
  `range` variable / `select` clause binder / `if`-`for` init declaration that PRECEDES the
  statement in its enclosing blocks, in declaration order (`jsonDeclaredLocals`; the `block`
  arm of `decodeStmt` folds the environment statement by statement, the control-flow arms
  extend it for their bodies). The `unseq` arm resolves every source-local atom to the LAST
  entry of its name — the innermost declaration in scope — and checks the atom's `type`
  annotation against it (the E6a audit fix round, 2026-09-24, F2: the tip's flat per-function
  table let a forged annotation equal to ANOTHER declaration of the same name pass — a
  type-switch clause binder, a block-shadowed name). Empty outside a function body. -/
  locals : Array LocalDecl := #[]

/-- B6 (2026-09-30): the decoder's per-function interning state — the
`$`-temporaries seen so far (the frontend's and the decoder's own), in
first-sight order; temporary `k` has id `base + k`, `base` the wire table's
size. Reset at each function; per spelling per function, so nested desugars
that reuse a spelling shadow exactly as they did over strings (design D2). -/
private structure LowerSt where
  temps : Array String := #[]
  base : Nat := 0

private abbrev LowerM := ReaderT LowerCtx (StateT LowerSt (Except String))

private def fail {α} (msg : String) : LowerM α :=
  throw s!"native lowering: {msg}"

/-- Run a lowering action from a fresh interning state. -/
private def runLower {α} (act : LowerM α) (ctx : LowerCtx) : Except String α :=
  (act.run ctx).run' {}

/-- B6: intern a `$`-temporary's spelling in the current function (idempotent —
the same spelling returns the same id). -/
private def tmp (spelling : String) : LowerM VarId := do
  let st ← get
  match st.temps.findIdx? (· == spelling) with
  | some k => pure (st.base + k)
  | none =>
      set { st with temps := st.temps.push spelling }
      pure (st.base + st.temps.size)

/-- B6: the id a DECLARATION site carries. A `$`-spelling is a temporary — interned
here, never numbered by the frontend (a `local` index on one refuses); a source
spelling MUST carry its `local` index (c1: in range, and the table's spelling —
`wire` where the frontend renamed, else `name` — agrees with the node's). -/
private def declLocal (path name : String) (localJ : Option Json) : LowerM VarId := do
  if name.startsWith "$" then
    match localJ with
    | some _ => fail s!"{path}: the `$`-temporary '{name}' carries a `local` index — temporaries are interned by the decoder, never numbered by the frontend (B6, docs/2026-09-30_numeric-locals-design.md D2); refused by name"
    | none => tmp name
  else
    match localJ with
    | none => fail s!"{path}: the source local '{name}' carries no `local` declaration index — every source local on a golean-native-v3 wire is numbered by the frontend (B6 D1/D4); refused by name"
    | some j =>
        let id ← StrictJson.nat s!"{path}.local" j
        let table := (← read).table
        match table[id]? with
        | none => fail s!"{path}: local index {id} for '{name}' is past the function's name table ({table.size} entries) (B6 c1); refused by name"
        | some e =>
            let spelled := if e.wire.isEmpty then e.name else e.wire
            if spelled != name then
              fail s!"{path}: local index {id} names '{spelled}' in the function's name table, but the node spells '{name}' (B6 c1, spelling agreement); refused by name"
            pure id

/-- B6: the id a REFERENCE carries (`ident`, `ref`, a `var` target): `declLocal`'s
checks plus SCOPE — the innermost in-scope declaration of that spelling in the
R1 environment (the enclosing function's params/results and the declarations
preceding the statement in its enclosing blocks) must be this very declaration
(c3: in scope; c4: the frontend's go/types resolution and the decoder's lexical
walk AGREE — the pure-renaming certificate, design D1). -/
private def refLocal (path name : String) (localJ : Option Json) : LowerM VarId := do
  let id ← declLocal path name localJ
  if name.startsWith "$" then pure id
  else
    match (← read).locals.findRev? (·.name == name) with
    | none => fail s!"{path}: the source local '{name}' (declaration {id}) is not in scope at this statement — no declaration of that spelling among the enclosing function's params, results and the declarations that precede the statement in its enclosing blocks (B6 c3; the Stage E6a R1 environment); refused by name"
    | some d =>
        if d.id != id then
          fail s!"{path}: the source local '{name}' resolves to declaration {d.id} by lexical scope (the innermost in-scope declaration of that spelling), but the wire names declaration {id} — the frontend's resolution and the decoder's disagree (B6 c4); refused by name"
        pure id


/-! ## Exact-key discipline

Fidelity work program 2026-08-31, item 10 (assessment p2 claim 2): the
observation decoder has had `requireExactKeys` since birth; this wire
decoder had none — an unknown key on any node was silently ignored, so
a corrupted/foreign node could degrade toward a legal program instead
of refusing loudly. Every node decode now checks that EVERY PRESENT
KEY is one the emitter actually produces for that node kind (the
allowed lists below are the emitter's measured output — emit.go/
wire.go survey against a real wire, incl. the keys this decoder never
reads: `package`, `define`, the always-attached optional `type`, the
fmt-lift `operandType` on non-comparison `binary`). MISSING required
keys keep failing through the existing `StrictJson.field` reads, which
name the key and path; keys that are optional BY THE LANGUAGE (`cond`
on `for {}`, `cap` on `make(chan T)`) stay optional — their absence is
Go's own grammar, not corruption (p2 claim 2's corrected fact). This
is decode-layer hardening of the declared TCB seam: strictly more
refusals, never fewer. -/
private def checkAllowedKeys (path : String) (obj : StrictJson.Obj)
    (allowed : List String) : LowerM Unit := do
  for key in obj.keys do
    if !allowed.contains key then
      fail s!"unknown key '{key}' at {path} — the emitter never produces it for this node kind (exact-key discipline, fail closed)"

/-- Allowed key sets for type nodes, by `kind`. `none` = unknown kind
(the dispatch arm's own refusal names it). -/
private def tyAllowedKeys : String → Option (List String)
  | "bool" | "string" => some ["kind"]
  | "int" => some ["kind", "int"]
  | "float" => some ["kind", "float"]
  | "pointer" | "slice" => some ["kind", "elem"]
  | "array" => some ["kind", "len", "elem"]
  | "chan" => some ["kind", "dir", "elem"]
  | "map" => some ["kind", "key", "value"]
  | "sync" => some ["kind", "sync"]
  | "named" | "interface" => some ["kind", "name"]
  | "func" => some ["kind", "params", "results", "variadic"]
  | _ => none

/-- Allowed key sets for expression nodes, by `expr` tag. `type` is
allowed almost everywhere: the emitter post-attaches it to any
expression node whose type it can resolve. -/
private def exprAllowedKeys : String → Option (List String)
  | "ident" => some ["expr", "name", "type", "local"]
  | "func-value" => some ["expr", "func", "captured", "type"]
  | "int" | "bool" => some ["expr", "value", "type"]
  | "float" => some ["expr", "num", "den", "type"]
  | "string" => some ["expr", "bytes", "type"]
  | "nil" | "recover" => some ["expr", "type"]
  | "bytes-from-string" | "string-from-bytes" | "string-from-rune"
  | "runes-from-string" | "string-from-runes" => some ["expr", "x", "type"]
  | "float-bits" => some ["expr", "op", "x", "type"]
  | "min" | "max" => some ["expr", "args", "type"]
  | "ref" => some ["expr", "id", "type", "local"]
  | "globaladdr" => some ["expr", "gid", "type"]
  | "deref" | "addr-of-deref" => some ["expr", "ptr", "type"]
  | "field-get" => some ["expr", "recv", "typeId", "field", "type"]
  | "field-addr" => some ["expr", "base", "typeId", "field", "type"]
  | "index-get" | "index-addr" => some ["expr", "base", "index", "type"]
  | "builtin-len" | "builtin-cap" => some ["expr", "operand", "operandType", "type"]
  | "map-get" => some ["expr", "base", "index", "keyType", "valueType", "type"]
  | "slice" => some ["expr", "base", "low", "high", "max", "type"]
  | "convert" => some ["expr", "target", "x", "type"]
  | "default" => some ["expr", "type"]
  | "struct-lit" => some ["expr", "target", "args", "type"]
  | "array-lit" => some ["expr", "length", "elem", "elems", "type"]
  | "unary" => some ["expr", "op", "x", "type"]
  | "binary" => some ["expr", "op", "x", "y", "operandType", "type"]
  | "to-interface" => some ["expr", "target", "dynamic", "operand", "type"]
  | "type-assert" => some ["expr", "operand", "target", "source", "type"]
  | "call" => some ["expr", "func", "args", "resultTypes"]
  | "call-value" => some ["expr", "callee", "args", "resultTypes"]
  | "atomic-op" => some ["expr", "op", "kind", "args", "resultTypes"]
  | "sync-op" => some ["expr", "op", "args", "resultTypes"]
  | _ => none

/-- Does a wire JSON subtree contain a `recover()` expression node
(`{"expr": "recover"}`)? A syntactic walk over the JSON — used by the
`unseq-probe` decoder's fail-closed refusal (E13 option (b)). -/
private partial def jsonMentionsRecover : Json → Bool
  | .obj kvs =>
      (match kvs.get? "expr" with
        | some (Json.str "recover") => true
        | _ => false)
      || kvs.toList.any (fun (_, v) => jsonMentionsRecover v)
  | .arr xs => xs.any jsonMentionsRecover
  | _ => false

/-- Does a wire JSON subtree contain one of the two ALLOCATING strict-op
heads — `bytes-from-string` (`[]byte(s)`) or `runes-from-string`
(`[]rune(s)`)? These conversions allocate (`applyStrictOp`, Machine.lean:
`.bytesFromString` / `.runesFromString` call `s.alloc`), so a probe over
them would evaluate the allocation TWICE and advance the `Loc` counter
before the residual — the one way a probed operand is NOT state-free
(e13-b audit fix round R7; design §3 purity, §6 item 7). Closed
enumeration of two; the frontend never probes such an operand
(`containsAllocatingConversion`, emit.go), this is the fail-closed
backstop against drift. -/
private partial def jsonMentionsAllocatingConversion : Json → Bool
  | .obj kvs =>
      (match kvs.get? "expr" with
        | some (Json.str "bytes-from-string") => true
        | some (Json.str "runes-from-string") => true
        | _ => false)
      || kvs.toList.any (fun (_, v) => jsonMentionsAllocatingConversion v)
  | .arr xs => xs.any jsonMentionsAllocatingConversion
  | _ => false

/-- Allowed key sets for statement nodes, by `stmt` tag. `for` and
`range` are deliberately ABSENT (`none`): their decoders check keys
themselves, so the `labeled` wrapper's direct-dispatch path is covered
too. -/
private def stmtAllowedKeys : String → Option (List String)
  | "block" | "breakable" => some ["stmt", "body"]
  | "defer" | "go" => some ["stmt", "callee", "args"]
  | "panic" => some ["stmt", "value", "wrap", "runtimeError"]
  | "return" => some ["stmt", "results"]
  -- `define` is emitted (a := vs =) and deliberately unread here.
  | "assign" => some ["stmt", "lhs", "rhs", "define"]
  | "type-assert" => some ["stmt", "target", "okTarget", "expr", "targetType"]
  | "var" => some ["stmt", "decls"]
  | "if" => some ["stmt", "cond", "then", "init", "else"]
  | "incdec" => some ["stmt", "op", "target", "read", "type"]
  | "compound-assign" => some ["stmt", "op", "target", "read", "rhs"]
  | "expr" => some ["stmt", "expr"]
  | "new" => some ["stmt", "target", "value", "elemType"]
  | "make-slice" => some ["stmt", "target", "elem", "len", "cap"]
  | "make-map" => some ["stmt", "target", "keyType", "valueType", "hint"]
  | "make-chan" => some ["stmt", "target", "elem", "cap"]
  | "chan-send" => some ["stmt", "ch", "value", "elem"]
  | "chan-recv" => some ["stmt", "targets", "ch", "elem"]
  | "chan-close" => some ["stmt", "ch"]
  | "sync-op" => some ["stmt", "op", "args", "target"]
  | "select" => some ["stmt", "clauses", "default"]
  | "map-delete" => some ["stmt", "base", "index", "keyType"]
  | "clear-map" => some ["stmt", "base"]
  | "clear-slice" => some ["stmt", "base", "elem"]
  | "print" => some ["stmt", "newline", "args"]
  | "append" => some ["stmt", "target", "elem", "slice", "elems"]
  | "copy" => some ["stmt", "target", "dst", "src"]
  | "unseq-probe" => some ["stmt", "expr"]
  | "unseq" => some ["stmt", "cells", "occs", "stores", "then"]
  | "map-compound-assign" =>
      some ["stmt", "op", "base", "index", "read", "rhs", "keyType", "valueType"]
  | "map-assign" => some ["stmt", "base", "index", "value", "keyType", "valueType"]
  | "slice-lit" => some ["stmt", "target", "elem", "length", "elems"]
  | "map-lit" => some ["stmt", "target", "keyType", "valueType", "entries"]
  | "break" | "continue" => some ["stmt"]
  | "break-to" | "continue-to" => some ["stmt", "label"]
  | "labeled" => some ["stmt", "label", "body"]
  | _ => none

/-- Allowed key sets for assignment-target nodes, by `target` tag. -/
private def targetAllowedKeys : String → Option (List String)
  | "declare" => some ["target", "id", "type", "local"]
  | "var" => some ["target", "id", "local"]
  | "blank" => some ["target"]
  | "addr" => some ["target", "expr"]
  | "map" => some ["target", "base", "index", "keyType", "valueType"]
  | _ => none

/-- Allowed key sets for range statements, by `kind` (the shared base
plus the per-kind extras the emitter merges in). -/
private def rangeAllowedKeys : String → Option (List String)
  | "map" => some ["stmt", "keyVar", "valVar", "keyLocal", "valLocal", "collection", "body", "kind", "keyType", "valueType"]
  | "chan" | "slice" | "array" => some ["stmt", "keyVar", "valVar", "keyLocal", "valLocal", "collection", "body", "kind", "elemType"]
  | "int" => some ["stmt", "keyVar", "valVar", "keyLocal", "valLocal", "collection", "body", "kind", "operandType"]
  | "array-pointer" => some ["stmt", "keyVar", "valVar", "keyLocal", "valLocal", "collection", "body", "kind", "elemType", "arrType", "len"]
  | "string" => some ["stmt", "keyVar", "valVar", "keyLocal", "valLocal", "collection", "body", "kind"]
  | _ => none

/-- Dispatch-level key check: known kinds are checked; an unknown kind
passes through to the arm's own named refusal. -/
private def checkKindKeys (path : String) (obj : StrictJson.Obj)
    (table : String → Option (List String)) (kind : String) : LowerM Unit := do
  match table kind with
  | some allowed => checkAllowedKeys path obj allowed
  | none => pure ()

/-! ## Types -/

private def intKindOfName (name : String) : LowerM IntKind :=
  match name with
  | "int" => pure .int
  | "uint" => pure .uint
  | "int8" => pure .int8
  | "uint8" => pure .uint8
  | "int16" => pure .int16
  | "uint16" => pure .uint16
  | "int32" => pure .int32
  | "uint32" => pure .uint32
  | "int64" => pure .int64
  | "uint64" => pure .uint64
  | "byte" => pure .uint8
  | "rune" => pure .int32
  | "uintptr" => pure .uint64
  | other => fail s!"unsupported integer kind {other}"

/-- The array-type materialization budget (BUG-078): the largest array
length the decoder admits, in elements — a PER-TYPE FLAT bound on one
array type's own length, NOT a bound on a value's total element count
(a nested `[1024][1024][128]byte` is admitted: each level is a short
replicate of one shared element value, so its default value is cheap —
1.1 s measured — via persistent-array sharing).

Derivation (re-measured 2026-09-01 at the audit fix round on the tip
golean; the harness's per-case wall clock is 30 s —
`LEAN_TIMEOUT_SECONDS`, scripts/diff-coverage). The paths differ by
orders of magnitude, so each number names its path:

* DEFAULT-VALUE, read only (`var a [N]byte; a[0]`): `defaultValue`'s
  `Array.replicate` — linear and cheap: 0.03 s at 10^5, 0.06 s at
  1<<20. The earlier "10^5 fast / 10^6 grinds / ~10^8 aborts" numbers
  were this path's, and they said nothing about the path the bug
  names.
* LITERAL INITIALIZER (`var a = [N]byte{42}`): `.arrayLit` →
  `normalizeListWith`, the non-tail recursion with quadratic
  `#[h] ++ t` appends — QUADRATIC: 0.13 s at 10^4, 2.7 s at 5×10^4,
  5.0 s at 1<<16, 11.4 s at 10^5, 20.5 s at 1<<17, 46.0 s at 2×10^5
  (the auditor measured 224 s at 4×10^5; ≈25 min extrapolated at the
  old 1<<20 budget). So the old budget admitted types whose literal
  initialization could never finish inside the gate's wall clock,
  surfacing as a timeout kill, not a cause-naming refusal.
* ELEMENT STORE into a default array (`var a [N]byte; a[0] = 42`):
  the store re-normalizes the containing array — the SAME quadratic
  path: 5.5 s at 1<<16, 11.6 s at 10^5.

1<<16 (65 536) keeps both quadratic paths at ≈5–5.5 s (a >5× margin
under the 30 s wall, headroom for a loaded box running 8 workers) and
still exceeds the largest array type in the corpus/raft subject (128
elements) by two and a half orders of magnitude. What it does NOT
bound, recorded as BUG-078 residual (3): a single element store into
an admitted nested `[1024][1024][128]byte` measured 46 s (the store
re-normalizes through the nesting), so oversized NESTED values can
still reach the wall clock — an honest kill, never a wrong answer.
Raising the budget is a deliberate re-measure on the literal/store
paths, not a tweak; the owed linear normalize (BUG-078 residual (1),
TODO.md) is what lifts it. -/
def arrayLenBudget : Nat := 1 <<< 16

partial def decodeTy (path : String) (json : Json) : LowerM Ty := do
  let obj ← StrictJson.obj path json
  let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
  checkKindKeys path obj tyAllowedKeys kind
  match kind with
  | "bool" => pure .bool
  | "string" => pure .string
  | "int" =>
      let name ← StrictJson.string s!"{path}.int" (← StrictJson.field path obj "int")
      pure (.int (← intKindOfName name))
  | "float" =>
      let name ← StrictJson.string s!"{path}.float" (← StrictJson.field path obj "float")
      match name with
      | "float32" => pure (.float .float32)
      | "float64" => pure (.float .float64)
      | other => fail s!"unsupported float kind {other}"
  | "pointer" => pure (.pointer (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "slice" => pure (.slice (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "array" =>
      let len ← StrictJson.nat s!"{path}.len" (← StrictJson.field path obj "len")
      -- Materialization budget (BUG-078, $GOROOT/test issue34395's
      -- [100<<20]byte global): the machine materializes array values
      -- element-wise — the literal-initializer normalize path's
      -- non-tail element recursion with quadratic appends is the
      -- pathology (the default-value replicate is linear and cheap;
      -- see arrayLenBudget's docstring for the per-path numbers) —
      -- so an array TYPE past this bound either grinds past the
      -- gate's wall clock or kills the process with a native stack
      -- overflow — a process abort, not a refusal. Every array type reaches the machine through
      -- this decode (runtime-length allocations are slices, whose
      -- values normalize by reference), so the wire boundary is the
      -- single honest choke point: refuse HERE, naming the cause and
      -- the budget. A recorded idealization boundary (docs/BUGS.md
      -- BUG-078), not fidelity: gc materializes such arrays fine, and
      -- the delta stays a visible machine-refuses/gc-succeeds red.
      if len > arrayLenBudget then
        fail s!"array type of {len} elements exceeds the interpreter's materialization budget ({arrayLenBudget} elements; BUG-078 idealization boundary) at {path}"
      pure (.array len (← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")))
  | "chan" =>
      let dir ← StrictJson.string s!"{path}.dir" (← StrictJson.field path obj "dir")
      let elem ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      match dir with
      | "both" => pure (.chan .both elem)
      | "send" => pure (.chan .send elem)
      | "recv" => pure (.chan .recv elem)
      | other => fail s!"unsupported channel direction {other} at {path}"
  | "map" =>
      let key ← decodeTy s!"{path}.key" (← StrictJson.field path obj "key")
      let value ← decodeTy s!"{path}.value" (← StrictJson.field path obj "value")
      pure (.map key value)
  | "sync" =>
      -- Sync primitive types (spec-parity slice 2, design note §3):
      -- exactly the four in-scope kinds; anything else under sync.*
      -- never reaches here (the emitter quarantines it).
      let name ← StrictJson.string s!"{path}.sync" (← StrictJson.field path obj "sync")
      match name with
      | "Mutex" => pure (.sync .mutex)
      | "RWMutex" => pure (.sync .rwmutex)
      | "WaitGroup" => pure (.sync .waitGroup)
      | "Once" => pure (.sync .once)
      | other => fail s!"unsupported sync kind {other} at {path}"
  | "named" =>
      -- A `named` reference resolves to its TABLE INDEX (C2). A name with
      -- no TypeDef on the wire is a dangling reference the frontend's
      -- wire-integrity check refuses before emission; refuse here too,
      -- by name — never mint an index for it.
      let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
      match (← read).typeIdx[name]? with
      | some idx => pure (.defined idx)
      | none => fail s!"named type {name} at {path} has no TypeDef on the wire (dangling reference; refused rather than resolved to an index)"
  | "interface" =>
      pure (.interface ⟨← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")⟩)
  | "func" =>
      let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
      let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
      -- REQUIRED: the variadic half of func TYPE identity (BUG-067 —
      -- spec#Type_identity distinguishes `func(...int)` from
      -- `func([]int)`; a missing marker silently collapsed them and a
      -- comma-ok assert answered true for both). The same fail-closed
      -- discipline as the func / method-table / interface-requirement
      -- decodes (§9.5 of the census).
      let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
      pure (.funcType
        (← params.toList.mapIdxM (fun i t => decodeTy s!"{path}.params[{i}]" t))
        (← results.toList.mapIdxM (fun i t => decodeTy s!"{path}.results[{i}]" t))
        variadic)
  | other => fail s!"unsupported type kind {other} at {path}"

/-- B6: decode a function's `locals` name table — `[{name, kind, pos?, wire?}]`, the
frontend's source entries in allotment order. Checked (c2): no `$`-prefixed source
name (that prefix is the temporaries' reservation), `kind` one of the five source
kinds (`temp` is the decoder's alone), spellings non-empty. -/
private def decodeLocalsTable (path : String) (obj : StrictJson.Obj) : LowerM (Array LocalName) := do
  let entries ← StrictJson.array s!"{path}.locals" (← StrictJson.field path obj "locals")
  entries.mapIdxM fun i e => do
    let ep := s!"{path}.locals[{i}]"
    let eo ← StrictJson.obj ep e
    checkAllowedKeys ep eo ["name", "kind", "pos", "wire"]
    let name ← StrictJson.string s!"{ep}.name" (← StrictJson.field ep eo "name")
    let kindS ← StrictJson.string s!"{ep}.kind" (← StrictJson.field ep eo "kind")
    let kind ← match kindS with
      | "recv" => pure LocalKind.recv
      | "param" => pure LocalKind.param
      | "result" => pure LocalKind.result
      | "capture" => pure LocalKind.capture
      | "local" => pure LocalKind.local
      | "temp" => fail s!"{ep}.kind: `temp` is the decoder's kind (interned `$`-temporaries), never a wire entry (B6 c2); refused by name"
      | other => fail s!"{ep}.kind: unknown local kind '{other}' (expected recv | param | result | capture | local) (B6 c2); refused by name"
    let pos ← match eo.get? "pos" with
      | some j => StrictJson.string s!"{ep}.pos" j
      | none => pure ""
    let wire ← match eo.get? "wire" with
      | some j => StrictJson.string s!"{ep}.wire" j
      | none => pure ""
    if name.isEmpty then fail s!"{ep}.name: an empty local name (B6 c2); refused by name"
    if name.startsWith "$" then
      fail s!"{ep}.name: the source local name '{name}' starts with `$`, the temporaries' reservation — a frontend temporary is interned by the decoder, never a table entry (B6 c2); refused by name"
    if wire.startsWith "$" then
      fail s!"{ep}.wire: the lowering spelling '{wire}' starts with `$`, the temporaries' reservation (B6 c2); refused by name"
    pure { name, kind, pos, wire }

/-- B6: open a function's interning state — temporaries are numbered after the wire
table's entries. -/
private def beginLocals (table : Array LocalName) : LowerM Unit :=
  set ({ temps := #[], base := table.size } : LowerSt)

/-- B6: close a function's interning state — the table the `Func` carries: the wire's
source entries, then the temporaries interned while decoding it, `kind := .temp`. -/
private def endLocals : LowerM (Array LocalName) := do
  let st ← get
  let table := (← read).table
  pure (table ++ st.temps.map fun t => { name := t, kind := .temp })

/-- B6 (c2, the signature): a wire-numbered receiver/parameter carries kind `recv`,
`param` or `capture`; a wire-numbered result carries kind `result`; and the
signature's ids are pairwise distinct (a repeated id would make two slots one
binding — `bindParams` binds each id to its own fresh cell, so a repeat is the
frontend's error, refused here rather than shadowed silently). -/
private def checkSignatureLocals (path : String) (table : Array LocalName)
    (args res : Array LocalDecl) : LowerM Unit := do
  for a in args do
    match table[a.id]? with
    | some e =>
        unless e.kind == .param || e.kind == .recv || e.kind == .capture do
          fail s!"{path}: parameter '{a.name}' (declaration {a.id}) is recorded with kind {repr e.kind} in the function's name table (expected recv | param | capture) (B6 c2); refused by name"
    | none => pure ()  -- a `$`-temporary parameter (a shim's, a stub's)
  for r in res do
    match table[r.id]? with
    | some e =>
        unless e.kind == .result do
          fail s!"{path}: result '{r.name}' (declaration {r.id}) is recorded with kind {repr e.kind} in the function's name table (expected result) (B6 c2); refused by name"
    | none => pure ()
  let ids := (args ++ res).map (·.id)
  if !namesDistinct ids.toList then
    fail s!"{path}: the signature binds a declaration id twice ({ids}) — each parameter and result is its own slot (B6 c2); refused by name"

/-- B6 (c5): the core's total check over the DECODED function — every id the tree
names is inside its table and the signature's ids are distinct
(`Func.localsOk`, `GoLean/GoCore/Locals.lean`). A decoded function that fails it
is refused here, so `localsOk f = true` holds of every function `decodeProgram`
returns (the customer's `decide`-able premise for `localsOk_covers`). -/
private def checkLocalsOk (path : String) (f : Func) : LowerM Unit := do
  unless f.localsOk do
    fail s!"{path}: the decoded function names a local outside its name table ({f.locals.size} entries) or binds a signature id twice — `Func.localsOk` is false (B6 c5); refused by name"

private def decodeParam (path : String) (json : Json) : LowerM LocalDecl := do
  let obj ← StrictJson.obj path json
  checkAllowedKeys path obj ["id", "type", "local"]
  let name ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
  let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
  -- B6: a parameter is a declaration site — its id from the wire (`local`) or, for a
  -- `$`-spelled synthesized parameter, interned.
  let id ← declLocal path name (obj.get? "local")
  pure { name, id, typ }

/-! ## Expressions

GoCore has no call expression (calls are statements), so calls are handled at
the statement layer. Any call reaching `decodeExpr` is a nested call in
expression position, which is not yet modeled. -/

private def optType (path : String) (obj : StrictJson.Obj) : LowerM (Option Ty) := do
  match obj.get? "type" with
  | some t => pure (some (← decodeTy s!"{path}.type" t))
  | none => pure none

partial def decodeExpr (path : String) (json : Json) : LowerM Expr := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.expr" (← StrictJson.field path obj "expr")
  checkKindKeys path obj exprAllowedKeys tag
  match tag with
  | "ident" =>
      let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
      pure (.var (← refLocal path name (obj.get? "local")))
  | "func-value" =>
      let fid ← StrictJson.string s!"{path}.func" (← StrictJson.field path obj "func")
      let captured ← StrictJson.array s!"{path}.captured" (← StrictJson.field path obj "captured")
      pure (.funcVal ⟨fid⟩
        (← captured.mapIdxM (fun i c => decodeExpr s!"{path}.captured[{i}]" c)))
  | "int" =>
      let s ← StrictJson.string s!"{path}.value" (← StrictJson.field path obj "value")
      match s.toInt? with
      | some v =>
          -- FAIL CLOSED on a missing or non-integer `type` (census §10
          -- H-b / J-1: the old `intKindOfOptType`'s `| _ => .int`
          -- default silently widened an untyped literal to 64-bit —
          -- BUG-042/043's defect class, already hardened at its two
          -- siblings, incdec and range-over-int; this arm is the third
          -- and last).
          match (← optType path obj) with
          | some (.int k) => pure (.intLit v k)
          | some other => fail s!"integer literal at {path} typed non-integer ({repr other})"
          | none => fail s!"integer literal at {path} carries no type"
      | none => fail s!"invalid integer literal {s} at {path}"
  | "float" =>
      -- The EXACT RATIONAL of a float-typed constant (floats design note
      -- decision 5); the machine performs the single rounding. Fail
      -- closed on malformed rationals: non-integer strings, zero
      -- denominator, a missing/non-float kind.
      let numS ← StrictJson.string s!"{path}.num" (← StrictJson.field path obj "num")
      let denS ← StrictJson.string s!"{path}.den" (← StrictJson.field path obj "den")
      let kind ← match (← optType path obj) with
        | some (.float k) => pure k
        | some other => fail s!"float literal at {path} typed non-float ({repr other})"
        | none => fail s!"float literal at {path} carries no type"
      match numS.toInt?, denS.toNat? with
      | some num, some den =>
          if den == 0 then fail s!"float literal at {path} has zero denominator"
          else pure (.floatLit num den kind)
      | _, _ => fail s!"invalid float literal {numS}/{denS} at {path}"
  | "bool" =>
      pure (.boolLit (← StrictJson.bool s!"{path}.value" (← StrictJson.field path obj "value")))
  | "string" =>
      -- Literal VALUE as raw bytes: a Go string may be invalid UTF-8, which
      -- a JSON string cannot carry (wrong-answers slice 0b).
      let arr ← StrictJson.array s!"{path}.bytes" (← StrictJson.field path obj "bytes")
      let bytes ← arr.mapIdxM (fun i b => do
        let n ← StrictJson.nat s!"{path}.bytes[{i}]" b
        if n < 256 then pure (UInt8.ofNat n)
        else fail s!"string literal byte out of range at {path}.bytes[{i}]: {n}")
      pure (.stringLit { bytes })
  | "nil" => pure (.nil (← optType path obj))
  | "recover" => pure .recoverCall
  | "bytes-from-string" =>
      pure (.bytesFromString (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "min" =>
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.minOf (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "max" =>
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.maxOf (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "string-from-bytes" =>
      pure (.stringFromByteSlice (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "string-from-rune" =>
      pure (.stringFromRune (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "runes-from-string" =>
      pure (.runesFromString (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "string-from-runes" =>
      pure (.stringFromRuneSlice (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "float-bits" =>
      -- The `float-bits` primitive (stdlib slice 3): one of the four
      -- documented math functions, by tag; anything else refuses by name.
      let opName ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let op ← match opName with
        | "f64bits" => pure FloatBitsOp.f64bits
        | "f64frombits" => pure FloatBitsOp.f64frombits
        | "f32bits" => pure FloatBitsOp.f32bits
        | "f32frombits" => pure FloatBitsOp.f32frombits
        | other => throw s!"{path}.op: unknown float-bits op {repr other} (the four are f64bits/f64frombits/f32bits/f32frombits)"
      pure (.floatBits op (← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")))
  | "ref" =>
      let name ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
      pure (.ref (← refLocal path name (obj.get? "local")))
  | "globaladdr" =>
      -- A statically resolved package-level variable (init slice,
      -- docs/2026-08-05_init-design.md §2): global `gid` (wire declaration
      -- order) lives at the driver-seeded cell `Loc.base ⟨gid⟩`; the core
      -- node is the INDEX (`Expr.global`, A4) — the machine resolves it to
      -- the address at evaluation time. The gid
      -- assignment is the emitter's single collection loop (dense by
      -- construction), and the BOUND CHECK here is the decode-boundary
      -- collision check (audit response 2026-08-05, C1): a dangling gid
      -- used NOT to go stuck at runtime — `storeLoc` materialized cells
      -- for unseeded locations, so it would alias the next allocation
      -- (closed core-side by BUG-085: the store now refuses `.internal`);
      -- a malformed wire still refuses loud here, at the boundary.
      let gid ← StrictJson.nat s!"{path}.gid" (← StrictJson.field path obj "gid")
      let nGlobals := (← read).nGlobals
      if gid < nGlobals then
        pure (.global gid)
      else
        fail s!"globaladdr gid {gid} out of range at {path} (program declares {nGlobals} global(s))"
  | "deref" =>
      let ptr ← decodeExpr s!"{path}.ptr" (← StrictJson.field path obj "ptr")
      let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
      pure (.deref ptr typ)
  | "addr-of-deref" =>
      -- `&*p` / `&(*p)` (BUG-056): nil-assert + pass-through, no load.
      let ptr ← decodeExpr s!"{path}.ptr" (← StrictJson.field path obj "ptr")
      pure (.addrOfDeref ptr)
  | "field-get" =>
      let recv ← decodeExpr s!"{path}.recv" (← StrictJson.field path obj "recv")
      let typeId ← StrictJson.string s!"{path}.typeId" (← StrictJson.field path obj "typeId")
      let field ← StrictJson.string s!"{path}.field" (← StrictJson.field path obj "field")
      pure (.fieldGet recv ⟨typeId⟩ field)
  | "field-addr" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let typeId ← StrictJson.string s!"{path}.typeId" (← StrictJson.field path obj "typeId")
      let field ← StrictJson.string s!"{path}.field" (← StrictJson.field path obj "field")
      pure (.fieldAddr base ⟨typeId⟩ field)
  | "index-get" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      pure (.indexGet base index)
  | "index-addr" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      pure (.indexAddr base index)
  | "builtin-len" =>
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      pure (.length operand (some (← decodeTy s!"{path}.operandType" (← StrictJson.field path obj "operandType"))))
  | "builtin-cap" =>
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      pure (.capacity operand (some (← decodeTy s!"{path}.operandType" (← StrictJson.field path obj "operandType"))))
  | "map-get" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valueTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (.mapGet base index keyTy valueTy)
  | "slice" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let low ← decodeExpr s!"{path}.low" (← StrictJson.field path obj "low")
      let high ← decodeExpr s!"{path}.high" (← StrictJson.field path obj "high")
      let max ← (match obj.get? "max" with
        | some m => do pure (some (← decodeExpr s!"{path}.max" m))
        | none => pure none)
      pure (.slice base low high max)
  | "convert" =>
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      pure (.convert target x)
  | "default" =>
      pure (.defaultValue (← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")))
  | "struct-lit" =>
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.structLit target (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "array-lit" =>
      let length ← StrictJson.nat s!"{path}.length" (← StrictJson.field path obj "length")
      let elem ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let elems ← StrictJson.array s!"{path}.elems" (← StrictJson.field path obj "elems")
      let pairs ← elems.mapIdxM (fun i el => do
        let eo ← StrictJson.obj s!"{path}.elems[{i}]" el
        checkAllowedKeys s!"{path}.elems[{i}]" eo ["index", "value"]
        let index ← StrictJson.int s!"{path}.elems[{i}].index" (← StrictJson.field s!"{path}.elems[{i}]" eo "index")
        let value ← decodeExpr s!"{path}.elems[{i}].value" (← StrictJson.field s!"{path}.elems[{i}]" eo "value")
        pure (index, value))
      pure (.arrayLit length elem pairs)
  | "unary" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      match op with
      -- Proper negation (floats design note §4 rider): value-directed
      -- Expr.neg — int stays 0 - v at the OPERAND's kind, float is the
      -- IEEE sign-bit flip. The old `.sub (intLit 0) x` lowering was
      -- wrong at x = +0 (gave +0; Go gives -0 — floats/signed-zero).
      | "-" => pure (.neg x)
      | "!" => pure (.not x)
      | "^" => pure (.bitNeg x)
      | other => fail s!"unsupported unary operator {other}"
  | "binary" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let x ← decodeExpr s!"{path}.x" (← StrictJson.field path obj "x")
      let y ← decodeExpr s!"{path}.y" (← StrictJson.field path obj "y")
      decodeBinary path obj op x y
  | "to-interface" =>
      -- The interface-conversion wrap (interfaces campaign S3): the
      -- machine boxes the operand with the canonical dynamic type.
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      let dynamic ← decodeTy s!"{path}.dynamic" (← StrictJson.field path obj "dynamic")
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      pure (.toInterface target dynamic operand)
  | "type-assert" =>
      -- Single-result assert `x.(T)` — panics on mismatch.
      let operand ← decodeExpr s!"{path}.operand" (← StrictJson.field path obj "operand")
      let target ← decodeTy s!"{path}.target" (← StrictJson.field path obj "target")
      -- The operand's STATIC interface type, for Go's panic message.
      let source ← match obj.get? "source" with
        | some t => some <$> decodeTy s!"{path}.source" t
        | none => pure none
      pure (.typeAssert operand target source)
  | "call" => fail "call in expression position is not modeled (calls are statements)"
  | "atomic-op" => fail "atomic op in expression position is not modeled (sync/atomic ops are statements, like calls)"
  | "sync-op" => fail "sync op in expression position is not modeled (TryLock/TryRLock are statements, like calls)"
  | other => fail s!"unsupported expression {other} at {path}"
where
  decodeBinary (path : String) (obj : StrictJson.Obj) (op : String) (x y : Expr) : LowerM Expr := do
    let operandTy : LowerM Ty := do
      match obj.get? "operandType" with
      | some t => decodeTy s!"{path}.operandType" t
      | none => fail s!"comparison at {path} missing operandType"
    match op with
    | "+" => pure (.add x y)
    | "-" => pure (.sub x y)
    | "*" => pure (.mul x y)
    | "/" => pure (.div x y)
    | "%" => pure (.mod x y)
    | "&" => pure (.bitAnd x y)
    | "|" => pure (.bitOr x y)
    | "^" => pure (.bitXor x y)
    | "&^" => pure (.bitClear x y)
    | "<<" => pure (.shiftLeft x y)
    | ">>" => pure (.shiftRight x y)
    | "&&" => pure (.and x y)
    | "||" => pure (.or x y)
    | "==" => pure (.eqCmp (← operandTy) x y)
    | "!=" => pure (.neqCmp (← operandTy) x y)
    | "<" => pure (.lessCmp x y)
    | "<=" => pure (.atMostCmp x y)
    | ">" => pure (.greaterCmp x y)
    | ">=" => pure (.atLeastCmp x y)
    | other => fail s!"unsupported binary operator {other}"

/-- Turn an expression used as an lvalue into a GoCore assignee. Plain locals
map to `.var`; addressable forms (deref/field/index) are added incrementally. -/
private def exprAsAssignee (path : String) : Expr → LowerM Assignee
  | .var id => pure (.var id)
  | .deref e _ => pure (.addr e)
  | other => fail s!"expression at {path} is not an assignable location ({repr other})"

/-- Combine a compound-assignment target and rhs (`x op= e` → `x op e`). Only
arithmetic/bitwise/shift operators are valid here. -/
private def decodeCompound (op : String) (lhs rhs : Expr) : LowerM Expr :=
  match op with
  | "+" => pure (.add lhs rhs)
  | "-" => pure (.sub lhs rhs)
  | "*" => pure (.mul lhs rhs)
  | "/" => pure (.div lhs rhs)
  | "%" => pure (.mod lhs rhs)
  | "&" => pure (.bitAnd lhs rhs)
  | "|" => pure (.bitOr lhs rhs)
  | "^" => pure (.bitXor lhs rhs)
  | "&^" => pure (.bitClear lhs rhs)
  | "<<" => pure (.shiftLeft lhs rhs)
  | ">>" => pure (.shiftRight lhs rhs)
  | other => fail s!"unsupported compound operator {other}"

/-- A decoded assignment target and whether it introduces a fresh local. -/
private structure Target where
  assignee : Assignee
  declare : Option Param

private def decodeTarget (path : String) (json : Json) : LowerM Target := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.target" (← StrictJson.field path obj "target")
  checkKindKeys path obj targetAllowedKeys tag
  match tag with
  | "declare" =>
      let name ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
      let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
      let id ← declLocal path name (obj.get? "local")
      pure { assignee := .var id, declare := some { id, typ } }
  | "var" =>
      let name ← StrictJson.string s!"{path}.id" (← StrictJson.field path obj "id")
      let id ← refLocal path name (obj.get? "local")
      pure { assignee := .var id, declare := none }
  | "blank" =>
      pure { assignee := .unsupported "blank assignment target", declare := none }
  | "addr" =>
      let e ← decodeExpr s!"{path}.expr" (← StrictJson.field path obj "expr")
      pure { assignee := .addr e, declare := none }
  | "map" =>
      -- A map-element delivery target (convergence round, BUG-030):
      -- consumed only by the channel-receive delivery plan; every other
      -- assignee position fails closed on it (`assigneeExpr` is `none`).
      let b ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let i ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let kt ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let vt ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure { assignee := .mapElem b i kt vt, declare := none }
  | other => fail s!"unsupported assignment target {other} at {path}"

private def targetAssignee (t : Target) : LowerM Assignee := pure t.assignee

/-- The expression that reads a declared local target (used to index into a
freshly-built slice/map temp). -/
private def targetBaseExpr (t : Target) (lit : VarId) : Expr :=
  match t.assignee with
  | .var id => .var id
  | _ => .var lit

private def declaresOf (targets : Array Target) : LowerM (Array Stmt) := do
  pure (targets.filterMap (fun t => t.declare.map Stmt.initialization))

/-- Whether a wire assignment target is the blank identifier `_`. -/
private def targetIsBlank (json : Json) : Bool :=
  match json.getObjVal? "target" with
  | .ok (.str "blank") => true
  | _ => false

/-- An optional string field: a JSON string, or `null`/absent → `none`. -/
private def optString (obj : StrictJson.Obj) (key : String) : Option String :=
  match obj.get? key with
  | some (.str s) => some s
  | _ => none

/-- The declared type carried on a wire expression node (fallback `int`). -/
private def exprTypeOf (path : String) (json : Json) : LowerM Ty := do
  let obj ← StrictJson.obj path json
  match obj.get? "type" with
  | some t => decodeTy s!"{path}.type" t
  | none => pure (.int .int)

/-! ## Statements -/

/-- Detect `m[k]` (a map index) as the RHS of a comma-ok lookup. -/
private def asMapGet? (json : Json) : LowerM (Option (Json × Json × Json × Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "map-get") =>
      let obj ← StrictJson.obj "map-get" json
      checkAllowedKeys "map-get" obj ["expr", "base", "index", "keyType", "valueType", "type"]
      pure (some (← StrictJson.field "map-get" obj "base", ← StrictJson.field "map-get" obj "index",
        ← StrictJson.field "map-get" obj "keyType", ← StrictJson.field "map-get" obj "valueType"))
  | _ => pure none

/-- The `resultTypes` vector of a call-shaped node (`call`, `call-value`,
`atomic-op`, `sync-op`): REQUIRED, and checked against the arity the
consumer expects (BUG-110; whole-project review 2026-09-11 F3 = the
2026-09-05 gate audit's F9). The frontend emits the vector on EVERY
call-shaped node (`emitResultTypes`), so an absent or mis-sized vector is
a forged or mutated wire: it refuses by name here and is never
reconstructed — the `resultTypes[i]?.getD .int` default that typed a
discard temp as `int` when the vector was missing is gone. -/
private def decodeResultTypes (path : String) (obj : StrictJson.Obj) (arity : Nat) :
    LowerM (Array Ty) := do
  let rt ← StrictJson.field path obj "resultTypes"
  let arr ← StrictJson.array s!"{path}.resultTypes" rt
  if arr.size != arity then
    fail s!"resultTypes arity {arr.size} does not match the {arity} target(s) at {path} (BUG-110: the vector is validated, never reconstructed)"
  arr.mapIdxM (fun i t => decodeTy s!"{path}.resultTypes[{i}]" t)

/-- Every call-shaped node must CARRY a `resultTypes` array (presence and
shape at recognition; the consumer checks the arity it needs). -/
private def requireResultTypes (kind : String) (obj : StrictJson.Obj) : LowerM Unit := do
  let _ ← StrictJson.array s!"{kind}.resultTypes" (← StrictJson.field kind obj "resultTypes")

/-- Detect a call whose result feeds an assignment / return / expression
statement, so it can lower to a GoCore call statement. -/
private def asCall? (json : Json) : LowerM (Option (String × Array Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "call") =>
      let obj ← StrictJson.obj "call" json
      checkAllowedKeys "call" obj ["expr", "func", "args", "resultTypes"]
      requireResultTypes "call" obj
      let name ← StrictJson.string "call.func" (← StrictJson.field "call" obj "func")
      let args ← StrictJson.array "call.args" (← StrictJson.field "call" obj "args")
      pure (some (name, args))
  | _ => pure none

/-- Recognize a `sync/atomic` op node (the atomics arc, wave 1 —
tools/nativefrontend/atomics.go) in a CALL position: the head, the
addressed cell's integer kind (one of the four wave-1 kinds — `uintptr`
already arrives as uint64 from the type table; anything else refuses by
name), and the operand array (address first). Strict keys; arity is
checked here AND again by `atomicPlan` (fail closed twice, the sync-op
discipline). -/
private def asAtomicOp? (json : Json) : LowerM (Option (AtomicStmtOp × IntKind × Array Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "atomic-op") =>
      let obj ← StrictJson.obj "atomic-op" json
      checkAllowedKeys "atomic-op" obj ["expr", "op", "kind", "args", "resultTypes"]
      requireResultTypes "atomic-op" obj -- (the F5 owed tightening, TODO.md; BUG-110)
      let opName ← StrictJson.string "atomic-op.op" (← StrictJson.field "atomic-op" obj "op")
      let op : AtomicStmtOp ← match opName with
        | "load" => pure .load
        | "store" => pure .store
        | "add" => pure .add
        | "swap" => pure .swap
        | "cas" => pure .cas
        | other => fail s!"unsupported atomic op {other} (wave 1 lowers load/store/add/swap/cas)"
      let kindTy ← decodeTy "atomic-op.kind" (← StrictJson.field "atomic-op" obj "kind")
      let kind ← match kindTy with
        | .int k@.int32 | .int k@.int64 | .int k@.uint32 | .int k@.uint64 => pure k
        | other => fail s!"unsupported atomic operand kind {repr other} (wave 1 models int32/int64/uint32/uint64; uintptr arrives as uint64)"
      let args ← StrictJson.array "atomic-op.args" (← StrictJson.field "atomic-op" obj "args")
      let arity := match op with
        | .load => 1 | .store => 2 | .add => 2 | .swap => 2 | .cas => 3
      if args.size != arity then
        fail s!"atomic op {opName} expects {arity} operand(s), got {args.size}"
      pure (some (op, kind, args))
  | _ => pure none

/-- Recognize the value-returning sync ops' EXPRESSION node (Q-TRYLOCK):
`{"expr":"sync-op","op":<tryLock|tryRLock|tryWLock>,"args":[recv],
"resultTypes":[bool]}` — the frontend emits it for `m.TryLock()` /
`rw.TryRLock()` / `rw.TryLock()` and hoists it exactly like a call, so
it is admitted ONLY where `atomic-op` is (an expression statement; the
single RHS of an assignment) and lowers to `Stmt.syncStmt` with the
result target. Same wire op names as the statement form (one op
identity — the Q-SYNCVAL identity principle); any other op name here
is a forged wire. `resultTypes` is REQUIRED here and in `asAtomicOp?`
(the F5 tightening TODO.md owed, discharged with BUG-110: an absent key
refuses by name; the assignment consumers check the arity). -/
private def asSyncValueOp? (json : Json) : LowerM (Option (SyncStmtOp × Array Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "sync-op") =>
      let obj ← StrictJson.obj "sync-op" json
      checkAllowedKeys "sync-op" obj ["expr", "op", "args", "resultTypes"]
      requireResultTypes "sync-op" obj
      let opName ← StrictJson.string "sync-op.op" (← StrictJson.field "sync-op" obj "op")
      let op : SyncStmtOp ← match opName with
        | "tryLock" => pure .tryLock
        | "tryRLock" => pure .tryRLock
        | "tryWLock" => pure .tryWLock
        | other => fail s!"unsupported value sync op {other} (only TryLock/TryRLock return a value)"
      let args ← StrictJson.array "sync-op.args" (← StrictJson.field "sync-op" obj "args")
      if args.size != 1 then
        fail s!"value sync op {opName} expects 1 operand (the receiver address), got {args.size}"
      pure (some (op, args))
  | _ => pure none

/-- Recognize a call through a func VALUE (a closure or func-typed
variable): the callee is an expression rather than a name (W5 §8). -/
private def asCallValue? (json : Json) : LowerM (Option (Json × Array Json)) := do
  match json.getObjVal? "expr" with
  | .ok (.str "call-value") =>
      let obj ← StrictJson.obj "call-value" json
      checkAllowedKeys "call-value" obj ["expr", "callee", "args", "resultTypes"]
      requireResultTypes "call-value" obj
      let callee ← StrictJson.field "call-value" obj "callee"
      let args ← StrictJson.array "call-value.args" (← StrictJson.field "call-value" obj "args")
      pure (some (callee, args))
  | _ => pure none

/-! ## The `unseq` construct — the wire arm (evaluation-order model v2.1 Stage C,
lane `core/unseq-stage-c-0919`, 2026-09-19; design
`docs/2026-09-19_unseq-stage-c-design.md` §4 the schema, §5 the decoder spec).

`{"stmt":"unseq","cells":[…],"occs":[…],"stores":[…],"then":STMT}` maps 1:1
onto `Stmt.unseq (g : UnseqGraph) thenB` (Syntax.lean): `cells` are the typed
VALUE binders, `occs` the occurrences in canonical rank order (`eval` /
`invoke` / `target` / `load` / `guard`, each with its ORDER prerequisites
`after` and its `region` guard), `stores` the phase-2 `(target, value)`
pairs, `then` the completion statement. The machine's own checks
(`UnseqGraph.wellFormed?` at ENTER; `skippedDep?`, `unproducedConsumer?`,
`unseqUnfrozenPlan?` dynamically — Stage B §9.1: the enforcement lives in
the trusted core, hand-built graphs cannot bypass it) stay the enforcement;
this arm is the STATIC net at the wire boundary, refusing BY NAME before a
graph exists: exact keys (D1), the `$` reservation and distinctness of
binders (D2, D5), a non-empty graph and distinct occurrence names (D3), the
kind (D4), sorts (D6), LIST ORDER = a linear extension of every edge —
cycles and forward references refused in one check (D7), the internal
NORMAL FORM of every head / callee / argument — no hidden read, no logical
operator, no `recover`, no allocation; a bare int/bool/string constant is an
admitted head — the copy into a cell (D8), head type = cell type (D9),
`resultTypes` = the bound cells' types (D10), guard cells bool with the
completion inside the region (D11 — `wellFormed?`), the STATIC G rule: a
region-confined binder is consumed only inside its region, the completion
binder being the only join — itself confined to its guard's enclosing region
when the guard is nested (D12), the target plan's shape (D13), and a
completion free of nested `unseq` / legacy `unseq-probe` (the whole-sweep
boundary, audit N2) and of `recover` (D14). Stage E6a (2026-09-24) adds two
named refusals ratified 2026-09-22 (the Stage E5 landing record items 3 and
6): every SOURCE-LOCAL atom the node mentions is a local the enclosing
function declares, its `type` annotation that declaration's (R1 —
`unseqCheckLocalAtoms`, over `LowerCtx.locals` — the locals IN SCOPE at the node since the audit fix round's F2), and a LITERAL allocation
carries no `after` edge (the Stage E audit's F8). -/

/-- Allowed key sets for `unseq` occurrence nodes, by `kind`. -/
private def unseqOccAllowedKeys : String → Option (List String)
  | "eval" => some ["name", "kind", "bind", "head", "after", "region"]
  | "invoke" => some ["name", "kind", "binds", "callee", "args", "resultTypes", "after", "region"]
  | "target" => some ["name", "kind", "bind", "lhs", "after", "region"]
  | "load" => some ["name", "kind", "bind", "target", "after", "region"]
  | "guard" => some ["name", "kind", "test", "when", "out", "after", "region"]
  | "recv" => some ["name", "kind", "binds", "ch", "elem", "after", "region"]
  | "allocate" => some ["name", "kind", "bind", "allocation", "after", "region"]
  | "wide" => some ["name", "kind", "binds", "wide", "after", "region"]
  | _ => none

/-- An ATOM on the wire (v2.1 §3.1's internal normal form): an identifier —
a slot or an admitted source local — or an int/bool/string constant. -/
private def unseqIsAtom (j : Json) : Bool :=
  match j.getObjVal? "expr" with
  | .ok (.str "ident") | .ok (.str "int") | .ok (.str "bool") | .ok (.str "string") => true
  | _ => false

/-- Stage E audit fix round F2 (2026-09-21): a `ref` whose `id` is a reserved `$` slot names a
GRAPH CELL — an address through which a callee could WRITE a binder (a cell is written only by
its producer; `unseqCheckTargetShape` refuses a `$` store target for the same reason) — and the
frontend never emits it (a receiver's frozen address is `ref` of a SOURCE local). The audit's
mutant M10b decoded and RAN: the callee incremented the binder cell through the address. -/
private def unseqRefOfBinder? (j : Json) : Option String :=
  match j.getObjVal? "expr", j.getObjVal? "id" with
  | .ok (.str "ref"), .ok (.str id) => if id.startsWith "$" then some id else none
  | _, _ => none

/-- Stage E E4 (2026-09-21): an ALLOCATION PAYLOAD / a struct literal's field — an
atom, a boxing `to-interface` of an atom, or a `default` (a field's zero value):
already-evaluated values only; anything else is a hidden read, refused by name. -/
private def unseqCheckPayload (path : String) (j : Json) : LowerM Unit := do
  if jsonMentionsRecover j then
    fail s!"unseq: recover() in an allocation payload at {path}; refused by name"
  if unseqIsAtom j then return
  -- Stage E5 E5d (2026-09-22): the ADDRESS of a source variable (`ref x` / `globaladdr`) is an
  -- already-evaluated value — no read, no failure; never `ref` of a `$` binder cell (audit F2).
  if let some id := unseqRefOfBinder? j then
    fail s!"unseq: an allocation payload at {path} takes the address of a binder cell '{id}' — a graph cell is written only by its producer (audit F2, 2026-09-21); refused by name"
  match j.getObjVal? "expr" with
  | .ok (.str "ref") | .ok (.str "globaladdr") => pure ()
  | .ok (.str "default") => pure ()
  | .ok (.str "to-interface") =>
      match j.getObjVal? "operand" with
      | .ok operand =>
          if !unseqIsAtom operand then
            fail s!"unseq: hidden read in an allocation payload — {path} boxes a non-atom; refused by name"
      | _ => fail s!"unseq: malformed to-interface at {path}; refused by name"
  | _ =>
      fail s!"unseq: hidden read in an allocation payload — {path} is not an atom (or a boxed atom / a zero value); an allocation's operands are already evaluated (v2.1 §3.1); refused by name"

/-- A constant `int` payload's value (`{"expr":"int","value":"…"}`), when the payload is one. -/
private def unseqConstInt? (j : Json) : Option Int :=
  match j.getObjVal? "expr", j.getObjVal? "value" with
  | .ok (.str "int"), .ok (.str s) => s.toInt?
  | _, _ => none

/-- Stage E audit fix round F3 (2026-09-21): a CONSTANT size operand of `make` must be a legal Go
constant argument — non-negative and representable as `int` (go/types rejects the program
otherwise: «negative … argument in make», «… argument too large»); the run-time classes (a
non-constant negative, a size over `maxAlloc`) stay the machine's own `makeslice` panics, as in Go.
The audit's mutant M6 (`len -1`) decoded and answered with a Go-observable panic. -/
private def unseqCheckConstSize (path what : String) (j : Json) : LowerM Unit := do
  match unseqConstInt? j with
  | some v =>
      if v < 0 then
        fail s!"unseq: {path}: negative constant {what} {v} in make — a compile-time error in Go, never a run-time panic (audit F3, 2026-09-21); refused by name"
      if v ≥ (platform.intExclusiveUpperBound : Int) then
        fail s!"unseq: {path}: constant {what} {v} in make does not fit the platform's int (a compile-time error in Go — audit F3, 2026-09-21); refused by name"
  | none => pure ()

/-- Stage E audit fix round F1 (2026-09-21): the static type a PAYLOAD carries on the wire, when it
carries one — a `$` slot's declared cell type (`none` for an undeclared slot: the graph-level
«unknown slot» check names that), a source local's / constant's / zero value's `type` annotation,
a boxing's `target`, a struct literal's `target`. Used to check `new`'s value against the
allocation's element type. -/
private def unseqPayloadTy? (cells : Array LocalDecl) (path : String) (j : Json) : LowerM (Option Ty) := do
  let typeField (key : String) : LowerM (Option Ty) := do
    match j.getObjVal? key with
    | .ok t => pure (some (← decodeTy s!"{path}.{key}" t))
    | _ => pure none
  match j.getObjVal? "expr" with
  | .ok (.str "ident") =>
      match j.getObjVal? "name" with
      | .ok (.str n) =>
          if n.startsWith "$" then pure ((cells.find? (·.name == n)).map (·.typ))
          else typeField "type"
      | _ => pure none
  | .ok (.str "int") | .ok (.str "bool") | .ok (.str "string") | .ok (.str "default") => typeField "type"
  | .ok (.str "to-interface") | .ok (.str "struct-lit") => typeField "target"
  | _ => pure none

/-- Stage E5 audit fix round F1 (2026-09-22): a MAP operand's `keyType`/`valueType` on the wire
must be the base atom's own DECLARED type — a `$` slot's cell type, a source local's `type`
annotation (`unseqPayloadTy?`) — spelled `map[K]V`. The `wide map-lookup` arm (E5b) and the
`map-get` head (E2) decoded the pair and typed the RESULT cells by it but never compared it with
the base: a forged wire (`keyType: string` on a `map[int]int` cell — the audit's mW12/mW17; the
head's mE2) DECODED and, on the canonical tape, answered a Go-observable value or stuck LATE (the
Stage E audit's F3 class: a malformed wire that decodes and answers). The frontend spells both from
the ONE go/types map type (`emitType(mt.Key())` / `emitType(mt.Elem())` beside the base's own
annotation), so no emitted wire changes; the `map` TARGET plan (E2's `{"target":"map"}`) is checked
the same way. Mutants `mut-wide-lookup-keytype-vs-base`, `mut-wide-lookup-valuetype-vs-base`,
`mut-mapget-keytype-vs-base`, `mut-map-target-keytype-vs-base`. -/
private def unseqCheckMapBase (cells : Array LocalDecl) (path what : String) (baseJ : Json)
    (keyTy valueTy : Ty) : LowerM Unit := do
  match ← unseqPayloadTy? cells path baseJ with
  | none =>
      fail s!"unseq: {what} at {path}: the map base carries no static type on the wire (a `$` cell's declared type or a source local's `type` annotation is needed to check keyType/valueType against it — audit F1, 2026-09-22); refused by name"
  | some t =>
      if t != .map keyTy valueTy then
        fail s!"unseq: {what} at {path}: keyType/valueType {repr keyTy} / {repr valueTy} disagree with the map base's declared type {repr t} (the wire's map[K]V must be the base's own — audit F1, 2026-09-22); refused by name"

/-- Stage E E4: a VALUE struct literal's arguments are payloads. -/
private def unseqCheckStructLit (path : String) (j : Json) : LowerM Unit := do
  let o ← StrictJson.obj path j
  let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path o "args")
  for k in [:args.size] do
    unseqCheckPayload s!"{path}.args[{k}]" args[k]!

/-- Does a wire JSON subtree contain a statement node whose `stmt` tag is one
of `tags`? (D14: no nested `unseq`, no legacy `unseq-probe` in a completion.) -/
private partial def jsonMentionsStmt (tags : List String) : Json → Bool
  | .obj kvs =>
      (match kvs.get? "stmt" with
        | some (Json.str t) => tags.contains t
        | _ => false)
      || kvs.toList.any (fun (_, v) => jsonMentionsStmt tags v)
  | .arr xs => xs.any (jsonMentionsStmt tags)
  | _ => false

/-- THE SCOPE RULE for the R1 declaration environment, one statement of it, audited construct by
construct (E6a audit fix round, 2026-09-24, the audit's F2; **corrected at fix round 2, the audit
RE-VERIFICATION's R1**): *a statement contributes to its ENCLOSING block exactly the declarations Go
gives the statements that FOLLOW it there, and nothing a scoped binder of its own introduces.* So
`jsonDeclaredLocals` — the walk the `block` fold runs per statement — descends into neither a
block-scoping statement's nested statement keys (`nestedStmtKeys`, below) NOR any binder a
construct declares for its own inner scope; the arm that decodes the construct extends the
environment itself, for the inner scope alone. The constructs with a scoped binder, each audited
once (fix round 2):

| wire node | binder | inner scope opened by | in the enclosing block |
| --- | --- | --- | --- |
| `block` / `breakable` / `labeled` | its `body`'s declarations | `decodeStmt`'s `block` fold | no (`body` skipped) |
| `if` | its `init`'s declarations | `decodeIf` (`initDeclaredLocals`, through a wrapping block) | no (`init`/`then`/`else` skipped) |
| `for` | its `init`'s declarations | `decodeFor` (`initDeclaredLocals`) | no (`init`/`post`/`condPre`/`body` skipped) |
| `range` | its `keyVar` / `valVar` | `decodeRange` (`rangeBinderLocals`) | **no** (`body` skipped AND the binders are not walked) |
| `select` | a receive clause's `targets` | the `select` arm, per clause | no (`clauses`/`default` skipped) |
| `func` / method | params, results | `decodeFunc` / `decodeMethod` | — (the function's own scope) |

A `switch` / type switch is not a wire node: the frontend desugars it, and its per-clause binder
arrives as a `declare` inside the clause's BLOCK — block scope, row one (witness `e6ats`). Every
other statement kind — the `unseq` node with its `then` completion and its allocation bodies
included — is ONE declaration site in its enclosing block and is walked whole.

The keys below are the nested-statement keys: a declaration under one of them belongs to the INNER
scope and never reaches the enclosing block's environment. -/
private def nestedStmtKeys : String → List String
  | "block" | "breakable" | "labeled" => ["body"]
  | "if" => ["init", "then", "else"]
  | "for" => ["init", "post", "condPre", "body"]
  | "range" => ["body"]
  | "select" => ["clauses", "default"]
  | _ => []

/-- A `range` statement's implicitly declared key / value variables, typed by the range kind exactly
as `decodeRange` types them: a map's key/value types, a channel's element, an index `int` + the
element for slices / arrays / array pointers, the operand's kind for an integer range, `int` +
`int32` for a string. They are declared for the loop's BODY and for nothing else — `decodeRange` is
the only caller (fix round 2 of the E6a audit, 2026-09-24, the re-verification's R1: while this
lived inside `jsonDeclaredLocals` the enclosing block's per-statement fold picked the binders up
when it walked the range node, and a legal program shadowing an outer variable of another type with
a range variable and graphing the OUTER one after the loop was refused whole — the scope rule on
`nestedStmtKeys`). -/
private def rangeBinderLocals (path : String) (kvs : StrictJson.Obj) : LowerM (Array LocalDecl) := do
  let var? (key : String) : Option String :=
    match kvs.get? key with
    | some (Json.str n) => some n
    | _ => none
  let tyOf (key : String) : LowerM (Option Ty) := do
    match kvs.get? key with
    | some t => pure (some (← decodeTy s!"{path}.range.{key}" t))
    | none => pure none
  -- B6: a range variable is a declaration site — `keyLocal` / `valLocal` carry the ids.
  let push (n? : Option String) (localKey : String) (t? : Option Ty) : LowerM (Array LocalDecl) := do
    match n?, t? with
    | some n, some t => pure #[{ name := n, id := ← declLocal s!"{path}.range.{localKey}" n (kvs.get? localKey), typ := t }]
    | _, _ => pure #[]
  match kvs.get? "kind" with
  | some (Json.str "map") =>
      pure ((← push (var? "keyVar") "keyLocal" (← tyOf "keyType")) ++ (← push (var? "valVar") "valLocal" (← tyOf "valueType")))
  | some (Json.str "chan") =>
      push (var? "keyVar") "keyLocal" (← tyOf "elemType")
  | some (Json.str "slice") | some (Json.str "array") | some (Json.str "array-pointer") =>
      pure ((← push (var? "keyVar") "keyLocal" (some (.int .int))) ++ (← push (var? "valVar") "valLocal" (← tyOf "elemType")))
  | some (Json.str "int") =>
      push (var? "keyVar") "keyLocal" (← tyOf "operandType")
  | some (Json.str "string") =>
      pure ((← push (var? "keyVar") "keyLocal" (some (.int .int))) ++ (← push (var? "valVar") "valLocal" (some (.int .int32))))
  | _ => pure #[]

/-- Stage E6a R1 (2026-09-24; the Stage E5 audit re-verification's R1, RATIFIED [USER] 2026-09-22
item 3 — «a decoder-wide cross-check of source-local annotations against their `declare` types»):
the LOCALS one statement DECLARES for the statements after it in its block, with their declared
types — a walk over the wire's own declaration spellings: every `{"target":"declare","id","type"}`
target (an assignment's lhs, the allocation / built-in / sync / type-assert / chan-recv targets — the
emitter's one target shape) and every `var` statement's `decls`. SCOPE-EXACT since the E6a audit fix
round (2026-09-24, F2): the walk does NOT descend into a block-scoping statement's nested bodies
(`nestedStmtKeys`) — what a `then` branch, a loop body or a `select` clause declares is theirs, not
the enclosing block's; the `block` arm of `decodeStmt` folds these per statement into
`LowerCtx.locals`, so at every statement the environment is exactly the declarations in scope
before it (Go: a variable's scope begins at the END of its declaration — a statement never sees its
own declarations). The tip's version walked the WHOLE body once per function (a flat table).
A construct's own scoped binders are NOT here either (fix round 2, the re-verification's R1): a
`range` node's key / value variables are `rangeBinderLocals`, opened by `decodeRange` for the body
alone — the scope rule on `nestedStmtKeys` has the full construct table. -/
private partial def jsonDeclaredLocals (path : String) : Json → LowerM (Array LocalDecl)
  | .obj kvs => do
      let mut acc : Array LocalDecl := #[]
      match kvs.get? "target", kvs.get? "id", kvs.get? "type" with
      | some (Json.str "declare"), some (Json.str name), some t =>
          let typ ← decodeTy s!"{path}.declare({name}).type" t
          let id ← declLocal s!"{path}.declare({name})" name (kvs.get? "local")
          acc := acc.push { name, id, typ }
      | _, _, _ => pure ()
      match kvs.get? "stmt" with
      | some (Json.str "var") =>
          match kvs.get? "decls" with
          | some (.arr ds) =>
              for d in ds do
                match d.getObjVal? "id", d.getObjVal? "type" with
                | .ok (Json.str name), .ok t =>
                    let typ ← decodeTy s!"{path}.var({name}).type" t
                    let id ← declLocal s!"{path}.var({name})" name (d.getObjVal? "local" |>.toOption)
                    acc := acc.push { name, id, typ }
                | _, _ => pure ()
          | _ => pure ()
      | _ => pure ()
      -- a `range` node's key / value variables are the BODY's alone (`rangeBinderLocals`, opened
      -- by `decodeRange`) — never the enclosing block's (fix round 2, the re-verification's R1)
      -- the nested bodies of a block-scoping statement are the INNER scope's (F2)
      let skip : List String := match kvs.get? "stmt" with
        | some (Json.str tag) => nestedStmtKeys tag
        | _ => []
      for (k, v) in kvs.toList do
        if !skip.contains k then
          acc := acc ++ (← jsonDeclaredLocals path v)
      pure acc
  | .arr xs => do
      let mut acc : Array LocalDecl := #[]
      for x in xs do
        acc := acc ++ (← jsonDeclaredLocals path x)
      pure acc
  | _ => pure #[]

/-- The declarations an `init` statement (of an `if` / `for`) contributes to the statement's own
scope: the init's declarations, looking THROUGH a wrapping `block` (the emitter may wrap an init
with its hoists) — Go's rule makes an init's declarations visible in the condition, the branches,
the loop body and the post statement, and nowhere after. -/
private partial def initDeclaredLocals (path : String) (json : Json) : LowerM (Array LocalDecl) := do
  match json with
  | .obj kvs =>
      match kvs.get? "stmt", kvs.get? "body" with
      | some (Json.str "block"), some (.arr body) => do
          let mut acc : Array LocalDecl := #[]
          for i in [:body.size] do
            acc := acc ++ (← initDeclaredLocals s!"{path}.body[{i}]" body[i]!)
          pure acc
      | _, _ => jsonDeclaredLocals path json
  | _ => jsonDeclaredLocals path json

/-- Decode under the environment extended by `more` (the declarations a control-flow statement
brings into scope for its bodies). -/
private def withLocals {α} (more : Array LocalDecl) (act : LowerM α) : LowerM α :=
  withReader (fun ctx => { ctx with locals := ctx.locals ++ more }) act

/-- Stage E6a R1: every SOURCE-LOCAL atom mentioned anywhere in an `unseq` node — an `ident` whose
name is not a reserved `$` slot, a `ref` of a source local — must be a local IN SCOPE at the node
(`LowerCtx.locals`: the enclosing function's params and results and the declarations that precede
the node in its enclosing blocks), and an `ident`'s `type` annotation must be the type of the
INNERMOST such declaration — the LAST entry of its name in the environment (a block-shadowing
redeclaration, a type-switch clause's per-clause binder, a per-iteration loop-variable copy sit
after the declaration they shadow). Stage C's D9 trusted a source-local atom's annotation (the
wire's word, not the decoder's knowledge): the E5 audit re-verification's mS1 / mS4 forged an
annotation together with a `map-lookup`'s / `map` target plan's keyType on a PRIVATE map base and
the wire decoded and ANSWERED; the emitter spells the annotation from the one go/types object the
`declare` carries, so no emitted wire changes. The E6a tip checked against the SET of every type
the whole function declared under the name (a flat table) — the E6a audit's F2 forged a
type-switch clause binder's annotation to the OTHER clause's type and the wire decoded and
answered; since the fix round (2026-09-24) the environment is scope-exact and that forgery, the
block-shadow forgery and an atom naming a local declared only later or in a sibling block all
refuse by name (`Tests/unseq-wire/mut-local-{annotation-shadowed,shadow-other-decl,out-of-scope}`). -/
private partial def unseqCheckLocalAtoms (locals : Array LocalDecl) (slots : Array String) (path : String) : Json → LowerM Unit
  | .obj kvs => do
      match kvs.get? "expr", kvs.get? "name" with
      | some (Json.str "ident"), some (Json.str n) =>
          -- B6: a `$`-spelled mention is a SLOT by the frontend's reservation (its temps and
          -- binders); one that is neither a cell nor a target binder is unknown, never an admitted
          -- source-local read (formerly `UnseqGraph.wellFormed?`'s «unknown slot» check — a spelling
          -- test, so it lives here since numeric locals).
          if n.startsWith "$" && !slots.contains n then
            fail s!"unseq: unknown slot '{n}' mentioned at {path} (neither a binder cell nor a target binder of this graph); refused by name"
          if !n.startsWith "$" then
            match locals.findRev? (·.name == n) with
            | none =>
                fail s!"unseq: source-local atom '{n}' at {path} has no declaration in the enclosing function that is in scope at this statement (its params, results, and the `declare` / var / range / clause declarations that precede the statement in its enclosing blocks) — the graph may name only locals in scope (Stage E6a R1, scope-exact since the audit fix round 2026-09-24); refused by name"
            | some d =>
                match kvs.get? "type" with
                | some t =>
                    let ty ← decodeTy s!"{path}.type" t
                    if d.typ != ty then
                      fail s!"unseq: source-local atom '{n}' at {path} is annotated {repr ty}, which disagrees with its declaration {repr d.typ} (the innermost declaration of '{n}' in scope at this statement) — a forged annotation must not type a graph operand (the Stage E5 audit re-verification's R1, ratified 2026-09-22; Stage E6a; scope-exact since the E6a audit fix round 2026-09-24); refused by name"
                | none => pure ()
      | _, _ => pure ()
      match kvs.get? "expr", kvs.get? "id" with
      | some (Json.str "ref"), some (Json.str n) =>
          if !n.startsWith "$" && !(locals.any (·.name == n)) then
            fail s!"unseq: `ref` of '{n}' at {path} names no local the enclosing function declares in scope at this statement (Stage E6a R1, 2026-09-24); refused by name"
      | _, _ => pure ()
      for (_, v) in kvs.toList do
        unseqCheckLocalAtoms locals slots path v
  | .arr xs => xs.forM (unseqCheckLocalAtoms locals slots path)
  | _ => pure ()

/-- D8 for an `eval` head: one of the admitted heads over ATOM operands, or a
bare CONSTANT (`int`/`bool`/`string`) — the emitter's copy of a constant into a
cell where the consumer needs one (a guard's test, a phase-2 store's value;
design §6 «a constant or atom value is copied into one»): trivially in normal
form (no read, no failure), typed by the wire's own annotation, which D9 checks
against the cell (a constant whose type disagrees with its slot refuses there).
Admitted at the Stage C audit fix round (2026-09-20, F2): the C1 arm listed no
constant head and refused the frontend's own emission — legal Go that ran on
main (`x := true && f()`, `a[f()] = 5`) refused by name; rows
`evalorder/unseq-const-cell/*`. The one structural exception is a `slice` whose
`high` is `builtin-len` of the SAME base atom — spec#Slice_expressions' default
high («the length of the sliced operand»), which the emitter spells as a length
of the one evaluated base. Stage E E1 (2026-09-21) admits the `deref` head over
an atom or a `globaladdr` pointer — the READ of a package-level variable
(`deref(globaladdr)`) and, for E2, of `*p`. -/
private def unseqCheckHead (cells : Array LocalDecl) (path : String) (head : Json) : LowerM Unit := do
  if jsonMentionsRecover head then
    fail s!"unseq: recover() inside an occurrence head at {path} — recover is an EVENT (it changes the continuation), never a pure op (v2.1 §3.1); refused by name"
  let obj ← StrictJson.obj path head
  let tag ← StrictJson.string s!"{path}.expr" (← StrictJson.field path obj "expr")
  let atom (key : String) : LowerM Unit := do
    let j ← StrictJson.field path obj key
    if !unseqIsAtom j then
      fail s!"unseq: hidden read in a pure node — {path}.{key} is not an atom (an identifier or an int/bool/string constant; v2.1 §3.1 internal normal form); refused by name"
  match tag with
  | "ident" => pure ()
  | "int" | "bool" | "string" => pure ()   -- a constant copied into a cell (D9 types it)
  | "index-get" => do atom "base"; atom "index"
  | "slice" => do
      atom "base"
      atom "low"
      let hi ← StrictJson.field path obj "high"
      if !unseqIsAtom hi then
        match hi.getObjVal? "expr", hi.getObjVal? "operand", obj.get? "base" with
        | .ok (.str "builtin-len"), .ok operand, some base =>
            if operand != base then
              fail s!"unseq: hidden read in a pure node — {path}.high is the length of an operand other than the slice's own base; refused by name"
        | _, _, _ =>
            fail s!"unseq: hidden read in a pure node — {path}.high is neither an atom nor the base's own length (the default high); refused by name"
      if obj.contains "max" then atom "max"
  | "builtin-len" | "builtin-cap" => atom "operand"
  | "min" | "max" =>
      -- Stage E5 E5a (2026-09-22): `min`/`max` are E1 participants (reading (a), RATIFIED [USER]
      -- 2026-09-22) — pure heads over ATOM operands (Expr.minOf/maxOf: ints or strings), their
      -- `after` edge the lowering's; at least one operand (Go's arity).
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      if args.isEmpty then
        fail s!"unseq: {tag} with no operands at {path} (Go requires at least one); refused by name"
      for k in [:args.size] do
        if !unseqIsAtom args[k]! then
          fail s!"unseq: hidden read in a pure node — {path}.args[{k}] is not an atom (an identifier or an int/bool/string constant; v2.1 §3.1 internal normal form); refused by name"
  | "binary" => do
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      if op == "&&" || op == "||" then
        fail s!"unseq: logical operator '{op}' in a head at {path} — a logical operation is a GUARD entry + completion (v2.1 §1 G), never a pure op; refused by name"
      atom "x"
      atom "y"
  | "unary" => atom "x"
  | "type-assert" => atom "operand"
  | "field-get" =>
      -- Stage E, family E2 (2026-09-21): ONE field read — the receiver is an atom (a struct
      -- value: a source local or a slot) or `deref(atom)` (through a pointer: the emitter's
      -- own spelling, `fieldBase`; the nil check and the load are one occurrence).
      let recv ← StrictJson.field path obj "recv"
      if !unseqIsAtom recv then
        match recv.getObjVal? "expr", recv.getObjVal? "ptr" with
        | .ok (.str "deref"), .ok p =>
            if !unseqIsAtom p then
              fail s!"unseq: hidden read in a pure node — {path}.recv dereferences a non-atom pointer; refused by name"
        | _, _ =>
            fail s!"unseq: hidden read in a pure node — {path}.recv is neither an atom nor the dereference of an atom (a field read selects on a struct VALUE or through a pointer VALUE; v2.1 §3.1 internal normal form); refused by name"
  | "map-get" =>
      -- Stage E E2: ONE map read on the frozen map VALUE and key VALUE (both atoms).
      atom "base"
      atom "index"
      -- Stage E5 audit fix round F1 (2026-09-22): the head's keyType/valueType are the base's own map type.
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valueTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      unseqCheckMapBase cells s!"{path}.base" "map-get head" (← StrictJson.field path obj "base") keyTy valueTy
  | "deref" =>
      -- Stage E, family E1 (2026-09-21, lane `core/unseq-stage-e-0921`): ONE checked read
      -- through a pointer VALUE — the pointer is an atom (a slot or an admitted local:
      -- `*p`, the E2 family's spelling) or a `globaladdr` (a package-level variable's
      -- statically resolved cell: `deref(globaladdr gid)` is the frontend's own spelling of a
      -- global READ, `emitIdent`). Anything else in the pointer position is a hidden read.
      let p ← StrictJson.field path obj "ptr"
      let isGlobal := match p.getObjVal? "expr" with
        | .ok (.str "globaladdr") => true
        | _ => false
      if !(unseqIsAtom p || isGlobal) then
        fail s!"unseq: hidden read in a pure node — {path}.ptr is neither an atom nor a globaladdr (a pointer read dereferences a pointer VALUE or a package-level variable's cell; v2.1 §3.1 internal normal form); refused by name"
  | "convert" | "bytes-from-string" | "string-from-bytes" | "string-from-rune"
  | "runes-from-string" | "string-from-runes" =>
      -- Stage E E4 (2026-09-21): a CONVERSION is a pure op over ONE atom — it cannot fail
      -- inside the frontend's type grammar (slice-to-array conversions are refused there;
      -- an interface target is a box, E5's), so it is never an occurrence of its own.
      atom "x"
  | "struct-lit" =>
      -- Stage E E4: a VALUE struct literal over PAYLOADS (atoms, boxed atoms, zero values).
      unseqCheckStructLit path head
  | other =>
      fail s!"unseq: head '{other}' at {path} is outside the admitted fragment (admitted heads: ident, a constant (int/bool/string), index-get, slice, builtin-len, builtin-cap, min, max, binary, unary, type-assert, deref, field-get, map-get, convert and the string/byte/rune conversion forms, struct-lit); refused by name"

/-- D8 for an `invoke` callee: an identifier (a func-typed local or slot) or
a `func-value` whose captures are addresses (`ref`/`ident`/`globaladdr`) of SOURCE
locations — never `ref` of a `$` binder cell (audit F2, 2026-09-21). -/
private def unseqCheckCallee (path : String) (callee : Json) : LowerM Unit := do
  if jsonMentionsRecover callee then
    fail s!"unseq: recover() in a callee at {path}; refused by name"
  match callee.getObjVal? "expr" with
  | .ok (.str "ident") => pure ()
  | .ok (.str "func-value") =>
      let obj ← StrictJson.obj path callee
      let caps ← StrictJson.array s!"{path}.captured" (← StrictJson.field path obj "captured")
      for c in caps do
        if let some id := unseqRefOfBinder? c then
          fail s!"unseq: a func-value capture at {path}.captured takes the address of a binder cell '{id}' — a graph cell is written only by its producer, and the frontend captures source locations only (audit F2, 2026-09-21); refused by name"
        match c.getObjVal? "expr" with
        | .ok (.str "ref") | .ok (.str "ident") | .ok (.str "globaladdr") => pure ()
        | _ => fail s!"unseq: a func-value capture at {path}.captured is not an address (ref / ident / globaladdr); refused by name"
  | _ => fail s!"unseq: callee at {path} is neither an identifier nor a func-value — an invocation's callee is already evaluated (v2.1 §3.1); refused by name"

/-- D8 for an `invoke` argument: an atom, a boxing `to-interface` of an atom, or —
Stage E E3 (2026-09-21) — a FROZEN ADDRESS (`ref` of a source local, `globaladdr`
of a package-level variable): the implicit `&x` of a pointer-receiver method call
on an addressable variable, an address formation that reads nothing and cannot
fail (spec#Address_operators; the callee's captures are the same shapes). -/
private def unseqCheckArg (path : String) (arg : Json) : LowerM Unit := do
  if jsonMentionsRecover arg then
    fail s!"unseq: recover() in an argument at {path}; refused by name"
  if let some id := unseqRefOfBinder? arg then
    fail s!"unseq: an invocation argument at {path} takes the address of a binder cell '{id}' — a graph cell is written only by its producer; an address argument is `ref` of a SOURCE local or a `globaladdr` (audit F2, 2026-09-21); refused by name"
  let isAddr := match arg.getObjVal? "expr" with
    | .ok (.str "ref") | .ok (.str "globaladdr") => true
    | _ => false
  if unseqIsAtom arg || isAddr then pure ()
  else
    match arg.getObjVal? "expr", arg.getObjVal? "operand" with
    | .ok (.str "to-interface"), .ok operand =>
        if !unseqIsAtom operand then
          fail s!"unseq: hidden read in an argument — {path} boxes a non-atom; refused by name"
    | _, _ =>
        fail s!"unseq: hidden read in an argument — {path} is not an atom (or a boxed atom); an invocation's arguments are already evaluated (v2.1 §3.1); refused by name"

/-- The guards whose regions enclose occurrence `o`, outermost last (regions
nest by chaining; bounded by the graph's size). -/
private def unseqRegionChain (g : UnseqGraph) (o : UnseqOcc) : List String :=
  let rec go (r : Option String) (fuel : Nat) : List String :=
    match fuel, r with
    | 0, _ => []
    | _, none => []
    | fuel + 1, some gn =>
        gn :: (match g.occs.find? (·.name == gn) with
          | some go' => go go'.region fuel
          | none => [])
  go o.region g.occs.length

/-- The region a binder is CONFINED to (D12, STATIC G): its producer's region —
unless the producer is that guard's completion (the one join), in which case
the binder is confined to THE GUARD'S OWN region (its `region`, if any; `none`
for a top-level guard). The audit fix round (2026-09-20, F3) added the second
half: the C1 arm exempted a completion binder from confinement altogether, so a
NESTED guard's completion (`(a && (b || f())) && g()`: the inner `||`'s `$u3`,
produced by its join inside the outer `&&`'s region) could be consumed by a
hand-built `then` OUTSIDE the outer region — the wire decoded, ran when the
outer region was active, and was refused only DYNAMICALLY when it was skipped
(`UnseqGraph.unproducedConsumer?`, GoLean/GoCore/Unseq.lean — the machine's
own refusal, unchanged, stays behind this static net as defence in depth;
mutant `mut-nested-completion-join`). -/
private def unseqConfinedTo? (g : UnseqGraph) (slot : VarId) : Option String :=
  match (g.producer? slot).bind (g.occs[·]?) with
  | some p =>
      match p.region with
      | some gn =>
          match g.occs.find? (·.name == gn) with
          | some ⟨_, .guard _ _ out, _, guardRegion⟩ =>
              if out == slot then guardRegion else some gn
          | _ => some gn
      | none => none
  | none => none

/-- D13: a target plan's shape — a plain source local; a slice element whose
base and index are atoms (the header FROZEN through the atom: a slot, or the
local read at the plan step — never `&a`, Stage B F2); and, since Stage E E2
(2026-09-21): a DEREFERENCE target on a pointer atom (`addr(p)` — the pointer
VALUE frozen), a FIELD target on a pointer atom or a variable's address
(`addr(field-addr(p | ref s | globaladdr))` — a stable anchor; the machine's
`unseqUnfrozenPlan?` refuses a slice-variable address under an index step, not
a field step), and a MAP-ELEMENT target on a map atom and a key atom
(`mapElem` — the map VALUE and key VALUE frozen; the store's nil-map check is
phase 2's). -/
private def unseqCheckTargetShape (path : String) (a : Assignee) : LowerM Unit :=
  let atomE : Expr → Bool
    | .var _ | .intLit _ _ | .boolLit _ | .stringLit _ => true
    | _ => false
  let anchorE : Expr → Bool
    | .var _ | .ref _ | .global _ => true
    | _ => false
  match a with
  | .var id => do
      -- B6: a binder / temporary is an INTERNED id (≥ the function's wire-table
      -- size); a source local's id is below it (the spelling test `$`, restated).
      if id ≥ (← get).base then
        fail s!"unseq: a binder (slot {id}) cannot be a store target at {path}; refused by name"
      else pure ()
  | .addr (.indexAddr base idx) =>
      if atomE base && atomE idx then pure ()
      else fail s!"unseq: target plan at {path} indexes with a non-atom base or index (the header and index are frozen VALUES, v2.1 §3.4); refused by name"
  | .addr (.var _) => pure ()
  | .addr (.fieldAddr base _ _) =>
      if anchorE base then pure ()
      else fail s!"unseq: target plan at {path} selects a field on a non-atom base (the pointer VALUE or the variable's address is the frozen anchor, v2.1 §3.4); refused by name"
  | .mapElem base key _ _ =>
      if atomE base && atomE key then pure ()
      else fail s!"unseq: target plan at {path} indexes a map with a non-atom base or key (the map VALUE and key VALUE are frozen, v2.1 §3.4); refused by name"
  | _ => fail s!"unseq: target plan at {path} is outside the admitted fragment (a local; a slice element, a dereference, a field or a map element on atoms); refused by name"

/-- B6: a graph BINDER (a cell, a value/target slot) is a `$`-temporary — the
frontend's reservation (audit F3, 2026-09-16, formerly `UnseqGraph.wellFormed?`'s
first check: the cells are declared into the SOURCE scope at ENTER, so a bare
name would shadow the source local of that name for the rest of the block) —
interned like every other temporary; a bare spelling refuses by name. -/
private def binder (path spelling : String) : LowerM VarId := do
  if spelling.startsWith "$" then tmp spelling
  else fail s!"unseq: binder '{spelling}' at {path} is not a reserved `$` slot name (every binder cell and target binder is `$`-prefixed — the frontend's reservation; a bare name would shadow the source local '{spelling}' for the rest of the block); refused by name"

mutual

/-- Lower a statement. `results` are the enclosing function's result params. -/
partial def decodeStmt (results : Array Param) (path : String) (json : Json) : LowerM Stmt := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.stmt" (← StrictJson.field path obj "stmt")
  -- `for`/`range` check their own keys (their decoders are also
  -- reached directly through the `labeled` wrapper).
  checkKindKeys path obj stmtAllowedKeys tag
  match tag with
  | "block" =>
      let body ← StrictJson.array s!"{path}.body" (← StrictJson.field path obj "body")
      -- E6a audit fix round (2026-09-24, F2 — the R1 environment is SCOPE-EXACT): each statement
      -- decodes under the locals declared BEFORE it in this block and in the enclosing scopes; its
      -- own declarations join the environment for the statements AFTER it, never for itself.
      let mut env := (← read).locals
      let mut stmts : Array Stmt := #[]
      for i in [:body.size] do
        let s := body[i]!
        stmts := stmts.push
          (← withReader (fun ctx => { ctx with locals := env }) (decodeStmt results s!"{path}.body[{i}]" s))
        env := env ++ (← jsonDeclaredLocals s!"{path}.body[{i}]" s)
      pure (.block #[] stmts)
  | "defer" =>
      let callee ← decodeExpr s!"{path}.callee" (← StrictJson.field path obj "callee")
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.deferCall callee
        (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "go" =>
      -- `go f(args)` (channels arc slice 2): the defer wire shape — the
      -- callee and arguments evaluate at the go statement, in the
      -- spawning goroutine; the spawn itself is the pool's step.
      let callee ← decodeExpr s!"{path}.callee" (← StrictJson.field path obj "callee")
      let args ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      pure (.goStmt callee
        (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)))
  | "panic" =>
      -- The payload's `any`-conversion: a "wrap" type wraps via the
      -- machine's `toInterface` (its `checkedDynamicTy` fails closed on
      -- unsupported dynamics); no "wrap" means the argument is already an
      -- interface (or the untyped-nil payload).
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      -- "runtimeError": the lowering SYNTHESIZED a Go runtime panic (today:
      -- the nil-interface method-value creation check, design note D6) —
      -- the payload boxes as the machine's `runtime.Error` sentinel so
      -- recover values, type asserts, and abort rendering all match Go's
      -- runtime errors, never a user string. A PRESENT key is decoded
      -- STRICTLY (audit F7: a malformed flag used to fall open to a
      -- user-string payload); `false` is well-formed and means "not a
      -- runtime error".
      let runtimeErr ← match obj.get? "runtimeError" with
        | some flag => StrictJson.bool s!"{path}.runtimeError" flag
        | none => pure false
      if runtimeErr then
        pure (.panicStmt (.toInterface (.interface ⟨"any"⟩)
          (.defined runtimeErrorTypeIdx) value))
      else
      match obj.get? "wrap" with
      | some t =>
          let ty ← decodeTy s!"{path}.wrap" t
          pure (.panicStmt (.toInterface (.interface ⟨"any"⟩) ty value))
      | none => pure (.panicStmt value)
  | "breakable" =>
      pure (.breakable (← decodeStmt results s!"{path}.body"
        (← StrictJson.field path obj "body")))
  | "return" =>
      decodeReturn results path obj
  | "assign" =>
      decodeAssign results path obj
  | "type-assert" =>
      -- Comma-ok assert `v, ok := x.(T)` (Stmt.typeAssert: never panics;
      -- blanks route to typed discard temps like decodeAssign's).
      let tJson ← StrictJson.field path obj "target"
      let okJson ← StrictJson.field path obj "okTarget"
      let e ← decodeExpr s!"{path}.expr" (← StrictJson.field path obj "expr")
      let ty ← decodeTy s!"{path}.targetType" (← StrictJson.field path obj "targetType")
      let mut decls : Array Stmt := #[]
      let mut vAssignee : Assignee := .unsupported "type-assert target"
      let mut okAssignee : Assignee := .unsupported "type-assert okTarget"
      if targetIsBlank tJson then
        let ta ← tmp "$ta"
        decls := decls.push (.initialization { id := ta, typ := ty })
        vAssignee := .var ta
      else
        let t ← decodeTarget s!"{path}.target" tJson
        decls := decls ++ (← declaresOf #[t])
        vAssignee := t.assignee
      if targetIsBlank okJson then
        let taok ← tmp "$taok"
        decls := decls.push (.initialization { id := taok, typ := .bool })
        okAssignee := .var taok
      else
        let okT ← decodeTarget s!"{path}.okTarget" okJson
        decls := decls ++ (← declaresOf #[okT])
        okAssignee := okT.assignee
      return .seqn (decls.push (.typeAssert vAssignee okAssignee e ty))
  | "var" =>
      decodeVar path obj
  | "if" =>
      decodeIf results path obj
  | "for" =>
      decodeFor results path obj
  | "incdec" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let read ← decodeExpr s!"{path}.read" (← StrictJson.field path obj "read")
      -- The synthetic 1 takes the OPERAND's kind: float operands get a
      -- float-kinded literal (floats slice F3 — an int 1 would be a
      -- kind-mismatched operand in the machine; floats/incdec pins it).
      -- FAIL CLOSED on a non-numeric carried type (BUG-042: a named wire
      -- type silently defaulted to int here, producing a kind-mismatched
      -- add; the frontend now resolves defined types to the underlying
      -- basic kind, and a named type reaching this slot again is a
      -- frontend defect, never a default).
      -- A MISSING type fails closed too (maint-check note: the frontend
      -- always emits one, and an absent-kind default is the same silent
      -- shape as the named-type default this arm just removed; the
      -- float-literal arm set the precedent).
      let one : Expr ← match (← optType path obj) with
        | some (.float k) => pure (.floatLit 1 1 k)
        | some (.int k) => pure (.intLit 1 k)
        | none => fail s!"incdec at {path} carries no operand type — the synthetic 1 has no kind to take"
        | some other => fail s!"incdec at {path} carries a non-numeric operand type ({repr other}) — the synthetic 1 has no kind to take"
      let rhs := if op == "-" then Expr.sub read one else Expr.add read one
      pure (.assign t.assignee rhs)
  | "compound-assign" =>
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let read ← decodeExpr s!"{path}.read" (← StrictJson.field path obj "read")
      let rhs ← decodeExpr s!"{path}.rhs" (← StrictJson.field path obj "rhs")
      let combined ← decodeCompound op read rhs
      pure (.assign t.assignee combined)
  | "expr" =>
      -- A bare statement-position call DISCARDS its results (spec
      -- §Expression statements: no `_ =` required). The machine's frame
      -- exit stores results into targets positionally and goes stuck on
      -- arity mismatch, so a value-returning callee needs typed discard
      -- temps — exactly decodeAssign's blank-target mechanism, driven by
      -- the call node's `resultTypes` (BUG-012 fix, arc-final audit F11,
      -- 2026-08-06). The vector is REQUIRED (BUG-110): its length IS the
      -- callee's arity, so an absent vector no longer falls back to the
      -- targetless lowering — a wire without it refuses by name.
      let e ← StrictJson.field path obj "expr"
      let discardTemps (prefixName : String) (callJson : Json) :
          LowerM (Array Stmt × Array Assignee) := do
        let callObj ← StrictJson.obj s!"{path}.expr" callJson
        let rt ← StrictJson.field s!"{path}.expr" callObj "resultTypes"
        let arr ← StrictJson.array s!"{path}.expr.resultTypes" rt
        let tys ← arr.mapIdxM (fun i t => decodeTy s!"{path}.expr.resultTypes[{i}]" t)
        let ids ← tys.mapIdxM (fun i _ => tmp s!"{prefixName}{i}")
        let decls := tys.mapIdx (fun i ty =>
          Stmt.initialization { id := ids[i]!, typ := ty })
        let assignees := tys.mapIdx (fun i _ =>
          Assignee.var ids[i]!)
        pure (decls, assignees)
      match ← asCall? e with
      | some (name, args) =>
          let (decls, assignees) ← discardTemps "$cr" e
          let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)
          if decls.isEmpty then
            pure (.call #[] ⟨name⟩ argsE)
          else
            pure (.seqn (decls.push (.call assignees ⟨name⟩ argsE)))
      | none =>
          match ← asCallValue? e with
          | some (callee, args) =>
              let (decls, assignees) ← discardTemps "$cv" e
              let calleeE ← decodeExpr s!"{path}.expr.callee" callee
              let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)
              if decls.isEmpty then
                pure (.callValue #[] calleeE argsE)
              else
                pure (.seqn (decls.push (.callValue assignees calleeE argsE)))
          | none =>
              -- A bare-statement `sync/atomic` op DISCARDS its result
              -- (atomics arc wave 1): no target — `atomicPlan` admits
              -- the empty target list for every head, and the machine
              -- drops the result value.
              match ← asAtomicOp? e with
              | some (op, kind, args) =>
                  let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)
                  pure (.atomicStmt op kind argsE #[])
              | none =>
              -- A bare `m.TryLock()` statement DISCARDS its result but
              -- still acquires (Q-TRYLOCK): no target — `syncPlan`
              -- admits the empty target list for the TRY heads.
              match ← asSyncValueOp? e with
              | some (op, args) =>
                  let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.expr.args[{i}]" a)
                  pure (.syncStmt op argsE #[])
              | none => fail s!"expression statement is not a call at {path} (calls are the only effectful expressions modeled)"
  | "range" =>
      decodeRange results path obj
  | "new" =>
      -- &T{...}: allocate `value` and bind its address into `target`.
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      let elemTy ← decodeTy s!"{path}.elemType" (← StrictJson.field path obj "elemType")
      pure (.seqn ((← declaresOf #[t]).push (.allocNew t.assignee value elemTy)))
  | "make-slice" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let lenE ← decodeExpr s!"{path}.len" (← StrictJson.field path obj "len")
      let capE ← (match obj.get? "cap" with
        | some c => do pure (some (← decodeExpr s!"{path}.cap" c))
        | none => pure none)
      pure (.seqn ((← declaresOf #[t]).push (.makeSlice t.assignee elemTy lenE capE)))
  | "make-map" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      -- `hint` is present EXACTLY when the Go source has a second `make`
      -- argument (emit.go `emitMake`, BUG-082 fix 2026-09-02); it decodes
      -- into `Stmt.makeMap`'s `initialSpace`, the operand the makeMap arm
      -- EVALUATES (spec#Order_of_evaluation) and then ignores (gc clamps).
      -- The two shapes are the only ones accepted: the strict key list
      -- refuses any other field, and a present-but-malformed hint fails
      -- in `decodeExpr` naming its path.
      let hintE ← (match obj.get? "hint" with
        | some h => do pure (some (← decodeExpr s!"{path}.hint" h))
        | none => pure none)
      pure (.seqn ((← declaresOf #[t]).push (.makeMap t.assignee keyTy valTy hintE)))
  -- Channel statements (channels arc slice 1). All decode arms fail
  -- closed on malformed shapes (target counts, clause kinds, directions).
  | "make-chan" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let capE ← (match obj.get? "cap" with
        | some c => do pure (some (← decodeExpr s!"{path}.cap" c))
        | none => pure none)
      pure (.seqn ((← declaresOf #[t]).push (.makeChan t.assignee elemTy capE)))
  | "chan-send" =>
      let chE ← decodeExpr s!"{path}.ch" (← StrictJson.field path obj "ch")
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.chanSend chE value elemTy)
  | "chan-recv" =>
      let targetsJ ← StrictJson.array s!"{path}.targets" (← StrictJson.field path obj "targets")
      if targetsJ.size > 2 then
        fail s!"channel receive with {targetsJ.size} targets at {path}"
      let ts ← targetsJ.mapIdxM (fun i t => decodeTarget s!"{path}.targets[{i}]" t)
      let chE ← decodeExpr s!"{path}.ch" (← StrictJson.field path obj "ch")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.seqn ((← declaresOf ts).push (.chanRecv (ts.map (·.assignee)) chE elemTy)))
  | "chan-close" =>
      pure (.closeChan (← decodeExpr s!"{path}.ch" (← StrictJson.field path obj "ch")))
  -- Sync statements (spec-parity slice 2, design note §§3-4): `args`
  -- carries the RECEIVER ADDRESS expression (plus the delta for
  -- wgAdd); `onceBegin` additionally carries the Once desugar's fresh
  -- bool target (declared here, the make-chan Target shape). Arity and
  -- target validation happen again in `syncPlan` (fail closed twice).
  | "sync-op" =>
      let opName ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let argsJ ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      let args ← argsJ.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a)
      let plain (op : SyncStmtOp) (arity : Nat) : LowerM Stmt := do
        if args.size != arity then
          fail s!"sync op {opName} expects {arity} operand(s), got {args.size} at {path}"
        pure (.syncStmt op args #[])
      let tryStmt (op : SyncStmtOp) : LowerM Stmt := do
        if args.size != 1 then
          fail s!"sync op {opName} expects 1 operand, got {args.size} at {path}"
        match obj.get? "target" with
        | none => pure (.syncStmt op args #[])
        | some tj => do
            let t ← decodeTarget s!"{path}.target" tj
            pure (.seqn ((← declaresOf #[t]).push (.syncStmt op args #[t.assignee])))
      match opName with
      | "lock" => plain .lock 1
      -- The TRY heads in STATEMENT position: with a `target` (the bodied
      -- stub's declared Bool temp — the onceBegin shape) or without (a
      -- bare `m.TryLock()` discards the result; the hoisted valued form
      -- arrives as the `sync-op` EXPRESSION node instead).
      | "tryLock" => tryStmt .tryLock
      | "tryRLock" => tryStmt .tryRLock
      | "tryWLock" => tryStmt .tryWLock
      | "unlock" => plain .unlock 1
      | "rlock" => plain .rlock 1
      | "runlock" => plain .runlock 1
      | "wlock" => plain .wlock 1
      | "wunlock" => plain .wunlock 1
      | "wgAdd" => plain .wgAdd 2
      | "wgWait" => plain .wgWait 1
      | "onceComplete" => plain .onceComplete 1
      | "onceBegin" => do
          if args.size != 1 then
            fail s!"sync op onceBegin expects 1 operand, got {args.size} at {path}"
          let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
          pure (.seqn ((← declaresOf #[t]).push (.syncStmt .onceBegin args #[t.assignee])))
      | other => fail s!"unsupported sync op {other} at {path}"
  | "select" =>
      -- Receive-clause targets are the frontend's fresh temps; their
      -- declares lift OUT in front of the select (fresh names — the
      -- pre-declaration is unobservable), leaving plain var targets for
      -- the machine's post-selection stores.
      let clausesJ ← StrictJson.array s!"{path}.clauses" (← StrictJson.field path obj "clauses")
      let mut decls : Array Stmt := #[]
      let mut cls : Array (SelectClauseHead × Stmt) := #[]
      for i in [:clausesJ.size] do
        match clausesJ[i]? with
        | some cJ =>
            let cpath := s!"{path}.clauses[{i}]"
            let co ← StrictJson.obj cpath cJ
            let ckind ← StrictJson.string s!"{cpath}.clause" (← StrictJson.field cpath co "clause")
            -- F2 (scope-exact R1): a receive clause's declared targets are in scope in THAT clause's
            -- body and nowhere else.
            let clauseLocals ← match co.get? "targets" with
              | some tJ => jsonDeclaredLocals s!"{cpath}.targets" tJ
              | none => pure #[]
            let body ← withLocals clauseLocals (decodeStmt results s!"{cpath}.body" (← StrictJson.field cpath co "body"))
            match ckind with
            | "send" =>
                checkAllowedKeys cpath co ["clause", "ch", "value", "elem", "body"]
                let chE ← decodeExpr s!"{cpath}.ch" (← StrictJson.field cpath co "ch")
                let value ← decodeExpr s!"{cpath}.value" (← StrictJson.field cpath co "value")
                let elemTy ← decodeTy s!"{cpath}.elem" (← StrictJson.field cpath co "elem")
                cls := cls.push (.send chE value elemTy, body)
            | "recv" =>
                checkAllowedKeys cpath co ["clause", "targets", "ch", "elem", "body"]
                let targetsJ ← StrictJson.array s!"{cpath}.targets" (← StrictJson.field cpath co "targets")
                if targetsJ.size > 2 then
                  fail s!"select receive with {targetsJ.size} targets at {cpath}"
                let ts ← targetsJ.mapIdxM (fun j t => decodeTarget s!"{cpath}.targets[{j}]" t)
                decls := decls ++ (← declaresOf ts)
                let chE ← decodeExpr s!"{cpath}.ch" (← StrictJson.field cpath co "ch")
                let elemTy ← decodeTy s!"{cpath}.elem" (← StrictJson.field cpath co "elem")
                cls := cls.push (.recv (ts.map (·.assignee)) chE elemTy, body)
            | other => fail s!"unsupported select clause kind {other} at {cpath}"
        | none => pure ()
      let default? ← (match obj.get? "default" with
        | some dJ => do pure (some (← decodeStmt results s!"{path}.default" dJ))
        | none => pure none)
      pure (.seqn (decls.push (.selectStmt cls default?)))
  | "map-delete" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      pure (.mapDelete base index keyTy)
  | "clear-map" =>
      pure (.clearMap (← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")))
  | "clear-slice" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      pure (.clearSlice base elemTy)
  | "print" =>
      -- `print`/`println` (stdlib slice 3): `newline` selects println.
      -- ZERO operands refuse here too (the frontend refuses first; the
      -- wide-statement mold has no nullary plan — A8), so a hand-edited
      -- wire cannot reach an unplanned statement.
      let newline ← StrictJson.bool s!"{path}.newline" (← StrictJson.field path obj "newline")
      let argsJ ← StrictJson.array s!"{path}.args" (← StrictJson.field path obj "args")
      if argsJ.isEmpty then
        throw s!"{path}.args: print/println with zero operands has no machine shape (refused by name; stdlib slice 3)"
      let args ← argsJ.mapIdxM (fun i j => decodeExpr s!"{path}.args[{i}]" j)
      pure (.print newline args)
  -- `sort-slice` (the quorum-pilot `sortSlice` machine op's wire node) is
  -- NOT decoded since 2026-09-04 (memo §3 row M, lane fr4-rowm audit fix
  -- round A3): the frontend never emits it — `slices.Sort` is the real
  -- source-through generic — and a hand-edited wire carrying it would
  -- realize a DIFFERENT sort member than the one the frontend now emits.
  -- It falls to the `unsupported statement` refusal below, by name. The
  -- `Stmt.sortSlice` constructor and its Machine/Ops arms are GoCore's;
  -- their deletion is the design-hygiene arc's item A11.
  | "append" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let slice ← decodeExpr s!"{path}.slice" (← StrictJson.field path obj "slice")
      let elems ← decodeExpr s!"{path}.elems" (← StrictJson.field path obj "elems")
      pure (.seqn ((← declaresOf #[t]).push (.appendSlice t.assignee elemTy slice elems)))
  | "copy" =>
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let dst ← decodeExpr s!"{path}.dst" (← StrictJson.field path obj "dst")
      let src ← decodeExpr s!"{path}.src" (← StrictJson.field path obj "src")
      pure (.seqn ((← declaresOf #[t]).push (.copySlice t.assignee dst src)))
  | "unseq-probe" =>
      -- The unsequenced-operand probe (latitude E13 option (b), lane e13-b
      -- 2026-09-05; `Stmt.unseqProbe` is the envelope statement). The
      -- frontend never probes an operand containing `recover()` — the
      -- machine evaluates a probed operand TWICE (once at the probe, once
      -- at its residual position), which would consume the recover; this
      -- decoder refuses such a probe BY NAME so a hand-edited or drifted
      -- wire cannot reach the machine with one (fail closed).
      let exprJ ← StrictJson.field path obj "expr"
      if jsonMentionsRecover exprJ then
        throw s!"{path}.expr: an unseq-probe operand mentions recover() — a probed operand is evaluated twice, which would consume the recover (E13 option (b), design §3 purity); refused by name"
      -- The two ALLOCATING conversions (`[]byte(s)`, `[]rune(s)`) are the
      -- one class of inline operand whose evaluation changes state (a
      -- fresh cell per evaluation); a probe over one would allocate
      -- twice. Refused by name (e13-b audit fix round R7; the frontend
      -- never emits such a probe — `containsAllocatingConversion`).
      if jsonMentionsAllocatingConversion exprJ then
        throw s!"{path}.expr: an unseq-probe operand contains an allocating conversion ([]byte(s) / []rune(s): `bytes-from-string` / `runes-from-string`) — a probed operand is evaluated twice, which would allocate twice (E13 option (b), design §3 purity / §6 item 7); refused by name"
      pure (.unseqProbe (← decodeExpr s!"{path}.expr" exprJ))
  | "unseq" => decodeUnseq results path obj
  | "map-compound-assign" =>
      -- m[k] op= v with base/key pre-hoisted by the frontend: read via
      -- mapGet, combine, store via mapAssign.
      let op ← StrictJson.string s!"{path}.op" (← StrictJson.field path obj "op")
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let read ← decodeExpr s!"{path}.read" (← StrictJson.field path obj "read")
      let rhs ← decodeExpr s!"{path}.rhs" (← StrictJson.field path obj "rhs")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      let combined ← decodeCompound op read rhs
      pure (.mapAssign base index combined keyTy valTy)
  | "map-assign" =>
      let base ← decodeExpr s!"{path}.base" (← StrictJson.field path obj "base")
      let index ← decodeExpr s!"{path}.index" (← StrictJson.field path obj "index")
      let value ← decodeExpr s!"{path}.value" (← StrictJson.field path obj "value")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (.mapAssign base index value keyTy valTy)
  | "slice-lit" =>
      -- slice literal: makeSlice into a temp, then assign each element.
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let elemTy ← decodeTy s!"{path}.elem" (← StrictJson.field path obj "elem")
      let length ← StrictJson.nat s!"{path}.length" (← StrictJson.field path obj "length")
      let elems ← StrictJson.array s!"{path}.elems" (← StrictJson.field path obj "elems")
      let lenLit : Expr := .intLit (Int.ofNat length) .int
      let mut stmts ← declaresOf #[t]
      stmts := stmts.push (.makeSlice t.assignee elemTy lenLit (some lenLit))
      for i in [:elems.size] do
        match elems[i]? with
        | some el =>
            let eo ← StrictJson.obj s!"{path}.elems[{i}]" el
            checkAllowedKeys s!"{path}.elems[{i}]" eo ["index", "value"]
            let index ← StrictJson.int s!"{path}.elems[{i}].index" (← StrictJson.field s!"{path}.elems[{i}]" eo "index")
            let value ← decodeExpr s!"{path}.elems[{i}].value" (← StrictJson.field s!"{path}.elems[{i}]" eo "value")
            stmts := stmts.push (.assign (.addr (.indexAddr (targetBaseExpr t (← tmp "$lit")) (.intLit index .int))) value)
        | none => pure ()
      pure (.seqn stmts)
  | "map-lit" =>
      -- map literal: makeMap into a temp, then assign each entry.
      let t ← decodeTarget s!"{path}.target" (← StrictJson.field path obj "target")
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      let entries ← StrictJson.array s!"{path}.entries" (← StrictJson.field path obj "entries")
      let base : Expr ←
        match t.assignee with
        | .var id => pure (.var id)
        | _ => do pure (.var (← tmp "$maplit"))
      let mut stmts ← declaresOf #[t]
      stmts := stmts.push (.makeMap t.assignee keyTy valTy none)
      for i in [:entries.size] do
        match entries[i]? with
        | some e =>
            let eo ← StrictJson.obj s!"{path}.entries[{i}]" e
            checkAllowedKeys s!"{path}.entries[{i}]" eo ["key", "value"]
            let key ← decodeExpr s!"{path}.entries[{i}].key" (← StrictJson.field s!"{path}.entries[{i}]" eo "key")
            let value ← decodeExpr s!"{path}.entries[{i}].value" (← StrictJson.field s!"{path}.entries[{i}]" eo "value")
            stmts := stmts.push (.mapAssign base key value keyTy valTy)
        | none => pure ()
      pure (.seqn stmts)
  | "break" => pure .breakStmt
  | "continue" => pure .continueStmt
  | "break-to" =>
      pure (.breakTo (← StrictJson.string s!"{path}.label" (← StrictJson.field path obj "label")))
  | "continue-to" =>
      pure (.continueTo (← StrictJson.string s!"{path}.label" (← StrictJson.field path obj "label")))
  | "labeled" =>
      -- A break/continue-targetable label. The machine label must sit
      -- DIRECTLY on the loop-forming statement (`contHeadLabel`'s
      -- placement invariant), so for/range push it inside their desugar;
      -- a switch's breakable is wrapped whole. Anything else fails
      -- closed (go/types only accepts these targets).
      let name ← StrictJson.string s!"{path}.label" (← StrictJson.field path obj "label")
      let bodyJson ← StrictJson.field path obj "body"
      let bobj ← StrictJson.obj s!"{path}.body" bodyJson
      let btag ← StrictJson.string s!"{path}.body.stmt"
        (← StrictJson.field s!"{path}.body" bobj "stmt")
      match btag with
      | "for" => decodeFor results s!"{path}.body" bobj (some name)
      | "range" => decodeRange results s!"{path}.body" bobj (some name)
      | "breakable" => pure (.labeled name (← decodeStmt results s!"{path}.body" bodyJson))
      | other => fail s!"labeled statement over unsupported form {other} at {path}"
  | other => fail s!"unsupported statement {other} at {path}"

/-- Lower `for k, v := range X`. Map range is the `mapRange` primitive; index
ranges (slice/array/int) desugar to an index `while` loop. The index is
incremented at the top of the loop body (guarded by a first-iteration flag) so
`continue` still advances it, matching Go. A `label` (from a wire "labeled"
wrapper) attaches DIRECTLY to the loop-forming statement — the machine's
`contHeadLabel` placement invariant. -/
partial def decodeRange (results : Array Param) (path : String) (obj : StrictJson.Obj)
    (label : Option String := none) : LowerM Stmt := do
  let kind ← StrictJson.string s!"{path}.kind" (← StrictJson.field path obj "kind")
  checkKindKeys path obj rangeAllowedKeys kind
  let keyVarName := optString obj "keyVar"
  let valVarName := optString obj "valVar"
  -- B6: the range variables' declaration ids (`keyLocal` / `valLocal`; a `$`-spelled
  -- variable is interned) — the same resolution `rangeBinderLocals` records for the body's scope.
  let keyVar ← match keyVarName with
    | some n => do pure (some (← declLocal s!"{path}.keyLocal" n (obj.get? "keyLocal")))
    | none => pure none
  let valVar ← match valVarName with
    | some n => do pure (some (← declLocal s!"{path}.valLocal" n (obj.get? "valLocal")))
    | none => pure none
  let collJson ← StrictJson.field path obj "collection"
  let coll ← decodeExpr s!"{path}.collection" collJson
  -- F2 (scope-exact R1), corrected at fix round 2 (the audit re-verification's R1): the range's
  -- implicitly declared key / value variables are in scope in the BODY and nowhere else —
  -- `rangeBinderLocals` is opened HERE and the enclosing block's fold never sees them. The walk
  -- over the node's remaining keys (its `body` skipped by `nestedStmtKeys`) keeps any `declare` a
  -- future emitter might hoist into the node itself; today it contributes nothing.
  let binders ← rangeBinderLocals path obj
  let rangeLocals := binders ++ (← jsonDeclaredLocals path (Json.mkObj obj.toList))
  let body ← withLocals rangeLocals (decodeStmt results s!"{path}.body" (← StrictJson.field path obj "body"))
  let lab : Stmt → Stmt := fun st =>
    match label with
    | some l => .labeled l st
    | none => st
  match kind with
  | "map" =>
      let keyTy ← decodeTy s!"{path}.keyType" (← StrictJson.field path obj "keyType")
      let valTy ← decodeTy s!"{path}.valueType" (← StrictJson.field path obj "valueType")
      pure (lab (.mapRange keyVar valVar coll keyTy valTy body))
  | "chan" =>
      -- Range over a channel (channels arc slice 1): a comma-ok receive
      -- loop until closed-and-drained (spec §For statements; pinned by
      -- channels/range-closed and channels/range-edge/*). NON-snapshot —
      -- each iteration receives from the live channel; an open, drained
      -- channel blocks (the sequential slice's deadlocked run, probe
      -- p16). `keyVar` is the single iteration variable, freshly bound
      -- per iteration; the pattern follows the index-able ranges, which
      -- also desugar to `while` (only `mapRange` is primitive, for its
      -- nondeterministic order).
      let collTy ← exprTypeOf s!"{path}.collection" collJson
      let elemTy ← decodeTy s!"{path}.elemType" (← StrictJson.field path obj "elemType")
      let rcoll ← tmp "$rcoll"
      let rrecv ← tmp "$rrecv"
      let rok ← tmp "$rok"
      let mut iter : Array Stmt := #[
        .chanRecv #[.var rrecv, .var rok] (.var rcoll) elemTy,
        .ifThenElse (.not (.var rok)) .breakStmt (.seqn #[])
      ]
      match keyVar with
      | some k => iter := iter ++ #[.initialization { id := k, typ := elemTy }, .assign (.var k) (.var rrecv)]
      | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := rcoll, typ := collTy }, .assign (.var rcoll) coll,
        .initialization { id := rrecv, typ := elemTy },
        .initialization { id := rok, typ := .bool },
        lab (.while (.boolLit true) (.block #[] iter))
      ])
  | "slice" | "array" | "int" | "array-pointer" =>
      let collTy ← exprTypeOf s!"{path}.collection" collJson
      let intTy : Ty := .int .int
      -- Range over an INTEGER: the iteration variable and the index
      -- arithmetic take the OPERAND's integer kind, carried on the wire
      -- as operandType (spec §For statements: the loop variable has the
      -- operand's type). BUG-043: this desugar previously hard-coded
      -- the default int kind for $ridx/$rlen/the loop variable/the
      -- increment — comparisons are kind-blind, so the conversion-only
      -- shape passed while arithmetic on the loop variable in the
      -- operand's kind went stuck. FAIL CLOSED on a missing or
      -- non-integer operandType (the incdec precedent: silent
      -- int-defaulting is exactly this defect class). Slice/array/
      -- array-pointer ranges index with int (spec), unchanged.
      let idxTy : Ty ←
        if kind == "int" then
          match obj.get? "operandType" with
          | some t =>
              match (← decodeTy s!"{path}.operandType" t) with
              | .int k => pure (.int k)
              | other => fail s!"range-over-int at {path} carries a non-integer operandType ({repr other})"
          | none => fail s!"range-over-int at {path} carries no operandType — the loop variable has no kind to take"
        else pure intTy
      let idxKind : IntKind := match idxTy with | .int k => k | _ => .int
      let rcoll ← tmp "$rcoll"
      let rlen ← tmp "$rlen"
      let ridxId ← tmp "$ridx"
      let rfirst ← tmp "$rfirst"
      let ridx : Expr := .var ridxId
      -- Range over *[N]T (value form): the pointer binds once; each
      -- iteration reads the element THROUGH it, so writes to the array
      -- during the loop are observed and a nil pointer panics at the
      -- first read (pre-merge audit 2026-07-26). N is static.
      let arrPtrTy? ← (match obj.get? "arrType" with
        | some t => do pure (some (← decodeTy s!"{path}.arrType" t))
        | none => pure none)
      let arrPtrLen? ← (match obj.get? "len" with
        | some l => do pure (some (← StrictJson.nat s!"{path}.len" l))
        | none => pure none)
      -- Length: len(collection) for slice/array; the int itself for int
      -- range; the static N for array-pointer.
      let lenExpr : Expr :=
        if kind == "int" then .var rcoll
        else match arrPtrLen? with
        | some n => .intLit (Int.ofNat n) .int
        | none => .length (.var rcoll) none
      -- Per-iteration loop-variable bindings.
      let mut iter : Array Stmt := #[
        -- increment index at top except on the first iteration (the
        -- synthetic 1 in the OPERAND's kind — BUG-043)
        .ifThenElse (.var rfirst)
          (.assign (.var rfirst) (.boolLit false))
          (.assign (.var ridxId) (.add ridx (.intLit 1 idxKind))),
        -- exit when the index reaches the length
        .ifThenElse (.atLeastCmp ridx (.var rlen)) .breakStmt (.seqn #[])
      ]
      match keyVar with
      | some k => iter := iter ++ #[.initialization { id := k, typ := idxTy }, .assign (.var k) ridx]
      | none => pure ()
      if kind != "int" then
        match valVar with
        | some v =>
            let elemTy ← decodeTy s!"{path}.elemType" (← StrictJson.field path obj "elemType")
            let base : Expr :=
              match arrPtrTy? with
              | some arrTy => .deref (.var rcoll) arrTy
              | none => .var rcoll
            iter := iter ++ #[.initialization { id := v, typ := elemTy }, .assign (.var v) (.indexGet base ridx)]
        | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := rcoll, typ := collTy }, .assign (.var rcoll) coll,
        .initialization { id := rlen, typ := idxTy }, .assign (.var rlen) lenExpr,
        .initialization { id := ridxId, typ := idxTy }, .assign (.var ridxId) (.intLit 0 idxKind),
        .initialization { id := rfirst, typ := .bool }, .assign (.var rfirst) (.boolLit true),
        lab (.while (.boolLit true) (.block #[] iter))
      ])
  | "string" =>
      -- Rune iteration: the key is the rune's starting BYTE offset, the
      -- value the decoded rune (invalid encodings: U+FFFD, width 1 — the
      -- machine's decodeRuneAt). The next offset advances at the TOP of
      -- each iteration, before the body, so `continue` re-tests with the
      -- advance already applied.
      let intTy : Ty := .int .int
      let rcoll ← tmp "$rcoll"
      let rnext ← tmp "$rnext"
      let roffId ← tmp "$roff"
      let roff : Expr := .var roffId
      let mut iter : Array Stmt := #[
        .ifThenElse (.atLeastCmp (.var rnext) (.length (.var rcoll) none))
          .breakStmt (.seqn #[]),
        .initialization { id := roffId, typ := intTy },
        .assign (.var roffId) (.var rnext),
        .assign (.var rnext) (.add roff (.runeSizeAt (.var rcoll) roff))
      ]
      match keyVar with
      | some k => iter := iter ++ #[.initialization { id := k, typ := intTy }, .assign (.var k) roff]
      | none => pure ()
      match valVar with
      | some v => iter := iter ++
          #[.initialization { id := v, typ := .int .int32 },
            .assign (.var v) (.runeAt (.var rcoll) roff)]
      | none => pure ()
      iter := iter.push body
      pure (.block #[] #[
        .initialization { id := rcoll, typ := .string }, .assign (.var rcoll) coll,
        .initialization { id := rnext, typ := intTy }, .assign (.var rnext) (.intLit 0 .int),
        lab (.while (.boolLit true) (.block #[] iter))
      ])
  | other => fail s!"unsupported range kind {other} at {path}"

partial def decodeReturn (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let rs ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  if rs.size == 0 then
    pure .returnStmt
  else if rs.size == 1 && results.size == 1 then
    -- return e1 at a ONE-result function  →  assign the result local,
    -- then returnStmt (one operand, one store: the two-phase split
    -- below is a no-op here and the single-assign form keeps the
    -- lowered shape unchanged). The arity guard is part of the arm
    -- (audit fix round 2026-09-01, BLOCKER 1): without
    -- `results.size == 1` this fast path ran BEFORE the arity check,
    -- so a one-operand return at a >=2-result function stored result
    -- 0 and left the rest ZERO-FILLED — a silent wrong answer on a
    -- corrupt wire where main's decoder refused by name. A 1-vs-n
    -- mismatch now falls through to the arity refusal below; the
    -- frontend never emits the shape (a multi-value `return f()` is
    -- splatted into n operands, emitReturn), so the refusal is the
    -- wire-corruption backstop, pinned in Tests/GoCoreEval.lean.
    match rs[0]?, results[0]? with
    | some rj, some rp =>
        pure (.seqn #[.assign (.var rp.id) (← decodeExpr s!"{path}.results[0]" rj),
                      .returnStmt])
    | _, _ => fail s!"return arity mismatch at {path}"
  else if rs.size == results.size then
    -- return e1, .., en  →  TWO-PHASE, like an assignment to the result
    -- variables (spec#Return_statements): evaluate EVERY operand into a
    -- fresh temp (left to right — a panic in a later operand fires
    -- before ANY result is stored), THEN store all temps to the result
    -- locals, then returnStmt. BUG-075 ($GOROOT/test issue43835): the
    -- previous sequential per-result assigns stored result 1 before
    -- operand 2 evaluated, so a recover observed the partial store
    -- through named/blank results.
    let mut evals : Array Stmt := #[]
    let mut stores : Array Stmt := #[]
    for i in [:rs.size] do
      match rs[i]?, results[i]? with
      | some rj, some rp =>
          let ret ← tmp s!"$ret{i}"
          evals := evals.push (.initialization { id := ret, typ := rp.typ })
          evals := evals.push (.assign (.var ret) (← decodeExpr s!"{path}.results[{i}]" rj))
          stores := stores.push (.assign (.var rp.id) (.var ret))
      | _, _ => pure ()
    pure (.seqn (evals ++ stores ++ #[.returnStmt]))
  else
    fail s!"return arity {rs.size} does not match {results.size} results at {path}"

partial def decodeAssign (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let _ := results
  let lhs ← StrictJson.array s!"{path}.lhs" (← StrictJson.field path obj "lhs")
  let rhs ← StrictJson.array s!"{path}.rhs" (← StrictJson.field path obj "rhs")
  -- Single call on the RHS assigned to targets → GoCore call statement.
  -- Blank targets route to fresh discard temps.
  if rhs.size == 1 then
    match ← asCall? rhs[0]! with
    | some (name, args) =>
        -- The call's `resultTypes` vector types the blank discard temps:
        -- REQUIRED and arity-checked against the targets (BUG-110 —
        -- replaces the `resultTypes[i]?.getD .int` reconstruction).
        let callObj ← StrictJson.obj s!"{path}.rhs[0]" rhs[0]!
        let resultTypes ← decodeResultTypes s!"{path}.rhs[0]" callObj lhs.size
        let mut decls : Array Stmt := #[]
        let mut assignees : Array Assignee := #[]
        for i in [:lhs.size] do
          let lj := lhs[i]!
          if targetIsBlank lj then
            let cr ← tmp s!"$cr{i}"
            let ty ← match resultTypes[i]? with
              | some ty => pure ty
              | none => fail s!"resultTypes[{i}] absent at {path}.rhs[0] (fail closed)"
            decls := decls.push (.initialization { id := cr, typ := ty })
            assignees := assignees.push (.var cr)
          else
            let t ← decodeTarget s!"{path}.lhs[{i}]" lj
            decls := decls ++ (← declaresOf #[t])
            assignees := assignees.push t.assignee
        return .seqn (decls.push (.call assignees ⟨name⟩ (← args.mapIdxM (fun i a => decodeExpr s!"{path}.args[{i}]" a))))
    | none => pure ()
  -- A `sync/atomic` op on the RHS (atomics arc wave 1): exactly ONE
  -- target (the single result — `store` has none and never reaches
  -- an assignment: go/types rejects it); a blank target routes to a
  -- typed discard temp like a call's.
  if rhs.size == 1 then
    match ← asAtomicOp? rhs[0]! with
    | some (op, kind, args) =>
        if op == .store then
          fail s!"atomic store assigned to a target at {path} (a sync/atomic Store returns nothing — a forged wire; go/types rejects the source form)"
        if lhs.size != 1 then
          fail s!"atomic op assigned to {lhs.size} targets at {path} (an atomic op has exactly one result)"
        let opObj ← StrictJson.obj s!"{path}.rhs[0]" rhs[0]!
        -- one result, REQUIRED (BUG-110 / the F5 tightening)
        let resultTypes ← decodeResultTypes s!"{path}.rhs[0]" opObj 1
        let lj := lhs[0]!
        let mut decls : Array Stmt := #[]
        let mut assignee : Assignee := .unsupported "atomic-op target"
        if targetIsBlank lj then
          match resultTypes[0]? with
          | some ty =>
              let ca0 ← tmp "$ca0"
              decls := decls.push (.initialization { id := ca0, typ := ty })
              assignee := .var ca0
          | none => fail s!"blank atomic-op target without a result type at {path} (fail closed)"
        else
          let t ← decodeTarget s!"{path}.lhs[0]" lj
          decls := decls ++ (← declaresOf #[t])
          assignee := t.assignee
        let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.rhs[0].args[{i}]" a)
        return .seqn (decls.push (.atomicStmt op kind argsE #[assignee]))
    | none => pure ()
  -- A value-returning sync op on the RHS (Q-TRYLOCK): exactly ONE
  -- target (the Bool result); a blank target drops the result — the op
  -- still takes effect (the empty target list, `syncPlan`).
  if rhs.size == 1 then
    match ← asSyncValueOp? rhs[0]! with
    | some (op, args) =>
        if lhs.size != 1 then
          fail s!"value sync op assigned to {lhs.size} targets at {path} (TryLock/TryRLock have exactly one result)"
        -- the one result is Bool, REQUIRED on the wire (BUG-110 / the F5 tightening)
        let opObj ← StrictJson.obj s!"{path}.rhs[0]" rhs[0]!
        let syncResultTypes ← decodeResultTypes s!"{path}.rhs[0]" opObj 1
        if syncResultTypes[0]? != some .bool then
          fail s!"value sync op result type is not bool at {path}.rhs[0].resultTypes[0] (TryLock/TryRLock return a bool; forged wire)"
        let lj := lhs[0]!
        let argsE ← args.mapIdxM (fun i a => decodeExpr s!"{path}.rhs[0].args[{i}]" a)
        if targetIsBlank lj then
          return .syncStmt op argsE #[]
        else
          let t ← decodeTarget s!"{path}.lhs[0]" lj
          let decls ← declaresOf #[t]
          return .seqn (decls.push (.syncStmt op argsE #[t.assignee]))
    | none => pure ()
  -- Same for a call through a func value.
  if rhs.size == 1 then
    match ← asCallValue? rhs[0]! with
    | some (calleeJ, args) =>
        let callObj ← StrictJson.obj s!"{path}.rhs[0]" rhs[0]!
        -- REQUIRED and arity-checked (BUG-110 — replaces the `.getD .int` reconstruction)
        let resultTypes ← decodeResultTypes s!"{path}.rhs[0]" callObj lhs.size
        let callee ← decodeExpr s!"{path}.rhs[0].callee" calleeJ
        let argEs ← args.mapIdxM (fun i a => decodeExpr s!"{path}.rhs[0].args[{i}]" a)
        let mut decls : Array Stmt := #[]
        let mut assignees : Array Assignee := #[]
        for i in [:lhs.size] do
          let lj := lhs[i]!
          if targetIsBlank lj then
            let cv ← tmp s!"$cv{i}"
            let ty ← match resultTypes[i]? with
              | some ty => pure ty
              | none => fail s!"resultTypes[{i}] absent at {path}.rhs[0] (fail closed)"
            decls := decls.push (.initialization { id := cv, typ := ty })
            assignees := assignees.push (.var cv)
          else
            let t ← decodeTarget s!"{path}.lhs[{i}]" lj
            decls := decls ++ (← declaresOf #[t])
            assignees := assignees.push t.assignee
        return .seqn (decls.push (.callValue assignees callee argEs))
    | none => pure ()
  -- Comma-ok map lookup: `v, ok := m[k]`. Blank targets route to fresh temps.
  if lhs.size == 2 && rhs.size == 1 then
    match ← asMapGet? rhs[0]! with
    | some (baseJ, indexJ, keyTyJ, valTyJ) =>
        let base ← decodeExpr s!"{path}.rhs[0].base" baseJ
        let index ← decodeExpr s!"{path}.rhs[0].index" indexJ
        let keyTy ← decodeTy s!"{path}.rhs[0].keyType" keyTyJ
        let valTy ← decodeTy s!"{path}.rhs[0].valueType" valTyJ
        let commaOkTarget (j : Json) (p : String) (ty : Ty) (tmpName : String) : LowerM (Assignee × Array Stmt) :=
          if targetIsBlank j then do
            let t ← tmp tmpName
            pure (.var t, #[.initialization { id := t, typ := ty }])
          else do
            let t ← decodeTarget p j
            pure (t.assignee, ← declaresOf #[t])
        let (a0, d0) ← commaOkTarget lhs[0]! s!"{path}.lhs[0]" valTy "$mlv"
        let (a1, d1) ← commaOkTarget lhs[1]! s!"{path}.lhs[1]" .bool "$mlok"
        return .seqn (d0 ++ d1 ++ #[.mapLookup a0 a1 base index keyTy valTy])
    | none => pure ()
  if lhs.size != rhs.size then
    fail s!"assignment arity {lhs.size} != {rhs.size} at {path}"
  else if lhs.any targetIsBlank then
    -- Blank targets discard their value but must still evaluate the RHS (so a
    -- panic in `_ = a/b` fires). Round 4 (BUG-035): the old lowering
    -- (RHS temps + per-target single assigns) collapsed spec
    -- §Assignments' phase 1 — a later target's index operands read an
    -- EARLIER store (`i, _, a[i]` saw the post-store `i`). Blanks now
    -- become fresh DISCARD locals (typed from the matching RHS
    -- expression) inside ONE `.assignMany`, so the whole statement
    -- rides the phase-split spine.
    if lhs.size == 1 then
      -- `_ = e`: evaluate for effect into a discard local.
      let ty ← exprTypeOf s!"{path}.rhs[0]" rhs[0]!
      let blank0 ← tmp "$blank0"
      pure (.seqn #[.initialization { id := blank0, typ := ty },
        .assign (.var blank0) (← decodeExpr s!"{path}.rhs[0]" rhs[0]!)])
    else do
      let mut decls : Array Stmt := #[]
      let mut assignees : Array Assignee := #[]
      let mut i := 0
      for l in lhs do
        if targetIsBlank l then
          let ty ← exprTypeOf s!"{path}.rhs[{i}]" rhs[i]!
          let blank ← tmp s!"$blank{i}"
          decls := decls.push (.initialization { id := blank, typ := ty })
          assignees := assignees.push (.var blank)
        else
          let t ← decodeTarget s!"{path}.lhs[{i}]" l
          decls := decls ++ (← declaresOf #[t])
          assignees := assignees.push t.assignee
        i := i + 1
      let exprs ← rhs.mapIdxM (fun i e => decodeExpr s!"{path}.rhs[{i}]" e)
      pure (.seqn (decls.push (.assignMany assignees exprs)))
  else
    -- No blanks: declarations first, then a simultaneous multi-assign so swaps
    -- are correct.
    let targets ← lhs.mapIdxM (fun i t => decodeTarget s!"{path}.lhs[{i}]" t)
    let exprs ← rhs.mapIdxM (fun i e => decodeExpr s!"{path}.rhs[{i}]" e)
    let assignees ← targets.mapM (fun t => targetAssignee t)
    let decls ← declaresOf targets
    if assignees.size == 1 then
      pure (.seqn (decls.push (.assign assignees[0]! exprs[0]!)))
    else
      pure (.seqn (decls.push (.assignMany assignees exprs)))

/-- Lower an `unseq` statement (the Stage C wire arm; docstring at the section head). -/
partial def decodeUnseq (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  -- cells (D2)
  let cellsJ ← StrictJson.array s!"{path}.cells" (← StrictJson.field path obj "cells")
  -- B6: every cell is a `$`-temporary (the F3 reservation, restated at the boundary) — checked on
  -- the SPELLINGS first, so a bare cell name refuses by that name, not as an unnumbered source local.
  for i in [:cellsJ.size] do
    let co ← StrictJson.obj s!"{path}.cells[{i}]" cellsJ[i]!
    let cname ← StrictJson.string s!"{path}.cells[{i}].id" (← StrictJson.field s!"{path}.cells[{i}]" co "id")
    let _ ← binder s!"{path}.cells[{i}]" cname
  let cells ← cellsJ.mapIdxM (fun i c => decodeParam s!"{path}.cells[{i}]" c)
  -- Stage E6a R1 (2026-09-24): every SOURCE-LOCAL atom the node mentions is a local the enclosing
  -- function declares, and its `type` annotation is that declaration's — checked before any
  -- occurrence decodes, over the whole node (heads, callees, arguments, payloads, plans, wide
  -- operands and the completion alike), so that no later check (`unseqPayloadTy?`,
  -- `unseqCheckMapBase`) reads a forged annotation. A name that is one of the graph's own CELLS is
  -- a binder, not a source local (its `$` reservation is `binder`'s check above), so it is skipped.
  let occsJ ← StrictJson.array s!"{path}.occs" (← StrictJson.field path obj "occs")
  -- the graph's SLOTS by spelling: its cells and its target binders (`kind: target`'s `bind`)
  let targetBinds : Array String := occsJ.filterMap fun o =>
    match o.getObjVal? "kind", o.getObjVal? "bind" with
    | .ok (Json.str "target"), .ok (Json.str b) => some b
    | _, _ => none
  unseqCheckLocalAtoms ((← read).locals ++ cells) (cells.map (·.name) ++ targetBinds) path (Json.mkObj (obj.toList))
  -- occurrences (D3, D4, D8–D10, D13)
  if occsJ.isEmpty then
    fail s!"unseq: empty graph at {path} — a sweep with no occurrence is not a sweep; refused by name"
  let mut occs : Array UnseqOcc := #[]
  for i in [:occsJ.size] do
    let opath := s!"{path}.occs[{i}]"
    let o ← StrictJson.obj opath occsJ[i]!
    let kind ← StrictJson.string s!"{opath}.kind" (← StrictJson.field opath o "kind")
    match unseqOccAllowedKeys kind with
    | some allowed => checkAllowedKeys opath o allowed
    | none => fail s!"unseq: unknown occurrence kind '{kind}' at {opath} (eval | invoke | target | load | guard | recv | allocate | wide); refused by name"
    let name ← StrictJson.string s!"{opath}.name" (← StrictJson.field opath o "name")
    if name.isEmpty then
      fail s!"unseq: empty occurrence name at {opath}; refused by name"
    let after ← match o.get? "after" with
      | some a =>
          let arr ← StrictJson.array s!"{opath}.after" a
          arr.toList.mapIdxM (fun j x => StrictJson.string s!"{opath}.after[{j}]" x)
      | none => pure []
    let region ← match o.get? "region" with
      | some r => some <$> StrictJson.string s!"{opath}.region" r
      | none => pure none
    let cellTy (bind : String) : LowerM Ty := do
      match cells.find? (·.name == bind) with
      | some c => pure c.typ
      | none => fail s!"unseq: result binder '{bind}' at {opath} is not a declared cell; refused by name"
    let body ← match kind with
      | "eval" => do
          let bind ← StrictJson.string s!"{opath}.bind" (← StrictJson.field opath o "bind")
          let headJ ← StrictJson.field opath o "head"
          unseqCheckHead cells s!"{opath}.head" headJ
          let hobj ← StrictJson.obj s!"{opath}.head" headJ
          let cty ← cellTy bind
          match hobj.get? "type" with
          | none => fail s!"unseq: the eval head at {opath}.head carries no type — the head's type must agree with cell '{bind}' ({repr cty}); refused by name"
          | some t =>
              let hty ← decodeTy s!"{opath}.head.type" t
              if hty != cty then
                fail s!"unseq: head type {repr hty} at {opath} disagrees with cell '{bind}' declared {repr cty}; refused by name"
          pure (UnseqBody.eval (← binder opath bind) (← decodeExpr s!"{opath}.head" headJ))
      | "invoke" => do
          let bindsJ ← StrictJson.array s!"{opath}.binds" (← StrictJson.field opath o "binds")
          let binds ← bindsJ.toList.mapIdxM (fun j b => StrictJson.string s!"{opath}.binds[{j}]" b)
          if binds.length > 2 then
            fail s!"unseq: invocation '{name}' with {binds.length} results is outside the Stage C fragment (0, 1 or 2); refused by name"
          let calleeJ ← StrictJson.field opath o "callee"
          unseqCheckCallee s!"{opath}.callee" calleeJ
          let argsJ ← StrictJson.array s!"{opath}.args" (← StrictJson.field opath o "args")
          for j in [:argsJ.size] do
            unseqCheckArg s!"{opath}.args[{j}]" argsJ[j]!
          let rts ← decodeResultTypes opath o binds.length
          for (b, t) in binds.zip rts.toList do
            let cty ← cellTy b
            if t != cty then
              fail s!"unseq: result type {repr t} at {opath}.resultTypes disagrees with cell '{b}' declared {repr cty}; refused by name"
          let callee ← decodeExpr s!"{opath}.callee" calleeJ
          let args ← argsJ.mapIdxM (fun j a => decodeExpr s!"{opath}.args[{j}]" a)
          pure (UnseqBody.invoke (← binds.mapM (binder opath)) callee args.toList)
      | "target" => do
          let bind ← StrictJson.string s!"{opath}.bind" (← StrictJson.field opath o "bind")
          let lhsJ ← StrictJson.field opath o "lhs"
          -- Stage E5 audit fix round F1 (2026-09-22): a map-element plan's keyType/valueType are the base's own map type.
          match lhsJ.getObjVal? "target" with
          | .ok (.str "map") =>
              let lo ← StrictJson.obj s!"{opath}.lhs" lhsJ
              let keyTy ← decodeTy s!"{opath}.lhs.keyType" (← StrictJson.field s!"{opath}.lhs" lo "keyType")
              let valueTy ← decodeTy s!"{opath}.lhs.valueType" (← StrictJson.field s!"{opath}.lhs" lo "valueType")
              unseqCheckMapBase cells s!"{opath}.lhs.base" "map-element target plan" (← StrictJson.field s!"{opath}.lhs" lo "base") keyTy valueTy
          | _ => pure ()
          let t ← decodeTarget s!"{opath}.lhs" lhsJ
          if t.declare.isSome then
            fail s!"unseq: a target plan at {opath} cannot declare its target; refused by name"
          unseqCheckTargetShape s!"{opath}.lhs" t.assignee
          pure (UnseqBody.target (← binder opath bind) t.assignee)
      | "load" => do
          let bind ← StrictJson.string s!"{opath}.bind" (← StrictJson.field opath o "bind")
          let tgt ← StrictJson.string s!"{opath}.target" (← StrictJson.field opath o "target")
          pure (UnseqBody.load (← binder opath bind) (← binder opath tgt))
      | "guard" => do
          let test ← StrictJson.string s!"{opath}.test" (← StrictJson.field opath o "test")
          let w ← StrictJson.bool s!"{opath}.when" (← StrictJson.field opath o "when")
          let out ← StrictJson.string s!"{opath}.out" (← StrictJson.field opath o "out")
          pure (UnseqBody.guard (← binder opath test) w (← binder opath out))
      | "recv" => do
          -- Stage E E3 (2026-09-21): a RECEIVE occurrence — the channel an ATOM (the
          -- channel VALUE already evaluated), one binder (the comma-ok form is E5's),
          -- the element type = the binder cell's type.
          let bindsJ ← StrictJson.array s!"{opath}.binds" (← StrictJson.field opath o "binds")
          let binds ← bindsJ.toList.mapIdxM (fun j b => StrictJson.string s!"{opath}.binds[{j}]" b)
          -- Stage E5 E5b (2026-09-22): the comma-ok receive `v, ok = <-ch` — two binders, the
          -- second the bool flag (the machine's `chanRecv` writes both; `wellFormed?` checks 1–2).
          if binds.length == 0 || binds.length > 2 then
            fail s!"unseq: receive '{name}' with {binds.length} binders is outside the admitted fragment (one received value, or two for the comma-ok form); refused by name"
          if binds.length == 2 then
            let okTy ← cellTy binds[1]!
            if okTy != .bool then
              fail s!"unseq: receive '{name}' at {opath}: the comma-ok flag cell '{binds[1]!}' is declared {repr okTy}, not bool; refused by name"
          let chJ ← StrictJson.field opath o "ch"
          if jsonMentionsRecover chJ then
            fail s!"unseq: recover() in a receive's channel at {opath}; refused by name"
          if !unseqIsAtom chJ then
            fail s!"unseq: hidden read in a receive — {opath}.ch is not an atom (the channel VALUE is already evaluated; v2.1 §3.1); refused by name"
          let elem ← decodeTy s!"{opath}.elem" (← StrictJson.field opath o "elem")
          let cty ← cellTy binds[0]!
          if elem != cty then
            fail s!"unseq: receive element type {repr elem} at {opath} disagrees with cell '{binds[0]!}' declared {repr cty}; refused by name"
          let ch ← decodeExpr s!"{opath}.ch" chJ
          pure (UnseqBody.recv (← binds.mapM (binder opath)) ch elem)
      | "allocate" => do
          -- Stage E E4 (2026-09-21): an ALLOCATION occurrence — the hoisted statement's
          -- shape (new | make-slice | make-map | make-chan | slice-lit) with the binder
          -- cell as its target; every operand an already-evaluated PAYLOAD; the cell's
          -- type = the allocation's own type (a pointer / slice / map / channel).
          let bind ← StrictJson.string s!"{opath}.bind" (← StrictJson.field opath o "bind")
          let cty ← cellTy bind
          let apath := s!"{opath}.allocation"
          let aJ ← StrictJson.field opath o "allocation"
          if jsonMentionsRecover aJ then
            fail s!"unseq: recover() in an allocation at {apath}; refused by name"
          let a ← StrictJson.obj apath aJ
          let tag ← StrictJson.string s!"{apath}.stmt" (← StrictJson.field apath a "stmt")
          let typeMismatch (yields : Ty) : LowerM Unit :=
            if yields != cty then
              fail s!"unseq: allocation '{name}' at {apath} yields {repr yields} but cell '{bind}' is declared {repr cty}; refused by name"
            else pure ()
          let optPayload (key : String) : LowerM (Option Expr) := do
            match a.get? key with
            | some c => do
                unseqCheckPayload s!"{apath}.{key}" c
                pure (some (← decodeExpr s!"{apath}.{key}" c))
            | none => pure none
          let spec ← match tag with
            | "new" => do
                checkAllowedKeys apath a ["stmt", "value", "elemType"]
                let vJ ← StrictJson.field apath a "value"
                let elemTy ← decodeTy s!"{apath}.elemType" (← StrictJson.field apath a "elemType")
                -- `new`'s value: a `struct-lit` over payloads (`&T{…}`), or a PAYLOAD — a zero value
                -- (`new(T)`) or, since the audit fix round F1 (2026-09-21), an atom / a boxed atom (Go
                -- 1.26 `new(x)`: the argument's already-evaluated value; the first cut admitted only the
                -- zero value, and the lowering emitted it for every `new`) — whose static type is the
                -- allocation's element type.
                (match vJ.getObjVal? "expr" with
                  | .ok (.str "struct-lit") => unseqCheckStructLit s!"{apath}.value" vJ
                  | _ => unseqCheckPayload s!"{apath}.value" vJ)
                match ← unseqPayloadTy? cells s!"{apath}.value" vJ with
                | some vt =>
                    if vt != elemTy then
                      fail s!"unseq: allocation '{name}' at {apath}: `new`'s value is typed {repr vt}, which disagrees with the allocation's element type {repr elemTy} (audit F1, 2026-09-21); refused by name"
                | none => pure ()
                typeMismatch (.pointer elemTy)
                pure (AllocSpec.new (← decodeExpr s!"{apath}.value" vJ) elemTy)
            | "make-slice" => do
                checkAllowedKeys apath a ["stmt", "elem", "len", "cap"]
                let elemTy ← decodeTy s!"{apath}.elem" (← StrictJson.field apath a "elem")
                let lenJ ← StrictJson.field apath a "len"
                unseqCheckPayload s!"{apath}.len" lenJ
                unseqCheckConstSize s!"{apath}.len" "len" lenJ
                if let some capJ := a.get? "cap" then
                  unseqCheckConstSize s!"{apath}.cap" "cap" capJ
                  match unseqConstInt? lenJ, unseqConstInt? capJ with
                  | some l, some c =>
                      if l > c then
                        fail s!"unseq: {apath}: constant len {l} larger than constant cap {c} in make — a compile-time error in Go (audit F3, 2026-09-21); refused by name"
                  | _, _ => pure ()
                let capE ← optPayload "cap"
                typeMismatch (.slice elemTy)
                pure (AllocSpec.makeSlice elemTy (← decodeExpr s!"{apath}.len" lenJ) capE)
            | "make-map" => do
                checkAllowedKeys apath a ["stmt", "keyType", "valueType", "hint"]
                let keyTy ← decodeTy s!"{apath}.keyType" (← StrictJson.field apath a "keyType")
                let valTy ← decodeTy s!"{apath}.valueType" (← StrictJson.field apath a "valueType")
                if let some hintJ := a.get? "hint" then
                  unseqCheckConstSize s!"{apath}.hint" "size" hintJ
                let hintE ← optPayload "hint"
                typeMismatch (.map keyTy valTy)
                pure (AllocSpec.makeMap keyTy valTy hintE)
            | "make-chan" => do
                checkAllowedKeys apath a ["stmt", "elem", "cap"]
                let elemTy ← decodeTy s!"{apath}.elem" (← StrictJson.field apath a "elem")
                if let some capJ := a.get? "cap" then
                  unseqCheckConstSize s!"{apath}.cap" "buffer" capJ
                let capE ← optPayload "cap"
                typeMismatch (.chan .both elemTy)
                pure (AllocSpec.makeChan elemTy capE)
            | "slice-lit" => do
                checkAllowedKeys apath a ["stmt", "elem", "length", "elems"]
                let elemTy ← decodeTy s!"{apath}.elem" (← StrictJson.field apath a "elem")
                let length ← StrictJson.nat s!"{apath}.length" (← StrictJson.field apath a "length")
                let elemsJ ← StrictJson.array s!"{apath}.elems" (← StrictJson.field apath a "elems")
                let elems ← elemsJ.toList.mapIdxM (fun k el => do
                  let epath := s!"{apath}.elems[{k}]"
                  let eo ← StrictJson.obj epath el
                  checkAllowedKeys epath eo ["index", "value"]
                  let index ← StrictJson.int s!"{epath}.index" (← StrictJson.field epath eo "index")
                  let vJ ← StrictJson.field epath eo "value"
                  unseqCheckPayload s!"{epath}.value" vJ
                  pure (index, ← decodeExpr s!"{epath}.value" vJ))
                -- audit F3 (2026-09-21): a Go slice literal's keys are constant, DISTINCT and within
                -- the literal's length (go/types rejects the rest); the emitter's `length` is the
                -- greatest index + 1. A malformed wire answered with a Go-observable index panic
                -- (M11) or ran with the second store winning (M12) — refused at decode by name.
                for (index, _) in elems do
                  if index < 0 || index ≥ (length : Int) then
                    fail s!"unseq: allocation '{name}' at {apath}: slice-literal index {index} is outside the literal's length {length} — the emitter's literal is dense and keyed by distinct constants within its length (audit F3, 2026-09-21); refused by name"
                let idxs := elems.map (·.1)
                if idxs.length != idxs.eraseDups.length then
                  fail s!"unseq: allocation '{name}' at {apath}: duplicate slice-literal index — the emitter's literal is keyed by DISTINCT constants (audit F3, 2026-09-21); refused by name"
                typeMismatch (.slice elemTy)
                pure (AllocSpec.sliceLit elemTy length elems)
            | "map-lit" => do
                -- Stage E5 E5c (2026-09-22): a MAP literal — the fresh map and its keyed entry stores in
                -- order; every key and value a PAYLOAD; duplicate CONSTANT keys are a compile-time error
                -- in Go (spec#Composite_literals) and refuse at decode by name; duplicate DYNAMIC keys are
                -- the successive stores' last-wins, as in Go.
                checkAllowedKeys apath a ["stmt", "keyType", "valueType", "entries"]
                let keyTy ← decodeTy s!"{apath}.keyType" (← StrictJson.field apath a "keyType")
                let valTy ← decodeTy s!"{apath}.valueType" (← StrictJson.field apath a "valueType")
                let entriesJ ← StrictJson.array s!"{apath}.entries" (← StrictJson.field apath a "entries")
                let entries ← entriesJ.toList.mapIdxM (fun k el => do
                  let epath := s!"{apath}.entries[{k}]"
                  let eo ← StrictJson.obj epath el
                  checkAllowedKeys epath eo ["key", "value"]
                  let kJ ← StrictJson.field epath eo "key"
                  let vJ ← StrictJson.field epath eo "value"
                  unseqCheckPayload s!"{epath}.key" kJ
                  unseqCheckPayload s!"{epath}.value" vJ
                  pure (← decodeExpr s!"{epath}.key" kJ, ← decodeExpr s!"{epath}.value" vJ))
                -- the CONSTANT keys, compared on their wire spelling (an int/bool/string constant node
                -- is spelled once per value by the emitter)
                let constKeys := entriesJ.toList.filterMap (fun el =>
                  match el.getObjVal? "key" with
                  | .ok k =>
                      match k.getObjVal? "expr" with
                      | .ok (.str "int") | .ok (.str "bool") | .ok (.str "string") => some k.compress
                      | _ => none
                  | _ => none)
                if constKeys.length != constKeys.eraseDups.length then
                  fail s!"unseq: allocation '{name}' at {apath}: duplicate constant key in a map literal — a compile-time error in Go (spec#Composite_literals); refused by name"
                typeMismatch (.map keyTy valTy)
                pure (AllocSpec.mapLit keyTy valTy entries)
            | other =>
                fail s!"unseq: allocation '{name}' at {apath}: statement '{other}' is outside the admitted fragment (new | make-slice | make-map | make-chan | slice-lit | map-lit); refused by name"
          -- Stage E6a (2026-09-24; the Stage E audit's F8, RATIFIED [USER] 2026-09-22 item 6): a LITERAL
          -- allocation — a slice literal, a map literal, `&T{…}` (a `new` over a `struct-lit`) — is a node
          -- WITHOUT E1 edges (v2.1 R3: a composite literal is not a call, receive or logical operation), and the
          -- lowering emits no `after` on one; an `after` edge here would FORCE the literal behind an event by an
          -- order the language does not impose — a narrowing the wire could not otherwise express. `make` /
          -- `new(T)` / `new(x)` are E1 participants (spec#Built-in_functions) and carry their anchor.
          let structLitValue := match a.get? "value" with
            | some v =>
                match v.getObjVal? "expr" with
                | .ok (Json.str "struct-lit") => true
                | _ => false
            | none => false
          if (tag == "slice-lit" || tag == "map-lit" || (tag == "new" && structLitValue)) && !after.isEmpty then
            fail s!"unseq: allocation '{name}' at {apath}: an `after` edge on a literal allocation ({tag}) — a composite literal is not an E1 participant (v2.1 R3), so the lowering never orders it behind an event; the edge would narrow the set by a policy the wire cannot express (Stage E audit F8, ratified 2026-09-22; Stage E6a); refused by name"
          pure (UnseqBody.allocate (← binder opath bind) spec)
      | "wide" => do
          -- Stage E5 E5a (2026-09-22): a WIDE built-in occurrence — `append` / `copy` (the comma-ok
          -- `map-lookup` / `type-assert` join at E5b) — the hoisted wide statement's shape with the
          -- binder cells as its targets; every operand an already-evaluated ATOM (never `ref` of a
          -- binder cell — audit F2); the cells' types = the statement's result types (the slice type
          -- for append, `int` for copy's count); exactly the statement's arity of binders
          -- (`UnseqGraph.wellFormed?` checks it again at ENTER).
          let bindsJ ← StrictJson.array s!"{opath}.binds" (← StrictJson.field opath o "binds")
          let binds ← bindsJ.toList.mapIdxM (fun j b => StrictJson.string s!"{opath}.binds[{j}]" b)
          let wpath := s!"{opath}.wide"
          let wJ ← StrictJson.field opath o "wide"
          if jsonMentionsRecover wJ then
            fail s!"unseq: recover() in a wide built-in at {wpath}; refused by name"
          let w ← StrictJson.obj wpath wJ
          let tag ← StrictJson.string s!"{wpath}.stmt" (← StrictJson.field wpath w "stmt")
          let atomField (key : String) : LowerM Expr := do
            let j ← StrictJson.field wpath w key
            if let some id := unseqRefOfBinder? j then
              fail s!"unseq: a wide built-in operand at {wpath}.{key} takes the address of a binder cell '{id}' — a graph cell is written only by its producer (audit F2, 2026-09-21); refused by name"
            if !unseqIsAtom j then
              fail s!"unseq: hidden read in a wide built-in — {wpath}.{key} is not an atom (an identifier or an int/bool/string constant; the statement's operands are already evaluated, v2.1 §3.1); refused by name"
            decodeExpr s!"{wpath}.{key}" j
          let oneBind (what : String) : LowerM String := do
            match binds with
            | [b] => pure b
            | _ => fail s!"unseq: wide built-in '{name}' ({what}) with {binds.length} results at {opath}; the statement writes exactly one; refused by name"
          -- Stage E5 E5b: the comma-ok forms write TWO cells — the value and the bool flag.
          let twoBinds (what : String) (valTy : Ty) : LowerM (String × String) := do
            match binds with
            | [v, ok] =>
                let cv ← cellTy v
                if cv != valTy then
                  fail s!"unseq: wide {what} '{name}' at {wpath} yields {repr valTy} but its value cell '{v}' is declared {repr cv}; refused by name"
                let cok ← cellTy ok
                if cok != .bool then
                  fail s!"unseq: wide {what} '{name}' at {wpath}: the comma-ok flag cell '{ok}' is declared {repr cok}, not bool; refused by name"
                pure (v, ok)
            | _ => fail s!"unseq: wide built-in '{name}' ({what}) with {binds.length} results at {opath}; the statement writes exactly two (the value and the ok flag); refused by name"
          let spec ← match tag with
            | "append" => do
                checkAllowedKeys wpath w ["stmt", "elem", "slice", "elems"]
                let elemTy ← decodeTy s!"{wpath}.elem" (← StrictJson.field wpath w "elem")
                let slice ← atomField "slice"
                let elems ← atomField "elems"
                let b ← oneBind "append"
                let cty ← cellTy b
                if cty != .slice elemTy then
                  fail s!"unseq: wide append '{name}' at {wpath} yields {repr (Ty.slice elemTy)} but cell '{b}' is declared {repr cty}; refused by name"
                pure (WideSpec.append elemTy slice elems)
            | "copy" => do
                checkAllowedKeys wpath w ["stmt", "dst", "src"]
                let dst ← atomField "dst"
                let src ← atomField "src"
                let b ← oneBind "copy"
                let cty ← cellTy b
                if cty != .int .int then
                  fail s!"unseq: wide copy '{name}' at {wpath} yields int (the copied count) but cell '{b}' is declared {repr cty}; refused by name"
                pure (WideSpec.copy dst src)
            | "map-lookup" => do
                -- Stage E5 E5b: `v, ok = m[k]` — ONE read of the frozen map VALUE at the key VALUE.
                checkAllowedKeys wpath w ["stmt", "base", "index", "keyType", "valueType"]
                let base ← atomField "base"
                let index ← atomField "index"
                let kt ← decodeTy s!"{wpath}.keyType" (← StrictJson.field wpath w "keyType")
                let vt ← decodeTy s!"{wpath}.valueType" (← StrictJson.field wpath w "valueType")
                -- Stage E5 audit fix round F1 (2026-09-22): kt/vt are the base's own map type (the audit's mW12/mW17).
                unseqCheckMapBase cells s!"{wpath}.base" s!"wide map lookup '{name}'" (← StrictJson.field wpath w "base") kt vt
                let _ ← twoBinds "map lookup" vt
                pure (WideSpec.mapLookup base index kt vt)
            | "type-assert" => do
                -- Stage E5 E5b: `v, ok = x.(T)` — a pure op on the interface VALUE, never failing.
                checkAllowedKeys wpath w ["stmt", "operand", "target"]
                let operand ← atomField "operand"
                let target ← decodeTy s!"{wpath}.target" (← StrictJson.field wpath w "target")
                let _ ← twoBinds "type assertion" target
                pure (WideSpec.typeAssert operand target)
            | other =>
                fail s!"unseq: wide built-in '{name}' at {wpath}: statement '{other}' is outside the admitted fragment (append | copy | map-lookup | type-assert); refused by name"
          pure (UnseqBody.wide (← binds.mapM (binder opath)) spec)
      | other => fail s!"unseq: unknown occurrence kind '{other}' at {opath}; refused by name"
    occs := occs.push { name, body, after, region }
  -- stores
  let storesJ ← StrictJson.array s!"{path}.stores" (← StrictJson.field path obj "stores")
  let stores ← storesJ.toList.mapIdxM (fun i s => do
    let spath := s!"{path}.stores[{i}]"
    let so ← StrictJson.obj spath s
    checkAllowedKeys spath so ["target", "value"]
    let t ← StrictJson.string s!"{spath}.target" (← StrictJson.field spath so "target")
    let v ← StrictJson.string s!"{spath}.value" (← StrictJson.field spath so "value")
    pure (← binder spath t, ← binder spath v))
  -- the completion (D14)
  let thenJ ← StrictJson.field path obj "then"
  if jsonMentionsStmt ["unseq"] thenJ then
    fail s!"unseq: nested unseq inside the completion at {path}.then; refused by name"
  if jsonMentionsStmt ["unseq-probe"] thenJ then
    fail s!"unseq: legacy unseq-probe inside an unseq completion at {path}.then — a sweep is lowered EITHER as one unseq graph OR by the legacy probe path, never a mixture (v2.1 §3.7); refused by name"
  if jsonMentionsRecover thenJ then
    fail s!"unseq: recover() inside the completion at {path}.then; refused by name"
  let thenB ← decodeStmt results s!"{path}.then" thenJ
  let g : UnseqGraph := { cells := cells.toList.map (·.param), occs := occs.toList, stores }
  -- the machine's static shape check, at the boundary (D2, D5, D6, D11)
  match g.wellFormed? with
  | some msg => fail s!"unseq: malformed graph at {path} — {msg}; refused by name"
  | none => pure ()
  -- D7: list order is a linear extension of every edge (cycles, forward references)
  for i in [:g.occs.length] do
    let o := g.occs[i]!
    for d in g.deps o do
      match g.producer? d with
      | some p =>
          if p ≥ i then
            fail s!"unseq: list order is not a linear extension at {path} — '{o.name}' (rank {i}) consumes '{d}', produced by '{(g.occs[p]!).name}' (rank {p} ≥ {i}): a cycle or a forward reference; refused by name"
      | none => pure ()
    for a in o.after do
      match g.index? a with
      | some p =>
          if p ≥ i then
            fail s!"unseq: list order is not a linear extension at {path} — '{o.name}' (rank {i}) follows '{a}' (rank {p} ≥ {i}): a cycle or a forward reference; refused by name"
      | none => pure ()
    match o.region with
    | some gn =>
        match g.index? gn with
        | some p =>
            if p ≥ i then
              fail s!"unseq: list order is not a linear extension at {path} — '{o.name}' (rank {i}) lies in the region of '{gn}' (rank {p} ≥ {i}); refused by name"
        | none => pure ()
    | none => pure ()
  -- D12: the STATIC G rule — a region-confined binder is consumed only inside its region
  for o in g.occs do
    let chain := unseqRegionChain g o
    for d in g.deps o do
      match unseqConfinedTo? g d with
      | some gn =>
          if !chain.contains gn then
            fail s!"unseq: invalid branch join at {path} — '{o.name}' uses '{d}', confined to the region of '{gn}' (the completion binder is the only join; v2.1 §1 G); refused by name"
      | none => pure ()
  for (t, v) in g.stores do
    for x in [t, v] do
      match unseqConfinedTo? g x with
      | some gn => fail s!"unseq: invalid branch join at {path} — the phase-2 store ({t} ← {v}) uses '{x}', confined to the region of '{gn}'; refused by name"
      | none => pure ()
  for c in thenB.names.filter g.isCell do
    match unseqConfinedTo? g c with
    | some gn => fail s!"unseq: invalid branch join at {path} — the completion statement uses '{c}', confined to the region of '{gn}'; refused by name"
    | none => pure ()
  pure (.unseq g thenB)

partial def decodeVar (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  let decls ← StrictJson.array s!"{path}.decls" (← StrictJson.field path obj "decls")
  let mut stmts : Array Stmt := #[]
  for i in [:decls.size] do
    let d ← StrictJson.obj s!"{path}.decls[{i}]" decls[i]!
    checkAllowedKeys s!"{path}.decls[{i}]" d ["id", "type", "init", "local"]
    let name ← StrictJson.string s!"{path}.decls[{i}].id" (← StrictJson.field path d "id")
    let typ ← decodeTy s!"{path}.decls[{i}].type" (← StrictJson.field path d "type")
    let id ← declLocal s!"{path}.decls[{i}]" name (d.get? "local")
    stmts := stmts.push (.initialization { id, typ })
    match d.get? "init" with
    | some initE => stmts := stmts.push (.assign (.var id) (← decodeExpr s!"{path}.decls[{i}].init" initE))
    | none => pure ()
  pure (.seqn stmts)

partial def decodeIf (results : Array Param) (path : String) (obj : StrictJson.Obj) : LowerM Stmt := do
  -- F2 (scope-exact R1): the init statement decodes first, under the enclosing environment; what it
  -- declares is in scope for the condition and both branches (Go's if-statement scope) — and nowhere
  -- after (the enclosing block's fold skips `init`, `then`, `else`: `nestedStmtKeys`).
  let core (initLocals : Array LocalDecl) : LowerM Stmt := withLocals initLocals do
    let cond ← decodeExpr s!"{path}.cond" (← StrictJson.field path obj "cond")
    let thenS ← decodeStmt results s!"{path}.then" (← StrictJson.field path obj "then")
    let elseS ← (match obj.get? "else" with
      | some e => decodeStmt results s!"{path}.else" e
      | none => pure (.seqn #[]))
    pure (Stmt.ifThenElse cond thenS elseS)
  match obj.get? "init" with
  | some initE =>
      let initS ← decodeStmt results s!"{path}.init" initE
      let initLocals ← initDeclaredLocals s!"{path}.init" initE
      pure (.block #[] #[initS, ← core initLocals])
  | none => core #[]

partial def decodeFor (results : Array Param) (path : String) (obj : StrictJson.Obj)
    (label : Option String := none) : LowerM Stmt := do
  checkAllowedKeys path obj ["stmt", "body", "init", "cond", "post", "condPre"]
  -- F2 (scope-exact R1): the init statement decodes first, under the enclosing environment; what it
  -- declares is in scope for the condition, its hoists, the post statement and the body (Go's
  -- for-statement scope) — and nowhere after (the enclosing block's fold skips them: `nestedStmtKeys`).
  let initS? ← (match obj.get? "init" with
    | some initE => some <$> decodeStmt results s!"{path}.init" initE
    | none => pure none)
  let initLocals ← (match obj.get? "init" with
    | some initE => initDeclaredLocals s!"{path}.init" initE
    | none => pure #[])
  let (cond, body, post, condPre) ← withLocals initLocals do
    let cond ← (match obj.get? "cond" with
      | some c => decodeExpr s!"{path}.cond" c
      | none => pure (.boolLit true))
    let body ← decodeStmt results s!"{path}.body" (← StrictJson.field path obj "body")
    let post ← (match obj.get? "post" with
      | some p => decodeStmt results s!"{path}.post" p
      | none => pure (.seqn #[]))
    -- `condPre`: the condition's hoisted call/alloc temps, re-run before
    -- EVERY test (the test happens inside the loop body, so hoists are
    -- legal here — control-flow slice, docs/2026-08-04_control-flow-design.md).
    let condPre ← (match obj.get? "condPre" with
      | some cp => do
          let arr ← StrictJson.array s!"{path}.condPre" cp
          arr.mapIdxM (fun i s => decodeStmt results s!"{path}.condPre[{i}]" s)
      | none => pure #[])
    pure (cond, body, post, condPre)
  -- `continue` must still run the post statement, but GoCore's `while` re-runs
  -- its whole body on continue. So run post at the top of the body except on
  -- the first iteration (guarded by a flag), then re-check the condition; this
  -- makes `for init; cond; post` faithful under continue and break.
  let forFirst ← tmp "$forFirst"
  let loopBody := Stmt.block #[] #[
    .ifThenElse (.var forFirst)
      (.assign (.var forFirst) (.boolLit false))
      post,
    .seqn condPre,
    .ifThenElse cond (.seqn #[]) .breakStmt,
    body
  ]
  -- A label (from a wire "labeled" wrapper) attaches DIRECTLY to the
  -- `.while` — the machine's `contHeadLabel` placement invariant.
  let whileStmt : Stmt :=
    match label with
    | some l => .labeled l (.while (.boolLit true) loopBody)
    | none => .while (.boolLit true) loopBody
  let loop := Stmt.block #[] #[
    .initialization { id := forFirst, typ := .bool },
    .assign (.var forFirst) (.boolLit true),
    whileStmt
  ]
  match initS? with
  | some initS => pure (.block #[] #[initS, loop])
  | none => pure loop

end

/-! ## Program -/

private def decodeFieldDef (path : String) (json : Json) : LowerM FieldDef := do
  let obj ← StrictJson.obj path json
  checkAllowedKeys path obj ["name", "type", "embedded"]
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let typ ← decodeTy s!"{path}.type" (← StrictJson.field path obj "type")
  let embedded ← StrictJson.bool s!"{path}.embedded" (← StrictJson.field path obj "embedded")
  pure { name, typ, embedded }

/-- One interface method REQUIREMENT: I1 identity plus the signature types and the
VARIADIC marker, receiver excluded. `variadic` is REQUIRED on the wire — a
missing marker would silently default a variadic requirement to
non-variadic and re-open finding 0's wrong `ok`. -/
private def decodeMethodSig (path : String) (json : Json) : LowerM MethodSig := do
  let obj ← StrictJson.obj path json
  checkAllowedKeys path obj ["id", "params", "results", "variadic"]
  let id ← NativeDeclaration.decodeMemberId s!"{path}.id" (← StrictJson.field path obj "id")
  let paramsJson ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let resultsJson ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
  let params ← paramsJson.mapIdxM (fun i t => decodeTy s!"{path}.params[{i}]" t)
  let results ← resultsJson.mapIdxM (fun i t => decodeTy s!"{path}.results[{i}]" t)
  pure { id, params, results, variadic }

/-- One `program.types[i]` entry: the TypeDef under its identity KEY plus
its DISPLAY record (design note `docs/2026-09-05_fr19-bug097-design.md`
§3.1). `display` (gc's type string) and `pkg` (declaring import path,
`""` for unnamed/universe/synthetic) are REQUIRED — an old wire, or an
emitter that forgets them, refuses at decode, never at the first panic
text (the `methodSets` discipline). -/
private def decodeTypeDef (path : String) (json : Json) :
    LowerM ((TypeId × TypeDef) × TypeDisplay) := do
  let obj ← StrictJson.obj path json
  checkAllowedKeys path obj ["name", "def", "display", "pkg"]
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  let display ← StrictJson.string s!"{path}.display" (← StrictJson.field path obj "display")
  let pkg ← StrictJson.string s!"{path}.pkg" (← StrictJson.field path obj "pkg")
  let defObj ← StrictJson.obj s!"{path}.def" (← StrictJson.field path obj "def")
  let kind ← StrictJson.string s!"{path}.def.kind" (← StrictJson.field s!"{path}.def" defObj "kind")
  -- NOTE: the def-object `kind` vocabulary is DISTINCT from the type
  -- nodes' (`struct`/`defined`/`interface`/`unsupported` here). `alias`
  -- is NOT accepted (C2): a Go alias is identity-erasing and the frontend
  -- inlines it at every use (`types.Unalias`), so an alias declaration on
  -- the wire is an emitter fault — refused by name, never a table entry.
  checkKindKeys s!"{path}.def" defObj
    (fun k => match k with
      | "struct" => some ["kind", "fields"]
      | "defined" => some ["kind", "target"]
      | "interface" => some ["kind", "methods"]
      | "unsupported" => some ["kind", "feature"]
      | "alias" => some ["kind", "target"]
      | _ => none) kind
  let td : TypeId × TypeDef ← match kind with
  | "struct" =>
      let fields ← StrictJson.array s!"{path}.def.fields" (← StrictJson.field s!"{path}.def" defObj "fields")
      pure (⟨name⟩, .struct (← fields.mapIdxM (fun i f => decodeFieldDef s!"{path}.def.fields[{i}]" f)))
  | "alias" =>
      fail s!"alias TypeDef {name} at {path}: aliases are identity-erasing and are inlined by the frontend at every use; an alias declaration is not accepted on the wire (C2)"
  | "defined" =>
      -- Identity-bearing named type over a non-struct underlying
      -- (interfaces campaign S2): resolution stops here for identity
      -- purposes; operations resolve through `target`.
      pure (⟨name⟩, .defined (← decodeTy s!"{path}.def.target" (← StrictJson.field s!"{path}.def" defObj "target")))
  | "interface" =>
      -- An interface DECLARATION: the full method set (embedded interfaces
      -- already flattened by the frontend). Satisfaction requirements come
      -- from here; an interface name with no declaration fails closed.
      let methods ← StrictJson.array s!"{path}.def.methods" (← StrictJson.field s!"{path}.def" defObj "methods")
      let requirements ← methods.mapIdxM
        (fun i m => decodeMethodSig s!"{path}.def.methods[{i}]" m)
      let mut seen : List Declaration.MemberId := []
      for req in requirements do
        if seen.contains req.id then
          fail s!"{path}.def.methods: duplicate interface member {req.id.package}:{req.name}"
        seen := req.id :: seen
      pure (⟨name⟩, .interfaceDef requirements)
  | "unsupported" =>
      -- An EXISTENCE-only marker (imported named types, design note D5):
      -- the type is KNOWN to the wire — its method-set stubs make
      -- satisfaction answerable — while every structural use (defaults,
      -- normalization, conversion) keeps failing closed on the reason.
      let feature ← StrictJson.string s!"{path}.def.feature"
        (← StrictJson.field s!"{path}.def" defObj "feature")
      pure (⟨name⟩, .opaqueDecl feature)
  | other => fail s!"unsupported type definition kind {other} at {path}"
  pure (td, { name := display, pkg })

private def decodeFunc (path : String) (json : Json) : LowerM Func := do
  let obj ← StrictJson.obj path json
  -- Two emitter shapes: quarantined {name, unsupported, arity} vs
  -- normal {name, params, results, variadic, body}.
  if obj.contains "unsupported" then
    checkAllowedKeys path obj ["name", "unsupported", "arity"]
  else
    checkAllowedKeys path obj ["name", "params", "results", "variadic", "body", "locals"]
  let name ← StrictJson.string s!"{path}.name" (← StrictJson.field path obj "name")
  -- A QUARANTINED declaration (per-decl fail-closed, slice 1 of arc
  -- wrong-answers-builtins): the frontend could not lower this function
  -- (e.g. generics, floats), but other declarations in the package can
  -- still run. The stub's params carry `Ty.unsupported`, so a CALL fails
  -- closed with the original reason at bind time (arity preserved); a
  -- nullary call hits the unsupported body. Merely being declared — or
  -- taken as a value — is fine.
  match obj.get? "unsupported" with
  | some r =>
      let reason ← StrictJson.string s!"{path}.unsupported" r
      -- The marker prefix lets the differential runner classify a call
      -- into a stub as the frontend coverage gap it is (stage
      -- frontend-export), keeping the fidelity ledger for machine gaps.
      let reason := s!"frontend-quarantined: {reason}"
      let arity ← StrictJson.nat s!"{path}.arity" (← StrictJson.field path obj "arity")
      -- B6: the stub's parameters are `$`-temporaries of an empty table.
      beginLocals #[]
      let args ← (Array.range arity).mapM
        (fun i => do pure ({ id := ← tmp s!"$stub{i}", typ := .unsupported reason } : Param))
      let locals ← endLocals
      pure { id := ⟨name⟩, args, results := #[], body := .unsupported reason, locals }
  | none =>
  let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  -- REQUIRED: Go's variadic marker, the half of the signature interface
  -- satisfaction compares (audit finding 0). A wire without it fails
  -- closed rather than defaulting to non-variadic.
  let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
  -- B6: the function's wire name table opens the interning state and the reader's
  -- table BEFORE any declaration decodes (params and results are declaration sites).
  let table ← decodeLocalsTable path obj
  beginLocals table
  withReader (fun ctx => { ctx with table }) do
  let args ← params.mapIdxM (fun i p => decodeParam s!"{path}.params[{i}]" p)
  let res ← results.mapIdxM (fun i p => decodeParam s!"{path}.results[{i}]" p)
  checkSignatureLocals path table args res
  let bodyJ ← StrictJson.field path obj "body"
  -- Stage E6a R1: the function's params and results open the environment for the `unseq` arm's
  -- annotation cross-check; the body's `block` fold adds each declaration as it is passed (F2).
  let locals := args ++ res
  let resP := res.map (·.param)
  let body ← withReader (fun ctx => { ctx with locals }) (decodeStmt resP s!"{path}.body" bodyJ)
  let tableAll ← endLocals
  let f : Func := { id := ⟨name⟩, args := args.map (·.param), results := resP, body, variadic, locals := tableAll }
  checkLocalsOk path f
  pure f

/-- The receiver key used to derive a callable target and the receiver type
used by method resolution must denote the same carrier. This checks the
supported outer shapes, not general Go source typing. -/
private def methodReceiverAgrees (ctx : LowerCtx) (key : String) : Ty → Bool
  | .defined idx => ctx.typeIdx[key]? == some idx
  | .pointer (.defined idx) => ctx.typeIdx[key]? == some idx
  | .interface id => key == id.key
  | .sync kind => key == "sync." ++ kind.name
  | .pointer (.sync kind) => key == "sync." ++ kind.name
  | _ => false

/-- A method lowers to a receiver/member-derived GoCore function (receiver
as the first parameter) plus a `MethodInfo` dispatch-table entry. -/
private def decodeMethod (path : String) (json : Json) : LowerM (Func × MethodInfo) := do
  let obj ← StrictJson.obj path json
  -- Union of the three emitter method shapes (declared / interface anchor /
  -- declaration-only stub) — anchors and stubs carry no body, which the
  -- arms below handle. G-P S2 (2026-09-28, design note
  -- `docs/2026-09-28_gp-method-promotion-design.md` §4): the synthesized
  -- promotion WRAPPERS are gone — a promoted method-set entry is a record
  -- in `program.promotions` — so the `wrapper` marker left the allowed-key
  -- set and a wire carrying it is refused BY NAME (below), never read.
  if obj.contains "wrapper" then
    fail s!"{path}.wrapper: the synthesized-promotion-wrapper marker was retired at G-P S2 (2026-09-28) — a promoted method-set entry is a record in program.promotions, and `methods` carries declared methods, interface anchors and imported stubs only; a wire carrying `wrapper` predates the v2 schema and is refused"
  checkAllowedKeys path obj
    ["id", "recvType", "recv", "params", "results", "variadic",
     "interface", "unsupported", "body", "locals"]
  let id ← NativeDeclaration.decodeMemberId s!"{path}.id" (← StrictJson.field path obj "id")
  let recvType ← StrictJson.string s!"{path}.recvType" (← StrictJson.field path obj "recvType")
  -- B6: the method's wire name table opens the interning state before the receiver,
  -- params and results (declaration sites) decode.
  let table ← decodeLocalsTable path obj
  beginLocals table
  withReader (fun ctx => { ctx with table }) do
  let recv ← decodeParam s!"{path}.recv" (← StrictJson.field path obj "recv")
  unless methodReceiverAgrees (← read) recvType recv.typ do
    fail s!"method receiver identity disagrees at {path}.recvType / {path}.recv.type: {recvType}"
  let params ← StrictJson.array s!"{path}.params" (← StrictJson.field path obj "params")
  let results ← StrictJson.array s!"{path}.results" (← StrictJson.field path obj "results")
  let variadic ← StrictJson.bool s!"{path}.variadic" (← StrictJson.field path obj "variadic")
  let args ← params.mapIdxM (fun i p => decodeParam s!"{path}.params[{i}]" p)
  let res ← results.mapIdxM (fun i p => decodeParam s!"{path}.results[{i}]" p)
  checkSignatureLocals path table (#[recv] ++ args) res
  let funcId := methodFuncId recvType id
  let info : MethodInfo := { id, funcId, recv := recv.typ }
  -- A declaration-only STUB (imported named types, design note D5): the
  -- REAL signature — `satisfiesMethodSig` compares it — over a fail-closed
  -- body, so satisfaction answers while a CALL refuses with the reason.
  match obj.get? "unsupported" with
  | some r =>
      let reason ← StrictJson.string s!"{path}.unsupported" r
      let locals ← endLocals
      let argsP := (#[recv] ++ args).map (·.param)
      let resP := res.map (·.param)
      let body : Stmt := .unsupported s!"frontend-quarantined: {reason}"
      let f : Func := { id := funcId, args := argsP, results := resP, body, variadic, locals }
      checkLocalsOk path f
      pure (f, info)
  | none =>
  -- A present `interface` key is decoded STRICTLY (delta-review R2,
  -- 2026-08-05 — same class as the F7 `runtimeError` fix; this presence-only
  -- match is 2026-07-30 vintage, surfaced by adjacency): bool or refuse;
  -- `false` is well-formed and means a concrete method.
  let ifaceFlag ← match obj.get? "interface" with
    | some flag => StrictJson.bool s!"{path}.interface" flag
    | none => pure false
  if ifaceFlag then
      -- An INTERFACE method: a signature-only dispatch anchor.
      -- `enterFrame` finds this Func, `dynamicDispatch?` redirects on the
      -- receiver box (or raises Go's nil-interface panic); the stub body
      -- is unreachable and fails STUCK (call to a nonexistent function)
      -- if a dispatch bug ever reaches it — never a silent zero return.
      let stub : Stmt := .call #[] ⟨"$interface-method-unreachable"⟩ #[]
      let locals ← endLocals
      let argsP := (#[recv] ++ args).map (·.param)
      let resP := res.map (·.param)
      let f : Func := { id := funcId, args := argsP, results := resP, body := stub, variadic, locals }
      checkLocalsOk path f
      pure (f, info)
  else
      let bodyJ ← StrictJson.field path obj "body"
      -- Stage E6a R1: the receiver, params and results open the environment; the body's `block`
      -- fold adds each declaration as it is passed (F2)
      let locals := #[recv] ++ args ++ res
      let resP := res.map (·.param)
      let body ← withReader (fun ctx => { ctx with locals }) (decodeStmt resP s!"{path}.body" bodyJ)
      let tableAll ← endLocals
      let argsP := (#[recv] ++ args).map (·.param)
      let f : Func := { id := funcId, args := argsP, results := resP, body, variadic, locals := tableAll }
      checkLocalsOk path f
      pure (f, info)

/-! ## Promotion records (G-P S1 — validated; G-P S2 — the machine's only source)

Design note `docs/2026-09-28_gp-method-promotion-design.md` §2 S2 (option (b): the
frontend records the `go/types` selection, the decoder VALIDATES it and fails closed) and
§4 (the wire shape); G-P PASSED [USER] 2026-09-28, relayed. The wire's REQUIRED
`program.promotions` array carries one record per promoted method-set entry:
`{type, member, inPtrSetOnly, path:[{owner, field, ptr}], adjust, target: {method} |
{iface}, unsupported?, sig?}`. Every record is checked here against the type table and
the method table:

- each hop is an EMBEDDED field of the previous hop's struct (the first hop's owner is
  the carrier); `ptr` agrees with the field's type; an intermediate hop reaches a struct
  declared on the wire (an imported embedded type's fields are not on the wire — a hop
  INTO one refuses by name);
- the last hop's type (through `ptr`) is the target's receiver base (a declared method)
  or the interface type itself (an `iface` target, which must declare the member);
- `member` equals the target's package-qualified identity; `sig.id` equals `member`;
- `inPtrSetOnly` follows spec#Struct_types (embedding `T`: both sets get `T`-receiver
  methods, only `*S` gets `*T`-receiver ones; embedding `*T`: both sets get both — so the
  entry is in `*S`'s set only iff the target has a pointer receiver and no hop is an
  embedded pointer);
- `adjust` is the one the hop kinds and the target's receiver require;
- no duplicate `(type, member)`; a record's `(type, member)` is not a DECLARED method of
  the carrier (the carrier's method table has no entry of that id — a carrier cannot both
  declare and promote one member, which keeps `resolveMethod?`'s arms disjoint).

The S1 cross-check against the synthesized wrappers RETIRED with the wrappers at G-P S2
(2026-09-28; design §5 S2): the records are now the machine's ONLY source for a promoted
entry (`resolveMethod?` / `receiverAt` / `callee?`, `GoLean/GoCore/Ops.lean` and
`Machine.lean`). A stub record's `unsupported` cause is stored with the machine's
`frontend-quarantined: ` marker, exactly as the retired stub body carried it, so a call
through the record refuses with the same text the differential classifies today. -/

private def decodePromotionHop (path : String) (json : Json) : LowerM PromotionHop := do
  let obj ← StrictJson.obj path json
  checkAllowedKeys path obj ["owner", "field", "ptr"]
  let owner ← StrictJson.string s!"{path}.owner" (← StrictJson.field path obj "owner")
  let field ← StrictJson.string s!"{path}.field" (← StrictJson.field path obj "field")
  let ptr ← StrictJson.bool s!"{path}.ptr" (← StrictJson.field path obj "ptr")
  pure { owner := ⟨owner⟩, field, ptr }

private def decodePromotion (path : String) (json : Json) : LowerM Promotion := do
  let obj ← StrictJson.obj path json
  checkAllowedKeys path obj
    ["type", "member", "inPtrSetOnly", "path", "adjust", "target", "unsupported", "sig"]
  let type ← StrictJson.string s!"{path}.type" (← StrictJson.field path obj "type")
  let member ← NativeDeclaration.decodeMemberId s!"{path}.member" (← StrictJson.field path obj "member")
  let inPtrSetOnly ← StrictJson.bool s!"{path}.inPtrSetOnly"
    (← StrictJson.field path obj "inPtrSetOnly")
  let hopsJ ← StrictJson.array s!"{path}.path" (← StrictJson.field path obj "path")
  let hops ← hopsJ.mapIdxM (fun i h => decodePromotionHop s!"{path}.path[{i}]" h)
  let adjustS ← StrictJson.string s!"{path}.adjust" (← StrictJson.field path obj "adjust")
  let adjust ← match adjustS with
    | "asIs" => pure PromotionAdjust.asIs
    | "deref" => pure PromotionAdjust.deref
    | "addr" => pure PromotionAdjust.addr
    | other => fail s!"{path}.adjust must be asIs|deref|addr, got {other}"
  let tobj ← StrictJson.obj s!"{path}.target" (← StrictJson.field path obj "target")
  let target ← match tobj.get? "method", tobj.get? "iface" with
    | some m, none =>
        checkAllowedKeys s!"{path}.target" tobj ["method"]
        pure (PromotionTarget.method ⟨← StrictJson.string s!"{path}.target.method" m⟩)
    | none, some i =>
        checkAllowedKeys s!"{path}.target" tobj ["iface"]
        pure (PromotionTarget.iface ⟨← StrictJson.string s!"{path}.target.iface" i⟩)
    | _, _ => fail s!"{path}.target must carry exactly one of method|iface"
  -- The stub record's cause carries the machine's frontend-quarantine marker
  -- (the retired stub BODY carried `frontend-quarantined: <reason>`; a call
  -- through the record refuses with that same text — G-P S2).
  let unsupported ← match obj.get? "unsupported" with
    | some u => pure (some s!"frontend-quarantined: {← StrictJson.string s!"{path}.unsupported" u}")
    | none => pure none
  let sig ← match obj.get? "sig" with
    | some sg => pure (some (← decodeMethodSig s!"{path}.sig" sg))
    | none => pure none
  match unsupported, sig with
  | some _, none =>
      fail s!"{path}: unsupported without sig — a stub record carries its signature; the two keys are present exactly together (design §4)"
  | none, some _ =>
      fail s!"{path}: sig without unsupported — a signature is carried only by a stub record; the two keys are present exactly together (design §4)"
  | _, _ => pure ()
  pure { type := ⟨type⟩, member, inPtrSetOnly, path := hops, adjust, target, unsupported, sig }

private def tyBase : Ty → Ty
  | .pointer t => t
  | t => t

private def promRefuse {α} (i : Nat) (p : Promotion) (msg : String) : Except String α :=
  throw s!"native lowering: program.promotions[{i}] ({p.type.key}.{p.member.name}): {msg}"

/-- Validate one promotion record (design §2 S2 (b)) against the type and method tables.
Every refusal names the record, the hop and the fact that disagrees. (The S1 cross-check
against the record's synthesized wrapper retired with the wrappers at S2.) -/
private def validatePromotion (types : TypeEnv) (funcs : Array Func)
    (methods : Array MethodInfo) (i : Nat) (p : Promotion) :
    Except String Unit := do
  let refuse {α} (msg : String) : Except String α := promRefuse i p msg
  -- The carrier: a struct declared on the wire.
  let cidx ← match types.lookupName? p.type with
    | some (cidx, .struct _) => pure cidx
    | some _ => refuse s!"carrier {p.type.key} is not a struct type (a promotion walks an embedded field)"
    | none => refuse s!"carrier {p.type.key} is not declared on the wire"
  if p.path.isEmpty then
    refuse "empty path (a promotion has at least one embedded hop)"
  -- The hops.
  let mut owner := p.type
  let mut reached : Ty := .defined cidx
  for k in [:p.path.size] do
    let h := p.path[k]!
    if h.owner != owner then
      refuse s!"path[{k}].owner is {h.owner.key}, but the path has reached {owner.key}"
    let fields ← match types.lookupName? h.owner with
      | some (_, .struct fs) => pure fs
      | some (_, .opaqueDecl _) =>
          refuse s!"path[{k}].owner {h.owner.key} is an imported/opaque declaration whose fields are not on the wire (a hop into it cannot be validated)"
      | some _ => refuse s!"path[{k}].owner {h.owner.key} is not a struct type"
      | none => refuse s!"path[{k}].owner {h.owner.key} is not declared on the wire"
    let fd ← match fields.find? (·.name == h.field) with
      | some fd => pure fd
      | none => refuse s!"path[{k}]: {h.owner.key} has no field {h.field}"
    if !fd.embedded then
      refuse s!"path[{k}]: {h.owner.key}.{h.field} is not an embedded field"
    let inner ← match fd.typ, h.ptr with
      | .pointer t, true => pure t
      | .pointer _, false =>
          refuse s!"path[{k}]: {h.owner.key}.{h.field} is an embedded POINTER but ptr is false"
      | _, true => refuse s!"path[{k}]: {h.owner.key}.{h.field} is an embedded value but ptr is true"
      | t, false => pure t
    reached := inner
    if k + 1 < p.path.size then
      match inner with
      | .defined j =>
          match types[j]? with
          | some (name, .struct _) => owner := name
          | some (name, _) =>
              refuse s!"path[{k}] reaches {name.key}, which is not a struct, yet the path continues"
          | none => refuse s!"path[{k}] reaches type index {j}, which the table does not have"
      | _ => refuse s!"path[{k}] reaches a non-struct type ({repr inner}), yet the path continues"
  let lastPtr := (p.path.back?.map (·.ptr)).getD false
  -- The target, and its receiver kind (the callee id the S1 cross-check
  -- compared against the wrapper is no longer needed: the machine reads the
  -- record itself).
  let (_, targetIsPtr) ← match p.target with
    | .method f =>
        match methods.find? (·.funcId == f) with
        | some info =>
            if info.id != p.member then
              refuse s!"member identity {p.member.package}:{p.member.name} disagrees with the target's {info.id.package}:{info.id.name} (package-qualified identity)"
            match info.recv with
            | .interface _ => refuse s!"target {f.key} is an interface anchor, not a declared method"
            | _ => pure ()
            if tyBase info.recv != reached then
              refuse s!"the last hop reaches {repr reached}, which is not the target's receiver base {repr (tyBase info.recv)}"
            match findFunctionIn? funcs f with
            | some _ => pure ()
            | none => refuse s!"target {f.key} has no Func on the wire"
            pure (f, match info.recv with | .pointer _ => true | _ => false)
        | none =>
            -- No declaration on the wire. The ONE legitimate case: an UNEXPORTED
            -- method of an IMPORTED embedded type — the imported stub passes carry
            -- exported members only (contract note
            -- `docs/2026-08-10_method-set-record-contract.md` §5), while go/types
            -- promotes the unexported member too (the raft twin's
            -- `raft.DefaultLogger` over `*log.Logger` promotes `log.output`; design
            -- §3 «twin log.output stays (log, output)»). The retired wrapper forwarded
            -- to the same absent key (a call went STUCK); since S2 a CALL through the
            -- record REFUSES BY NAME (`dynamicDispatch?`/`promotedCallee`), so the
            -- record is not refused for the wire's incompleteness; the key itself pins
            -- the receiver base AND the member (`methodFuncId` is injective in both),
            -- so both facts are decided from the key, and the receiver KIND is read
            -- back from the record's own adjustment. A locally declared reached type
            -- has its FULL method table on the wire (D2), so an absent target there is
            -- a frontend fault and refuses.
            let reachedKey ← match reached with
              | .defined j =>
                  match types[j]? with
                  | some (n, .opaqueDecl _) => pure n.key
                  | some (n, _) =>
                      refuse s!"target method {f.key} is not on the wire, yet the last hop reaches the locally declared {n.key}, whose full method table is on the wire (D2)"
                  | none => refuse s!"target method {f.key} is not on the wire and the last hop reaches type index {j}, which the table does not have"
              | _ =>
                  refuse s!"target method {f.key} is not on the wire and the last hop reaches {repr reached}, which is not an imported declaration"
            if f != methodFuncId reachedKey p.member then
              refuse s!"target method {f.key} is not on the wire and is not the member {p.member.package}:{p.member.name} of the reached imported type {reachedKey} (that key is {(methodFuncId reachedKey p.member).key})"
            let targetIsPtr ← match p.adjust, lastPtr with
              | .asIs, b => pure b
              | .deref, true => pure false
              | .addr, false => pure true
              | .deref, false => refuse "deref adjustment at a value last hop (nothing to dereference)"
              | .addr, true => refuse "addr adjustment at a pointer last hop (the field already is the address)"
            pure (f, targetIsPtr)
    | .iface ifc =>
        if reached != .interface ifc then
          refuse s!"the last hop reaches {repr reached}, not the embedded interface {ifc.key}"
        let reqs ← match types.lookupName? ifc with
          | some (_, .interfaceDef reqs) => pure reqs
          | _ => refuse s!"interface {ifc.key} has no declaration on the wire"
        if !(reqs.any (·.id == p.member)) then
          refuse s!"{ifc.key} does not declare the member {p.member.package}:{p.member.name}"
        pure (methodFuncId ifc.key p.member, false)
  -- spec#Struct_types' membership rule.
  let anyPtrHop := p.path.any (·.ptr)
  let expectSetOnly := targetIsPtr && !anyPtrHop
  if p.inPtrSetOnly != expectSetOnly then
    refuse s!"inPtrSetOnly is {p.inPtrSetOnly}; spec#Struct_types gives {expectSetOnly} (pointer-receiver target: {targetIsPtr}; embedded-pointer hop: {anyPtrHop})"
  -- The adjustment the hop kinds and the target's receiver require.
  let expectAdjust : PromotionAdjust := match p.target with
    | .iface _ => .asIs
    | .method _ =>
        if targetIsPtr then (if lastPtr then .asIs else .addr)
        else (if lastPtr then .deref else .asIs)
  if p.adjust != expectAdjust then
    refuse s!"adjust is {repr p.adjust}; a {if lastPtr then "pointer" else "value"} last hop against the target's {if targetIsPtr then "pointer" else "value"} receiver requires {repr expectAdjust}"
  match p.sig with
  | some sg =>
      if sg.id != p.member then
        refuse s!"sig.id {sg.id.package}:{sg.id.name} disagrees with member {p.member.package}:{p.member.name}"
  | none => pure ()
  -- A carrier cannot both DECLARE and promote one member: a record whose
  -- `(type, member)` is a method of the carrier's own table refuses (the S1
  -- cross-check's declared-conflict rule, kept; `resolveMethod?`'s arms stay
  -- disjoint). The carrier's method of that identity is exactly
  -- `methodFuncId type member`.
  let wid := methodFuncId p.type.key p.member
  if methods.any (·.funcId == wid) || (findFunctionIn? funcs wid).isSome then
    refuse s!"{p.type.key}.{p.member.name} is a DECLARED method of the carrier ({wid.key} is on the wire), so it is not promoted"

/-- The file-selection target this machine realizes — gc on linux/amd64
with cgo enabled and no build tags: the identity half of the pin whose
layout half is `GoCore.Platform.gcAmd64` (Platform.lean) and whose
frontend spelling is `pinnedBuildContext` (tools/nativefrontend/
fileselect.go). BUG-108: the frontend selects a package's files by
go/build's rules under this target and records the target on the wire
(`program.buildContext`); a wire lowered for any other target selects a
DIFFERENT PROGRAM from the same directory, so the decoder refuses it
here by name. Three spellings of one pin: a move of any one is a loud
red at the others. -/
structure SelectionTarget where
  goos : String
  goarch : String
  compiler : String
  cgoEnabled : Bool
  buildTags : Array String
  deriving Repr, BEq

def pinnedSelectionTarget : SelectionTarget :=
  { goos := "linux", goarch := "amd64", compiler := "gc", cgoEnabled := true, buildTags := #[] }

/-- Decode and check the wire's `buildContext` against the pin. Required:
a wire without it predates BUG-108's fix and its file set is not known
to be gc's. -/
def decodeBuildContext (obj : StrictJson.Obj) : Except String Unit := do
  let bcj ← match obj.get? "buildContext" with
    | some j => pure j
    | none => throw "native lowering: program.buildContext is missing — the frontend records the file-selection target it lowered for (BUG-108); a wire without it was emitted by a frontend that lowered files gc excludes, and is refused"
  let bc ← StrictJson.obj "program.buildContext" bcj
  for key in bc.keys do
    if !["goos", "goarch", "compiler", "cgoEnabled", "buildTags"].contains key then
      throw s!"native lowering: unknown key '{key}' at program.buildContext (exact-key discipline, fail closed)"
  let goos ← StrictJson.string "program.buildContext.goos" (← StrictJson.field "program.buildContext" bc "goos")
  let goarch ← StrictJson.string "program.buildContext.goarch" (← StrictJson.field "program.buildContext" bc "goarch")
  let compiler ← StrictJson.string "program.buildContext.compiler" (← StrictJson.field "program.buildContext" bc "compiler")
  let cgo ← StrictJson.bool "program.buildContext.cgoEnabled" (← StrictJson.field "program.buildContext" bc "cgoEnabled")
  let tagsJ ← StrictJson.array "program.buildContext.buildTags" (← StrictJson.field "program.buildContext" bc "buildTags")
  let tags ← tagsJ.mapIdxM (fun i t => StrictJson.string s!"program.buildContext.buildTags[{i}]" t)
  let got : SelectionTarget := { goos, goarch, compiler, cgoEnabled := cgo, buildTags := tags }
  if got != pinnedSelectionTarget then
    throw s!"native lowering: the wire's file-selection target is {repr got}; this machine realizes {repr pinnedSelectionTarget} (GoCore.Platform.gcAmd64) — a wire lowered for another target selects a different program from the same directory (BUG-108); refused"

/-- Decode the whole wire program. Runs OUTSIDE `LowerM`: the globals
table decodes FIRST, and its size is the reader context every
body-decoding call runs under — that is what arms the `globaladdr`
bound check (audit response 2026-08-05, C1). -/
partial def decodeProgram (json : Json) : Except String Program := do
  let obj ← StrictJson.obj "program" json
  -- `package` is emitted and deliberately unread; `globals` is absent
  -- on a globals-free wire.
  -- `fileOrder` (T1 dc122857, integration fix per audit T3-10): the E8
  -- file-presentation-order record the emitter writes at program level
  -- (list of {package, files}). It is frontend METADATA — a wire-level
  -- record of the order the frontend presented files in — with no
  -- machine consumer yet, so it is EXPLICITLY IGNORED here (the
  -- `package` precedent: known key, deliberately unread, named in this
  -- comment), not shape-validated: validation without a consumer would
  -- be dead code free to drift from the emitter. When a machine
  -- consumer appears, it decodes strictly like every other read key.
  let noCtx : LowerCtx := { nGlobals := 0, typeIdx := {} }
  let _ ← (checkAllowedKeys "program" obj
    ["schema", "package", "types", "funcs", "methods", "methodSets", "globals",
     "fileOrder", "buildContext", "promotions"]) |> (runLower · noCtx)
  let schema ← StrictJson.string "program.schema" (← StrictJson.field "program" obj "schema")
  -- G-P S2 (2026-09-28): the schema moved to v2 — promotion wrappers retired,
  -- `program.promotions` consumed, `wrapper` refused. A v1 wire is refused BY
  -- NAME: its promoted entries are synthesized `Func`s this decoder no longer
  -- accepts, so re-export with the current frontend.
  if schema == "golean-native-v1" then
    throw "native lowering: schema golean-native-v1 predates G-P S2 (2026-09-28: promotion wrappers retired, promotion records consumed — docs/2026-09-28_gp-method-promotion-design.md §4); this decoder reads golean-native-v3 — re-export the package with the current frontend"
  -- B6 (2026-09-30): the schema moved to v3 — locals are numbered (every source
  -- local carries its `local` declaration index and every function its `locals`
  -- name table; docs/2026-09-30_numeric-locals-design.md D4). A v2 wire is
  -- refused BY NAME: its locals are spellings this decoder no longer accepts.
  if schema == "golean-native-v2" then
    throw "native lowering: schema golean-native-v2 predates B6 (2026-09-30: numeric locals — `local` declaration indices and per-function `locals` name tables; docs/2026-09-30_numeric-locals-design.md D4); this decoder reads golean-native-v3 — re-export the package with the current frontend"
  if schema != "golean-native-v3" then
    throw s!"native lowering: unexpected schema {schema}"
  -- `buildContext` (BUG-108): the file-selection target, REQUIRED and
  -- checked against this machine's pin — unlike `fileOrder` it has a
  -- consumer (this check), so it is decoded strictly.
  decodeBuildContext obj
  -- Package-level variables (init slice): declaration order; the driver
  -- seeds cell i at `Loc.base ⟨i⟩`. Optional key — a globals-free wire
  -- decodes exactly as before. Duplicate names are impossible in a
  -- type-checked package; refuse anyway (boundary collision-check).
  --
  -- The TYPE TABLE's names come first (C2): every `named` reference in
  -- a global's type, a body, a signature or a TypeDef body resolves to a
  -- table INDEX, so the name → index map is built from the wire's
  -- `types` entries before anything else decodes. The two machine-
  -- reserved entries (`TypeEnv.reserved`: `struct{}` at 0, the runtime-
  -- error payload type at 1) lead the table; a wire entry at position k
  -- lands at index k + 2. A wire TypeDef spelling a reserved key, or a
  -- duplicate TypeId, is refused (collision-check at the boundary).
  let typesJson ← StrictJson.array "program.types" (← StrictJson.field "program" obj "types")
  let mut typeIdx : Std.HashMap String TypeIdx := {}
  for e in TypeEnv.reserved do
    typeIdx := typeIdx.insert e.1.key typeIdx.size
  for (t, k) in typesJson.toList.zipIdx do
    let tobj ← StrictJson.obj s!"program.types[{k}]" t
    let name ← StrictJson.string s!"program.types[{k}].name"
      (← StrictJson.field s!"program.types[{k}]" tobj "name")
    if TypeEnv.reserved.any (fun e => e.1.key == name) then
      throw s!"native lowering: duplicate TypeId {name} at program.types[{k}] — it is the machine-reserved TypeId {name} (`TypeEnv.reserved` owns that entry; the wire never declares it)"
    if typeIdx.contains name then
      throw s!"native lowering: duplicate TypeId {name} at program.types[{k}] (two declarations would alias in the type table)"
    typeIdx := typeIdx.insert name (k + TypeEnv.reserved.size)
  let ctx0 : LowerCtx := { nGlobals := 0, typeIdx }
  let globals ←
    match obj.get? "globals" with
    | none => pure #[]
    | some gj => do
        let arr ← StrictJson.array "program.globals" gj
        arr.mapIdxM (fun i g => do
          let gobj ← StrictJson.obj s!"program.globals[{i}]" g
          let _ ← (checkAllowedKeys s!"program.globals[{i}]" gobj ["name", "type"]) |> (runLower · ctx0)
          let name ← StrictJson.string s!"program.globals[{i}].name"
            (← StrictJson.field s!"program.globals[{i}]" gobj "name")
          let typ ← (decodeTy s!"program.globals[{i}].type"
            (← StrictJson.field s!"program.globals[{i}]" gobj "type")) |> (runLower · ctx0)
          pure ({ name, typ } : GlobalDef))
  let mut seenGlobals : Std.HashSet String := {}
  for g in globals do
    if seenGlobals.contains g.name then
      throw s!"native lowering: duplicate global {g.name} in program"
    seenGlobals := seenGlobals.insert g.name
  let ctx : LowerCtx := { nGlobals := globals.size, typeIdx }
  let funcsJson ← StrictJson.array "program.funcs" (← StrictJson.field "program" obj "funcs")
  let funcs ← funcsJson.mapIdxM (fun i f => runLower (decodeFunc s!"program.funcs[{i}]" f) ctx)
  let declaredEntries ← typesJson.mapIdxM (fun i t => runLower (decodeTypeDef s!"program.types[{i}]" t) ctx)
  let declaredDefs := declaredEntries.map (·.1)
  -- The machine-reserved prefix leads (the canonical empty struct —
  -- `map[K]struct{}` sets — and the runtime-error payload type).
  -- (Duplicate TypeIds and wire entries spelling a reserved key were
  -- refused above, when the name → index map was built — the boundary
  -- collision check of the globals / function-id / method-set-record
  -- siblings, fr19 audit fix round R7 composed with C2.)
  let typeDefs : TypeEnv := TypeEnv.reserved ++ declaredDefs
  -- The display records beside the table, ONE PER ENTRY IN TABLE ORDER
  -- (design note 2026-09-05 §3.1 × C2): the reserved entries' records
  -- lead (`TypeEnv.reservedDisplays` — gc spells the empty struct
  -- `struct {}`; the runtime-error entry carries the cause-naming
  -- marker), then each declared TypeDef's `display`/`pkg`. So the key
  -- read back from entry `i` (`TypeEnv.nameOf?`) is the key of record
  -- `i`, and the renderers' name-keyed record lookup resolves to the
  -- entry the index resolves to.
  let typeDisplays : Array (TypeId × TypeDisplay) :=
    TypeEnv.reservedDisplays ++ declaredEntries.map (fun e => (e.1.1, e.2))
  -- THE ACCEPTANCE CLAUSE (C2; plan §1.9 `Accepted`): the table must be
  -- DEPENDENCY-ORDERED — every table dependency of entry i (struct
  -- fields and defined targets, through array elements) at a smaller
  -- index — or every index descent in the machine would be a fuel walk
  -- again. Decided HERE, by the core's own predicate; a violation is
  -- refused naming the edge (a forward reference or a cycle; the
  -- frontend orders the table and self-checks the same contract, so this
  -- is the machine's independent, fail-closed re-decision).
  if !typeDefs.WellFounded then
    match typeDefs.firstViolation? with
    | some (i, j) =>
        let nm := fun k => match typeDefs.nameOf? k with | some n => n.key | none => "?"
        throw s!"native lowering: program.types is not dependency-ordered — table entry {i} ({nm i}) depends on entry {j} ({nm j}) with {j} ≥ {i} (a forward reference or a cycle; indices count the two machine-reserved entries)"
    | none => throw "native lowering: program.types failed the well-foundedness decision but no violating edge was found (internal inconsistency; fail closed)"
  let methodsJson ← StrictJson.array "program.methods" (← StrictJson.field "program" obj "methods")
  let methodPairs ← methodsJson.mapIdxM (fun i m => runLower (decodeMethod s!"program.methods[{i}]" m) ctx)
  -- Method bodies are executable functions (looked up by FuncId on call);
  -- MethodInfo is the dispatch table.
  let allFuncs := funcs ++ methodPairs.map Prod.fst
  -- Collision check at the boundary (CLAUDE.md: every identity constructor
  -- collision-checks). Duplicate FuncIds would make findFunctionIn? silently
  -- run the FIRST body for BOTH callers — the 2026-07-25 pre-merge audit
  -- found exactly that via same-named methods' lifted literals.
  let mut seen : Std.HashSet String := {}
  for f in allFuncs do
    if seen.contains f.id.key then
      throw s!"native lowering: duplicate function id {f.id.key} in program"
    seen := seen.insert f.id.key
  -- Method-set records (class closure of BUG-053, contract note
  -- `docs/2026-08-10_method-set-record-contract.md` §3/§4): REQUIRED —
  -- an old wire, or a new emitter that forgets the field, refuses at
  -- decode, not at query. Strict entry shape, coverage enum closed,
  -- duplicate keys refused (collision-check at the boundary, CLAUDE.md).
  -- The canonical empty-struct record is synthesized alongside its
  -- synthetic TypeDef above: `struct{}` is a carrier by kind and
  -- genuinely method-free.
  let msJson ← StrictJson.array "program.methodSets"
    (← StrictJson.field "program" obj "methodSets")
  let declaredRecords ← msJson.mapIdxM (fun i m => do
    let mobj ← StrictJson.obj s!"program.methodSets[{i}]" m
    let _ ← (checkAllowedKeys s!"program.methodSets[{i}]" mobj ["type", "coverage"]) |> (runLower · noCtx)
    let key ← StrictJson.string s!"program.methodSets[{i}].type"
      (← StrictJson.field s!"program.methodSets[{i}]" mobj "type")
    let covStr ← StrictJson.string s!"program.methodSets[{i}].coverage"
      (← StrictJson.field s!"program.methodSets[{i}]" mobj "coverage")
    let coverage ← match covStr with
      | "full" => pure MethodSetCoverage.full
      | "exported" => pure MethodSetCoverage.exported
      | other => throw s!"native lowering: program.methodSets[{i}].coverage \
must be full|exported, got {other}"
    pure ({ key, coverage } : MethodSetRecord))
  let methodSets := #[({ key := "struct{}", coverage := .full } : MethodSetRecord)]
    ++ declaredRecords
  let mut seenRecords : Std.HashSet String := {}
  for r in methodSets do
    if seenRecords.contains r.key then
      throw s!"native lowering: duplicate method-set record for {r.key} in program"
    seenRecords := seenRecords.insert r.key
  -- Promotion records (G-P S1/S2, design note
  -- `docs/2026-09-28_gp-method-promotion-design.md` §4/§5; the validation
  -- is `validatePromotion` above): REQUIRED — a wire without the field
  -- refuses by name; each record decodes strictly under the type-index
  -- context (`sig` types resolve through it) and is validated against the
  -- tables; duplicates refuse. Since S2 the records are the machine's only
  -- source for a promoted method-set entry (`resolveMethod?`).
  let promJson ← match obj.get? "promotions" with
    | some j => StrictJson.array "program.promotions" j
    | none =>
        throw "native lowering: program.promotions is missing — the frontend records every promoted method-set entry as data (G-P, docs/2026-09-28_gp-method-promotion-design.md §4); a wire without the field predates the records and is refused"
  let promotions ← promJson.mapIdxM
    (fun i pj => runLower (decodePromotion s!"program.promotions[{i}]" pj) ctx)
  let methods := methodPairs.map Prod.snd
  let mut seenPromotions : Std.HashSet String := {}
  for i in [:promotions.size] do
    let p := promotions[i]!
    let k := (methodFuncId p.type.key p.member).key
    if seenPromotions.contains k then
      throw s!"native lowering: program.promotions[{i}]: duplicate promotion record for {p.type.key}.{p.member.package}:{p.member.name}"
    seenPromotions := seenPromotions.insert k
    validatePromotion typeDefs allFuncs methods i p
  pure { typeDefs, funcs := allFuncs, methods, globals,
         methodSets, typeDisplays, promotions }

end GoLean.NativeToIR
