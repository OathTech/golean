import GoLean.GoCore.Value

namespace GoLean.GoCore

-- `FuncId` now lives in `Value.lean` (beside `TypeId`) so `GoValue.funcVal`
-- can carry it; `Ty` moved there too (interfaces campaign S3, 2026-07-30)
-- so `GoValue.interface` can carry its dynamic type structurally. Both are
-- re-exported by this module's namespace.

structure Param where
  id : String
  typ : Ty
  deriving Repr, BEq

structure FieldDef where
  name : String
  typ : Ty
  /-- Go's ANONYMOUS (embedded) field flag, carried verbatim from the
  frontend. Method PROMOTION through embedded fields is unmodeled
  (BUG-007), and this is what lets interface satisfaction fail CLOSED on a
  type where promotion could apply instead of answering `false` — which was
  a silent wrong answer on the comma-ok assert path (pre-merge audit
  2026-07-31, finding 5). -/
  embedded : Bool := false
  deriving Repr, BEq

/-- One method of an interface's method set: the name plus the signature
with the RECEIVER excluded. Interface satisfaction compares these against a
concrete method's `Func` (arguments minus the receiver, its results, AND
its variadic marker), all canonicalized — a name-only match reported
satisfaction for a differently typed method (pre-merge audit 2026-07-31,
finding 2).

`variadic` is Go's marker on the LAST parameter, and it is part of the
signature Go compares for method-set membership: `M(xs ...int)` and
`M(xs []int)` share the param TYPE `[]int` but are DIFFERENT methods, so
neither type implements the other's interface. Comparing only the type
lists accepted both directions — a silent wrong `ok` on the comma-ok
assert and an ill-typed dispatch where Go panics (pre-merge audit
2026-07-31, finding 0). -/
structure MethodSig where
  name : String
  params : Array Ty
  results : Array Ty
  variadic : Bool := false
  deriving Repr, BEq

inductive TypeDef where
  | struct (fields : Array FieldDef)
  | alias (target : Ty)
  /-- An INTERFACE declaration: its FULL method set (embedded interfaces
  already flattened by the frontend). Satisfaction requirements come from
  HERE, not from the dispatch table — the dispatch table records only
  methods actually CALLED, so an interface with no call site had an empty
  requirement list and every dynamic type satisfied it vacuously
  (pre-merge audit 2026-07-31, finding 0). A name with no such declaration
  therefore FAILS CLOSED; the canonical empty interface (`any`) is
  satisfied by design and carries no declaration. -/
  | interfaceDef (methods : Array MethodSig)
  /-- An identity-BEARING named type over a non-struct underlying
  (`type T int`, `type MC map[uint64]struct{}`) — BUG-004's fix
  (interfaces campaign S2, 2026-07-30). Runtime values share the
  underlying representation (normalize/default/convert/equality resolve
  through it); the identity matters at interface boxing, type asserts,
  and method sets, where the STATIC type at the site carries it. `type
  T = U` remains `.alias` (identity erased, correctly). Defined types
  over STRUCT underlyings stay `.struct` (their values are
  name-tagged); defined-over-defined-struct fails closed at the
  consumer until a case needs it. -/
  | defined (underlying : Ty)
  | unsupported (feature : String)
  deriving Repr, BEq

inductive Expr where
  | var (id : String)
  | nil (typ : Option Ty)
  | intLit (value : Int) (kind : IntKind := .unbounded "integer")
  /-- A float constant as its EXACT RATIONAL (floats slice, design note
  decision 5): go/constant's folded value travels un-rounded
  (`num/den`, `den > 0` — the decoder fails closed on malformed), and
  the machine performs the ONE spec-mandated rounding to `kind` via the
  `FloatBits` rational kernel at evaluation. Keeping the rounding in
  GoCore keeps it differentially validated (a go/constant quirk would
  surface as a red case, not be silently shared with the oracle). -/
  | floatLit (num : Int) (den : Nat) (kind : FloatKind)
  | stringLit (value : GoString)
  | boolLit (value : Bool)
  | convert (typ : Ty) (operand : Expr)
  | bytesFromString (operand : Expr)
  | stringFromByteSlice (operand : Expr)
  | stringFromRune (operand : Expr)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  | div (left right : Expr)
  | mod (left right : Expr)
  | shiftLeft (left right : Expr)
  | shiftRight (left right : Expr)
  | bitAnd (left right : Expr)
  | bitOr (left right : Expr)
  | bitXor (left right : Expr)
  | bitClear (left right : Expr)
  | bitNeg (operand : Expr)
  /-- Unary minus, VALUE-directed (floats slice, note §4 rider): ints
  negate as `0 - v` at the operand's kind; floats are the IEEE sign-bit
  flip (`fneg`) — lowering `-x` as `0 - x` is WRONG at `x = +0`
  (`0 - (+0) = +0`, Go gives `-0`; pinned by `floats/signed-zero`). -/
  | neg (operand : Expr)
  | eqCmp (typ : Ty) (left right : Expr)
  | neqCmp (typ : Ty) (left right : Expr)
  | atMostCmp (left right : Expr)
  | atLeastCmp (left right : Expr)
  | lessCmp (left right : Expr)
  | greaterCmp (left right : Expr)
  | and (left right : Expr)
  | or (left right : Expr)
  | not (operand : Expr)
  | ref (id : String)
  /-- Build a **function value**: the lifted callee's identity plus the
  expressions producing its captured values (addresses — Go captures by
  reference; §8 of the coverage-scoping note). Operands evaluate left to
  right like any strict form. -/
  | funcVal (fid : FuncId) (captured : Array Expr)
  /-- A resolved location literal — evaluates to its address. Two
  producers: the relation's name-resolution substitution (`substLoc`; the
  location-resolved core of `docs/2026-07-19_reshape-mechanics-design.md`),
  and — since the init slice (`docs/2026-08-05_init-design.md` §2, revising
  the original "never emitted by the frontend") — the frontend's statically
  resolved PACKAGE-LEVEL variable references: global `i` (wire declaration
  order) lives at the driver-seeded cell `Loc.base ⟨i⟩`. It remains unused
  for anything env-resolved. -/
  | locLit (l : Loc)
  | deref (ptr : Expr) (typ : Ty)
  | structLit (typ : Ty) (args : Array Expr)
  | fieldGet (recv : Expr) (typeId : TypeId) (fieldName : String)
  | fieldAddr (base : Expr) (typeId : TypeId) (fieldName : String)
  | arrayLit (length : Nat) (elem : Ty) (args : Array (Int × Expr))
  | defaultValue (typ : Ty)
  | toInterface (target dynamic : Ty) (operand : Expr)
  /-- Single-result assert `x.(T)` — panics on mismatch. `source` is the
  operand's STATIC interface type, which Go's panic message names
  (`interface conversion: main.I is main.T, not *main.T`) and which cannot
  be recovered from the runtime value; `none` means the lowering did not
  carry it and the message falls back to the empty-interface spelling
  (pre-merge audit 2026-07-31, finding 8). -/
  | typeAssert (operand : Expr) (target : Ty) (source : Option Ty := none)
  | indexGet (base index : Expr)
  | indexAddr (base index : Expr)
  | mapGet (base index : Expr) (keyTy valueTy : Ty)
  | slice (base low high : Expr) (max : Option Expr)
  | length (operand : Expr) (typ : Option Ty := none)
  | capacity (operand : Expr) (typ : Option Ty := none)
  /-- `min(...)` / `max(...)` over ints or strings (Go's ordered builtins;
  constant-folded calls never reach here). Operands evaluate left to
  right like any strict form. -/
  | minOf (args : Array Expr)
  | maxOf (args : Array Expr)
  /-- UTF-8 rune decode at a byte offset — the range-over-string desugar's
  primitives (`decodeRuneAt`: invalid encodings yield U+FFFD, width 1). -/
  | runeAt (s off : Expr)
  | runeSizeAt (s off : Expr)
  /-- The `recover()` builtin. Not a strict operator: its value depends on
  the continuation (it recovers exactly when called directly by a deferred
  function invoked by a panic — the unwinding arc,
  `docs/2026-07-25_unwinding-arc.md` §A1). -/
  | recoverCall
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Assignee where
  | var (id : String)
  | addr (loc : Expr)
  /-- A MAP-element target `m[k] = v` (convergence round, BUG-030): maps
  are not addressable, so a map-element assignment target cannot be an
  address expression — it carries the base and key expressions and the
  map's key/value types (the `mapAssign` normalization discipline).
  Only the channel-receive delivery path consumes it (`targetPlan`);
  every other assignee position resolves through `assigneeExpr`, which
  is `none` here — those statements fail closed, exactly as before this
  constructor existed. -/
  | mapElem (base index : Expr) (keyTy valueTy : Ty)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

/-- One communication clause HEAD of a `select` statement (channels arc
slice 1): the operands evaluated at select ENTRY (channel operand; send
RHS), with the clause BODY carried beside it in the `selectStmt` pair
array (a nested-inductive shape via `Prod`, the `arrayLit` precedent —
no mutual inductive). Receive targets are Assignees evaluated only AFTER
selection (spec §Select statements, step 4); the frontend lowers
short-variable-declaration and effectful LHS forms into fresh pre-declared
temps plus a body-side assignment, so step-4 side effects stay inside the
selected clause. `elem` is the channel's element type (zero value on
closed receive; send-value normalization). -/
inductive SelectClauseHead where
  | send (ch value : Expr) (elem : Ty)
  | recv (targets : Array Assignee) (ch : Expr) (elem : Ty)
  deriving Repr, BEq, Inhabited

/-- The sync-package statement operations (spec-parity slice 2, design
note §3). Surface-level heads only; the machine-level `SyncOp` (with
the validated `onceBegin` target payload) is derived by `syncPlan`,
exactly the `chanPlan`/`ChanStOp` split. `Once.Do(f)` is a FRONTEND
desugar over `onceBegin`/`onceComplete` (design note §3: the begin
blocks while f runs elsewhere and reports whether to run f; the
complete rides the existing defer machinery so a panicking f still
completes — probe p05). -/
inductive SyncStmtOp where
  | lock
  | unlock
  | rlock
  | runlock
  | wlock
  | wunlock
  | wgAdd
  | wgWait
  | onceBegin
  | onceComplete
  deriving Repr, BEq, Inhabited, DecidableEq

inductive Stmt where
  | seqn (stmts : Array Stmt)
  | block (decls : Array Param) (stmts : Array Stmt)
  /-- A **breakable scope**: `break` inside `body` exits this statement;
  `continue`/`return` pass through to the enclosing loop/frame. Go's
  `switch` and `select` bodies are breakable scopes, so this is Go runtime
  semantics, not a frontend quirk (W2 slice 2,
  `docs/2026-07-24_sequential-coverage-scoping.md`): a frontend flag
  desugaring would be a shortcut that labeled break and `select` later
  have to undo, which the arc's defer-never-foreclose rule forbids. -/
  | breakable (body : Stmt)
  | initialization (var : Param)
  | assign (left : Assignee) (right : Expr)
  | assignMany (left : Array Assignee) (right : Array Expr)
  | newValue (target : Assignee) (value : Expr) (typ : Option Ty := none)
  | makeSlice (target : Assignee) (elem : Ty) (len : Expr) (cap : Option Expr)
  | makeMap (target : Assignee) (key value : Ty) (initialSpace : Option Expr)
  | mapAssign (base index value : Expr) (keyTy valueTy : Ty)
  /-- `delete(m, k)`: remove the key's entry. A nil map is a no-op — the
  base and key still evaluate, in that order (Go; the clear-delete-edge
  suite pins both). -/
  | mapDelete (base index : Expr) (keyTy : Ty)
  /-- `clear(m)`: remove every entry (nil map no-op). -/
  | clearMap (base : Expr)
  /-- `clear(s)`: zero the slice's visible elements IN PLACE (aliases
  observe it). -/
  | clearSlice (base : Expr) (elem : Ty)
  /-- `slices.Sort(s)` at an INTEGER element kind: ascending in-place
  sort of the visible elements (the quorum-pilot extern,
  `docs/2026-07-30_quorum-extern-policy.md` — exact for integers, where
  Go's instability is unobservable; every other `slices.*` use fails
  closed at the frontend). -/
  | sortSlice (base : Expr) (elem : Ty)
  | mapLookup (target okTarget : Assignee) (base index : Expr) (keyTy valueTy : Ty)
  | typeAssert (target okTarget : Assignee) (expr : Expr) (targetTy : Ty)
  | appendSlice (target : Assignee) (elem : Ty) (slice elems : Expr)
  | copySlice (target : Assignee) (dst src : Expr)
  | call (targets : Array Assignee) (func : FuncId) (args : Array Expr)
  /-- Call through a function VALUE (a closure, method value, or func-typed
  variable). The callee expression evaluates to a `GoValue.funcVal`, whose
  captured values are prepended to the arguments at frame entry — the
  lambda-lifting protocol of §8. Calling a `nil` func value panics. -/
  | callValue (targets : Array Assignee) (callee : Expr) (args : Array Expr)
  /-- `defer f(args)`: evaluate the callee and arguments NOW, and prepend
  the pending call to the innermost frame's defer chain, which runs at
  frame exit before the results are read (W3 §9). -/
  | deferCall (callee : Expr) (args : Array Expr)
  | ifThenElse (cond : Expr) (thenBranch elseBranch : Stmt)
  | while (cond : Expr) (body : Stmt)
  /-- Map iteration primitive (the one nondeterministic iteration form). The
  abstract map is an unordered finite map; the iteration order is drawn from
  the choice oracle, one choice per step (next key among those remaining).
  Index-able ranges (slice/array/string/int) desugar to `while` and are not
  represented here. See `docs/nondeterminism-design.md`. `keyVar`/`valVar` are
  `none` for blank or absent range variables. -/
  | mapRange (keyVar valVar : Option String) (mapExpr : Expr) (keyTy valTy : Ty) (body : Stmt)
  | returnStmt
  | breakStmt
  | continueStmt
  /-- A LABELED statement (control-flow slice,
  `docs/2026-08-04_control-flow-design.md`): the label a `breakTo`/
  `continueTo` targets. The frontend attaches it DIRECTLY around the
  loop-forming statement (the desugared `while`, the `mapRange`, the
  switch's `breakable`) — the machine's `contHeadLabel` test relies on
  that placement. Inert labels (goto-only or unreferenced) never lower
  to this. -/
  | labeled (label : String) (body : Stmt)
  /-- `break L`: terminate the enclosing statement labeled `L`. -/
  | breakTo (label : String)
  /-- `continue L`: advance the enclosing loop labeled `L` (post/cond
  re-run by the loop's own desugar). -/
  | continueTo (label : String)
  /-- The `panic(v)` builtin: evaluate the payload, then start unwinding
  with a fresh one-entry panic chain. The payload expression carries the
  Go `any`-conversion (lowering wraps non-interface arguments in
  `.toInterface`); a nil-interface payload becomes the Go 1.21+
  `PanicNilError` runtime error at the panic step (`panicPayload`,
  modern semantics adopted at the arc-final audit F21 2026-08-06; the
  oracle is aligned with `GODEBUG=panicnil=0`). The unwinding arc,
  `docs/2026-07-25_unwinding-arc.md`. -/
  | panicStmt (payload : Expr)
  | label (name : String)
  -- Channel statements (channels arc slice 1,
  -- `docs/2026-08-06_channels-arc-design.md` D7). Range-over-channel is a
  -- FRONTEND desugar to a receive loop (recorded in the design note's
  -- build log): the corpus's other range forms already desugar to `while`
  -- (`mapRange` is primitive only for its nondeterministic order), and a
  -- channel range is exactly repeated comma-ok receive until closed —
  -- no snapshot, no new iteration frame.
  /-- `make(chan T, n)`: allocate a `chanData` cell (empty buffer,
  capacity `n`, open). Negative `n` is the recoverable run-time panic
  `makechan: size out of range` (spec §Making slices, maps and channels;
  probe p21). Routed through the wide-statement (`StmtOp`) machinery like
  `makeMap`. -/
  | makeChan (target : Assignee) (elem : Ty) (capacity : Option Expr)
  /-- `ch <- v`: channel then value, evaluated in that order (pinned by
  `channels/make-edge/ordinary-send-eval-order`), then ONE send step:
  nil → block; closed → panic "send on closed channel"; room → FIFO
  enqueue (normalized at `elem`); full → block. -/
  | chanSend (ch value : Expr) (elem : Ty)
  /-- Receive statement covering `<-ch` (0 targets), `x = <-ch`
  (1 target), and `x, ok = <-ch` (2 targets). Spec §Assignments is
  TWO-PHASE (audit response BUG-022): the channel evaluates and the
  COMMUNICATION happens first — nil → block; buffered value → dequeue,
  `ok = true`; closed-and-drained → zero value at `elem`, `ok = false`;
  open-and-empty → block — and only then do the target addresses
  evaluate and store (their nil-deref / out-of-range panics are phase-2
  events, AFTER the receive; pinned by `channels/recv-edge/*`).
  Spec-ordered evaluations inside the targets (`len(ch)`) are pre-bound
  by the frontend's hoists, which keep lexical order. Receive in
  expression position lowers frontend-side into a temp via this
  statement. -/
  | chanRecv (targets : Array Assignee) (ch : Expr) (elem : Ty)
  /-- `close(ch)`: nil → panic "close of nil channel"; already closed →
  panic "close of closed channel"; else set the closed flag (buffered
  values remain receivable — close does not drain). -/
  | closeChan (ch : Expr)
  /-- `select`: clause operands (channel; send RHS) evaluate once, in
  source order, at ENTRY (spec step 1); one readiness step follows —
  exactly-one-ready commits it, none-ready takes `default` (consuming
  NOTHING — deterministic) or blocks without one. MULTI-ready select
  fails closed in this slice (slice 4 adds the L2 choice envelope). A
  send clause on a CLOSED channel counts as READY and panics when
  selected (probe p23; `select.go` checks closed first). -/
  | selectStmt (clauses : Array (SelectClauseHead × Stmt)) (default? : Option Stmt)
  /-- `go f(args)` (channels arc slice 2, the registry's spawn entry):
  the function value and parameters are evaluated NOW, in the SPAWNING
  goroutine (spec §Go statements: "evaluated as usual in the calling
  goroutine") — the `deferCall` eval-now frame shape (`goCalleeK`/
  `goArgsK`). The SPAWN itself is a POOL-level step (`stepMulti`): the
  per-goroutine relation is silent at the evaluated spawn configuration
  and `stepFn` fails closed there — which is exactly what keeps `go`
  during `$pkginit` refused this slice (the init phase runs on the
  sequential driver). A nil callee is gc's "go of nil func value"
  FATAL at the spawn, in the spawner (probed 2026-08-07, REFUTING the
  machine-shape note §6's child-panic-at-first-step analysis); the
  fatal class is unmodeled — refused fail-closed at the spawn step. -/
  | goStmt (callee : Expr) (args : Array Expr)
  | unsupported (feature : String)
  /-- A sync-package primitive operation (spec-parity slice 2, design
  note `docs/2026-08-09_sync-package-design.md` §3): `args` is the
  RECEIVER ADDRESS expression (every in-scope sync method has a pointer
  receiver; the frontend emits `&recv` for addressable receivers),
  plus the delta expression for `wgAdd` (`Done()` lowers to
  `wgAdd(-1)`, gc's own definition). `targets` is used ONLY by
  `onceBegin` (one fresh frontend temp receiving the run-f bool of the
  Once desugar; empty for every other op) — `syncPlan` validates the
  shape and fails closed on drift. Appended at the END of the inductive
  so positional case tags stay stable. -/
  | syncStmt (op : SyncStmtOp) (args : Array Expr) (targets : Array Assignee)
  deriving Repr, BEq, Inhabited

structure Func where
  id : FuncId
  args : Array Param
  results : Array Param
  body : Stmt
  /-- Go's variadic marker on the LAST parameter, carried verbatim from the
  frontend. It does NOT change how a call binds arguments — the frontend
  already packs the spread into a slice at the call site — it is the half
  of the signature interface satisfaction must compare against a
  `MethodSig`'s own marker (pre-merge audit 2026-07-31, finding 0).
  Defaults to `false` so hand-built GoCore programs (tests, proofs) stay
  non-variadic; the wire always carries it explicitly. -/
  variadic : Bool := false
  /-- A compiler-SYNTHESIZED promotion wrapper (wire `"wrapper": true`,
  design note 2026-08-05 D1.3): the frame it enters is marked so the
  recover walk treats it as transparent, exactly gc's
  `abi.FuncIDWrapper` (BUG-015, arc-final audit F1, 2026-08-06).
  Defaults to `false` — hand-built programs and every user-declared
  function are non-wrappers; only the frontend's synthesized promotion
  wrappers set it. -/
  wrapper : Bool := false
  deriving Repr, BEq

structure MethodInfo where
  name : String
  funcId : FuncId
  recv : Ty
  deriving Repr, BEq

/-- How much of a type's method set the wire records
(`docs/2026-08-10_method-set-record-contract.md` §3). `full` — the
complete set (locally declared named types; the D2 wire contract).
`exported` — exported methods only (D5 imported markers, the sync
primitives): a definite-"no" that hinges on an UNEXPORTED requirement
refuses instead of answering. -/
inductive MethodSetCoverage where
  | full
  | exported
  deriving Repr, BEq

/-- One method-set record: the frontend's explicit statement that
`key`'s method set is on the wire at the stated coverage —
empty-but-present means GENUINELY empty. The satisfaction/dispatch
guards answer ONLY from these records (class closure of BUG-053, user
direction 2026-08-10): a queried method-carrying type with no record
refuses visibly, never answers. `key` is the carrier key —
`TypeId.key` for `.defined`, `sync.<Kind>` for `.sync`
(`methodCarrierKey?`, Ops.lean). -/
structure MethodSetRecord where
  key : String
  coverage : MethodSetCoverage
  deriving Repr, BEq

/-- A package-level variable declaration (init slice,
`docs/2026-08-05_init-design.md` §2): the driver seeds one heap cell per
entry — zero value at the declared type — as the FIRST allocations, in
array order, so entry `i`'s cell is exactly `Loc.base ⟨i⟩` and the
frontend can resolve every reference statically (`Expr.locLit`). `name`
is carried for diagnostics only; runtime resolution never consults it. -/
structure GlobalDef where
  name : String
  typ : Ty
  deriving Repr, BEq

structure Program where
  typeDefs : Array (TypeId × TypeDef) := #[]
  funcs : Array Func
  methods : Array MethodInfo := #[]
  /-- Package-level variables, in declaration order (files in lexical
  filename order). Empty for globals-free programs — every existing
  construction site is untouched. -/
  globals : Array GlobalDef := #[]
  /-- The method-set records (contract note §3, 2026-08-10): REQUIRED
  on the wire — the decoder refuses a wire without the field — and
  defaulted `#[]` here so hand-built programs FAIL CLOSED on carrier
  queries rather than answering from absence. -/
  methodSets : Array MethodSetRecord := #[]
  deriving Repr, BEq

def findFunctionIn? (funcs : Array Func) (id : FuncId) : Option Func :=
  funcs.foldl
    (fun found func =>
      match found with
      | some f => some f
      | none => if func.id == id then some func else none)
    none

/-- The machine-internal `TypeId` of a Go runtime error payload. `$` cannot
appear in a Go identifier OR package name, so no source-level `TypeId` — now
that they are package-QUALIFIED (`main.T`) — can collide with it. The old
`"runtime.Error"` sentinel justified itself with "Go identifiers cannot
contain `.`", which package qualification falsified: a package named
`runtime` declaring `type Error string` produced the identical key, and
`r.(Error)` then bound the runtime message as a user value (pre-merge audit
2026-07-31, finding 9). Lives in Syntax (moved from Machine, 2026-08-05)
so the wire decoder can synthesize runtime-panic payloads (the
nil-interface method-value creation check) without importing the machine. -/
def runtimeErrorTypeId : TypeId := ⟨"$runtime.Error"⟩

/-- The reserved id of the synthesized package-initialization function
(init slice, `docs/2026-08-05_init-design.md`): the frontend emits it —
package-level variable initializers in `go/types`' `InitOrder`, then the
`init()` functions (exported as `$init0`, `$init1`, … in source order) —
and the driver runs it to completion before the subject. The same
`$`-cannot-appear-in-a-Go-identifier argument as `runtimeErrorTypeId`
keeps every `$`-prefixed id collision-free against user code. -/
def pkgInitFuncId : FuncId := ⟨"$pkginit"⟩
