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
  T = U` is identity-ERASING and never reaches the table (C2, 2026-09-05:
  the frontend inlines aliases at every use — `types.Unalias` — and the
  decoder refuses an `alias` TypeDef; the old `.alias` constructor,
  reachable from no wire, is deleted). Defined types over STRUCT
  underlyings stay `.struct` (their values are name-tagged);
  defined-over-defined-struct fails closed at the consumer until a case
  needs it. -/
  | defined (underlying : Ty)
  /-- A declaration the frontend marks OPAQUE by design (imported/quarantined
  types): its uses refuse by name (`reason`). Renamed from `unsupported` (A8; `opaque` itself is a Lean keyword)
  so it is not confused with `Ty.unsupported`/`Expr.unsupported`. -/
  | opaqueDecl (reason : String)
  deriving Repr, BEq

/-! ## The type table and its well-foundedness (C-arc C2, 2026-09-05)

Design note `docs/2026-09-05_c-arc-c2-design.md`. Gate G-C2 («Frontend
emits typeDefs in dependency order with aliases inlined; `TypeEnv`
becomes index-keyed and well-founded by an `Accepted` clause decided at
decode; the fuel towers, `typeResolutionFuel` and the `irreducible` seal
are deleted») RULED [USER] 2026-09-04 as recommended, CONFIRMED [USER]
2026-09-05 — both relayed by the [AGENT] coordinator, cited as relayed. -/

/-- The program's type table: the declared types in DEPENDENCY ORDER,
`Ty.defined i` naming entry `i`. The `TypeId` beside each body is the
type's key for interface identity, method-set records and every
gc-visible text; it is never used to resolve a `Ty.defined`. -/
abbrev TypeEnv := Array (TypeId × TypeDef)

/-- The TABLE DEPENDENCIES of a type: the entries a type-directed
recursion (`defaultValue`, `tySizeAlign`, `tyUncomparable`,
normalization, conversion, equality — `Ops.lean`) descends into. Exactly
`.defined` itself and `.defined` through ARRAY elements; pointer, slice,
map, channel, function and interface types are LEAVES of every such
recursion (Go permits recursive types only through them — `type L
struct{ next *L }` — and their values never contain the pointee), so
they contribute no edge. Interface method signatures are compared by
`Ty.eqb`, never resolved, so an `.interfaceDef` has no dependencies. -/
def Ty.deps : Ty → List TypeIdx
  | .defined i => [i]
  | .array _ elem => Ty.deps elem
  | _ => []

@[inherit_doc Ty.deps]
def TypeDef.deps : TypeDef → List TypeIdx
  | .struct fields => fields.toList.flatMap (fun f => f.typ.deps)
  | .defined underlying => underlying.deps
  | .interfaceDef _ => []
  | .opaqueDecl _ => []

/-- THE well-foundedness clause of `Accepted` (plan §1.9): every table
dependency of entry `i` sits at a SMALLER index. Decided at decode
(`NativeToIR`), refused by name when violated; on a table satisfying it
every index descent in `Ops.lean` — seeded at `types.size`, one index
consumed per `.defined` resolution — provably never reaches its
exhaustion arm, because a dependency chain from index `i` has at most
`i + 1` entries. Stated over the enumerated list so the `Decidable`
instance is the library's (`List.decidableBAll`). -/
def TypeEnv.WellFounded (types : TypeEnv) : Prop :=
  ∀ e ∈ types.toList.zipIdx, ∀ j ∈ e.1.2.deps, j < e.2

instance (types : TypeEnv) : Decidable types.WellFounded :=
  inferInstanceAs (Decidable (∀ e ∈ types.toList.zipIdx, ∀ j ∈ e.1.2.deps, j < e.2))

/-- The FIRST violating edge of `TypeEnv.WellFounded`, for the decoder's
refusal text: `(i, j)` with entry `i` depending on entry `j`, `j ≥ i`
(a forward reference or a cycle). `none` exactly when the table is
well-founded (`TypeEnv.firstViolation?_eq_none_iff`). -/
def TypeEnv.firstViolation? (types : TypeEnv) : Option (TypeIdx × TypeIdx) :=
  types.toList.zipIdx.findSome? fun e =>
    (e.1.2.deps.find? (fun j => e.2 ≤ j)).map fun j => (e.2, j)

theorem TypeEnv.firstViolation?_eq_none_iff (types : TypeEnv) :
    types.firstViolation? = none ↔ types.WellFounded := by
  unfold TypeEnv.firstViolation? TypeEnv.WellFounded
  simp only [List.findSome?_eq_none_iff, Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h e he j hj
    exact Nat.lt_of_not_le (by simpa using h e he j hj)
  · intro h e he j hj
    simpa using Nat.not_le.mpr (h e he j hj)

/-- The entry's key, read back from an index (texts, records, the
observation channel). `none` for an index the table does not have — the
callers fail closed on it. -/
def TypeEnv.nameOf? (types : TypeEnv) (idx : TypeIdx) : Option TypeId :=
  (types[idx]?).map Prod.fst

/-- Name-keyed lookup, for the two consumers whose key is a VALUE tag or
an interface name rather than a `Ty`: struct-tag compatibility and
interface declarations. Linear, and never on a `Ty.defined` path. -/
def TypeEnv.lookupName? (types : TypeEnv) (needle : TypeId) : Option (TypeIdx × TypeDef) :=
  types.toList.zipIdx.findSome? fun e =>
    if e.1.1 == needle then some (e.2, e.1.2) else none

/-- The four documented bit-reinterpretation functions of `math`
(`Float64bits`/`Float64frombits`/`Float32bits`/`Float32frombits` —
`deps/go/src/math/unsafe.go:21-41` @ go1.26.5; `math` is not a
source-through package, so the `godoc:` grammar — pinned-manifest
packages only, gate G3 — does not apply and the file:line citation is
the one the runtime-source rows use) as ONE machine op with a
direction/width tag — the `float-bits` PRIMITIVE (stdlib register class
`primitive`, 1 of 2; ADMITTED [USER] 2026-09-04, relayed by the [AGENT]
coordinator, cited as relayed: «so the question is whether to add this as
a primitive language operation? This sounds reasonable, do it»). The
language has no operation for "the bits of a float" — `math`'s own bodies
are `*(*uint64)(unsafe.Pointer(&f))` — and the machine's float
representation IS the bit pattern (`GoValue.float bits kind`,
`FloatBits.lean`), so the op is the identity on the representation in
both directions: NaN payloads, the sign of zero, quiet/signalling all
round-trip BIT-EXACT (the audit's admission condition). Design note:
`docs/2026-09-04_stdlib-slice-3-design.md` §2. -/
inductive FloatBitsOp where
  | f64bits
  | f64frombits
  | f32bits
  | f32frombits
  deriving Repr, BEq, Inhabited, DecidableEq

def FloatBitsOp.name : FloatBitsOp → String
  | .f64bits => "math.Float64bits"
  | .f64frombits => "math.Float64frombits"
  | .f32bits => "math.Float32bits"
  | .f32frombits => "math.Float32frombits"

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
  /-- A PACKAGE-LEVEL variable by its global index (design-hygiene A4,
  2026-09-04; was `locLit (l : Loc)`): the frontend's statically resolved
  reference to global `gid` (wire declaration order,
  `docs/2026-08-05_init-design.md` §2). The MACHINE turns it into the
  address `Loc.base ⟨gid⟩` at evaluation time — the driver seeds global
  `i` as the `i`-th allocation — after checking the cell exists, so program
  text is ADDRESS-FREE: a `Program` is a constant and `StateWf` is about the
  heap alone. The only `Expr` form that names a global; env-resolved
  references stay `ref`. -/
  | global (gid : Nat)
  | deref (ptr : Expr) (typ : Ty)
  /-- `&*p` / `&(*p)` — the spec's own composite (spec#Address_operators:
  "if the evaluation of `x` would cause a run-time panic, then the
  evaluation of `&x` does too", with `&*x // causes a run-time panic`
  as its exhibit): assert the pointer non-nil, yield the SAME pointer,
  touch NO memory. gc compiles it to a single uninstrumented hardware
  nil-probe (`TESTB`) with no pointee load, so lowering it through a
  real `deref` would fabricate a race-visible read gc never performs
  (BUG-056, memo §2–§3; fix ruled 2026-08-19, memo §6). -/
  | addrOfDeref (ptr : Expr)
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
  /-- `[]rune(s)` / `string([]rune)` (triage L1, 2026-08-19): the two
  rune-slice conversion directions, over the same `decodeRuneAt` /
  `GoString.fromCodePoint` kernels as the range desugar and
  `string(int)`. Appended at the end of the strict forms so positional
  proofs over earlier constructors stay put. -/
  | runesFromString (operand : Expr)
  | stringFromRuneSlice (operand : Expr)
  /-- `math.Float64bits(x)` and its three siblings (stdlib slice 3,
  2026-09-04): the `float-bits` primitive, `FloatBitsOp` above. A pure
  strict form appended after the rune conversions. -/
  | floatBits (op : FloatBitsOp) (operand : Expr)
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
completes — probe p05).

The TRY heads (Q-TRYLOCK, RULED [USER] 2026-08-31 — `docs/2026-08-31_
qrow-rulings.md` row 5 — implemented 2026-09-03): `tryLock` =
`sync.Mutex.TryLock`, `tryRLock` = `sync.RWMutex.TryRLock`, `tryWLock`
= `sync.RWMutex.TryLock` (the `lock`/`rlock`/`wlock` naming). They are
the VALUE-RETURNING sync ops: `targets` carries the Bool result target
(at most one; a bare `m.TryLock()` statement discards it but still
acquires). Their machine semantics — mem#locks' spurious-failure member
as the width-2 `ChoiceSite.tryLock` — is `applySyncOp`'s
(Machine.lean). -/
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
  | tryLock
  | tryRLock
  | tryWLock
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The `sync/atomic` integer-op HEADS (the atomics arc, wave 1 —
Q-ATOMIC RULED [USER] 2026-09-02 option A′,
`docs/2026-08-31_qrow-rulings.md` row 2; charter
`docs/2026-09-01_qatomic-owner-proposal.md` §4; design note
`docs/2026-09-03_atomics-w1-design.md`). Surface-level heads only; the
machine-level `AtomicOp` (head + the cell's integer kind + the
validated result target) is derived by `atomicPlan`, exactly the
`syncPlan`/`SyncOp` split. `Load`/`Store`/`Add`/`Swap`/
`CompareAndSwap` over the integer kinds the frontend admits
(`int32`/`int64`/`uint32`/`uint64`; `uintptr` arrives as `uint64`, the
R1 pin). `And`/`Or`, the `unsafe.Pointer` family, and
`atomic.Value`/`Bool`/`Pointer` are wave 2 and refuse at the frontend
by name. -/
inductive AtomicStmtOp where
  | load
  | store
  | add
  | swap
  | cas
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
  | allocNew (target : Assignee) (value : Expr) (typ : Ty)
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
  | inertLabel (name : String)
  -- Channel statements (channels arc slice 1,
  -- `docs/2026-08-06_channels-arc-design.md` D7). Range-over-channel is a
  -- FRONTEND desugar to a receive loop (recorded in the design note's
  -- build log): the corpus's other range forms already desugar to `while`
  -- (`mapRange` is primitive only for its nondeterministic order), and a
  -- channel range is exactly repeated comma-ok receive until closed —
  -- no snapshot, no new iteration frame.
  /-- `make(chan T, n)`: allocate a `chanPayload` cell (empty buffer,
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
  /-- A `sync/atomic` integer operation (the atomics arc, wave 1 —
  design note `docs/2026-09-03_atomics-w1-design.md`): ONE fused
  registry op — the read-modify-write of the addressed cell happens in
  a SINGLE machine step at a scheduling boundary, so mem#atomic's
  mandate ("All the atomic operations executed in a program behave as
  though executed in some sequentially consistent order") falls out of
  the L1 interleaving of indivisible steps with ZERO new choice sites
  (the envelope statement is at `applyAtomicOp`). `kind` is the
  integer kind of the addressed cell (the op's own type); `args` is
  the ADDRESS expression followed by the value operands — `store`/
  `add`/`swap`: one; `cas`: old, new; `load`: none — evaluated left to
  right like a call's arguments (spec#Order_of_evaluation; the ANF
  hoist statement-anchors the call, so no expression-position atomic
  step exists for a future expression-machine reshape to split — the
  F4 non-foreclosure argument, memo §2). `targets` receives the result
  (`load` → the value, `add` → the NEW value, `swap` → the OLD value,
  `cas` → the swapped bool): empty when the result is discarded, and
  always empty for `store`. `atomicPlan` validates the shape and fails
  closed on drift. Appended at the END of the inductive so positional
  case tags stay stable. -/
  | atomicStmt (op : AtomicStmtOp) (kind : IntKind) (args : Array Expr) (targets : Array Assignee)
  /-- `print(args…)` / `println(args…)` — spec#Bootstrapping's two
  built-ins (stdlib slice 3, 2026-09-04; G2 RULED [USER] 2026-09-03 as
  recommended, relayed by the [AGENT] coordinator: «print/println as
  machine built-ins with a stderr observable: accept with gc's pinned
  format for int/uint/bool/string, refuse address-printing kinds and
  initially floats»). `newline` selects `println` (space-separated,
  newline-terminated) over `print` (no separators). The statement writes
  the bytes gc's `runtime/print.go` writes to fd 2 — the machine's
  OUTPUT EVENT (`StepEvent.out`, pool layer; design gate G-OUT RULED
  [USER]: «Program output is a per-step EVENT (`StepEvent.out`), folded
  by the driver into `Readout`, not a `Store` field; `Obs.terminal`
  carries the stderr prefix»). Rides the wide-statement mold
  (`StmtOp.print`): operands evaluate left to right, then ONE apply step
  that changes no state (gc brackets the whole statement in
  `printlock`/`printunlock`, so one step is the exact atomicity). At
  least one operand — the zero-operand spellings refuse at the frontend
  by name (the mold's A8 invariant: no plan has an empty operand list).
  Appended at the END of the inductive so positional case tags stay
  stable. -/
  | print (newline : Bool) (args : Array Expr)
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
frontend can resolve every reference statically (`Expr.global`). `name`
is carried for diagnostics only; runtime resolution never consults it. -/
structure GlobalDef where
  name : String
  typ : Ty
  deriving Repr, BEq

/-- The DISPLAY record of a `TypeId` (design note
`docs/2026-09-05_fr19-bug097-design.md` §0/§3): `name` is gc's runtime
type string for the type (`NameString` — package-NAME qualified, no
scope information, deliberately ambiguous: `inner.T` for both
`red/inner.T` and `blue/inner.T`, `main.L` for every function-local `L`),
`pkg` its declaring import path (`""` for unnamed, universe and synthetic
types — gc's `pkgpath()` of an unnamed type). The machine RENDERS panic
texts from this and decides nothing by it; identity is the `TypeId.key`
alone. Carried on the wire per TypeDef (REQUIRED there); defaulted `#[]`
in `Program`/`ExecState` so hand-built programs render a visible
no-record marker rather than a fabricated gc text. -/
structure TypeDisplay where
  name : String
  pkg : String := ""
  deriving Repr, BEq

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

/-- The canonical anonymous empty struct `struct{}` — the one unnamed
struct type the wire can carry (BUG-011; `map[K]struct{}` sets). The
frontend references it by this key and emits no declaration; the machine
owns its entry (`TypeEnv.reserved`, index 0). -/
def emptyStructTypeId : TypeId := ⟨"struct{}"⟩

/-- Index of `struct{}` in every accepted table (`TypeEnv.reserved`). -/
def emptyStructTypeIdx : TypeIdx := 0

/-- Index of the runtime-error payload type in every accepted table
(`TypeEnv.reserved`); `runtimeErrorValue` boxes at `.defined` this. -/
def runtimeErrorTypeIdx : TypeIdx := 1

/-- The reason text of the runtime-error payload type's opaque entry. -/
def runtimeErrorOpaqueReason : String :=
  "the machine's runtime-error payload type ($runtime.Error): structural use (==, normalization or conversion at the type, default value) is unmodeled — gc realizes several runtime.Error types behind one abort text (BUG-059 kind clause), so the machine refuses rather than answers"

/-- The two MACHINE-RESERVED leading entries of every accepted type table
(C2): index 0 is `struct{}` (a real empty struct: comparable, its default
value exists, assignable across the BUG-011 escape), index 1 is the
runtime-error payload type as an OPAQUE declaration — every structural
use refuses by name, which is exactly the fail-closed behaviour the
absent declaration produced before the table was index-keyed. The
decoder prepends them and refuses a wire declaring either key; hand-built
programs prepend them too (`TypeEnv.reserved ++ …`). Neither entry has
table dependencies, so the prefix is well-founded by itself. -/
def TypeEnv.reserved : TypeEnv :=
  #[(emptyStructTypeId, .struct #[]), (runtimeErrorTypeId, .opaqueDecl runtimeErrorOpaqueReason)]

/-- The visible rendering of the machine-minted runtime-error payload
type (`runtimeErrorTypeId`, `$runtime.Error`; reserved index
`runtimeErrorTypeIdx`). gc has no ONE type here: a nil dereference is
`runtime.errorString`, an index fault `runtime.boundsError`, a failed
assert `*runtime.TypeAssertionError`, a zero divide
`runtime.runtimeError` — the machine collapses them onto one synthetic
entry and cannot spell the concrete one, so its display is a marker that
NAMES that cause (fr19 audit fix round R3, 2026-09-05 [AGENT]; BUG-099).
It is a text for refusal messages and the belt-and-suspenders reach;
`typeAssertPanicMessage` REFUSES before this could reach an observable
panic text. Lives beside the reserved prefix (moved from `Ops.lean` at
the round-17 rebase, [AGENT]) because the reserved entry's display
record carries it. -/
def runtimeErrorDisplayMarker : String :=
  "<runtime error payload: gc's concrete type (runtime.errorString / \
runtime.boundsError / *runtime.TypeAssertionError / …) is not modeled — \
one synthetic $runtime.Error id, BUG-009/BUG-053 class>"

/-- The display records of the two reserved entries (`TypeDisplay`, design
note `docs/2026-09-05_fr19-bug097-design.md` §3.1), in table order — the
decoder leads `Program.typeDisplays` with them exactly as it leads
`typeDefs` with `TypeEnv.reserved`, so on every decoded program record
`i` belongs to entry `i`. `struct{}` displays as gc spells the empty
struct, `struct {}`, with the empty pkgpath of an unnamed type; the
runtime-error entry displays the cause-naming marker (there is no single
gc-correct type string — BUG-099) with pkgpath `runtime`, which IS
gc-correct for every concrete fault type (`runtime.errorString`,
`runtime.boundsError`, `*runtime.TypeAssertionError`, … all live in
package `runtime`). -/
def TypeEnv.reservedDisplays : Array (TypeId × TypeDisplay) :=
  #[(emptyStructTypeId, { name := "struct {}", pkg := "" }),
    (runtimeErrorTypeId, { name := runtimeErrorDisplayMarker, pkg := "runtime" })]

/-- Does the table lead with the two reserved entries? The second clause
of the type-table acceptance (`TypeEnv.WellFounded` is the first). The
decoder does not EVALUATE this predicate — it CONSTRUCTS the prefix
(`NativeToIR.lean`, `TypeEnv.reserved ++ declaredDefs`) and refuses a
wire TypeDef spelling a reserved key; the predicate's consumers are the
two driver seams (`runProgramSetupM`, `CLI.enumSetup`), which refuse a
`Program` whose table does not lead with it before any step runs — a
hand-built table with a user type at index 1 would otherwise render a
user value as the runtime-error payload (audit fix R2, 2026-09-05). A
Bool, evaluated at run time: the comparison is a long-string `==`, not
`decide`-cheap (see the design note §8 on the owed `Accepted` Prop). -/
def TypeEnv.hasReservedPrefix (types : TypeEnv) : Bool :=
  types.extract 0 2 == TypeEnv.reserved

-- (`runtimeErrorTypeId` … `TypeEnv.hasReservedPrefix` sit ABOVE `Program`
-- because `Program.typeDefs` defaults to `TypeEnv.reserved` — audit fix R2.)

structure Program where
  /-- The type table (`TypeEnv`): dependency-ordered, `Ty.defined`
  indexes into it; the two machine-reserved entries lead
  (`TypeEnv.reserved`) — the default is the bare prefix, so a hand-built
  `Program` that declares no types is accepted by the driver seams'
  `hasReservedPrefix` check (audit fix R2). -/
  typeDefs : TypeEnv := TypeEnv.reserved
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
  /-- The display records (design note 2026-09-05 §3.1), one per TypeDef
  on a decoded wire, in table order (the reserved entries' records lead,
  `TypeEnv.reservedDisplays`); the default is the reserved entries'
  records, matching `typeDefs`'s default, so a declaration-free
  hand-built `Program` renders `struct {}` as gc does and a hand-built
  program that declares types renders the visible no-record marker for
  them unless it states their displays (fr19 × C2). -/
  typeDisplays : Array (TypeId × TypeDisplay) := TypeEnv.reservedDisplays
  deriving Repr, BEq

def findFunctionIn? (funcs : Array Func) (id : FuncId) : Option Func :=
  funcs.foldl
    (fun found func =>
      match found with
      | some f => some f
      | none => if func.id == id then some func else none)
    none

/-- The reserved id of the synthesized package-initialization function
(init slice, `docs/2026-08-05_init-design.md`): the frontend emits it —
package-level variable initializers in `go/types`' `InitOrder`, then the
`init()` functions (exported as `$init0`, `$init1`, … in source order) —
and the driver runs it to completion before the subject. The same
`$`-cannot-appear-in-a-Go-identifier argument as `runtimeErrorTypeId`
keeps every `$`-prefixed id collision-free against user code. -/
def pkgInitFuncId : FuncId := ⟨"$pkginit"⟩
