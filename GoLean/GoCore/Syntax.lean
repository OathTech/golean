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
  /-- A resolved location literal — evaluates to its address. Proof-facing:
  introduced only by the relation's name-resolution substitution (`substLoc`),
  never emitted by the frontend. The location-resolved core (Goose-aligned;
  `docs/2026-07-19_reshape-mechanics-design.md`) rewrites `var`/`ref` into this
  so the relation performs no runtime name lookup. -/
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
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

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
  `.toInterface`); a nil-interface payload stays nil — the oracle runs in
  GOPATH mode, where `panic(nil)` keeps its legacy semantics (`recover()`
  returns nil; see `panicPayload`). The unwinding arc,
  `docs/2026-07-25_unwinding-arc.md`. -/
  | panicStmt (payload : Expr)
  | label (name : String)
  | unsupported (feature : String)
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
  deriving Repr, BEq

structure MethodInfo where
  name : String
  funcId : FuncId
  recv : Ty
  deriving Repr, BEq

structure Program where
  typeDefs : Array (TypeId × TypeDef) := #[]
  funcs : Array Func
  methods : Array MethodInfo := #[]
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
