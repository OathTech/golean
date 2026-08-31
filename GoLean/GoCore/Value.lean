namespace GoLean

namespace GoCore

inductive IntKind where
  | int
  | uint
  | int8
  | uint8
  | int16
  | uint16
  | int32
  | uint32
  | int64
  | uint64
  | unbounded (name : String)
  deriving Repr, BEq, Inhabited, DecidableEq

def IntKind.name : IntKind → String
  | .int => "int"
  | .uint => "uint"
  | .int8 => "int8"
  | .uint8 => "uint8"
  | .int16 => "int16"
  | .uint16 => "uint16"
  | .int32 => "int32"
  | .uint32 => "uint32"
  | .int64 => "int64"
  | .uint64 => "uint64"
  | .unbounded name => name

/-- PINNED LATITUDE — `int`/`uint` width (inventory R1; register
extension #6; site caveat added 2026-08-31, closing §9 flag 2's owed
record). spec#Numeric_types makes the width of `int`/`uint` (and
`uintptr`, frontend-mapped to uint64) IMPLEMENTATION-SPECIFIC —
"either 32 or 64 bits"; the plausible envelope is {32, 64} as a
machine parameter. The `.int => some 64` / `.uint => some 64` arms
below pin the 64-bit member — the oracle host's realization (gc
linux/amd64), shared by the frontend's go/types Sizes and the
negative lane's acceptance. TRANSFER CAVEAT: any claim about
wrap/overflow at `int`/`uint` boundaries transfers only to 64-bit
targets; a 32-bit conforming implementation is outside this
singleton. Re-envelope (width as a parameter across normalize/
conversions/frontend Sizes/negative-lane acceptance) is XIMPL-gated —
blocked in practice on any 32-bit oracle lane; see inventory R1. -/
def IntKind.bits? : IntKind → Option Nat
  | .int => some 64
  | .uint => some 64
  | .int8 => some 8
  | .uint8 => some 8
  | .int16 => some 16
  | .uint16 => some 16
  | .int32 => some 32
  | .uint32 => some 32
  | .int64 => some 64
  | .uint64 => some 64
  | .unbounded _ => none

def IntKind.signed : IntKind → Bool
  | .int => true
  | .uint => false
  | .int8 => true
  | .uint8 => false
  | .int16 => true
  | .uint16 => false
  | .int32 => true
  | .uint32 => false
  | .int64 => true
  | .uint64 => false
  | .unbounded _ => true

def IntKind.normalize (kind : IntKind) (value : Int) : Int :=
  match kind.bits? with
  | none => value
  | some bits =>
      let modulus : Int := (2 : Int) ^ bits
      let wrapped := value % modulus
      if kind.signed then
        let half : Int := (2 : Int) ^ (bits - 1)
        if wrapped >= half then wrapped - modulus else wrapped
      else
        wrapped

def IntKind.isFlexible : IntKind → Bool
  | .unbounded _ => true
  | _ => false

/-- Go's floating-point kinds (floats slice F2, 2026-08-05;
`docs/2026-08-04_floats-design.md` decision 6). Unlike `IntKind` there is
no flexible/unbounded member: the frontend types every float constant
(go/types), so a float value's kind is always concrete. -/
inductive FloatKind where
  | float32
  | float64
  deriving Repr, BEq, Inhabited, DecidableEq

def FloatKind.name : FloatKind → String
  | .float32 => "float32"
  | .float64 => "float64"

def FloatKind.bits : FloatKind → Nat
  | .float32 => 32
  | .float64 => 64

/-- The width invariant's enforcement mask, exactly parallel to
`IntKind.normalize`: a stored `GoValue.float`'s bit pattern is always
`< 2^width` (design note §6; `FloatBits`' raw-encoding comparisons and
sign XORs assume it). Idempotent on well-formed patterns. -/
def FloatKind.normalizeBits (kind : FloatKind) (bits : Nat) : Nat :=
  bits % 2 ^ kind.bits

/-- Semantic function identity. The key is a canonical name produced only by
the frontend symbol map (source-level function name; receiver-scoped method
key; synthetic `F$litN` for a lifted func literal). Raw frontend names must
not construct this directly — lowering resolves them through its symbol map
and fails closed on unknown or colliding names.

Lives here rather than in `Syntax` because `GoValue.funcVal` carries it, the
same reason `TypeId` lives beside the values that carry it. -/
structure FuncId where
  key : String
  deriving Repr, BEq, Inhabited, DecidableEq

/-- Channel direction, a STATIC type property (spec §Channel types: "A
channel may be constrained only to send or only to receive by assignment
or explicit conversion" — direction lives in the type, never in the
runtime value; the negative corpus pins direction misuse at the compile
stage via go/types). Carried on `Ty.chan` because direction is part of
type IDENTITY (a directional conversion changes the type but not the
channel), which interface boxing/asserts and `Ty.eqb` key on. -/
inductive ChanDir where
  | both
  | send
  | recv
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The sync-package primitive KINDS modeled as machine types
(spec-parity slice 2, `docs/2026-08-09_sync-package-design.md` §3; scope
D4: Mutex/RWMutex/WaitGroup/Once in — atomics/Map/Cond/Pool out, each
failing closed at the frontend). Like `ChanDir` this is a STATIC type
property: `Ty.sync kind` is the type of the sync struct, whose zero
value is the zero primitive ("The zero value for a Mutex is an unlocked
mutex"). -/
inductive SyncKind where
  | mutex
  | rwmutex
  | waitGroup
  | once
  deriving Repr, BEq, Inhabited, DecidableEq

def SyncKind.name : SyncKind → String
  | .mutex => "Mutex"
  | .rwmutex => "RWMutex"
  | .waitGroup => "WaitGroup"
  | .once => "Once"

def IntKind.compatibleResult (left right : IntKind) : Option IntKind :=
  if left == right then
    some left
  else if left.isFlexible then
    some right
  else if right.isFlexible then
    some left
  else
    none

end GoCore

inductive GoError where
  | panic (message : String)
  | unsupported (feature : String)
  | stuck (message : String)
  | internal (message : String)
  /-- Fuel exhaustion — a MODEL artifact, not a program behavior: the
  bounded run ended before the program did. Distinct from `.stuck` (sem-
  adequacy arc slice 2, 2026-08-03) so interpreter-level safety can say
  "every run ends `.ok` or `.fuelOut`, never stuck/panicked" and mean it;
  conflating the two (the old shape distinguished them only by message
  text) would make that reading unstatable. -/
  | fuelOut
  /-- Deadlock — a PROGRAM behavior, not a model artifact (channels arc
  slice 1): the run reached a blocked configuration with no runnable
  goroutine, matching Go's runtime detector (`fatal error: all
  goroutines are asleep - deadlock!`, exit status 2 — a fatal, not a
  recoverable panic). In the zero-scheduler slice the single goroutine
  blocking IS whole-program deadlock, so `stepFn` classifies blocked
  configurations with this directly; the ThreadPool machine (slice 2)
  moves the all-blocked judgment to the pool level. The message text is
  the detector's fixed line — Go pins the abort MESSAGE, though the
  detection itself is the flagship's rendering of the spec's "blocks
  forever" (latitude row L6, ground-truth note §6). -/
  | deadlock
  /-- Data race — a PROGRAM-class refusal, not a model artifact
  (channels arc slice 3, D2+D3(b)): the pool's segment-level
  happens-before detector found two HB-unordered conflicting accesses
  from different goroutines. Races FAIL CLOSED per run (nondeterminism
  doctrine: no semantics below the DRF line — the memory model's
  ceiling for racy programs includes "report the race and terminate"
  and multiword corruption), on every run where the conflicting
  accesses execute, deterministically given the stream. The
  differential oracle for this class is `go run -race` (TSan; exit 66);
  the message is FIXED so per-stream refusal is choice-invariant in the
  harness. Never combined with deadlock expectations (-race suppresses
  the deadlock detector — ground-truth note §5). -/
  | raceDetected
  /-- An UNRECOVERABLE runtime throw — a PROGRAM behavior, not a model
  artifact (spec-parity slice 2, sync design note §2): gc's
  `fatal error: <msg>` aborts (exit status 2) that `recover` does NOT
  catch (probed: `sync: unlock of unlocked mutex` and the RWMutex
  misuse throws — runtime `fatal`, never a `panic()`), so they must not
  be modeled as `.panic` (a recover would wrongly intervene) nor as a
  refusal (the behavior is probed and deterministic — differentially
  testable, the deadlock terminal's pattern with a per-case message).
  The message is gc's fixed string after "fatal error: ", which the
  harness compares on both sides (`expected_status: fatal`). -/
  | fatal (message : String)
  deriving Repr, BEq, Inhabited

def GoError.status : GoError → String
  | .panic _ => "panic"
  | .unsupported _ => "unsupported"
  | .stuck _ => "stuck"
  | .internal _ => "error"
  | .fuelOut => "fuel-out"
  | .deadlock => "deadlock"
  | .raceDetected => "race"
  | .fatal _ => "fatal"

def GoError.message : GoError → String
  | .panic message => message
  | .unsupported feature => feature
  | .stuck message => message
  | .internal message => message
  | .fuelOut => "GoCore execution fuel exhausted"
  | .deadlock => "all goroutines are asleep - deadlock!"
  | .raceDetected => "data race detected"
  | .fatal message => message

structure Addr where
  id : Nat
  deriving Repr, BEq, DecidableEq

/-- Semantic type identity. The key is the canonical source-level type name.
It is constructed by frontend lowering, which strips frontend name mangling
in exactly one place and fails closed on collisions between distinct
declared types; raw frontend names must not be used as type identity. The
string representation is transitional pending a compact ID table. -/
structure TypeId where
  key : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The derived `BEq` is the field's (lawful) `String` equality; recording
lawfulness lets `simp` discharge `id == id` / `id != id` goals (needed by
the self-normalization soundness proofs, sem-adequacy slice 3). -/
instance : LawfulBEq TypeId where
  eq_of_beq {a b} h := by
    obtain ⟨k1⟩ := a
    obtain ⟨k2⟩ := b
    have hk : k1 == k2 := h
    simpa using hk
  rfl {a} := by
    obtain ⟨k⟩ := a
    show (k == k) = true
    simp

/-- Strip the LEADING package qualifier from a `TypeId` key, matching Go's
`reflect.Type.Name()` — the observation channel's naming contract
(`GoLean/CLI.lean`). Generic instantiation keys (`main.Pair[main.Inner]`,
generics slice 2026-08-05, design note §3.4) qualify their type ARGUMENTS
inside the brackets too, and `Name()` keeps those qualifiers
(`Pair[main.Inner]`) — so only the package segment BEFORE the first `[` is
stripped. The old `splitOn "." |>.getLast!` truncated such keys to
`"Inner]"`. For every pre-generics key (`main.T`, `struct{}`, `any`) the
behavior is unchanged. -/
def TypeId.unqualified (id : TypeId) : String :=
  -- The key prefix before any type-argument bracket; a `.` in it is the
  -- package qualifier (Go identifiers cannot contain `.` or `[`).
  let head := ((id.key.splitOn "[").headD id.key).splitOn "."
  match head with
  | [] => id.key
  | [_] => id.key
  | first :: _ => (id.key.drop (first.length + 1)).toString

namespace GoCore

/-- Go types. Lives here (not `Syntax.lean`) since the interfaces
campaign (S3, 2026-07-30) so `GoValue.interface` can carry its dynamic
type STRUCTURALLY — identity and typed operations on boxed values key on
canonical `Ty` equality (the Perennial `interface.mk_ok` design), never
on rendered name strings. Stays in the `GoCore` namespace (the golden
repr pins print `GoLean.GoCore.Ty.…`). -/
inductive Ty where
  | bool
  | int (kind : IntKind := IntKind.int)
  | float (kind : FloatKind)
  | string
  | array (length : Nat) (elem : Ty)
  | slice (elem : Ty)
  | map (key value : Ty)
  /-- A channel type `chan T` / `chan<- T` / `<-chan T` (channels arc
  slice 1, `docs/2026-08-06_channels-arc-design.md` D7). Direction is
  part of type identity; the runtime value (`GoValue.chan`) carries only
  the reference. -/
  | chan (dir : ChanDir) (elem : Ty)
  | pointer (elem : Ty)
  /-- A function type. Structural detail is carried for zero values,
  typing and TYPE IDENTITY (assert/boxing compare it structurally) —
  dispatch is by `FuncId`, never by this. `variadic` is the identity
  half spec#Type_identity adds beyond the param/result lists ("either
  both functions are variadic or neither is"): the variadic parameter's
  TYPE is `[]T` on both sides, so without the bit `func(...int)` and
  `func([]int)` are indistinguishable (BUG-067). -/
  | funcType (params results : List Ty) (variadic : Bool)
  | interface (id : TypeId)
  | defined (id : TypeId)
  | unsupported (feature : String)
  /-- A sync-package primitive type (`sync.Mutex` / `sync.RWMutex` /
  `sync.WaitGroup` / `sync.Once`; spec-parity slice 2, design note §3).
  Zero value = the zero primitive (`GoValue.syncData`). Appended at the
  END of the inductive so positional case tags stay stable. -/
  | sync (kind : GoCore.SyncKind)
  deriving Repr, Inhabited

/-- Fuel for structural `Ty` equality. Bounds COMBINED structural depth
and (for `funcType`) parameter-list length; the same 1024 budget the type
resolver uses (`typeResolutionFuel`, which lives downstream in `Ops.lean`
and so cannot be referenced here). -/
def tyEqFuel : Nat := 1024

/-! **Why `Ty` does NOT `deriving BEq`** (quorum pilot phase 4,
2026-07-31). `Ty` is a NESTED inductive (`funcType` carries `List Ty`), and
for nested inductives Lean's `deriving BEq` emits an **opaque** equality
function — no equation lemmas, no `unfold`, no `decide`, not even `rfl` on
two syntactically identical closed types. Dynamic-type identity is decided
by `==` on `Ty` (`concreteMethodForDynamic?`, `typeAssert`, boxing,
interface satisfaction), so with the derived instance **no dispatch fact
was kernel-provable at all** — every interface WP law would have had an
undischargeable premise. (It is also a `partial`-flavoured definition
sitting in the semantic core, which the "proof-facing code is total"
contract does not want.) The replacement is an ordinary total, transparent,
fuel-bounded structural equality that FAILS CLOSED (`false`) on exhaustion;
it agrees with the derived one on every type a program can write. -/
mutual

def Ty.eqbFuel : Nat → Ty → Ty → Bool
  | _, .bool, .bool => true
  | _, .int k₁, .int k₂ => k₁ == k₂
  | _, .float k₁, .float k₂ => k₁ == k₂
  | _, .string, .string => true
  | f + 1, .array n₁ e₁, .array n₂ e₂ => n₁ == n₂ && Ty.eqbFuel f e₁ e₂
  | f + 1, .slice e₁, .slice e₂ => Ty.eqbFuel f e₁ e₂
  | f + 1, .map k₁ v₁, .map k₂ v₂ => Ty.eqbFuel f k₁ k₂ && Ty.eqbFuel f v₁ v₂
  | f + 1, .chan d₁ e₁, .chan d₂ e₂ => d₁ == d₂ && Ty.eqbFuel f e₁ e₂
  | f + 1, .pointer e₁, .pointer e₂ => Ty.eqbFuel f e₁ e₂
  | f + 1, .funcType p₁ r₁ v₁, .funcType p₂ r₂ v₂ =>
      v₁ == v₂ && Ty.eqbListFuel f p₁ p₂ && Ty.eqbListFuel f r₁ r₂
  | _, .interface a, .interface b => a == b
  | _, .defined a, .defined b => a == b
  | _, .unsupported a, .unsupported b => a == b
  | _, .sync a, .sync b => a == b
  | _, _, _ => false

def Ty.eqbListFuel : Nat → List Ty → List Ty → Bool
  | _, [], [] => true
  | f + 1, a :: as, b :: bs => Ty.eqbFuel f a b && Ty.eqbListFuel f as bs
  | _, _, _ => false

end

/-- Structural `Ty` equality — the identity relation dispatch and type
asserts key on. -/
def Ty.eqb (a b : Ty) : Bool := Ty.eqbFuel tyEqFuel a b

instance : BEq Ty := ⟨Ty.eqb⟩

/-- Structural rendering of a (canonical) dynamic type for the
OBSERVATION channel only — identity never keys on this (S3). Named types
render UNQUALIFIED, like the struct `typeName` field beside them: the
observation channel's stated contract is `reflect.Type.Name()`, and the
qualified spelling contradicted it inside a single JSON object
(pre-merge audit 2026-07-31, finding 12). -/
def Ty.dynamicName : Ty → String
  | .bool => "bool"
  | .int kind => kind.name
  | .float kind => kind.name
  | .string => "string"
  | .defined id => id.unqualified
  | .interface id => id.unqualified
  | .pointer e => "*" ++ Ty.dynamicName e
  | .slice e => "[]" ++ Ty.dynamicName e
  | .array n e => s!"[{n}]" ++ Ty.dynamicName e
  | .map k v => s!"map[{Ty.dynamicName k}]{Ty.dynamicName v}"
  -- reflect renders direction exactly this way ("chan int",
  -- "<-chan int", "chan<- int").
  | .chan .both e => "chan " ++ Ty.dynamicName e
  | .chan .send e => "chan<- " ++ Ty.dynamicName e
  | .chan .recv e => "<-chan " ++ Ty.dynamicName e
  | .funcType _ _ _ => "func"
  | .unsupported f => s!"<unsupported {f}>"
  -- reflect.Type.Name() on sync.Mutex is "Mutex" (package-unqualified,
  -- the observation channel's contract).
  | .sync kind => kind.name

end GoCore

inductive Loc where
  | base (addr : Addr)
  | field (base : Loc) (typeId : TypeId) (fieldName : String)
  | index (base : Loc) (index : Int)
  deriving Repr, BEq, DecidableEq

/-- The derived `BEq Addr` is the field's `Nat` equality — lawful. Needed
so heap-key disequalities (`Heap.set` at a FRESH address leaves bounded
lookups unchanged) are provable (∀-choices kit, sem-adequacy slice 3). -/
instance : LawfulBEq Addr where
  eq_of_beq {a b} h := by
    obtain ⟨i⟩ := a
    obtain ⟨j⟩ := b
    have hij : i == j := h
    simpa using hij
  rfl {a} := by
    obtain ⟨i⟩ := a
    show (i == i) = true
    simp

/-- Lawfulness of the derived `BEq Loc` (componentwise from `Addr`/
`TypeId`/`String`/`Int`) — same motivation as `LawfulBEq Addr` above. -/
instance : LawfulBEq Loc where
  eq_of_beq {a b} h := by
    induction a generalizing b <;> cases b
    case base.base x y =>
      have hx : x == y := h
      simp [eq_of_beq hx]
    case field.field ba ta fa ih bb tb fb =>
      have h' : (ba == bb && (ta == tb && fa == fb)) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨h1, h2, h3⟩ := h'
      simp [ih h1, eq_of_beq h2, eq_of_beq h3]
    case index.index ba ia ih bb ib =>
      have h' : (ba == bb && ia == ib) = true := h
      simp only [Bool.and_eq_true] at h'
      obtain ⟨h1, h2⟩ := h'
      simp [ih h1, eq_of_beq h2]
    all_goals exact Bool.noConfusion (h : false = true)
  rfl {a} := by
    induction a
    case base x =>
      show (x == x) = true
      simp
    case field b t f ih =>
      show (b == b && (t == t && f == f)) = true
      simp [ih]
    case index b i ih =>
      show (b == b && i == i) = true
      simp [ih]

structure SliceValue where
  base : Option Loc
  offset : Nat
  len : Nat
  cap : Nat
  deriving Repr, BEq

structure MapValue where
  base : Option Loc
  deriving Repr, BEq

/-- A channel REFERENCE (channels arc slice 1, the `MapValue` precedent):
`base` addresses the `GoValue.chanData` heap cell; `none` is the nil
channel. Channel `==` is reference identity (spec: "equal if they were
created by the same call to `make` or if both have value `nil`") — the
derived `BEq` (base equality) IS that relation, which is also why
channels are valid map keys. Direction is NOT here: it is a static type
property (`Ty.chan`), and a directional conversion returns the same
reference. -/
structure ChanValue where
  base : Option Loc
  deriving Repr, BEq

/-- The runtime STATE of a sync-package primitive (spec-parity slice 2,
design note §§3-4). Sync structs are Go VALUES — probe p10: a copy of a
locked mutex carries the locked state and the runtime detects nothing —
so the state lives in the heap cell where the variable lives (no
reference cell, no registry), and struct copies copy it, exactly gc.
Every scalar here is state gc itself keeps in its state words:
`pendingW` (blocked write-lockers) realizes the DOCUMENTED
writer-exclusion of new readers (rwmutex.go: "a blocked Lock call
excludes new readers from acquiring the lock"); `waiters` (parked
Wait callers) mirrors gc's state-word wait count — reset by the
zeroing Add exactly as gc's `wg.state.Store(0)` (waitgroup.go:134-135;
its consumers are the wg-sema race pair's first-waiter condition and
the wake bookkeeping — the Add-side misuse panic gc guards with it is
unreachable at registry granularity and carries no arm here). NO waiter queues, no identities, no order — the
blocked goroutines themselves are `Config.blockedSync` shapes. -/
inductive SyncPrim where
  | mutex (locked : Bool)
  | rwmutex (writer : Bool) (readers : Nat) (pendingW : Nat)
  | waitGroup (counter : Int) (waiters : Nat)
  | once (started : Bool) (done : Bool)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The zero value of a sync kind ("The zero value for a Mutex is an
unlocked mutex" — and likewise for the other three). -/
def GoCore.SyncKind.zero : GoCore.SyncKind → SyncPrim
  | .mutex => .mutex false
  | .rwmutex => .rwmutex false 0 0
  | .waitGroup => .waitGroup 0 0
  | .once => .once false false

/-- The kind a primitive's state belongs to (the normalizer's
kind-compatibility check). -/
def SyncPrim.kind : SyncPrim → GoCore.SyncKind
  | .mutex _ => .mutex
  | .rwmutex _ _ _ => .rwmutex
  | .waitGroup _ _ => .waitGroup
  | .once _ _ => .once

structure GoString where
  bytes : Array UInt8
  deriving Repr, BEq

namespace GoString

def empty : GoString :=
  { bytes := #[] }

def fromLeanString (value : String) : GoString :=
  { bytes := value.toUTF8.data }

def replacementRune : GoString :=
  { bytes := #[0xef, 0xbf, 0xbd] }

def utf8Byte (value : Nat) : UInt8 :=
  UInt8.ofNat value

def fromCodePointNat (code : Nat) : GoString :=
  if code <= 0x7f then
    { bytes := #[utf8Byte code] }
  else if code <= 0x7ff then
    { bytes := #[
        utf8Byte (0xc0 + code / 0x40),
        utf8Byte (0x80 + code % 0x40)
      ] }
  else if code <= 0xffff then
    if 0xd800 <= code && code <= 0xdfff then
      replacementRune
    else
      { bytes := #[
          utf8Byte (0xe0 + code / 0x1000),
          utf8Byte (0x80 + (code / 0x40) % 0x40),
          utf8Byte (0x80 + code % 0x40)
        ] }
  else if code <= 0x10ffff then
    { bytes := #[
        utf8Byte (0xf0 + code / 0x40000),
        utf8Byte (0x80 + (code / 0x1000) % 0x40),
        utf8Byte (0x80 + (code / 0x40) % 0x40),
        utf8Byte (0x80 + code % 0x40)
      ] }
  else
    replacementRune

def fromCodePoint (code : Int) : GoString :=
  if code < 0 then
    replacementRune
  else
    fromCodePointNat code.toNat

def append (left right : GoString) : GoString :=
  { bytes := left.bytes ++ right.bytes }

def length (value : GoString) : Nat :=
  value.bytes.size

def byte? (value : GoString) (index : Nat) : Option UInt8 :=
  value.bytes[index]?

def slice (value : GoString) (low high : Nat) : GoString :=
  { bytes := value.bytes.extract low high }

def compareAt (left right : Array UInt8) (index : Nat) : Ordering :=
  match hl : left[index]?, right[index]? with
  | some l, some r =>
      if l.toNat < r.toNat then
        .lt
      else if r.toNat < l.toNat then
        .gt
      else
        have : index < left.size := (Array.getElem?_eq_some_iff.mp hl).1
        compareAt left right (index + 1)
  | none, some _ => .lt
  | some _, none => .gt
  | none, none => .eq
termination_by left.size - index

def compare (left right : GoString) : Ordering :=
  compareAt left.bytes right.bytes 0

def byteNats (value : GoString) : Array Nat :=
  value.bytes.map (fun b => b.toNat)

end GoString

inductive GoValue where
  | unit
  | bool (value : Bool)
  | int (value : Int) (kind : GoCore.IntKind := .int)
  /-- An IEEE-754 float as its BIT PATTERN (floats slice, design note
  decision 6): `bits < 2^kind.bits`, enforced by
  `FloatKind.normalizeBits` at every construction/normalization site.
  Semantics of the pattern live in `GoCore/FloatBits.lean`. NOTE the
  three equalities (note §4): Go `==` is `valueEq`'s IEEE arm
  (NaN ≠ NaN, +0 == -0); `GoValue.eqb` below is BIT equality
  (proof/infrastructure identity, never Go `==`). -/
  | float (bits : Nat) (kind : GoCore.FloatKind)
  | string (value : GoString)
  | addr (loc : Loc)
  | nil
  /-- An interface box: the CANONICAL dynamic type (aliases resolved at
  box time, defined-type identity kept — `canonicalDynamicTy`) plus the
  boxed value. Identity comparisons, type asserts, method dispatch, and
  equality-at-dynamic-type all key on `dynamic` structurally (interfaces
  campaign S3, 2026-07-30; was a rendered `String`). A nil interface is
  `GoValue.nil`, never a box. -/
  | interface (dynamic : GoCore.Ty) (value : GoValue)
  | struct (typeId : TypeId) (fields : Array (String × GoValue))
  | array (values : Array GoValue)
  | slice (value : SliceValue)
  | map (value : MapValue)
  | mapData (entries : Array (GoValue × GoValue))
  /-- A channel reference (channels arc slice 1; the `map` precedent). -/
  | chan (value : ChanValue)
  /-- A channel's heap-cell payload (the `mapData` precedent — a value no
  expression may produce): the buffered elements in FIFO order (spec:
  "Channels act as first-in-first-out queues" — deterministic, strict
  lane), the buffer capacity (`cap = 0` ⟺ unbuffered — ONE spec rule,
  not two channel kinds), and the closed flag. NO waiter queues (design
  of record D7): blocked goroutines are blocked-Config shapes, never
  channel state. -/
  | chanData (buf : Array GoValue) (capacity : Nat) (closed : Bool)
  /-- A **function value**: the callee's semantic identity plus the values
  captured at closure-creation time. Closures are lambda-lifted by the
  frontend (`docs/2026-07-24_sequential-coverage-scoping.md` §8), so the
  captured values are the ADDRESSES of the captured variables — Go captures
  by reference, and making that explicit here is what keeps two closures
  over one variable sharing it. Method values and (later) deferred calls use
  the same shape. The zero value of a func type is `nil`, not this. -/
  | funcVal (fid : GoCore.FuncId) (captured : List GoValue)
  /-- A sync-package primitive's state, living in the cell where the
  sync struct lives (spec-parity slice 2, design note §3 — the VALUE
  model: copies carry state, probe p10). Contains no locations. -/
  | syncData (p : SyncPrim)
  deriving Repr


/-! ## Structural `GoValue` equality (arc-final audit, 2026-08-04)

`GoValue` is a NESTED inductive (arrays/lists of itself), so `deriving
BEq` compiles to a `partial`-class OPAQUE stub — a constant whose LOGICAL
value is an arbitrary inhabitant (`fun _ _ => default`), even though its
COMPILED behavior is real structural equality. That is the worst shape
for this project: the differential validates the compiled function while
theorems quantify the logical one, and at any semantic use the two can
disagree (found at `renderPanicHead`'s recovered-collapse check; same
class `Ty.eqb` fixed for `Ty` in the interfaces campaign, whose recipe
this mirrors). The replacement is total, transparent, fuel-structural
(depth-only — the parameterized list helpers keep elements free, the
de-WF recipe), kernel-reducible, and FAILS CLOSED (`false`) on depth
exhaustion; it agrees with the derived instance's compiled behavior on
every value a program can build. -/

/-- Depth budget for structural value equality; nesting depth, never node
count (list helpers are parameterized). 1024 mirrors `typeResolutionFuel`
— no real Go value nests deeper. -/
def valueEqbFuel : Nat := 1024

/-- Pairwise equality over a list with the already-decremented element
comparator. -/
def GoValue.eqbListWith (f : GoValue → GoValue → Bool) :
    List GoValue → List GoValue → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && GoValue.eqbListWith f as bs
  | _, _ => false

/-- Pairwise equality over entry pairs. -/
def GoValue.eqbPairsWith (f : GoValue → GoValue → Bool) :
    List (GoValue × GoValue) → List (GoValue × GoValue) → Bool
  | [], [] => true
  | (k₁, v₁) :: as, (k₂, v₂) :: bs =>
      f k₁ k₂ && f v₁ v₂ && GoValue.eqbPairsWith f as bs
  | _, _ => false

/-- Pairwise equality over named fields. -/
def GoValue.eqbFieldsWith (f : GoValue → GoValue → Bool) :
    List (String × GoValue) → List (String × GoValue) → Bool
  | [], [] => true
  | (n₁, v₁) :: as, (n₂, v₂) :: bs =>
      n₁ == n₂ && f v₁ v₂ && GoValue.eqbFieldsWith f as bs
  | _, _ => false

def GoValue.eqbFuel : Nat → GoValue → GoValue → Bool
  | _, .unit, .unit => true
  | _, .bool a, .bool b => a == b
  | _, .int v₁ k₁, .int v₂ k₂ => v₁ == v₂ && k₁ == k₂
  -- BIT equality on purpose (note §4): NaN == NaN at identical bits,
  -- +0 ≠ -0 — structural identity, never Go's ==.
  | _, .float b₁ k₁, .float b₂ k₂ => b₁ == b₂ && k₁ == k₂
  | _, .string a, .string b => a == b
  | _, .addr a, .addr b => a == b
  | _, .nil, .nil => true
  | f + 1, .interface t₁ v₁, .interface t₂ v₂ =>
      GoCore.Ty.eqb t₁ t₂ && GoValue.eqbFuel f v₁ v₂
  | f + 1, .struct id₁ fs₁, .struct id₂ fs₂ =>
      id₁ == id₂ && GoValue.eqbFieldsWith (GoValue.eqbFuel f) fs₁.toList fs₂.toList
  | f + 1, .array a, .array b =>
      GoValue.eqbListWith (GoValue.eqbFuel f) a.toList b.toList
  | _, .slice a, .slice b => a == b
  | _, .map a, .map b => a == b
  | f + 1, .mapData a, .mapData b =>
      GoValue.eqbPairsWith (GoValue.eqbFuel f) a.toList b.toList
  | _, .chan a, .chan b => a == b
  | f + 1, .chanData b₁ c₁ k₁, .chanData b₂ c₂ k₂ =>
      c₁ == c₂ && k₁ == k₂ && GoValue.eqbListWith (GoValue.eqbFuel f) b₁.toList b₂.toList
  | f + 1, .funcVal id₁ c₁, .funcVal id₂ c₂ =>
      id₁ == id₂ && GoValue.eqbListWith (GoValue.eqbFuel f) c₁ c₂
  | _, .syncData a, .syncData b => a == b
  | _, _, _ => false

/-- Structural `GoValue` equality — THE `BEq GoValue` instance (replacing
the logically-opaque derived one). -/
def GoValue.eqb (a b : GoValue) : Bool := GoValue.eqbFuel valueEqbFuel a b

instance : BEq GoValue := ⟨GoValue.eqb⟩

namespace GoCore

abbrev Value := GoValue

end GoCore
end GoLean
