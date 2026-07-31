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
  deriving Repr, BEq, Inhabited

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
  deriving Repr, BEq, Inhabited

def GoError.status : GoError → String
  | .panic _ => "panic"
  | .unsupported _ => "unsupported"
  | .stuck _ => "stuck"
  | .internal _ => "error"

def GoError.message : GoError → String
  | .panic message => message
  | .unsupported feature => feature
  | .stuck message => message
  | .internal message => message

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

/-- Strip the package qualifier from a `TypeId` key, matching Go's
`reflect.Type.Name()` — the observation channel's naming contract
(`GoLean/CLI.lean`). -/
def TypeId.unqualified (id : TypeId) : String :=
  match id.key.splitOn "." with
  | [] => id.key
  | parts => parts.getLast!

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
  | string
  | array (length : Nat) (elem : Ty)
  | slice (elem : Ty)
  | map (key value : Ty)
  | pointer (elem : Ty)
  /-- A function type. Structural detail is carried for zero values and
  typing only — dispatch is by `FuncId`, never by this. -/
  | funcType (params results : List Ty)
  | interface (id : TypeId)
  | defined (id : TypeId)
  | unsupported (feature : String)
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
  | _, .string, .string => true
  | f + 1, .array n₁ e₁, .array n₂ e₂ => n₁ == n₂ && Ty.eqbFuel f e₁ e₂
  | f + 1, .slice e₁, .slice e₂ => Ty.eqbFuel f e₁ e₂
  | f + 1, .map k₁ v₁, .map k₂ v₂ => Ty.eqbFuel f k₁ k₂ && Ty.eqbFuel f v₁ v₂
  | f + 1, .pointer e₁, .pointer e₂ => Ty.eqbFuel f e₁ e₂
  | f + 1, .funcType p₁ r₁, .funcType p₂ r₂ =>
      Ty.eqbListFuel f p₁ p₂ && Ty.eqbListFuel f r₁ r₂
  | _, .interface a, .interface b => a == b
  | _, .defined a, .defined b => a == b
  | _, .unsupported a, .unsupported b => a == b
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
  | .string => "string"
  | .defined id => id.unqualified
  | .interface id => id.unqualified
  | .pointer e => "*" ++ Ty.dynamicName e
  | .slice e => "[]" ++ Ty.dynamicName e
  | .array n e => s!"[{n}]" ++ Ty.dynamicName e
  | .map k v => s!"map[{Ty.dynamicName k}]{Ty.dynamicName v}"
  | .funcType _ _ => "func"
  | .unsupported f => s!"<unsupported {f}>"

end GoCore

inductive Loc where
  | base (addr : Addr)
  | field (base : Loc) (typeId : TypeId) (fieldName : String)
  | index (base : Loc) (index : Int)
  deriving Repr, BEq, DecidableEq

structure SliceValue where
  base : Option Loc
  offset : Nat
  len : Nat
  cap : Nat
  deriving Repr, BEq

structure MapValue where
  base : Option Loc
  deriving Repr, BEq

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
  /-- A **function value**: the callee's semantic identity plus the values
  captured at closure-creation time. Closures are lambda-lifted by the
  frontend (`docs/2026-07-24_sequential-coverage-scoping.md` §8), so the
  captured values are the ADDRESSES of the captured variables — Go captures
  by reference, and making that explicit here is what keeps two closures
  over one variable sharing it. Method values and (later) deferred calls use
  the same shape. The zero value of a func type is `nil`, not this. -/
  | funcVal (fid : GoCore.FuncId) (captured : List GoValue)
  deriving Repr, BEq

namespace GoCore

abbrev Value := GoValue

end GoCore
end GoLean
