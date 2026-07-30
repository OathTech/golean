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
  deriving Repr, BEq, Inhabited

/-- Structural rendering of a (canonical) dynamic type for the
OBSERVATION channel only — identity never keys on this (S3). -/
def Ty.dynamicName : Ty → String
  | .bool => "bool"
  | .int kind => kind.name
  | .string => "string"
  | .defined id => id.key
  | .interface id => id.key
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
