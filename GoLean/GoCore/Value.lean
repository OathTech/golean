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

inductive Loc where
  | base (addr : Addr)
  | field (base : Loc) (typeName fieldName : String)
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

def append (left right : GoString) : GoString :=
  { bytes := left.bytes ++ right.bytes }

def length (value : GoString) : Nat :=
  value.bytes.size

def byte? (value : GoString) (index : Nat) : Option UInt8 :=
  value.bytes[index]?

def slice (value : GoString) (low high : Nat) : GoString :=
  { bytes := value.bytes.extract low high }

partial def compareAt (left right : Array UInt8) (index : Nat) : Ordering :=
  match left[index]?, right[index]? with
  | some l, some r =>
      if l.toNat < r.toNat then
        .lt
      else if r.toNat < l.toNat then
        .gt
      else
        compareAt left right (index + 1)
  | none, some _ => .lt
  | some _, none => .gt
  | none, none => .eq

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
  | struct (typeName : String) (fields : Array (String × GoValue))
  | array (values : Array GoValue)
  | slice (value : SliceValue)
  | map (value : MapValue)
  | mapData (entries : Array (GoValue × GoValue))
  deriving Repr, BEq

namespace GoCore

abbrev Value := GoValue

end GoCore
end GoLean
