namespace GoLean

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

inductive GoValue where
  | unit
  | bool (value : Bool)
  | int (value : Int)
  | addr (loc : Loc)
  | nil
  | struct (typeName : String) (fields : Array (String × GoValue))
  | array (values : Array GoValue)
  deriving Repr, BEq

structure GoState where
  nextAddr : Nat := 0
  deriving Repr

abbrev GoM (α : Type) := EStateM GoError GoState α

def unsupported {α : Type} (feature : String) : GoM α :=
  throw (.unsupported feature)

end GoLean
