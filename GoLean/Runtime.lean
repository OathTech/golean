namespace GoLean

inductive GoError where
  | panic (message : String)
  | unsupported (feature : String)
  | stuck (message : String)
  deriving Repr, BEq

structure Addr where
  id : Nat
  deriving Repr, BEq, DecidableEq

inductive GoValue where
  | unit
  | bool (value : Bool)
  | int (value : Int)
  | addr (addr : Addr)
  | nil
  deriving Repr, BEq

structure GoState where
  nextAddr : Nat := 0
  deriving Repr

abbrev GoM (α : Type) := EStateM GoError GoState α

def unsupported {α : Type} (feature : String) : GoM α :=
  throw (.unsupported feature)

end GoLean
