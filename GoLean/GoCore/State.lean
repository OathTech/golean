import GoLean.GoCore.Syntax
import GoLean.GoCore.Value

namespace GoLean.GoCore

open GoLean

abbrev LocalEnv := List (String × Loc)
abbrev Heap := List (Loc × GoValue)
abbrev TypeEnv := List (String × TypeDef)

structure ExecState where
  types : TypeEnv := []
  functions : Array Func := #[]
  locals : LocalEnv := []
  heap : Heap := []
  nextAddr : Nat := 0
  deriving Repr, BEq

structure Result where
  values : Array GoValue
  deriving Repr, BEq

inductive ExecOutcome where
  | normal (state : ExecState)
  | returned (state : ExecState)
  | broke (state : ExecState)
  | continued (state : ExecState)
  deriving Repr, BEq

def ExecOutcome.state : ExecOutcome → ExecState
  | .normal state => state
  | .returned state => state
  | .broke state => state
  | .continued state => state

def LocalEnv.lookup : LocalEnv → String → Option Loc
  | [], _ => none
  | (name, loc) :: rest, needle =>
      if name == needle then some loc else LocalEnv.lookup rest needle

def LocalEnv.set : LocalEnv → String → Loc → LocalEnv
  | [], name, loc => [(name, loc)]
  | (name, old) :: rest, needle, loc =>
      if name == needle then
        (name, loc) :: rest
      else
        (name, old) :: LocalEnv.set rest needle loc

def Heap.lookup : Heap → Loc → Option GoValue
  | [], _ => none
  | (loc, value) :: rest, needle =>
      if loc == needle then some value else Heap.lookup rest needle

def Heap.set : Heap → Loc → GoValue → Heap
  | [], loc, value => [(loc, value)]
  | (loc, old) :: rest, needle, value =>
      if loc == needle then
        (loc, value) :: rest
      else
        (loc, old) :: Heap.set rest needle value

def TypeEnv.lookup : TypeEnv → String → Option TypeDef
  | [], _ => none
  | (name, defn) :: rest, needle =>
      if name == needle then some defn else TypeEnv.lookup rest needle

def StructFields.lookup : Array (String × GoValue) → String → Option GoValue
  | fields, needle =>
      fields.foldl
        (fun found (name, value) =>
          match found with
          | some value => some value
          | none => if name == needle then some value else none)
        none

def StructFields.set (fields : Array (String × GoValue)) (needle : String)
    (value : GoValue) : Except GoError (Array (String × GoValue)) := do
  let mut out := #[]
  let mut found := false
  for (name, old) in fields do
    if name == needle then
      out := out.push (name, value)
      found := true
    else
      out := out.push (name, old)
  if found then
    return out
  else
    throw (.stuck s!"unknown GoCore struct field: {needle}")

def ExecState.freshLoc (state : ExecState) : Loc × ExecState :=
  let loc := Loc.base { id := state.nextAddr }
  (loc, { state with nextAddr := state.nextAddr + 1 })

def ExecState.bindLocal (state : ExecState) (name : String) (value : GoValue) :
    ExecState :=
  match LocalEnv.lookup state.locals name with
  | some loc =>
      { state with heap := Heap.set state.heap loc value }
  | none =>
      let (loc, state) := state.freshLoc
      { state with
        locals := LocalEnv.set state.locals name loc,
        heap := Heap.set state.heap loc value
      }

def ExecState.alloc (state : ExecState) (value : GoValue) : Loc × ExecState :=
  let (loc, state) := state.freshLoc
  (loc, { state with heap := Heap.set state.heap loc value })

def unsupported {α : Type} (feature : String) : Except GoError α :=
  throw (.unsupported feature)

def panic {α : Type} (message : String) : Except GoError α :=
  throw (.panic message)

def stuck {α : Type} (message : String) : Except GoError α :=
  throw (.stuck message)

def lookupLoc (state : ExecState) (name : String) : Except GoError Loc :=
  match LocalEnv.lookup state.locals name with
  | some loc => return loc
  | none => stuck s!"unbound GoCore variable address: {name}"
