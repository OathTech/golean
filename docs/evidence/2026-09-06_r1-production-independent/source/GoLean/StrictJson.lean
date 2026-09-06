import Lean.Data.Json

namespace GoLean.StrictJson

open Lean

abbrev Obj := Std.TreeMap.Raw String Json compare

def keys (obj : Obj) : List String :=
  obj.keys

def exactKeys (obj : Obj) (expected : List String) : Bool :=
  obj.size == expected.length && expected.all (fun key => obj.contains key)

def requireExactKeys (path : String) (obj : Obj) (expected : List String) : Except String Unit := do
  if exactKeys obj expected then
    pure ()
  else
    throw s!"{path}: expected exactly keys {repr expected}, got {repr (keys obj)}"

def obj (path : String) (json : Json) : Except String Obj :=
  match json.getObj? with
  | .ok value => .ok value
  | .error err => .error s!"{path}: {err}"

def field (path : String) (obj : Obj) (key : String) : Except String Json :=
  match obj.get? key with
  | some value => .ok value
  | none => .error s!"{path}: missing field '{key}'"

def string (path : String) (json : Json) : Except String String :=
  match json.getStr? with
  | .ok value => .ok value
  | .error err => .error s!"{path}: {err}"

def bool (path : String) (json : Json) : Except String Bool :=
  match json.getBool? with
  | .ok value => .ok value
  | .error err => .error s!"{path}: {err}"

def int (path : String) (json : Json) : Except String Int :=
  match json.getInt? with
  | .ok value => .ok value
  | .error err => .error s!"{path}: {err}"

def nat (path : String) (json : Json) : Except String Nat :=
  match json.getNat? with
  | .ok value => .ok value
  | .error err => .error s!"{path}: {err}"

def array (path : String) (json : Json) : Except String (Array Json) :=
  match json.getArr? with
  | .ok value => .ok value
  | .error err => .error s!"{path}: {err}"

def mapArrayIdx {α β : Type} (xs : Array α) (f : Nat → α → Except String β) :
    Except String (Array β) := do
  let mut out := #[]
  let mut i := 0
  for x in xs do
    out := out.push (← f i x)
    i := i + 1
  return out

end GoLean.StrictJson
