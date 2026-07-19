import GoLean.GoCore.Syntax
import GoLean.GoCore.Value

namespace GoLean.GoCore

open GoLean

/-- One lexical scope: bindings from local names to heap-backed locations,
innermost binding first. -/
abbrev Scope := List (String × Loc)

/-- Lexical scope stack, innermost scope first. Name lookup walks scopes
inner to outer; declaration always creates a fresh binding in the innermost
scope, so shadowing gets a fresh location instead of reusing the outer one.
Block execution pushes a scope on entry and pops it on every exit path. -/
abbrev LocalEnv := List Scope

/-- A heap cell records the value and, when known at allocation, the declared
type of the allocation. Stores to a typed cell are normalized against the
declared type; untyped cells (legacy allocation paths, tracked for closure in
the semantics upgrade) fall back to value-shape coercion. -/
structure HeapCell where
  declaredTy : Option Ty := none
  value : GoValue
  deriving Repr, BEq

abbrev Heap := List (Loc × HeapCell)
abbrev TypeEnv := List (TypeId × TypeDef)

structure ExecState where
  types : TypeEnv := []
  functions : Array Func := #[]
  methods : Array MethodInfo := #[]
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

def Scope.lookup : Scope → String → Option Loc
  | [], _ => none
  | (name, loc) :: rest, needle =>
      if name == needle then some loc else Scope.lookup rest needle

def LocalEnv.lookup : LocalEnv → String → Option Loc
  | [], _ => none
  | scope :: outer, needle =>
      match Scope.lookup scope needle with
      | some loc => some loc
      | none => LocalEnv.lookup outer needle

/-- Bind a name in the innermost scope. An empty environment is treated as a
single empty scope so frame setup can start from `[]`. -/
def LocalEnv.declare : LocalEnv → String → Loc → LocalEnv
  | [], name, loc => [[(name, loc)]]
  | scope :: outer, name, loc => ((name, loc) :: scope) :: outer

def LocalEnv.pushScope (env : LocalEnv) : LocalEnv :=
  [] :: env

def LocalEnv.popScope : LocalEnv → LocalEnv
  | [] => []
  | _ :: outer => outer

def Heap.lookup : Heap → Loc → Option HeapCell
  | [], _ => none
  | (loc, cell) :: rest, needle =>
      if loc == needle then some cell else Heap.lookup rest needle

def Heap.set : Heap → Loc → HeapCell → Heap
  | [], loc, cell => [(loc, cell)]
  | (loc, old) :: rest, needle, cell =>
      if loc == needle then
        (loc, cell) :: rest
      else
        (loc, old) :: Heap.set rest needle cell

def TypeEnv.lookup : TypeEnv → TypeId → Option TypeDef
  | [], _ => none
  | (id, defn) :: rest, needle =>
      if id == needle then some defn else TypeEnv.lookup rest needle

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

/-- The nondeterminism choice stream ("parser of randomness"): each
nondeterministic point (map iteration order, append capacity) consumes the next
choice. It is threaded by the interpreter **external to `ExecState`**, so the
relation and the interpreter/relation correspondence compare oracle-free states.
GoCore never commits to determinism Go lacks; the interpreter only picks a
behavior by instantiating this oracle, a testing convenience — see
`docs/nondeterminism-design.md` and
`docs/2026-07-19_reshape-b-oracle-externalization.md`. -/
abbrev Choices := List Nat

/-- Consume the next nondeterministic choice from the external stream, bounded by
the number of alternatives at this point. Exhaustion yields 0 (the canonical
default). This is the sole way the interpreter resolves nondeterminism. -/
def Choices.consume (choices : Choices) (bound : Nat) : Nat × Choices :=
  let b := max 1 bound
  match choices with
  | [] => (0, choices)
  | c :: rest => (c % b, rest)

def ExecState.freshLoc (state : ExecState) : Loc × ExecState :=
  let loc := Loc.base { id := state.nextAddr }
  (loc, { state with nextAddr := state.nextAddr + 1 })

/-- Declare a local: always a fresh location in the innermost scope, even
when the name shadows an outer binding. Assignment to an existing local goes
through `lookupLoc`/`storeLoc`, never through this. -/
def ExecState.declareLocal (state : ExecState) (name : String) (typ : Option Ty)
    (value : GoValue) : ExecState :=
  let (loc, state) := state.freshLoc
  { state with
    locals := LocalEnv.declare state.locals name loc,
    heap := Heap.set state.heap loc { declaredTy := typ, value }
  }

def ExecState.alloc (state : ExecState) (value : GoValue) (typ : Option Ty := none) :
    Loc × ExecState :=
  let (loc, state) := state.freshLoc
  (loc, { state with heap := Heap.set state.heap loc { declaredTy := typ, value } })

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
