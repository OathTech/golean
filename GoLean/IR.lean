import GoLean.Runtime

namespace GoLean.GoCore

open GoLean

inductive Ty where
  | bool
  | int
  | pointer (elem : Ty)
  | defined (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Param where
  id : String
  typ : Ty
  deriving Repr, BEq

inductive Assignee where
  | var (id : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Expr where
  | var (id : String)
  | intLit (value : Int)
  | boolLit (value : Bool)
  | add (left right : Expr)
  | mul (left right : Expr)
  | eqCmp (left right : Expr)
  | atMostCmp (left right : Expr)
  | atLeastCmp (left right : Expr)
  | lessCmp (left right : Expr)
  | ref (id : String)
  | old (operand : Expr)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Assertion where
  | expr (expr : Expr)
  | sepAnd (left right : Assertion)
  | implication (left right : Assertion)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

inductive Stmt where
  | seqn (stmts : Array Stmt)
  | block (decls : Array Param) (stmts : Array Stmt)
  | initialization (var : Param)
  | assign (left : Assignee) (right : Expr)
  | assert (assertion : Assertion)
  | while (cond : Expr) (body : Stmt)
  | label (name : String)
  | unsupported (feature : String)
  deriving Repr, BEq, Inhabited

structure Func where
  name : String
  args : Array Param
  results : Array Param
  pres : Array Assertion
  posts : Array Assertion
  body : Stmt
  deriving Repr, BEq

structure Program where
  funcs : Array Func
  deriving Repr, BEq

abbrev Env := List (String × GoValue)
abbrev RefEnv := List (String × Addr)

structure ExecState where
  values : Env := []
  refs : RefEnv := []
  nextAddr : Nat := 0
  deriving Repr, BEq

structure Result where
  values : Array GoValue
  deriving Repr, BEq

private def Env.lookup : Env → String → Option GoValue
  | [], _ => none
  | (name, value) :: rest, needle =>
      if name == needle then some value else Env.lookup rest needle

private def Env.set : Env → String → GoValue → Env
  | [], name, value => [(name, value)]
  | (name, old) :: rest, needle, value =>
      if name == needle then
        (name, value) :: rest
      else
        (name, old) :: Env.set rest needle value

private def RefEnv.lookup : RefEnv → String → Option Addr
  | [], _ => none
  | (name, addr) :: rest, needle =>
      if name == needle then some addr else RefEnv.lookup rest needle

private def ExecState.ensureRef (state : ExecState) (name : String) : ExecState :=
  match RefEnv.lookup state.refs name with
  | some _ => state
  | none =>
      { state with
        refs := (name, { id := state.nextAddr }) :: state.refs,
        nextAddr := state.nextAddr + 1
      }

private def ExecState.setValue (state : ExecState) (name : String) (value : GoValue) :
    ExecState :=
  let state := state.ensureRef name
  { state with values := Env.set state.values name value }

private def unsupported {α : Type} (feature : String) : Except String α :=
  throw s!"unsupported GoCore execution feature: {feature}"

private def lookup (state : ExecState) (name : String) : Except String GoValue :=
  match Env.lookup state.values name with
  | some value => return value
  | none => throw s!"unbound GoCore variable: {name}"

private def lookupRef (state : ExecState) (name : String) : Except String Addr :=
  match RefEnv.lookup state.refs name with
  | some addr => return addr
  | none => throw s!"unbound GoCore variable address: {name}"

private def defaultValue : Ty → Except String GoValue
  | .bool => return .bool false
  | .int => return .int 0
  | .pointer _ => return .nil
  | .defined name => unsupported s!"default value for defined type {name}"
  | .unsupported feature => unsupported s!"default value for {feature}"

private def valueAsInt : GoValue → Except String Int
  | .int value => return value
  | other => throw s!"expected int value, got {repr other}"

private def valueAsBool : GoValue → Except String Bool
  | .bool value => return value
  | other => throw s!"expected bool value, got {repr other}"

mutual
  partial def evalExpr (state : ExecState) : Expr → Except String GoValue
    | .var id => lookup state id
    | .intLit value => return .int value
    | .boolLit value => return .bool value
    | .add left right => do
        return .int ((← valueAsInt (← evalExpr state left)) + (← valueAsInt (← evalExpr state right)))
    | .mul left right => do
        return .int ((← valueAsInt (← evalExpr state left)) * (← valueAsInt (← evalExpr state right)))
    | .eqCmp left right => do
        let leftValue ← evalExpr state left
        let rightValue ← evalExpr state right
        return .bool (leftValue == rightValue)
    | .atMostCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) <= (← valueAsInt (← evalExpr state right)))
    | .atLeastCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) >= (← valueAsInt (← evalExpr state right)))
    | .lessCmp left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) < (← valueAsInt (← evalExpr state right)))
    | .ref id => return .addr (← lookupRef state id)
    | .old operand => evalExpr state operand
    | .unsupported feature => unsupported feature

  partial def evalAssertion (state : ExecState) : Assertion → Except String Bool
    | .expr expr => do
        valueAsBool (← evalExpr state expr)
    | .sepAnd left right => do
        return (← evalAssertion state left) && (← evalAssertion state right)
    | .implication left right => do
        if ← evalAssertion state left then
          evalAssertion state right
        else
          return true
    | .unsupported feature => unsupported feature

  partial def assignAssignee (state : ExecState) (assignee : Assignee) (value : GoValue) :
      Except String ExecState :=
    match assignee with
    | .var id => return state.setValue id value
    | .unsupported feature => unsupported feature

  partial def execDecl (state : ExecState) (param : Param) : Except String ExecState := do
    return state.setValue param.id (← defaultValue param.typ)

  partial def execDecls (state : ExecState) (decls : Array Param) : Except String ExecState := do
    let mut state := state
    for decl in decls do
      state ← execDecl state decl
    return state

  partial def execStmts (fuel : Nat) (state : ExecState) (stmts : Array Stmt) :
      Except String ExecState := do
    let mut state := state
    for stmt in stmts do
      state ← execStmt fuel state stmt
    return state

  partial def execStmt (fuel : Nat) (state : ExecState) : Stmt → Except String ExecState
    | .seqn stmts => execStmts fuel state stmts
    | .block decls stmts => do
        execStmts fuel (← execDecls state decls) stmts
    | .initialization var => execDecl state var
    | .assign left right => do
        assignAssignee state left (← evalExpr state right)
    | .assert assertion => do
        if ← evalAssertion state assertion then
          return state
        else
          throw "GoCore assertion failed"
    | .while cond body => do
        if fuel == 0 then
          throw "GoCore execution fuel exhausted"
        if ← valueAsBool (← evalExpr state cond) then
          execStmt (fuel - 1) (← execStmt fuel state body) (.while cond body)
        else
          return state
    | .label _ => return state
    | .unsupported feature => unsupported feature
end

private def checkAssertions (state : ExecState) (kind : String) (assertions : Array Assertion) :
    Except String Unit := do
  for assertion in assertions do
    if ← evalAssertion state assertion then
      pure ()
    else
      throw s!"GoCore {kind} failed"

private def bindParams (state : ExecState) (params : Array Param) (args : Array GoValue) :
    Except String ExecState := do
  if params.size != args.size then
    throw s!"expected {params.size} argument(s), got {args.size}"
  let mut state := state
  let mut i := 0
  for param in params do
    match args[i]? with
    | some value =>
        state := state.setValue param.id value
        i := i + 1
    | none => throw s!"missing argument {i}"
  return state

private def initResults (state : ExecState) (results : Array Param) : Except String ExecState := do
  let mut state := state
  for result in results do
    state := state.setValue result.id (← defaultValue result.typ)
  return state

private def collectResults (state : ExecState) (results : Array Param) :
    Except String (Array GoValue) := do
  let mut values := #[]
  for result in results do
    values := values.push (← lookup state result.id)
  return values

def runFunction (fuel : Nat) (func : Func) (args : Array GoValue) : Except String Result := do
  let state ← bindParams {} func.args args
  let state ← initResults state func.results
  checkAssertions state "precondition" func.pres
  let state ← execStmt fuel state func.body
  checkAssertions state "postcondition" func.posts
  return { values := (← collectResults state func.results) }

def findFunction? (program : Program) (name : String) : Option Func :=
  program.funcs.foldl
    (fun found func =>
      match found with
      | some f => some f
      | none => if func.name == name then some func else none)
    none

def runNamedFunction (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) :
    Except String Result := do
  let func ←
    match findFunction? program name with
    | some func => pure func
    | none => throw s!"GoCore function not found: {name}"
  runFunction fuel func args

def runNamedFunctionInts (fuel : Nat) (program : Program) (name : String) (args : Array Int) :
    Except String Result :=
  runNamedFunction fuel program name (args.map GoValue.int)

end GoLean.GoCore
