import GoLean.GobraJson
import GoLean.Runtime

namespace GoLean.GobraEval

open GoLean

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
  throw s!"unsupported Gobra execution feature: {feature}"

private def lookup (state : ExecState) (name : String) : Except String GoValue :=
  match Env.lookup state.values name with
  | some value => return value
  | none => throw s!"unbound Gobra variable: {name}"

private def lookupRef (state : ExecState) (name : String) : Except String Addr :=
  match RefEnv.lookup state.refs name with
  | some addr => return addr
  | none => throw s!"unbound Gobra variable address: {name}"

private def defaultValue : GobraJson.Ty → Except String GoValue
  | .bool _ => return .bool false
  | .int _ _ => return .int 0
  | .pointer _ _ => return .nil
  | ty => unsupported s!"default value for type {repr ty}"

private def varRefId : GobraJson.VarRef → String
  | .local var => var.id
  | .inParam param => param.id
  | .outParam param => param.id

private def valueAsInt : GoValue → Except String Int
  | .int value => return value
  | other => throw s!"expected int value, got {repr other}"

private def valueAsBool : GoValue → Except String Bool
  | .bool value => return value
  | other => throw s!"expected bool value, got {repr other}"

mutual
  partial def evalExpr (state : ExecState) : GobraJson.Expr → Except String GoValue
    | .var ref => lookup state (varRefId ref)
    | .intLit _ value _ _ => return .int value
    | .boolLit _ value => return .bool value
    | .add _ left right => do
        return .int ((← valueAsInt (← evalExpr state left)) + (← valueAsInt (← evalExpr state right)))
    | .mul _ left right => do
        return .int ((← valueAsInt (← evalExpr state left)) * (← valueAsInt (← evalExpr state right)))
    | .eqCmp _ left right => do
        let leftValue ← evalExpr state left
        let rightValue ← evalExpr state right
        return .bool (leftValue == rightValue)
    | .atMostCmp _ left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) <= (← valueAsInt (← evalExpr state right)))
    | .atLeastCmp _ left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) >= (← valueAsInt (← evalExpr state right)))
    | .lessCmp _ left right => do
        return .bool ((← valueAsInt (← evalExpr state left)) < (← valueAsInt (← evalExpr state right)))
    | .old _ operand => evalExpr state operand
    | .ref _ assignee _ =>
        match assignee with
        | .var _ ref => return .addr (← lookupRef state (varRefId ref))
        | .field .. => unsupported "reference to field"
    | .deref .. => unsupported "deref expression"
    | .fieldRef .. => unsupported "field reference expression"
    | .address .. => unsupported "address expression"
    | .structLit .. => unsupported "struct literal expression"
    | .pureMethodCall .. => unsupported "pure method call expression"
    | .mPredicateAccess .. => unsupported "method predicate access expression"
    | .predicate .. => unsupported "predicate expression"

  partial def evalAssertion (state : ExecState) : GobraJson.Assertion → Except String Bool
    | .expr expr => do
        valueAsBool (← evalExpr state expr)
    | .exprAssertion _ expr => do
        valueAsBool (← evalExpr state expr)
    | .sepAnd _ left right => do
        return (← evalAssertion state left) && (← evalAssertion state right)
    | .implication _ left right => do
        if ← evalAssertion state left then
          evalAssertion state right
        else
          return true
    | .access .. => unsupported "access assertion"

  partial def assignAssignee (state : ExecState) (assignee : GobraJson.Assignee) (value : GoValue) :
      Except String ExecState :=
    match assignee with
    | .var _ ref => return state.setValue (varRefId ref) value
    | .field .. => unsupported "field assignment"

  partial def execDecl (state : ExecState) : GobraJson.Decl → Except String ExecState
    | .local var => do
        return state.setValue var.id (← defaultValue var.typ)
    | .label _ => return state

  partial def execDecls (state : ExecState) (decls : Array GobraJson.Decl) :
      Except String ExecState := do
    let mut state := state
    for decl in decls do
      state ← execDecl state decl
    return state

  partial def execStmts (fuel : Nat) (state : ExecState) (stmts : Array GobraJson.Stmt) :
      Except String ExecState := do
    let mut state := state
    for stmt in stmts do
      state ← execStmt fuel state stmt
    return state

  partial def execStmt (fuel : Nat) (state : ExecState) : GobraJson.Stmt → Except String ExecState
    | .seqn _ stmts => execStmts fuel state stmts
    | .block _ decls stmts => do
        execStmts fuel (← execDecls state decls) stmts
    | .initialization _ var => return state.setValue var.id (← defaultValue var.typ)
    | .singleAss _ left right => do
        assignAssignee state left (← evalExpr state right)
    | .assert _ assertion => do
        if ← evalAssertion state assertion then
          return state
        else
          throw "Gobra assertion failed"
    | .while _ cond _invs _terminationMeasure body => do
        if fuel == 0 then
          throw "Gobra execution fuel exhausted"
        if ← valueAsBool (← evalExpr state cond) then
          execStmt (fuel - 1) (← execStmt fuel state body) (.while .internal cond #[] none body)
        else
          return state
    | .label _ _ => return state
    | .functionCall .. => unsupported "function call statement"
    | .methodCall .. => unsupported "method call statement"
end

private def execMethodBody (fuel : Nat) (state : ExecState) (body : GobraJson.MethodBody) :
    Except String ExecState := do
  let state ← execDecls state body.decls
  let state ← execStmts fuel state body.seqn.stmts
  execStmts fuel state body.postprocessing

private def checkAssertions (state : ExecState) (kind : String) (assertions : Array GobraJson.Assertion) :
    Except String Unit := do
  for assertion in assertions do
    if ← evalAssertion state assertion then
      pure ()
    else
      throw s!"Gobra {kind} failed"

private def bindParams (state : ExecState) (params : Array GobraJson.Parameter) (args : Array GoValue) :
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

private def initResults (state : ExecState) (results : Array GobraJson.Parameter) :
    Except String ExecState := do
  let mut state := state
  for result in results do
    state := state.setValue result.id (← defaultValue result.typ)
  return state

private def collectResults (state : ExecState) (results : Array GobraJson.Parameter) :
    Except String (Array GoValue) := do
  let mut values := #[]
  for result in results do
    values := values.push (← lookup state result.id)
  return values

def runFunctionMember (fuel : Nat) (member : GobraJson.FunctionMember) (args : Array GoValue) :
    Except String Result := do
  let body : GobraJson.MethodBody ←
    match member.body with
    | some body => pure body
    | none => unsupported s!"bodyless function {member.name.name}"
  let state ← bindParams {} member.args args
  let state ← initResults state member.results
  checkAssertions state "precondition" member.pres
  let state ← execMethodBody fuel state body
  checkAssertions state "postcondition" member.posts
  return { values := (← collectResults state member.results) }

private def findFunction? (program : GobraJson.Program) (name : String) :
    Option GobraJson.FunctionMember :=
  program.members.foldl
    (fun found member =>
      match found, member with
      | some f, _ => some f
      | none, .function f => if f.name.name == name then some f else none
      | none, _ => none)
    none

def runFunction (fuel : Nat) (doc : GobraJson.Document) (name : String) (args : Array GoValue) :
    Except String Result := do
  let member : GobraJson.FunctionMember ←
    match findFunction? doc.program name with
    | some member => pure member
    | none => throw s!"Gobra function not found: {name}"
  runFunctionMember fuel member args

def runFunctionInts (fuel : Nat) (doc : GobraJson.Document) (name : String) (args : Array Int) :
    Except String Result :=
  runFunction fuel doc name (args.map GoValue.int)

end GoLean.GobraEval
