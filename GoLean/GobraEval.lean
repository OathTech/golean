import GoLean.GobraJson
import GoLean.Runtime

namespace GoLean.GobraEval

open GoLean

abbrev Env := List (String × GoValue)

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

private def unsupported {α : Type} (feature : String) : Except String α :=
  throw s!"unsupported Gobra execution feature: {feature}"

private def lookup (env : Env) (name : String) : Except String GoValue :=
  match Env.lookup env name with
  | some value => return value
  | none => throw s!"unbound Gobra variable: {name}"

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
  partial def evalExpr (env : Env) : GobraJson.Expr → Except String GoValue
    | .var ref => lookup env (varRefId ref)
    | .intLit _ value _ _ => return .int value
    | .boolLit _ value => return .bool value
    | .add _ left right => do
        return .int ((← valueAsInt (← evalExpr env left)) + (← valueAsInt (← evalExpr env right)))
    | .mul _ left right => do
        return .int ((← valueAsInt (← evalExpr env left)) * (← valueAsInt (← evalExpr env right)))
    | .eqCmp _ left right => do
        let leftValue ← evalExpr env left
        let rightValue ← evalExpr env right
        return .bool (leftValue == rightValue)
    | .atMostCmp _ left right => do
        return .bool ((← valueAsInt (← evalExpr env left)) <= (← valueAsInt (← evalExpr env right)))
    | .atLeastCmp _ left right => do
        return .bool ((← valueAsInt (← evalExpr env left)) >= (← valueAsInt (← evalExpr env right)))
    | .lessCmp _ left right => do
        return .bool ((← valueAsInt (← evalExpr env left)) < (← valueAsInt (← evalExpr env right)))
    | .old _ operand => evalExpr env operand
    | .deref .. => unsupported "deref expression"
    | .fieldRef .. => unsupported "field reference expression"
    | .address .. => unsupported "address expression"
    | .ref .. => unsupported "reference expression"
    | .structLit .. => unsupported "struct literal expression"
    | .pureMethodCall .. => unsupported "pure method call expression"
    | .mPredicateAccess .. => unsupported "method predicate access expression"
    | .predicate .. => unsupported "predicate expression"

  partial def evalAssertion (env : Env) : GobraJson.Assertion → Except String Bool
    | .expr expr => do
        valueAsBool (← evalExpr env expr)
    | .exprAssertion _ expr => do
        valueAsBool (← evalExpr env expr)
    | .sepAnd _ left right => do
        return (← evalAssertion env left) && (← evalAssertion env right)
    | .implication _ left right => do
        if ← evalAssertion env left then
          evalAssertion env right
        else
          return true
    | .access .. => unsupported "access assertion"

  partial def assignAssignee (env : Env) (assignee : GobraJson.Assignee) (value : GoValue) :
      Except String Env :=
    match assignee with
    | .var _ ref => return Env.set env (varRefId ref) value
    | .field .. => unsupported "field assignment"

  partial def execDecl (env : Env) : GobraJson.Decl → Except String Env
    | .local var => do
        return Env.set env var.id (← defaultValue var.typ)
    | .label _ => return env

  partial def execDecls (env : Env) (decls : Array GobraJson.Decl) : Except String Env := do
    let mut env := env
    for decl in decls do
      env ← execDecl env decl
    return env

  partial def execStmts (fuel : Nat) (env : Env) (stmts : Array GobraJson.Stmt) :
      Except String Env := do
    let mut env := env
    for stmt in stmts do
      env ← execStmt fuel env stmt
    return env

  partial def execStmt (fuel : Nat) (env : Env) : GobraJson.Stmt → Except String Env
    | .seqn _ stmts => execStmts fuel env stmts
    | .block _ decls stmts => do
        execStmts fuel (← execDecls env decls) stmts
    | .initialization _ var => return Env.set env var.id (← defaultValue var.typ)
    | .singleAss _ left right => do
        assignAssignee env left (← evalExpr env right)
    | .assert _ assertion => do
        if ← evalAssertion env assertion then
          return env
        else
          throw "Gobra assertion failed"
    | .while _ cond _invs _terminationMeasure body => do
        if fuel == 0 then
          throw "Gobra execution fuel exhausted"
        if ← valueAsBool (← evalExpr env cond) then
          execStmt (fuel - 1) (← execStmt fuel env body) (.while .internal cond #[] none body)
        else
          return env
    | .label _ _ => return env
    | .functionCall .. => unsupported "function call statement"
    | .methodCall .. => unsupported "method call statement"
end

private def execMethodBody (fuel : Nat) (env : Env) (body : GobraJson.MethodBody) :
    Except String Env := do
  let env ← execDecls env body.decls
  let env ← execStmts fuel env body.seqn.stmts
  execStmts fuel env body.postprocessing

private def checkAssertions (env : Env) (kind : String) (assertions : Array GobraJson.Assertion) :
    Except String Unit := do
  for assertion in assertions do
    if ← evalAssertion env assertion then
      pure ()
    else
      throw s!"Gobra {kind} failed"

private def bindParams (env : Env) (params : Array GobraJson.Parameter) (args : Array GoValue) :
    Except String Env := do
  if params.size != args.size then
    throw s!"expected {params.size} argument(s), got {args.size}"
  let mut env := env
  let mut i := 0
  for param in params do
    match args[i]? with
    | some value =>
        env := Env.set env param.id value
        i := i + 1
    | none => throw s!"missing argument {i}"
  return env

private def initResults (env : Env) (results : Array GobraJson.Parameter) : Except String Env := do
  let mut env := env
  for result in results do
    env := Env.set env result.id (← defaultValue result.typ)
  return env

private def collectResults (env : Env) (results : Array GobraJson.Parameter) :
    Except String (Array GoValue) := do
  let mut values := #[]
  for result in results do
    values := values.push (← lookup env result.id)
  return values

def runFunctionMember (fuel : Nat) (member : GobraJson.FunctionMember) (args : Array GoValue) :
    Except String Result := do
  let body : GobraJson.MethodBody ←
    match member.body with
    | some body => pure body
    | none => unsupported s!"bodyless function {member.name.name}"
  let env ← bindParams [] member.args args
  let env ← initResults env member.results
  checkAssertions env "precondition" member.pres
  let env ← execMethodBody fuel env body
  checkAssertions env "postcondition" member.posts
  return { values := (← collectResults env member.results) }

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
