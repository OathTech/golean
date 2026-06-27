import GoLean.GobraJson
import GoLean.IR

namespace GoLean.GobraToIR

private def varRefId : GoLean.GobraJson.VarRef → String
  | .local var => var.id
  | .inParam param => param.id
  | .outParam param => param.id

partial def lowerTy : GoLean.GobraJson.Ty → GoLean.GoCore.Ty
  | .bool _ => .bool
  | .int _ _ => .int
  | .array length elem _ =>
      if length < 0 then
        .unsupported s!"negative array length {length}"
      else
        .array length.toNat (lowerTy elem)
  | .pointer elem _ => .pointer (lowerTy elem)
  | .defined name _ => .defined name
  | .interface name _ => .unsupported s!"interface type {name}"
  | .struct _ _ _ => .unsupported "anonymous struct type"
  | .string _ => .unsupported "string type"
  | .void => .unsupported "void type"
  | .float32 _ => .unsupported "float32 type"
  | .float64 _ => .unsupported "float64 type"
  | .function .. => .unsupported "function type"
  | .permission _ => .unsupported "permission type"
  | .sort => .unsupported "sort type"
  | .slice .. => .unsupported "slice type"
  | .map .. => .unsupported "map type"
  | .sequence .. => .unsupported "sequence type"
  | .set .. => .unsupported "set type"
  | .multiset .. => .unsupported "multiset type"
  | .mathMap .. => .unsupported "math map type"
  | .option .. => .unsupported "option type"
  | .tuple .. => .unsupported "tuple type"
  | .pred .. => .unsupported "predicate type"
  | .domain name _ => .unsupported s!"domain type {name}"
  | .adt name _ _ => .unsupported s!"ADT type {name}"
  | .adtClause name _ _ _ => .unsupported s!"ADT clause type {name}"
  | .channel .. => .unsupported "channel type"

def lowerParam (param : GoLean.GobraJson.Parameter) : GoLean.GoCore.Param :=
  { id := param.id, typ := lowerTy param.typ }

def lowerVariable (var : GoLean.GobraJson.Variable) : GoLean.GoCore.Param :=
  { id := var.id, typ := lowerTy var.typ }

def lowerFieldDef (field : GoLean.GobraJson.FieldInfo) : GoLean.GoCore.FieldDef :=
  { name := field.name, typ := lowerTy field.typ }

private def typeNameOfTy? : GoLean.GoCore.Ty → Option String
  | .defined name => some name
  | _ => none

private def varRefTy : GoLean.GobraJson.VarRef → GoLean.GobraJson.Ty
  | .local var => var.typ
  | .inParam param => param.typ
  | .outParam param => param.typ

partial def lowerExprTy? : GoLean.GobraJson.Expr → Option GoLean.GoCore.Ty
  | .var ref => some (lowerTy (varRefTy ref))
  | .deref _ _ typ =>
      match lowerTy typ with
      | .pointer elem => some elem
      | other => some other
  | .fieldRef _ _ field => some (lowerTy field.typ)
  | .address _ operand =>
      match lowerExprTy? operand with
      | some typ => some (.pointer typ)
      | none => none
  | .ref _ _ typ => some (lowerTy typ)
  | .old _ operand => lowerExprTy? operand
  | .structLit _ typ _ => some (lowerTy typ)
  | .arrayLit _ length elem _ =>
      if length < 0 then
        some (.unsupported s!"negative array length {length}")
      else
        some (.array length.toNat (lowerTy elem))
  | .indexedExp _ _ _ baseUnderlyingType =>
      match lowerTy baseUnderlyingType with
      | .array _ elem => some elem
      | .unsupported feature => some (.unsupported feature)
      | other => some (.unsupported s!"indexing non-array type {repr other}")
  | _ => none

mutual
partial def lowerAddressOfExpr : GoLean.GobraJson.Expr → GoLean.GoCore.Expr
  | .var ref => .ref (varRefId ref)
  | .deref _ exp _ => lowerExpr exp
  | .indexedExp _ base index _ => .indexAddr (lowerAddressOfExpr base) (lowerExpr index)
  | .fieldRef _ recv field =>
      match (lowerExprTy? recv).bind typeNameOfTy? with
      | some typeName => .fieldAddr (lowerAddressOfExpr recv) typeName field.name
      | none => .unsupported "field address without defined receiver type"
  | .address _ operand => lowerAddressOfExpr operand
  | .old _ operand => lowerAddressOfExpr operand
  | _ => .unsupported "address of unsupported expression"

partial def lowerAssignee : GoLean.GobraJson.Assignee → GoLean.GoCore.Assignee
  | .var _ ref => .var (varRefId ref)
  | .field _ op => .addr (lowerAddressOfExpr op)
  | .index _ op => .addr (lowerAddressOfExpr op)

partial def lowerExpr : GoLean.GobraJson.Expr → GoLean.GoCore.Expr
  | .var ref => .var (varRefId ref)
  | .intLit _ value _ _ => .intLit value
  | .boolLit _ value => .boolLit value
  | .add _ left right => .add (lowerExpr left) (lowerExpr right)
  | .sub _ left right => .sub (lowerExpr left) (lowerExpr right)
  | .mul _ left right => .mul (lowerExpr left) (lowerExpr right)
  | .div _ left right => .div (lowerExpr left) (lowerExpr right)
  | .mod _ left right => .mod (lowerExpr left) (lowerExpr right)
  | .eqCmp _ left right => .eqCmp (lowerExpr left) (lowerExpr right)
  | .uneqCmp _ left right => .neqCmp (lowerExpr left) (lowerExpr right)
  | .atMostCmp _ left right => .atMostCmp (lowerExpr left) (lowerExpr right)
  | .atLeastCmp _ left right => .atLeastCmp (lowerExpr left) (lowerExpr right)
  | .lessCmp _ left right => .lessCmp (lowerExpr left) (lowerExpr right)
  | .greaterCmp _ left right => .greaterCmp (lowerExpr left) (lowerExpr right)
  | .and _ left right => .and (lowerExpr left) (lowerExpr right)
  | .or _ left right => .or (lowerExpr left) (lowerExpr right)
  | .negation _ operand => .not (lowerExpr operand)
  | .ref _ assignee _ =>
      match assignee with
      | .var _ ref => .ref (varRefId ref)
      | .field _ op => lowerAddressOfExpr op
      | .index _ op => lowerAddressOfExpr op
  | .old _ operand => .old (lowerExpr operand)
  | .deref _ exp typ => .deref (lowerExpr exp) (lowerTy typ)
  | .fieldRef _ recv field =>
      match (lowerExprTy? recv).bind typeNameOfTy? with
      | some typeName => .fieldGet (lowerExpr recv) typeName field.name
      | none => .unsupported "field reference without defined receiver type"
  | .address _ op => lowerAddressOfExpr op
  | .structLit _ typ args => .structLit (lowerTy typ) (args.map lowerExpr)
  | .arrayLit _ length elem args =>
      if length < 0 then
        .unsupported s!"negative array length {length}"
      else
        .arrayLit length.toNat (lowerTy elem) (args.map (fun arg => (arg.key, lowerExpr arg.value)))
  | .indexedExp _ base index _ => .indexGet (lowerExpr base) (lowerExpr index)
  | .pureMethodCall .. => .unsupported "pure method call expression"
  | .mPredicateAccess .. => .unsupported "method predicate access expression"
  | .predicate .. => .unsupported "predicate expression"
end

partial def lowerAssertion : GoLean.GobraJson.Assertion → GoLean.GoCore.Assertion
  | .expr expr => .expr (lowerExpr expr)
  | .exprAssertion _ expr => .expr (lowerExpr expr)
  | .sepAnd _ left right => .sepAnd (lowerAssertion left) (lowerAssertion right)
  | .implication _ left right => .implication (lowerAssertion left) (lowerAssertion right)
  | .access .. => .unsupported "access assertion"

private def lowerDecls (decls : Array GoLean.GobraJson.Decl) : Array GoLean.GoCore.Param :=
  decls.foldl
    (fun out decl =>
      match decl with
      | .local var => out.push (lowerVariable var)
      | .label _ => out)
    #[]

partial def lowerStmt : GoLean.GobraJson.Stmt → GoLean.GoCore.Stmt
  | .seqn _ stmts => .seqn (stmts.map lowerStmt)
  | .block _ decls stmts => .block (lowerDecls decls) (stmts.map lowerStmt)
  | .initialization _ var => .initialization (lowerVariable var)
  | .singleAss _ left right => .assign (lowerAssignee left) (lowerExpr right)
  | .assert _ assertion => .assert (lowerAssertion assertion)
  | .while _ cond _invs _terminationMeasure body => .while (lowerExpr cond) (lowerStmt body)
  | .label _ id => .label id.name
  | .functionCall _ func targets args =>
      .call (targets.map lowerAssignee) func.name (args.map lowerExpr)
  | .methodCall _ recv meth targets args =>
      .call (targets.map lowerAssignee) meth.uniqueName (#[lowerExpr recv] ++ args.map lowerExpr)

private def lowerMethodBody (body : GoLean.GobraJson.MethodBody) : GoLean.GoCore.Stmt :=
  .block (lowerDecls body.decls)
    (body.seqn.stmts.map lowerStmt ++ body.postprocessing.map lowerStmt)

private def hasTypeDef (defs : Array (String × GoLean.GoCore.TypeDef)) (name : String) : Bool :=
  defs.any (fun (existing, _) => existing == name)

private def lowerTypeDefsFromTypes : List GoLean.GobraJson.Ty →
    Array (String × GoLean.GoCore.TypeDef) → Array (String × GoLean.GoCore.TypeDef)
  | .nil, defs => defs
  | (.defined name _) :: (.struct fields _ghost _) :: rest, defs =>
      let defs :=
        if hasTypeDef defs name then
          defs
        else
          defs.push (name, .struct (fields.map lowerFieldDef))
      lowerTypeDefsFromTypes rest defs
  | _ :: rest, defs => lowerTypeDefsFromTypes rest defs

def lowerTypeDefs (types : Array GoLean.GobraJson.Ty) :
    Array (String × GoLean.GoCore.TypeDef) :=
  lowerTypeDefsFromTypes types.toList #[]

def lowerFunctionMember (member : GoLean.GobraJson.FunctionMember) : Except String GoLean.GoCore.Func := do
  let body ←
    match member.body with
    | some body => pure body
    | none => throw s!"bodyless function {member.name.name}"
  return {
    name := member.name.name,
    args := member.args.map lowerParam,
    results := member.results.map lowerParam,
    pres := member.pres.map lowerAssertion,
    posts := member.posts.map lowerAssertion,
    body := lowerMethodBody body
  }

def lowerBodylessFunctionMember (member : GoLean.GobraJson.FunctionMember) : GoLean.GoCore.Func := {
  name := member.name.name,
  args := member.args.map lowerParam,
  results := member.results.map lowerParam,
  pres := member.pres.map lowerAssertion,
  posts := member.posts.map lowerAssertion,
  body := .unsupported s!"bodyless function {member.name.name}"
}

def lowerMethodMember (member : GoLean.GobraJson.MethodMember) : Except String GoLean.GoCore.Func := do
  let body ←
    match member.body with
    | some body => pure body
    | none => throw s!"bodyless method {member.name.uniqueName}"
  return {
    name := member.name.uniqueName,
    args := #[lowerParam member.receiver] ++ member.args.map lowerParam,
    results := member.results.map lowerParam,
    pres := member.pres.map lowerAssertion,
    posts := member.posts.map lowerAssertion,
    body := lowerMethodBody body
  }

def lowerBodylessMethodMember (member : GoLean.GobraJson.MethodMember) : GoLean.GoCore.Func := {
  name := member.name.uniqueName,
  args := #[lowerParam member.receiver] ++ member.args.map lowerParam,
  results := member.results.map lowerParam,
  pres := member.pres.map lowerAssertion,
  posts := member.posts.map lowerAssertion,
  body := .unsupported s!"bodyless method {member.name.uniqueName}"
}

def lowerProgram (program : GoLean.GobraJson.Program) : Except String GoLean.GoCore.Program := do
  let mut funcs := #[]
  for member in program.members do
    match member with
    | .function member =>
        match member.body with
        | some _ => funcs := funcs.push (← lowerFunctionMember member)
        | none => funcs := funcs.push (lowerBodylessFunctionMember member)
    | .method member =>
        match member.body with
        | some _ => funcs := funcs.push (← lowerMethodMember member)
        | none => funcs := funcs.push (lowerBodylessMethodMember member)
    | .mPredicate _ =>
        pure ()
  return { typeDefs := lowerTypeDefs program.types, funcs }

def lowerDocument (doc : GoLean.GobraJson.Document) : Except String GoLean.GoCore.Program :=
  lowerProgram doc.program

end GoLean.GobraToIR
