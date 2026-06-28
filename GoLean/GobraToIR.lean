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
  | .string _ => .string
  | .void => .unsupported "void type"
  | .float32 _ => .unsupported "float32 type"
  | .float64 _ => .unsupported "float64 type"
  | .function .. => .unsupported "function type"
  | .permission _ => .unsupported "permission type"
  | .sort => .unsupported "sort type"
  | .slice elem _ => .slice (lowerTy elem)
  | .map key value _ => .map (lowerTy key) (lowerTy value)
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

private def pointerTypeNameOfTy? : GoLean.GoCore.Ty → Option String
  | .pointer (.defined name) => some name
  | _ => none

private def varRefTy : GoLean.GobraJson.VarRef → GoLean.GobraJson.Ty
  | .local var => var.typ
  | .inParam param => param.typ
  | .outParam param => param.typ

partial def lowerExprTy? : GoLean.GobraJson.Expr → Option GoLean.GoCore.Ty
  | .var ref => some (lowerTy (varRefTy ref))
  | .stringLit .. => some .string
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
  | .dfltVal _ typ => some (lowerTy typ)
  | .indexedExp _ _ _ baseUnderlyingType =>
      match lowerTy baseUnderlyingType with
      | .array _ elem => some elem
      | .slice elem => some elem
      | .map _ value => some value
      | .unsupported feature => some (.unsupported feature)
      | other => some (.unsupported s!"indexing non-array/slice/map type {repr other}")
  | .slice _ _ _ _ _ baseUnderlyingType =>
      match lowerTy baseUnderlyingType with
      | .array _ elem => some (.slice elem)
      | .pointer (.array _ elem) => some (.slice elem)
      | .slice elem => some (.slice elem)
      | .unsupported feature => some (.unsupported feature)
      | other => some (.unsupported s!"slicing non-array/slice type {repr other}")
  | .length .. => some .int
  | .capacity .. => some .int
  | _ => none

mutual
partial def lowerAddressOfExpr : GoLean.GobraJson.Expr → GoLean.GoCore.Expr
  | .var ref => .ref (varRefId ref)
  | .deref _ exp _ => lowerExpr exp
  | .indexedExp _ base index _ =>
      match lowerExprTy? base with
      | some (.pointer (.array ..)) => .indexAddr (lowerExpr base) (lowerExpr index)
      | _ => .indexAddr (lowerAddressOfExpr base) (lowerExpr index)
  | .fieldRef _ recv field =>
      match lowerExprTy? recv with
      | some recvTy =>
          match typeNameOfTy? recvTy with
          | some typeName => .fieldAddr (lowerAddressOfExpr recv) typeName field.name
          | none =>
              match pointerTypeNameOfTy? recvTy with
              | some typeName => .fieldAddr (lowerExpr recv) typeName field.name
              | none => .unsupported "field address without defined receiver type"
      | none => .unsupported "field address without receiver type"
  | .address _ operand => lowerAddressOfExpr operand
  | .old _ operand => lowerAddressOfExpr operand
  | _ => .unsupported "address of unsupported expression"

partial def lowerAssignee : GoLean.GobraJson.Assignee → GoLean.GoCore.Assignee
  | .var _ ref => .var (varRefId ref)
  | .field _ op => .addr (lowerAddressOfExpr op)
  | .index _ op => .addr (lowerAddressOfExpr op)
  | .pointer _ (.deref _ exp _) => .addr (lowerExpr exp)
  | .pointer _ _ => .unsupported "pointer assignee without dereference operand"

partial def lowerExpr : GoLean.GobraJson.Expr → GoLean.GoCore.Expr
  | .var ref => .var (varRefId ref)
  | .nilLit _ typ => .nil (some (lowerTy typ))
  | .intLit _ value _ _ => .intLit value
  | .stringLit _ value => .stringLit value
  | .boolLit _ value => .boolLit value
  | .add _ left right => .add (lowerExpr left) (lowerExpr right)
  | .sub _ left right => .sub (lowerExpr left) (lowerExpr right)
  | .mul _ left right => .mul (lowerExpr left) (lowerExpr right)
  | .div _ left right => .div (lowerExpr left) (lowerExpr right)
  | .mod _ left right => .mod (lowerExpr left) (lowerExpr right)
  | .eqCmp _ left right => .eqCmp (lowerExpr left) (lowerExpr right)
  | .ghostEqCmp .. => .unsupported "ghost equality expression"
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
      | .pointer _ (.deref _ exp _) => lowerExpr exp
      | .pointer _ _ => .unsupported "reference to pointer assignee without dereference operand"
  | .old _ operand => .old (lowerExpr operand)
  | .deref _ exp typ => .deref (lowerExpr exp) (lowerTy typ)
  | .fieldRef _ recv field =>
      match lowerExprTy? recv with
      | some recvTy =>
          match typeNameOfTy? recvTy with
          | some typeName => .fieldGet (lowerExpr recv) typeName field.name
          | none =>
              match pointerTypeNameOfTy? recvTy with
              | some typeName => .fieldGet (.deref (lowerExpr recv) (.defined typeName)) typeName field.name
              | none => .unsupported "field reference without defined receiver type"
      | none => .unsupported "field reference without receiver type"
  | .address _ op => lowerAddressOfExpr op
  | .structLit _ typ args => .structLit (lowerTy typ) (args.map lowerExpr)
  | .arrayLit _ length elem args =>
      if length < 0 then
        .unsupported s!"negative array length {length}"
      else
        .arrayLit length.toNat (lowerTy elem) (args.map (fun arg => (arg.key, lowerExpr arg.value)))
  | .dfltVal _ typ => .defaultValue (lowerTy typ)
  | .indexedExp _ base index _ =>
      match lowerExprTy? base with
      | some (.pointer arrayTy@(.array ..)) => .indexGet (.deref (lowerExpr base) arrayTy) (lowerExpr index)
      | some (.map _ valueTy) => .mapGet (lowerExpr base) (lowerExpr index) valueTy
      | _ => .indexGet (lowerExpr base) (lowerExpr index)
  | .slice _ base low high max baseUnderlyingType =>
      let loweredBase :=
        match lowerTy baseUnderlyingType with
        | .array .. => lowerAddressOfExpr base
        | _ => lowerExpr base
      .slice loweredBase (lowerExpr low) (lowerExpr high) (max.map lowerExpr)
  | .length _ exp => .length (lowerExpr exp)
  | .capacity _ exp => .capacity (lowerExpr exp)
  | .pureMethodCall .. => .unsupported "pure method call expression"
  | .mPredicateAccess .. => .unsupported "method predicate access expression"
  | .predicate .. => .unsupported "predicate expression"
end

private def lowerDecls (decls : Array GoLean.GobraJson.Decl) : Array GoLean.GoCore.Param :=
  decls.foldl
    (fun out decl =>
      match decl with
      | .local var => out.push (lowerVariable var)
      | .label _ => out)
    #[]

private def sliceLiteralLength? (elems : Array GoLean.GobraJson.ArrayLitElem) : Option Nat :=
  elems.foldl
    (fun acc elem =>
      match acc with
      | none => none
      | some length =>
          if elem.key < (0 : Int) then none else some (max length (elem.key.toNat + 1)))
    (some 0)

private def lowerMapIndex? : GoLean.GobraJson.Expr → Option (GoLean.GoCore.Expr × GoLean.GoCore.Expr × GoLean.GoCore.Ty)
  | .indexedExp _ base index baseUnderlyingType =>
      match lowerTy baseUnderlyingType with
      | .map _ valueTy => some (lowerExpr base, lowerExpr index, valueTy)
      | _ => none
  | _ => none

partial def lowerNewSliceLit (target : GoLean.GobraJson.Variable) (memberType : GoLean.GobraJson.Ty)
    (elems : Array GoLean.GobraJson.ArrayLitElem) : GoLean.GoCore.Stmt :=
  match sliceLiteralLength? elems with
  | none => .unsupported "slice literal with negative element key"
  | some length =>
      let elemTy := lowerTy memberType
      let init := #[
        GoLean.GoCore.Stmt.makeSlice
          (.var target.id)
          elemTy
          (.intLit (Int.ofNat length))
          (some (.intLit (Int.ofNat length)))
      ]
      let stmts := elems.foldl
        (fun stmts elem => stmts.push
          (.assign
            (.addr (.indexAddr (.var target.id) (.intLit elem.key)))
            (lowerExpr elem.value)))
        init
      .seqn stmts

partial def lowerNewMapLit (target : GoLean.GobraJson.Variable) (keys values : GoLean.GobraJson.Ty)
    (entries : Array GoLean.GobraJson.MapLitEntry) : GoLean.GoCore.Stmt :=
  let keyTy := lowerTy keys
  let valueTy := lowerTy values
  let init := #[
    GoLean.GoCore.Stmt.makeMap
      (.var target.id)
      keyTy
      valueTy
      (some (.intLit (Int.ofNat entries.size)))
  ]
  let stmts := entries.foldl
    (fun stmts entry => stmts.push (.mapAssign (.var target.id) (lowerExpr entry.key) (lowerExpr entry.value)))
    init
  .seqn stmts

private def lowerTempVarAssignee? : GoLean.GobraJson.Assignee → Option String
  | .var _ (.local var) => some var.id
  | _ => none

private def lowerVarExprId? : GoLean.GobraJson.Expr → Option String
  | .var (.local var) => some var.id
  | _ => none

private def splitAt? {α : Type} (xs : Array α) (n : Nat) : Option (Array α × Array α) := do
  if n <= xs.size then
    return (xs.extract 0 n, xs.extract n xs.size)
  else
    none

private def lowerDesugaredMultiAssign? (stmts : Array GoLean.GobraJson.Stmt) :
    Option GoLean.GoCore.Stmt := do
  if stmts.size == 0 || stmts.size % 2 != 0 then
    none
  let n := stmts.size / 2
  let (tempStmts, targetStmts) ← splitAt? stmts n
  let mut tempIds := #[]
  let mut loweredTemps := #[]
  for stmt in tempStmts do
    match stmt with
    | .singleAss _ left right =>
        let id ← lowerTempVarAssignee? left
        tempIds := tempIds.push id
        loweredTemps := loweredTemps.push (GoLean.GoCore.Stmt.assign (.var id) (lowerExpr right))
    | _ => none
  let mut targets := #[]
  let mut values := #[]
  let mut i := 0
  for stmt in targetStmts do
    match stmt with
    | .singleAss _ left right =>
        let id ← lowerVarExprId? right
        match tempIds[i]? with
        | some expected =>
            if id != expected then
              none
        | none => none
        targets := targets.push (lowerAssignee left)
        values := values.push (GoLean.GoCore.Expr.var id)
        i := i + 1
    | _ => none
  return .seqn (loweredTemps.push (.assignMany targets values))

partial def lowerStmtWithReturnPost (returnPostprocessing : Array GoLean.GoCore.Stmt) :
      GoLean.GobraJson.Stmt → GoLean.GoCore.Stmt
    | .seqn _ stmts =>
        match lowerDesugaredMultiAssign? stmts with
        | some stmt => stmt
        | none => .seqn (stmts.map (lowerStmtWithReturnPost returnPostprocessing))
    | .block _ decls stmts =>
        .block (lowerDecls decls) (stmts.map (lowerStmtWithReturnPost returnPostprocessing))
    | .initialization _ var => .initialization (lowerVariable var)
    | .singleAss _ left right =>
        match left with
        | .index _ op =>
            match lowerMapIndex? op with
            | some (base, index, _valueTy) => .mapAssign base index (lowerExpr right)
            | none => .assign (lowerAssignee left) (lowerExpr right)
        | _ => .assign (lowerAssignee left) (lowerExpr right)
    | .new _ target expr => .newValue (.var target.id) (lowerExpr expr)
    | .makeSlice _ target typeParam lenArg capArg =>
        match lowerTy typeParam with
        | .slice elem => .makeSlice (.var target.id) elem (lowerExpr lenArg) (capArg.map lowerExpr)
        | other => .unsupported s!"MakeSlice with non-slice type {repr other}"
    | .makeMap _ target typeParam initialSpaceArg =>
        match lowerTy typeParam with
        | .map key value => .makeMap (.var target.id) key value (initialSpaceArg.map lowerExpr)
        | other => .unsupported s!"MakeMap with non-map type {repr other}"
    | .newSliceLit _ target memberType elems => lowerNewSliceLit target memberType elems
    | .newMapLit _ target keys values entries => lowerNewMapLit target keys values entries
    | .safeMapLookup _ resTarget successTarget mapLookup =>
        match lowerMapIndex? mapLookup with
        | some (base, index, valueTy) =>
            .mapLookup (.var resTarget.id) (.var successTarget.id) base index valueTy
        | none => .unsupported "SafeMapLookup with non-map lookup"
    | .goSliceAppend _ target slice elems =>
        .appendSlice (.var target.id) (lowerExpr slice) (lowerExpr elems)
    | .goSliceCopy _ target dst src =>
        .copySlice (.var target.id) (lowerExpr dst) (lowerExpr src)
    | .assert .. => .seqn #[]
    | .assume .. => .seqn #[]
    | .ifStmt _ cond thn els =>
        .ifThenElse (lowerExpr cond)
          (lowerStmtWithReturnPost returnPostprocessing thn)
          (lowerStmtWithReturnPost returnPostprocessing els)
    | .while _ cond _invs _terminationMeasure body =>
        .while (lowerExpr cond) (lowerStmtWithReturnPost returnPostprocessing body)
    | .returnStmt _ => .seqn (returnPostprocessing.push .returnStmt)
    | .breakStmt _ none _ => .breakStmt
    | .breakStmt _ (some label) _ => .unsupported s!"labeled break {label}"
    | .continueStmt _ none _ => .continueStmt
    | .continueStmt _ (some label) _ => .unsupported s!"labeled continue {label}"
    | .label _ id => .label id.name
    | .functionCall _ func targets args =>
        .call (targets.map lowerAssignee) func.name (args.map lowerExpr)
    | .methodCall _ recv meth targets args =>
        .call (targets.map lowerAssignee) meth.uniqueName (#[lowerExpr recv] ++ args.map lowerExpr)

partial def lowerStmt : GoLean.GobraJson.Stmt → GoLean.GoCore.Stmt :=
  lowerStmtWithReturnPost #[]

private def lowerMethodBody (body : GoLean.GobraJson.MethodBody) : GoLean.GoCore.Stmt :=
  let postprocessing := body.postprocessing.map lowerStmt
  .block (lowerDecls body.decls)
    (body.seqn.stmts.map (lowerStmtWithReturnPost postprocessing) ++ postprocessing)

private def hasTypeDef (defs : Array (String × GoLean.GoCore.TypeDef)) (name : String) : Bool :=
  defs.any (fun (existing, _) => existing == name)

private def structFields? : GoLean.GobraJson.Ty → Option (Array GoLean.GobraJson.FieldInfo)
  | .struct fields _ghost _ => some fields
  | _ => none

private def firstStructFields? : List GoLean.GobraJson.Ty → Option (Array GoLean.GobraJson.FieldInfo)
  | [] => none
  | ty :: rest =>
      match structFields? ty with
      | some fields => some fields
      | none => firstStructFields? rest

private def firstStructFieldsBeforeNextDefined? :
    List GoLean.GobraJson.Ty → Option (Array GoLean.GobraJson.FieldInfo)
  | [] => none
  | (.defined ..) :: _ => none
  | ty :: rest =>
      match structFields? ty with
      | some fields => some fields
      | none => firstStructFieldsBeforeNextDefined? rest

private def lowerTypeDefsFromTypes : List GoLean.GobraJson.Ty →
    Option (Array GoLean.GobraJson.FieldInfo) →
    Array (String × GoLean.GoCore.TypeDef) → Array (String × GoLean.GoCore.TypeDef)
  | .nil, _, defs => defs
  | ty :: rest, lastStruct, defs =>
      let lastStruct :=
        match structFields? ty with
        | some fields => some fields
        | none => lastStruct
      let defs :=
        match ty with
        | .defined name _ =>
            if hasTypeDef defs name then
              defs
            else
              let fields? :=
                match firstStructFieldsBeforeNextDefined? rest with
                | some fields => some fields
                | none => lastStruct
              match fields? with
              | some fields => defs.push (name, .struct (fields.map lowerFieldDef))
              | none => defs
        | _ => defs
      lowerTypeDefsFromTypes rest lastStruct defs

def lowerTypeDefs (types : Array GoLean.GobraJson.Ty) :
    Array (String × GoLean.GoCore.TypeDef) :=
  lowerTypeDefsFromTypes types.toList none #[]

def lowerFunctionMember (member : GoLean.GobraJson.FunctionMember) : Except String GoLean.GoCore.Func := do
  let body ←
    match member.body with
    | some body => pure body
    | none => throw s!"bodyless function {member.name.name}"
  return {
    name := member.name.name,
    args := member.args.map lowerParam,
    results := member.results.map lowerParam,
    body := lowerMethodBody body
  }

def lowerBodylessFunctionMember (member : GoLean.GobraJson.FunctionMember) : GoLean.GoCore.Func := {
  name := member.name.name,
  args := member.args.map lowerParam,
  results := member.results.map lowerParam,
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
    body := lowerMethodBody body
  }

def lowerBodylessMethodMember (member : GoLean.GobraJson.MethodMember) : GoLean.GoCore.Func := {
  name := member.name.uniqueName,
  args := #[lowerParam member.receiver] ++ member.args.map lowerParam,
  results := member.results.map lowerParam,
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
