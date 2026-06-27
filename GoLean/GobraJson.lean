import GoLean.StrictJson

namespace GoLean.GobraJson

open Lean
open System
structure Schema where
  name : String
  version : Nat
  encoding : String
  failClosed : Bool
  deriving Repr, BEq

structure KnownTag where
  name : String
  deriving Repr, BEq

private def knownTagNames : List String := [
  "Access", "Add", "Address", "Assert", "AtLeastCmp", "AtMostCmp", "Capacity",
  "ArrayLit", "ArrayT", "Block", "BoolLit", "BoolT", "BoundedInteger", "Decimal", "DefinedT", "DfltVal",
  "Break", "Continue", "Deref", "Div", "EqCmp", "ExprAssertion", "Field", "FieldRef", "FullPerm",
  "Function", "FunctionCall", "FunctionProxy", "GoSliceAppend", "GoSliceCopy", "GreaterCmp", "Implication", "In",
  "If", "Index", "IndexedExp", "Initialization", "IntLit", "IntT", "InterfaceT", "Internal", "ItfTupleTerminationMeasure",
  "Label", "LabelProxy", "Length", "LessCmp", "LocalVar", "MPredicate",
  "MPredicateAccess", "MPredicateProxy", "MakeSlice", "Method", "MethodBody", "MethodBodySeqn",
  "MethodCall", "MethodProxy", "Mod", "Mul", "Negation", "NewSliceLit", "NilLit", "NonItfTupleTerminationMeasure",
  "None", "Old", "Or", "Out", "PointerT", "Predicate", "Program", "PureMethod",
  "PureMethodCall", "Ref", "Return", "SepAnd", "Seqn", "Single", "SingleAss", "Slice", "Some",
  "SliceT", "StringT", "StructLit", "StructT", "Sub", "UnboundedInteger", "UneqCmp", "Var", "While",
  "WildcardPerm"
]

def KnownTag.ofString? (name : String) : Option KnownTag :=
  if knownTagNames.contains name then Option.some { name } else Option.none

def isKnownTagName (name : String) : Bool :=
  (KnownTag.ofString? name).isSome

structure LineColumn where
  line : Nat
  column : Nat
  deriving Repr, BEq

structure Position where
  file : String
  start : LineColumn
  «end» : Option LineColumn
  deriving Repr, BEq

structure Origin where
  tag : String
  position : Position
  deriving Repr, BEq

inductive Source where
  | internal
  | single (origin : Origin)
  deriving Repr, BEq

inductive IntegerKind where
  | unbounded (name : String)
  | bounded (name : String) (bits : Nat) (lower upper : Int)
  deriving Repr, BEq

inductive Addressability where
  | shared
  | exclusive
  deriving Repr, BEq

mutual
  inductive Ty where
    | bool (addressability : Addressability)
    | int (addressability : Addressability) (kind : IntegerKind)
    | float32 (addressability : Addressability)
    | float64 (addressability : Addressability)
    | string (addressability : Addressability)
    | void
    | function (args results : Array Ty) (addressability : Addressability)
    | permission (addressability : Addressability)
    | sort
    | array (length : Int) (elem : Ty) (addressability : Addressability)
    | slice (elem : Ty) (addressability : Addressability)
    | map (keys values : Ty) (addressability : Addressability)
    | sequence (elem : Ty) (addressability : Addressability)
    | set (elem : Ty) (addressability : Addressability)
    | multiset (elem : Ty) (addressability : Addressability)
    | mathMap (keys values : Ty) (addressability : Addressability)
    | option (elem : Ty) (addressability : Addressability)
    | defined (name : String) (addressability : Addressability)
    | pointer (elem : Ty) (addressability : Addressability)
    | tuple (types : Array Ty) (addressability : Addressability)
    | pred (args : Array Ty) (addressability : Addressability)
    | struct (fields : Array FieldInfo) (ghost : Bool) (addressability : Addressability)
    | interface (name : String) (addressability : Addressability)
    | domain (name : String) (addressability : Addressability)
    | adt (name definedName : String) (addressability : Addressability)
    | adtClause (name : String) (adt : Ty) (fields : Array FieldInfo) (addressability : Addressability)
    | channel (elem : Ty) (addressability : Addressability)
    deriving Repr, BEq

  structure FieldInfo where
    source : Source
    name : String
    typ : Ty
    ghost : Bool
    deriving Repr, BEq
end

structure Parameter where
  source : Source
  id : String
  typ : Ty
  deriving Repr, BEq

structure Variable where
  source : Source
  id : String
  typ : Ty
  deriving Repr, BEq

inductive VarRef where
  | local (var : Variable)
  | inParam (param : Parameter)
  | outParam (param : Parameter)
  deriving Repr, BEq

structure FunctionProxy where
  source : Source
  name : String
  deriving Repr, BEq

structure MethodProxy where
  source : Source
  name : String
  uniqueName : String
  deriving Repr, BEq

structure LabelProxy where
  source : Source
  name : String
  deriving Repr, BEq

inductive BackendAnnotation where
  deriving Repr, BEq

mutual
  inductive Decl where
    | local (var : Variable)
    | label (label : LabelProxy)
    deriving Repr, BEq

  inductive Assignee where
    | var (source : Source) (op : VarRef)
    | field (source : Source) (op : Expr)
    | index (source : Source) (op : Expr)
    deriving Repr, BEq

  structure ArrayLitElem where
    key : Int
    value : Expr
    deriving Repr, BEq

  inductive Expr where
    | var (ref : VarRef)
    | nilLit (source : Source) (typ : Ty)
    | intLit (source : Source) (value : Int) (kind : IntegerKind) (base : Nat)
    | boolLit (source : Source) (value : Bool)
    | add (source : Source) (left right : Expr)
    | sub (source : Source) (left right : Expr)
    | mul (source : Source) (left right : Expr)
    | div (source : Source) (left right : Expr)
    | mod (source : Source) (left right : Expr)
    | eqCmp (source : Source) (left right : Expr)
    | uneqCmp (source : Source) (left right : Expr)
    | atMostCmp (source : Source) (left right : Expr)
    | atLeastCmp (source : Source) (left right : Expr)
    | lessCmp (source : Source) (left right : Expr)
    | greaterCmp (source : Source) (left right : Expr)
    | and (source : Source) (left right : Expr)
    | or (source : Source) (left right : Expr)
    | negation (source : Source) (operand : Expr)
    | deref (source : Source) (exp : Expr) (underlyingTypeExpr : Ty)
    | fieldRef (source : Source) (recv : Expr) (field : FieldInfo)
    | address (source : Source) (op : Expr)
    | ref (source : Source) (ref : Assignee) (typ : Ty)
    | arrayLit (source : Source) (length : Int) (memberType : Ty)
        (elems : Array ArrayLitElem)
    | dfltVal (source : Source) (typ : Ty)
    | indexedExp (source : Source) (base index : Expr) (baseUnderlyingType : Ty)
    | slice (source : Source) (base low high : Expr) (max : Option Expr) (baseUnderlyingType : Ty)
    | length (source : Source) (exp : Expr)
    | capacity (source : Source) (exp : Expr)
    | old (source : Source) (operand : Expr)
    | structLit (source : Source) (typ : Ty) (args : Array Expr)
    | pureMethodCall (source : Source) (recv : Expr) (meth : MethodProxy)
        (args : Array Expr) (typ : Ty) (reveal : Bool)
    | mPredicateAccess (source : Source) (recv : Expr) (pred : MethodProxy)
        (args : Array Expr)
    | predicate (source : Source) (op : Expr)
    deriving Repr, BEq

  inductive Permission where
    | full (source : Source)
    | wildcard (source : Source)
    deriving Repr, BEq

  inductive Assertion where
    | expr (expr : Expr)
    | exprAssertion (source : Source) (exp : Expr)
    | access (source : Source) (e : Expr) (p : Permission)
    | sepAnd (source : Source) (left right : Assertion)
    | implication (source : Source) (left right : Assertion)
    deriving Repr, BEq

  inductive Stmt where
    | seqn (source : Source) (stmts : Array Stmt)
    | block (source : Source) (decls : Array Decl) (stmts : Array Stmt)
    | initialization (source : Source) (left : Variable)
    | singleAss (source : Source) (left : Assignee) (right : Expr)
    | makeSlice (source : Source) (target : Variable) (typeParam : Ty)
        (lenArg : Expr) (capArg : Option Expr)
    | newSliceLit (source : Source) (target : Variable) (memberType : Ty)
        (elems : Array ArrayLitElem)
    | goSliceAppend (source : Source) (target : Variable) (slice elems : Expr)
    | goSliceCopy (source : Source) (target : Variable) (dst src : Expr)
    | assert (source : Source) (ass : Assertion)
    | ifStmt (source : Source) (cond : Expr) (thn els : Stmt)
    | while (source : Source) (cond : Expr) (invs : Array Assertion)
        (terminationMeasure : Option TerminationMeasure) (body : Stmt)
    | returnStmt (source : Source)
    | breakStmt (source : Source) (label : Option String) (escLabel : String)
    | continueStmt (source : Source) (label : Option String) (escLabel : String)
    | label (source : Source) (id : LabelProxy)
    | functionCall (source : Source) (func : FunctionProxy)
        (targets : Array Assignee) (args : Array Expr)
    | methodCall (source : Source) (recv : Expr) (meth : MethodProxy)
        (targets : Array Assignee) (args : Array Expr)
    deriving Repr, BEq

  structure MethodBodySeqn where
    source : Source
    stmts : Array Stmt
    deriving Repr, BEq

  structure MethodBody where
    source : Source
    decls : Array Decl
    seqn : MethodBodySeqn
    postprocessing : Array Stmt
    deriving Repr, BEq

  inductive TerminationMeasure where
    | itfTuple (source : Source) (tuple : Array Assertion) (cond : Option Expr)
    | nonItfTuple (source : Source) (tuple : Array Assertion) (cond : Option Expr)
    deriving Repr, BEq
end

structure FunctionMember where
  source : Source
  name : FunctionProxy
  args : Array Parameter
  results : Array Parameter
  pres : Array Assertion
  posts : Array Assertion
  terminationMeasures : Array TerminationMeasure
  backendAnnotations : Array BackendAnnotation
  body : Option MethodBody
  deriving Repr, BEq

structure MethodMember where
  source : Source
  receiver : Parameter
  name : MethodProxy
  args : Array Parameter
  results : Array Parameter
  pres : Array Assertion
  posts : Array Assertion
  terminationMeasures : Array TerminationMeasure
  backendAnnotations : Array BackendAnnotation
  body : Option MethodBody
  isPure : Bool
  isOpaque : Bool
  deriving Repr, BEq

structure MPredicateMember where
  source : Source
  receiver : Parameter
  name : MethodProxy
  args : Array Parameter
  body : Option Assertion
  deriving Repr, BEq

inductive Member where
  | function (member : FunctionMember)
  | method (member : MethodMember)
  | mPredicate (member : MPredicateMember)
  deriving Repr, BEq

structure Program where
  source : Source
  types : Array Ty
  members : Array Member
  deriving Repr, BEq

structure Document where
  schema : Schema
  inputs : Array String
  program : Program
  deriving Repr, BEq

private def taggedObj (path : String) (json : Json) (tag : String) (expected : List String) :
    Except String GoLean.StrictJson.Obj := do
  let obj ← GoLean.StrictJson.obj path json
  GoLean.StrictJson.requireExactKeys path obj expected
  let actual ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  if actual == tag then
    return obj
  else
    throw s!"{path}.tag: expected {repr tag}, got {repr actual}"

private def decodeLineColumn (path : String) (json : Json) : Except String LineColumn := do
  let obj ← GoLean.StrictJson.obj path json
  GoLean.StrictJson.requireExactKeys path obj ["column", "line"]
  let line ← GoLean.StrictJson.nat s!"{path}.line" (← GoLean.StrictJson.field path obj "line")
  let column ← GoLean.StrictJson.nat s!"{path}.column" (← GoLean.StrictJson.field path obj "column")
  return { line, column }

private def decodePosition (path : String) (json : Json) : Except String Position := do
  let obj ← GoLean.StrictJson.obj path json
  GoLean.StrictJson.requireExactKeys path obj ["end", "file", "start"]
  let file ← GoLean.StrictJson.string s!"{path}.file" (← GoLean.StrictJson.field path obj "file")
  let start ← decodeLineColumn s!"{path}.start" (← GoLean.StrictJson.field path obj "start")
  let endJson ← GoLean.StrictJson.field path obj "end"
  let endPos ←
    match endJson with
    | .null => pure none
    | _ => do
        let lineColumn ← decodeLineColumn s!"{path}.end" endJson
        pure (some lineColumn)
  return { file, start, «end» := endPos }

private def decodeOrigin (path : String) (json : Json) : Except String Origin := do
  let obj ← GoLean.StrictJson.obj path json
  GoLean.StrictJson.requireExactKeys path obj ["position", "tag"]
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  let position ← decodePosition s!"{path}.position" (← GoLean.StrictJson.field path obj "position")
  return { tag, position }

private def decodeSource (path : String) (json : Json) : Except String Source := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "Internal" =>
      GoLean.StrictJson.requireExactKeys path obj ["tag"]
      return .internal
  | "Single" =>
      GoLean.StrictJson.requireExactKeys path obj ["origin", "tag"]
      return .single (← decodeOrigin s!"{path}.origin" (← GoLean.StrictJson.field path obj "origin"))
  | other =>
      throw s!"{path}.tag: expected source tag, got {repr other}"

private def decodeAddressability (path : String) (json : Json) : Except String Addressability := do
  match ← GoLean.StrictJson.string path json with
  | "shared" => return .shared
  | "exclusive" => return .exclusive
  | other => throw s!"{path}: unknown addressability {repr other}"

private def decodeIntegerKind (path : String) (json : Json) : Except String IntegerKind := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "UnboundedInteger" =>
      GoLean.StrictJson.requireExactKeys path obj ["name", "tag"]
      return .unbounded (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name"))
  | "BoundedInteger" =>
      GoLean.StrictJson.requireExactKeys path obj ["bits", "lower", "name", "tag", "upper"]
      let name ← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name")
      let bits ← GoLean.StrictJson.nat s!"{path}.bits" (← GoLean.StrictJson.field path obj "bits")
      let lower ← GoLean.StrictJson.int s!"{path}.lower" (← GoLean.StrictJson.field path obj "lower")
      let upper ← GoLean.StrictJson.int s!"{path}.upper" (← GoLean.StrictJson.field path obj "upper")
      return .bounded name bits lower upper
  | other =>
      throw s!"{path}.tag: expected integer kind tag, got {repr other}"

private def decodeArrayOf {α : Type} (path : String) (json : Json)
    (decodeOne : String → Json → Except String α) : Except String (Array α) := do
  let values ← GoLean.StrictJson.array path json
  GoLean.StrictJson.mapArrayIdx values (fun i value => decodeOne s!"{path}[{i}]" value)

mutual
  partial def decodeTy (path : String) (json : Json) : Except String Ty := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    let addr (fields : List String) : Except String Addressability := do
      GoLean.StrictJson.requireExactKeys path obj fields
      decodeAddressability s!"{path}.addressability" (← GoLean.StrictJson.field path obj "addressability")
    match tag with
    | "BoolT" => return .bool (← addr ["addressability", "tag"])
    | "IntT" =>
        let a ← addr ["addressability", "kind", "tag"]
        let k ← decodeIntegerKind s!"{path}.kind" (← GoLean.StrictJson.field path obj "kind")
        return .int a k
    | "Float32T" => return .float32 (← addr ["addressability", "tag"])
    | "Float64T" => return .float64 (← addr ["addressability", "tag"])
    | "StringT" => return .string (← addr ["addressability", "tag"])
    | "VoidT" =>
        GoLean.StrictJson.requireExactKeys path obj ["tag"]
        return .void
    | "FunctionT" =>
        let a ← addr ["addressability", "args", "results", "tag"]
        return .function
          (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeTy)
          (← decodeArrayOf s!"{path}.results" (← GoLean.StrictJson.field path obj "results") decodeTy)
          a
    | "PermissionT" => return .permission (← addr ["addressability", "tag"])
    | "SortT" =>
        GoLean.StrictJson.requireExactKeys path obj ["tag"]
        return .sort
    | "ArrayT" =>
        let a ← addr ["addressability", "elems", "length", "tag"]
        return .array (← GoLean.StrictJson.int s!"{path}.length" (← GoLean.StrictJson.field path obj "length"))
          (← decodeTy s!"{path}.elems" (← GoLean.StrictJson.field path obj "elems")) a
    | "SliceT" =>
        let a ← addr ["addressability", "elems", "tag"]
        return .slice (← decodeTy s!"{path}.elems" (← GoLean.StrictJson.field path obj "elems")) a
    | "MapT" =>
        let a ← addr ["addressability", "keys", "tag", "values"]
        return .map (← decodeTy s!"{path}.keys" (← GoLean.StrictJson.field path obj "keys"))
          (← decodeTy s!"{path}.values" (← GoLean.StrictJson.field path obj "values")) a
    | "SequenceT" =>
        let a ← addr ["addressability", "elem", "tag"]
        return .sequence (← decodeTy s!"{path}.elem" (← GoLean.StrictJson.field path obj "elem")) a
    | "SetT" =>
        let a ← addr ["addressability", "elem", "tag"]
        return .set (← decodeTy s!"{path}.elem" (← GoLean.StrictJson.field path obj "elem")) a
    | "MultisetT" =>
        let a ← addr ["addressability", "elem", "tag"]
        return .multiset (← decodeTy s!"{path}.elem" (← GoLean.StrictJson.field path obj "elem")) a
    | "MathMapT" =>
        let a ← addr ["addressability", "keys", "tag", "values"]
        return .mathMap (← decodeTy s!"{path}.keys" (← GoLean.StrictJson.field path obj "keys"))
          (← decodeTy s!"{path}.values" (← GoLean.StrictJson.field path obj "values")) a
    | "OptionT" =>
        let a ← addr ["addressability", "elem", "tag"]
        return .option (← decodeTy s!"{path}.elem" (← GoLean.StrictJson.field path obj "elem")) a
    | "DefinedT" =>
        let a ← addr ["addressability", "name", "tag"]
        return .defined (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name")) a
    | "PointerT" =>
        let a ← addr ["addressability", "elem", "tag"]
        return .pointer (← decodeTy s!"{path}.elem" (← GoLean.StrictJson.field path obj "elem")) a
    | "TupleT" =>
        let a ← addr ["addressability", "tag", "types"]
        return .tuple (← decodeArrayOf s!"{path}.types" (← GoLean.StrictJson.field path obj "types") decodeTy) a
    | "PredT" =>
        let a ← addr ["addressability", "args", "tag"]
        return .pred (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeTy) a
    | "StructT" =>
        let a ← addr ["addressability", "fields", "ghost", "tag"]
        return .struct (← decodeArrayOf s!"{path}.fields" (← GoLean.StrictJson.field path obj "fields") decodeFieldInfo)
          (← GoLean.StrictJson.bool s!"{path}.ghost" (← GoLean.StrictJson.field path obj "ghost")) a
    | "InterfaceT" =>
        let a ← addr ["addressability", "name", "tag"]
        return .interface (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name")) a
    | "DomainT" =>
        let a ← addr ["addressability", "name", "tag"]
        return .domain (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name")) a
    | "AdtT" =>
        let a ← addr ["addressability", "definedName", "name", "tag"]
        return .adt (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name"))
          (← GoLean.StrictJson.string s!"{path}.definedName" (← GoLean.StrictJson.field path obj "definedName")) a
    | "AdtClauseT" =>
        let a ← addr ["addressability", "adt", "fields", "name", "tag"]
        return .adtClause (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name"))
          (← decodeTy s!"{path}.adt" (← GoLean.StrictJson.field path obj "adt"))
          (← decodeArrayOf s!"{path}.fields" (← GoLean.StrictJson.field path obj "fields") decodeFieldInfo) a
    | "ChannelT" =>
        let a ← addr ["addressability", "elem", "tag"]
        return .channel (← decodeTy s!"{path}.elem" (← GoLean.StrictJson.field path obj "elem")) a
    | other => throw s!"{path}.tag: unsupported type tag {repr other}"

  partial def decodeFieldInfo (path : String) (json : Json) : Except String FieldInfo := do
    let obj ← taggedObj path json "Field" ["ghost", "name", "source", "tag", "typ"]
    return {
      source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
      name := (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name")),
      typ := (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ")),
      ghost := (← GoLean.StrictJson.bool s!"{path}.ghost" (← GoLean.StrictJson.field path obj "ghost"))
    }
end

private def decodeParameterWithTag (tag path : String) (json : Json) : Except String Parameter := do
  let obj ← taggedObj path json tag ["id", "source", "tag", "typ"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    id := (← GoLean.StrictJson.string s!"{path}.id" (← GoLean.StrictJson.field path obj "id")),
    typ := (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
  }

private def decodeParam (path : String) (json : Json) : Except String Parameter := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "In" => decodeParameterWithTag "In" path json
  | "Out" => decodeParameterWithTag "Out" path json
  | other => throw s!"{path}.tag: expected parameter tag, got {repr other}"

private def decodeVariableWithTag (tag path : String) (json : Json) : Except String Variable := do
  let obj ← taggedObj path json tag ["id", "source", "tag", "typ"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    id := (← GoLean.StrictJson.string s!"{path}.id" (← GoLean.StrictJson.field path obj "id")),
    typ := (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
  }

private def decodeVarRef (path : String) (json : Json) : Except String VarRef := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "LocalVar" => return .local (← decodeVariableWithTag "LocalVar" path json)
  | "In" => return .inParam (← decodeParameterWithTag "In" path json)
  | "Out" => return .outParam (← decodeParameterWithTag "Out" path json)
  | other => throw s!"{path}.tag: expected variable reference tag, got {repr other}"

private def decodeFunctionProxy (path : String) (json : Json) : Except String FunctionProxy := do
  let obj ← taggedObj path json "FunctionProxy" ["name", "source", "tag"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    name := (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name"))
  }

private def decodeMethodProxyWithTag (tag path : String) (json : Json) : Except String MethodProxy := do
  let obj ← taggedObj path json tag ["name", "source", "tag", "uniqueName"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    name := (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name")),
    uniqueName := (← GoLean.StrictJson.string s!"{path}.uniqueName" (← GoLean.StrictJson.field path obj "uniqueName"))
  }

private def decodeLabelProxy (path : String) (json : Json) : Except String LabelProxy := do
  let obj ← taggedObj path json "LabelProxy" ["name", "source", "tag"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    name := (← GoLean.StrictJson.string s!"{path}.name" (← GoLean.StrictJson.field path obj "name"))
  }

private def decodeOptionOf {α : Type} (path : String) (json : Json)
    (decodeOne : String → Json → Except String α) : Except String (Option α) := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "None" =>
      GoLean.StrictJson.requireExactKeys path obj ["tag"]
      return none
  | "Some" =>
      GoLean.StrictJson.requireExactKeys path obj ["tag", "value"]
      return some (← decodeOne s!"{path}.value" (← GoLean.StrictJson.field path obj "value"))
  | other =>
      throw s!"{path}.tag: expected Option tag, got {repr other}"

private def decodeDecimalBase (path : String) (json : Json) : Except String Nat := do
  let obj ← taggedObj path json "Decimal" ["base", "tag"]
  GoLean.StrictJson.nat s!"{path}.base" (← GoLean.StrictJson.field path obj "base")

private def decodeBackendAnnotation (path : String) (_json : Json) : Except String BackendAnnotation :=
  throw s!"{path}: unsupported backend annotation"

mutual
  partial def decodeDecl (path : String) (json : Json) : Except String Decl := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    match tag with
    | "LocalVar" => return .local (← decodeVariableWithTag "LocalVar" path json)
    | "LabelProxy" => return .label (← decodeLabelProxy path json)
    | other => throw s!"{path}.tag: unsupported declaration tag {repr other}"

  partial def decodeAssignee (path : String) (json : Json) : Except String Assignee := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    match tag with
    | "LocalVar" | "In" | "Out" =>
        return .var
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVarRef path json)
    | "Var" =>
        let obj ← taggedObj path json "Var" ["op", "source", "tag"]
        return .var
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVarRef s!"{path}.op" (← GoLean.StrictJson.field path obj "op"))
    | "Field" =>
        let obj ← taggedObj path json "Field" ["op", "source", "tag"]
        return .field
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.op" (← GoLean.StrictJson.field path obj "op"))
    | "Index" =>
        let obj ← taggedObj path json "Index" ["op", "source", "tag"]
        return .index
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.op" (← GoLean.StrictJson.field path obj "op"))
    | other => throw s!"{path}.tag: unsupported assignee tag {repr other}"

  partial def decodeArrayLitElem (path : String) (json : Json) : Except String ArrayLitElem := do
    let obj ← GoLean.StrictJson.obj path json
    GoLean.StrictJson.requireExactKeys path obj ["key", "value"]
    return {
      key := (← GoLean.StrictJson.int s!"{path}.key" (← GoLean.StrictJson.field path obj "key")),
      value := (← decodeExpr s!"{path}.value" (← GoLean.StrictJson.field path obj "value"))
    }

  partial def decodeExpr (path : String) (json : Json) : Except String Expr := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    let binary (expected : String) (mk : Source → Expr → Expr → Expr) : Except String Expr := do
      let obj ← taggedObj path json expected ["left", "right", "source", "tag"]
      return mk
        (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
        (← decodeExpr s!"{path}.left" (← GoLean.StrictJson.field path obj "left"))
        (← decodeExpr s!"{path}.right" (← GoLean.StrictJson.field path obj "right"))
    match tag with
    | "LocalVar" | "In" | "Out" => return .var (← decodeVarRef path json)
    | "NilLit" =>
        let obj ← taggedObj path json "NilLit" ["source", "tag", "typ"]
        return .nilLit
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
    | "IntLit" =>
        let obj ← taggedObj path json "IntLit" ["base", "kind", "source", "tag", "v"]
        return .intLit
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← GoLean.StrictJson.int s!"{path}.v" (← GoLean.StrictJson.field path obj "v"))
          (← decodeIntegerKind s!"{path}.kind" (← GoLean.StrictJson.field path obj "kind"))
          (← decodeDecimalBase s!"{path}.base" (← GoLean.StrictJson.field path obj "base"))
    | "BoolLit" =>
        let obj ← taggedObj path json "BoolLit" ["b", "source", "tag"]
        return .boolLit
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← GoLean.StrictJson.bool s!"{path}.b" (← GoLean.StrictJson.field path obj "b"))
    | "Add" => binary "Add" .add
    | "Sub" => binary "Sub" .sub
    | "Mul" => binary "Mul" .mul
    | "Div" => binary "Div" .div
    | "Mod" => binary "Mod" .mod
    | "EqCmp" => binary "EqCmp" .eqCmp
    | "UneqCmp" => binary "UneqCmp" .uneqCmp
    | "AtMostCmp" => binary "AtMostCmp" .atMostCmp
    | "AtLeastCmp" => binary "AtLeastCmp" .atLeastCmp
    | "LessCmp" => binary "LessCmp" .lessCmp
    | "GreaterCmp" => binary "GreaterCmp" .greaterCmp
    | "And" => binary "And" .and
    | "Or" => binary "Or" .or
    | "Negation" =>
        let obj ← taggedObj path json "Negation" ["operand", "source", "tag"]
        return .negation
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.operand" (← GoLean.StrictJson.field path obj "operand"))
    | "Deref" =>
        let obj ← taggedObj path json "Deref" ["exp", "source", "tag", "underlyingTypeExpr"]
        return .deref
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.exp" (← GoLean.StrictJson.field path obj "exp"))
          (← decodeTy s!"{path}.underlyingTypeExpr" (← GoLean.StrictJson.field path obj "underlyingTypeExpr"))
    | "FieldRef" =>
        let obj ← taggedObj path json "FieldRef" ["field", "recv", "source", "tag"]
        return .fieldRef
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.recv" (← GoLean.StrictJson.field path obj "recv"))
          (← decodeFieldInfo s!"{path}.field" (← GoLean.StrictJson.field path obj "field"))
    | "Address" =>
        let obj ← taggedObj path json "Address" ["op", "source", "tag"]
        return .address
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.op" (← GoLean.StrictJson.field path obj "op"))
    | "Ref" =>
        let obj ← taggedObj path json "Ref" ["ref", "source", "tag", "typ"]
        return .ref
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeAssignee s!"{path}.ref" (← GoLean.StrictJson.field path obj "ref"))
          (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
    | "ArrayLit" =>
        let obj ← taggedObj path json "ArrayLit" ["elems", "length", "memberType", "source", "tag"]
        return .arrayLit
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← GoLean.StrictJson.int s!"{path}.length" (← GoLean.StrictJson.field path obj "length"))
          (← decodeTy s!"{path}.memberType" (← GoLean.StrictJson.field path obj "memberType"))
          (← decodeArrayOf s!"{path}.elems" (← GoLean.StrictJson.field path obj "elems") decodeArrayLitElem)
    | "DfltVal" =>
        let obj ← taggedObj path json "DfltVal" ["source", "tag", "typ"]
        return .dfltVal
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
    | "IndexedExp" =>
        let obj ← taggedObj path json "IndexedExp" ["base", "baseUnderlyingType", "index", "source", "tag"]
        return .indexedExp
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.base" (← GoLean.StrictJson.field path obj "base"))
          (← decodeExpr s!"{path}.index" (← GoLean.StrictJson.field path obj "index"))
          (← decodeTy s!"{path}.baseUnderlyingType" (← GoLean.StrictJson.field path obj "baseUnderlyingType"))
    | "Slice" =>
        let obj ← taggedObj path json "Slice" ["base", "baseUnderlyingType", "high", "low", "max", "source", "tag"]
        return .slice
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.base" (← GoLean.StrictJson.field path obj "base"))
          (← decodeExpr s!"{path}.low" (← GoLean.StrictJson.field path obj "low"))
          (← decodeExpr s!"{path}.high" (← GoLean.StrictJson.field path obj "high"))
          (← decodeOptionOf s!"{path}.max" (← GoLean.StrictJson.field path obj "max") decodeExpr)
          (← decodeTy s!"{path}.baseUnderlyingType" (← GoLean.StrictJson.field path obj "baseUnderlyingType"))
    | "Length" =>
        let obj ← taggedObj path json "Length" ["exp", "source", "tag"]
        return .length
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.exp" (← GoLean.StrictJson.field path obj "exp"))
    | "Capacity" =>
        let obj ← taggedObj path json "Capacity" ["exp", "source", "tag"]
        return .capacity
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.exp" (← GoLean.StrictJson.field path obj "exp"))
    | "Old" =>
        let obj ← taggedObj path json "Old" ["operand", "source", "tag"]
        return .old
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.operand" (← GoLean.StrictJson.field path obj "operand"))
    | "StructLit" =>
        let obj ← taggedObj path json "StructLit" ["args", "source", "tag", "typ"]
        return .structLit
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
          (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeExpr)
    | "PureMethodCall" =>
        let obj ← taggedObj path json "PureMethodCall" ["args", "meth", "recv", "reveal", "source", "tag", "typ"]
        return .pureMethodCall
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.recv" (← GoLean.StrictJson.field path obj "recv"))
          (← decodeMethodProxyWithTag "MethodProxy" s!"{path}.meth" (← GoLean.StrictJson.field path obj "meth"))
          (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeExpr)
          (← decodeTy s!"{path}.typ" (← GoLean.StrictJson.field path obj "typ"))
          (← GoLean.StrictJson.bool s!"{path}.reveal" (← GoLean.StrictJson.field path obj "reveal"))
    | "MPredicateAccess" =>
        let obj ← taggedObj path json "MPredicateAccess" ["args", "pred", "recv", "source", "tag"]
        return .mPredicateAccess
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.recv" (← GoLean.StrictJson.field path obj "recv"))
          (← decodeMethodProxyWithTag "MPredicateProxy" s!"{path}.pred" (← GoLean.StrictJson.field path obj "pred"))
          (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeExpr)
    | "Predicate" =>
        let obj ← taggedObj path json "Predicate" ["op", "source", "tag"]
        return .predicate
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.op" (← GoLean.StrictJson.field path obj "op"))
    | other => throw s!"{path}.tag: unsupported expression tag {repr other}"

  partial def decodePermission (path : String) (json : Json) : Except String Permission := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    match tag with
    | "FullPerm" =>
        let obj ← taggedObj path json "FullPerm" ["source", "tag"]
        return .full (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
    | "WildcardPerm" =>
        let obj ← taggedObj path json "WildcardPerm" ["source", "tag"]
        return .wildcard (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
    | other => throw s!"{path}.tag: unsupported permission tag {repr other}"

  partial def decodeAssertion (path : String) (json : Json) : Except String Assertion := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    match tag with
    | "ExprAssertion" =>
        let obj ← taggedObj path json "ExprAssertion" ["exp", "source", "tag"]
        return .exprAssertion
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.exp" (← GoLean.StrictJson.field path obj "exp"))
    | "Access" =>
        let obj ← taggedObj path json "Access" ["e", "p", "source", "tag"]
        return .access
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.e" (← GoLean.StrictJson.field path obj "e"))
          (← decodePermission s!"{path}.p" (← GoLean.StrictJson.field path obj "p"))
    | "SepAnd" =>
        let obj ← taggedObj path json "SepAnd" ["left", "right", "source", "tag"]
        return .sepAnd
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeAssertion s!"{path}.left" (← GoLean.StrictJson.field path obj "left"))
          (← decodeAssertion s!"{path}.right" (← GoLean.StrictJson.field path obj "right"))
    | "Implication" =>
        let obj ← taggedObj path json "Implication" ["left", "right", "source", "tag"]
        return .implication
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeAssertion s!"{path}.left" (← GoLean.StrictJson.field path obj "left"))
          (← decodeAssertion s!"{path}.right" (← GoLean.StrictJson.field path obj "right"))
    | _ =>
        return .expr (← decodeExpr path json)

  partial def decodeStmt (path : String) (json : Json) : Except String Stmt := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    match tag with
    | "Seqn" =>
        let obj ← taggedObj path json "Seqn" ["source", "stmts", "tag"]
        return .seqn
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeArrayOf s!"{path}.stmts" (← GoLean.StrictJson.field path obj "stmts") decodeStmt)
    | "Block" =>
        let obj ← taggedObj path json "Block" ["decls", "source", "stmts", "tag"]
        return .block
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeArrayOf s!"{path}.decls" (← GoLean.StrictJson.field path obj "decls") decodeDecl)
          (← decodeArrayOf s!"{path}.stmts" (← GoLean.StrictJson.field path obj "stmts") decodeStmt)
    | "Initialization" =>
        let obj ← taggedObj path json "Initialization" ["left", "source", "tag"]
        return .initialization
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVariableWithTag "LocalVar" s!"{path}.left" (← GoLean.StrictJson.field path obj "left"))
    | "SingleAss" =>
        let obj ← taggedObj path json "SingleAss" ["left", "right", "source", "tag"]
        return .singleAss
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeAssignee s!"{path}.left" (← GoLean.StrictJson.field path obj "left"))
          (← decodeExpr s!"{path}.right" (← GoLean.StrictJson.field path obj "right"))
    | "MakeSlice" =>
        let obj ← taggedObj path json "MakeSlice" ["capArg", "lenArg", "source", "tag", "target", "typeParam"]
        return .makeSlice
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVariableWithTag "LocalVar" s!"{path}.target" (← GoLean.StrictJson.field path obj "target"))
          (← decodeTy s!"{path}.typeParam" (← GoLean.StrictJson.field path obj "typeParam"))
          (← decodeExpr s!"{path}.lenArg" (← GoLean.StrictJson.field path obj "lenArg"))
          (← decodeOptionOf s!"{path}.capArg" (← GoLean.StrictJson.field path obj "capArg") decodeExpr)
    | "NewSliceLit" =>
        let obj ← taggedObj path json "NewSliceLit" ["elems", "memberType", "source", "tag", "target"]
        return .newSliceLit
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVariableWithTag "LocalVar" s!"{path}.target" (← GoLean.StrictJson.field path obj "target"))
          (← decodeTy s!"{path}.memberType" (← GoLean.StrictJson.field path obj "memberType"))
          (← decodeArrayOf s!"{path}.elems" (← GoLean.StrictJson.field path obj "elems") decodeArrayLitElem)
    | "GoSliceAppend" =>
        let obj ← taggedObj path json "GoSliceAppend" ["elems", "slice", "source", "tag", "target"]
        return .goSliceAppend
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVariableWithTag "LocalVar" s!"{path}.target" (← GoLean.StrictJson.field path obj "target"))
          (← decodeExpr s!"{path}.slice" (← GoLean.StrictJson.field path obj "slice"))
          (← decodeExpr s!"{path}.elems" (← GoLean.StrictJson.field path obj "elems"))
    | "GoSliceCopy" =>
        let obj ← taggedObj path json "GoSliceCopy" ["dst", "source", "src", "tag", "target"]
        return .goSliceCopy
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeVariableWithTag "LocalVar" s!"{path}.target" (← GoLean.StrictJson.field path obj "target"))
          (← decodeExpr s!"{path}.dst" (← GoLean.StrictJson.field path obj "dst"))
          (← decodeExpr s!"{path}.src" (← GoLean.StrictJson.field path obj "src"))
    | "Assert" =>
        let obj ← taggedObj path json "Assert" ["ass", "source", "tag"]
        return .assert
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeAssertion s!"{path}.ass" (← GoLean.StrictJson.field path obj "ass"))
    | "If" =>
        let obj ← taggedObj path json "If" ["cond", "els", "source", "tag", "thn"]
        return .ifStmt
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.cond" (← GoLean.StrictJson.field path obj "cond"))
          (← decodeStmt s!"{path}.thn" (← GoLean.StrictJson.field path obj "thn"))
          (← decodeStmt s!"{path}.els" (← GoLean.StrictJson.field path obj "els"))
    | "While" =>
        let obj ← taggedObj path json "While" ["body", "cond", "invs", "source", "tag", "terminationMeasure"]
        return .while
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.cond" (← GoLean.StrictJson.field path obj "cond"))
          (← decodeArrayOf s!"{path}.invs" (← GoLean.StrictJson.field path obj "invs") decodeAssertion)
          (← decodeOptionOf s!"{path}.terminationMeasure" (← GoLean.StrictJson.field path obj "terminationMeasure") decodeTerminationMeasure)
          (← decodeStmt s!"{path}.body" (← GoLean.StrictJson.field path obj "body"))
    | "Return" =>
        let obj ← taggedObj path json "Return" ["source", "tag"]
        return .returnStmt
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
    | "Break" =>
        let obj ← taggedObj path json "Break" ["escLabel", "label", "source", "tag"]
        return .breakStmt
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeOptionOf s!"{path}.label" (← GoLean.StrictJson.field path obj "label") GoLean.StrictJson.string)
          (← GoLean.StrictJson.string s!"{path}.escLabel" (← GoLean.StrictJson.field path obj "escLabel"))
    | "Continue" =>
        let obj ← taggedObj path json "Continue" ["escLabel", "label", "source", "tag"]
        return .continueStmt
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeOptionOf s!"{path}.label" (← GoLean.StrictJson.field path obj "label") GoLean.StrictJson.string)
          (← GoLean.StrictJson.string s!"{path}.escLabel" (← GoLean.StrictJson.field path obj "escLabel"))
    | "Label" =>
        let obj ← taggedObj path json "Label" ["id", "source", "tag"]
        return .label
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeLabelProxy s!"{path}.id" (← GoLean.StrictJson.field path obj "id"))
    | "FunctionCall" =>
        let obj ← taggedObj path json "FunctionCall" ["args", "func", "source", "tag", "targets"]
        return .functionCall
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeFunctionProxy s!"{path}.func" (← GoLean.StrictJson.field path obj "func"))
          (← decodeArrayOf s!"{path}.targets" (← GoLean.StrictJson.field path obj "targets") decodeAssignee)
          (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeExpr)
    | "MethodCall" =>
        let obj ← taggedObj path json "MethodCall" ["args", "meth", "recv", "source", "tag", "targets"]
        return .methodCall
          (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
          (← decodeExpr s!"{path}.recv" (← GoLean.StrictJson.field path obj "recv"))
          (← decodeMethodProxyWithTag "MethodProxy" s!"{path}.meth" (← GoLean.StrictJson.field path obj "meth"))
          (← decodeArrayOf s!"{path}.targets" (← GoLean.StrictJson.field path obj "targets") decodeAssignee)
          (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeExpr)
    | other => throw s!"{path}.tag: unsupported statement tag {repr other}"

  partial def decodeMethodBodySeqn (path : String) (json : Json) : Except String MethodBodySeqn := do
    let obj ← taggedObj path json "MethodBodySeqn" ["source", "stmts", "tag"]
    return {
      source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
      stmts := (← decodeArrayOf s!"{path}.stmts" (← GoLean.StrictJson.field path obj "stmts") decodeStmt)
    }

  partial def decodeMethodBody (path : String) (json : Json) : Except String MethodBody := do
    let obj ← taggedObj path json "MethodBody" ["decls", "postprocessing", "seqn", "source", "tag"]
    return {
      source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
      decls := (← decodeArrayOf s!"{path}.decls" (← GoLean.StrictJson.field path obj "decls") decodeDecl),
      seqn := (← decodeMethodBodySeqn s!"{path}.seqn" (← GoLean.StrictJson.field path obj "seqn")),
      postprocessing := (← decodeArrayOf s!"{path}.postprocessing" (← GoLean.StrictJson.field path obj "postprocessing") decodeStmt)
    }

  partial def decodeTerminationMeasure (path : String) (json : Json) : Except String TerminationMeasure := do
    let obj ← GoLean.StrictJson.obj path json
    let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
    let decodeTuple (expected : String) (mk : Source → Array Assertion → Option Expr → TerminationMeasure) := do
      let obj ← taggedObj path json expected ["cond", "source", "tag", "tuple"]
      return mk
        (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source"))
        (← decodeArrayOf s!"{path}.tuple" (← GoLean.StrictJson.field path obj "tuple") decodeAssertion)
        (← decodeOptionOf s!"{path}.cond" (← GoLean.StrictJson.field path obj "cond") decodeExpr)
    match tag with
    | "ItfTupleTerminationMeasure" => decodeTuple "ItfTupleTerminationMeasure" .itfTuple
    | "NonItfTupleTerminationMeasure" => decodeTuple "NonItfTupleTerminationMeasure" .nonItfTuple
    | other => throw s!"{path}.tag: unsupported termination measure tag {repr other}"
end

private def decodeFunctionMember (path : String) (json : Json) : Except String FunctionMember := do
  let obj ← taggedObj path json "Function" ["args", "backendAnnotations", "body", "name", "posts", "pres", "results", "source", "tag", "terminationMeasures"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    name := (← decodeFunctionProxy s!"{path}.name" (← GoLean.StrictJson.field path obj "name")),
    args := (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeParam),
    results := (← decodeArrayOf s!"{path}.results" (← GoLean.StrictJson.field path obj "results") decodeParam),
    pres := (← decodeArrayOf s!"{path}.pres" (← GoLean.StrictJson.field path obj "pres") decodeAssertion),
    posts := (← decodeArrayOf s!"{path}.posts" (← GoLean.StrictJson.field path obj "posts") decodeAssertion),
    terminationMeasures := (← decodeArrayOf s!"{path}.terminationMeasures" (← GoLean.StrictJson.field path obj "terminationMeasures") decodeTerminationMeasure),
    backendAnnotations := (← decodeArrayOf s!"{path}.backendAnnotations" (← GoLean.StrictJson.field path obj "backendAnnotations") decodeBackendAnnotation),
    body := (← decodeOptionOf s!"{path}.body" (← GoLean.StrictJson.field path obj "body") decodeMethodBody)
  }

private def decodeMethodMember (tag path : String) (isPure : Bool) (json : Json) : Except String MethodMember := do
  let expected :=
    if tag == "PureMethod" then
      ["args", "backendAnnotations", "body", "isOpaque", "name", "posts", "pres", "receiver", "results", "source", "tag", "terminationMeasures"]
    else
      ["args", "backendAnnotations", "body", "name", "posts", "pres", "receiver", "results", "source", "tag", "terminationMeasures"]
  let obj ← taggedObj path json tag expected
  let isOpaque ←
    if tag == "PureMethod" then
      GoLean.StrictJson.bool s!"{path}.isOpaque" (← GoLean.StrictJson.field path obj "isOpaque")
    else
      pure false
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    receiver := (← decodeParameterWithTag "In" s!"{path}.receiver" (← GoLean.StrictJson.field path obj "receiver")),
    name := (← decodeMethodProxyWithTag "MethodProxy" s!"{path}.name" (← GoLean.StrictJson.field path obj "name")),
    args := (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeParam),
    results := (← decodeArrayOf s!"{path}.results" (← GoLean.StrictJson.field path obj "results") decodeParam),
    pres := (← decodeArrayOf s!"{path}.pres" (← GoLean.StrictJson.field path obj "pres") decodeAssertion),
    posts := (← decodeArrayOf s!"{path}.posts" (← GoLean.StrictJson.field path obj "posts") decodeAssertion),
    terminationMeasures := (← decodeArrayOf s!"{path}.terminationMeasures" (← GoLean.StrictJson.field path obj "terminationMeasures") decodeTerminationMeasure),
    backendAnnotations := (← decodeArrayOf s!"{path}.backendAnnotations" (← GoLean.StrictJson.field path obj "backendAnnotations") decodeBackendAnnotation),
    body := (← decodeOptionOf s!"{path}.body" (← GoLean.StrictJson.field path obj "body") decodeMethodBody),
    isPure,
    isOpaque
  }

private def decodeMPredicateMember (path : String) (json : Json) : Except String MPredicateMember := do
  let obj ← taggedObj path json "MPredicate" ["args", "body", "name", "receiver", "source", "tag"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    receiver := (← decodeParameterWithTag "In" s!"{path}.receiver" (← GoLean.StrictJson.field path obj "receiver")),
    name := (← decodeMethodProxyWithTag "MPredicateProxy" s!"{path}.name" (← GoLean.StrictJson.field path obj "name")),
    args := (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeParam),
    body := (← decodeOptionOf s!"{path}.body" (← GoLean.StrictJson.field path obj "body") decodeAssertion)
  }

private def decodeMember (path : String) (json : Json) : Except String Member := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "Function" => return .function (← decodeFunctionMember path json)
  | "Method" => return .method (← decodeMethodMember "Method" path false json)
  | "PureMethod" => return .method (← decodeMethodMember "PureMethod" path true json)
  | "MPredicate" => return .mPredicate (← decodeMPredicateMember path json)
  | other => throw s!"{path}.tag: unsupported member tag {repr other}"

private def decodeProgram (path : String) (json : Json) : Except String Program := do
  let obj ← taggedObj path json "Program" ["members", "source", "tag", "types"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    types := (← decodeArrayOf s!"{path}.types" (← GoLean.StrictJson.field path obj "types") decodeTy),
    members := (← decodeArrayOf s!"{path}.members" (← GoLean.StrictJson.field path obj "members") decodeMember)
  }

private def decodeSchema (json : Json) : Except String Schema := do
  let obj ← GoLean.StrictJson.obj "schema" json
  GoLean.StrictJson.requireExactKeys "schema" obj ["encoding", "failClosed", "name", "version"]
  let name ← GoLean.StrictJson.string "schema.name" (← GoLean.StrictJson.field "schema" obj "name")
  let version ← GoLean.StrictJson.nat "schema.version" (← GoLean.StrictJson.field "schema" obj "version")
  let encoding ← GoLean.StrictJson.string "schema.encoding" (← GoLean.StrictJson.field "schema" obj "encoding")
  let failClosed ← GoLean.StrictJson.bool "schema.failClosed" (← GoLean.StrictJson.field "schema" obj "failClosed")
  if name != "gobra.internal" then
    throw s!"schema.name: expected 'gobra.internal', got {repr name}"
  if version != 1 then
    throw s!"schema.version: expected 1, got {version}"
  if encoding != "structural-adt" then
    throw s!"schema.encoding: expected 'structural-adt', got {repr encoding}"
  if !failClosed then
    throw "schema.failClosed: expected true"
  return { name, version, encoding, failClosed }

private def decodeInputs (json : Json) : Except String (Array String) := do
  let inputs ← GoLean.StrictJson.array "inputs" json
  GoLean.StrictJson.mapArrayIdx inputs (fun i value => GoLean.StrictJson.string s!"inputs[{i}]" value)

def decode (json : Json) : Except String Document := do
  let obj ← GoLean.StrictJson.obj "document" json
  GoLean.StrictJson.requireExactKeys "document" obj ["inputs", "program", "schema"]
  let schema ← decodeSchema (← GoLean.StrictJson.field "document" obj "schema")
  let inputs ← decodeInputs (← GoLean.StrictJson.field "document" obj "inputs")
  let program ← decodeProgram "program" (← GoLean.StrictJson.field "document" obj "program")
  return { schema, inputs, program }

def decodeString (contents : String) : Except String Document := do
  decode (← Json.parse contents)

def decodeFile (path : FilePath) : IO (Except String Document) := do
  return decodeString (← IO.FS.readFile path)

partial def collectTags (json : Json) : List String :=
  match json with
  | .null | .bool _ | .num _ | .str _ => []
  | .arr values => (values.toList.map collectTags).foldr (fun tags acc => tags ++ acc) []
  | .obj obj =>
      let childTags := ((GoLean.StrictJson.keys obj).map (fun key =>
        match obj.get? key with
        | some value => collectTags value
        | none => [])).foldr (fun tags acc => tags ++ acc) []
      let ownTag :=
        if GoLean.StrictJson.exactKeys obj ["position", "tag"] then
          []
        else
          match obj.get? "tag" with
          | some (.str tag) => [tag]
          | _ => []
      ownTag ++ childTags

def uniqueTags (tags : List String) : List String :=
  tags.eraseDups

def unknownTags (tags : List String) : List String :=
  uniqueTags tags |>.filter (fun tag => !isKnownTagName tag)

end GoLean.GobraJson
