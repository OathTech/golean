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
  "Access", "Add", "Address", "Assert", "AtLeastCmp", "AtMostCmp",
  "Block", "BoolLit", "BoolT", "BoundedInteger", "Decimal", "DefinedT",
  "Deref", "EqCmp", "ExprAssertion", "Field", "FieldRef", "FullPerm",
  "Function", "FunctionCall", "FunctionProxy", "Implication", "In",
  "Initialization", "IntLit", "IntT", "InterfaceT", "Internal", "ItfTupleTerminationMeasure",
  "Label", "LabelProxy", "LessCmp", "LocalVar", "MPredicate",
  "MPredicateAccess", "MPredicateProxy", "Method", "MethodBody", "MethodBodySeqn",
  "MethodCall", "MethodProxy", "Mul", "NonItfTupleTerminationMeasure",
  "None", "Old", "Out", "PointerT", "Predicate", "Program", "PureMethod",
  "PureMethodCall", "Ref", "SepAnd", "Seqn", "Single", "SingleAss", "Some",
  "StringT", "StructLit", "StructT", "UnboundedInteger", "Var", "While",
  "WildcardPerm"
]

def KnownTag.ofString? (name : String) : Option KnownTag :=
  if knownTagNames.contains name then Option.some { name } else Option.none

inductive Value where
  | null
  | bool (value : Bool)
  | int (value : Int)
  | string (value : String)
  | array (values : Array Value)
  | object (fields : List (String × Value))
  | tagged (tag : KnownTag) (fields : List (String × Value))
  deriving Repr, BEq

partial def decodeValue (path : String) (json : Json) : Except String Value := do
  match json with
  | .null => return .null
  | .bool b => return .bool b
  | .str s => return .string s
  | .num _ => return .int (← GoLean.StrictJson.int path json)
  | .arr values =>
      return .array (← GoLean.StrictJson.mapArrayIdx values (fun i value => decodeValue s!"{path}[{i}]" value))
  | .obj obj =>
      let fields ← (GoLean.StrictJson.keys obj).mapM (fun key => do
        let value ← GoLean.StrictJson.field path obj key
        return (key, ← decodeValue s!"{path}.{key}" value))
      match obj.get? "tag" with
      | none => return .object fields
      | some tagJson =>
          if GoLean.StrictJson.exactKeys obj ["position", "tag"] then
            return .object fields
          let tagName ← GoLean.StrictJson.string s!"{path}.tag" tagJson
          match KnownTag.ofString? tagName with
          | some tag => return .tagged tag fields
          | none => throw s!"{path}.tag: unknown Gobra tag {repr tagName}"

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

structure FunctionProxy where
  source : Source
  name : String
  deriving Repr, BEq

structure MethodProxy where
  source : Source
  name : String
  uniqueName : String
  deriving Repr, BEq

structure FunctionMember where
  source : Source
  name : FunctionProxy
  args : Array Parameter
  results : Array Parameter
  pres : Array Value
  posts : Array Value
  terminationMeasures : Array Value
  backendAnnotations : Array Value
  body : Option Value
  deriving Repr, BEq

structure MethodMember where
  source : Source
  receiver : Parameter
  name : MethodProxy
  args : Array Parameter
  results : Array Parameter
  pres : Array Value
  posts : Array Value
  terminationMeasures : Array Value
  backendAnnotations : Array Value
  body : Option Value
  isPure : Bool
  isOpaque : Bool
  deriving Repr, BEq

structure MPredicateMember where
  source : Source
  receiver : Parameter
  name : MethodProxy
  args : Array Parameter
  body : Option Value
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

private def decodeRawArray (path : String) (json : Json) : Except String (Array Value) :=
  decodeArrayOf path json decodeValue

private def decodeOptionValue (path : String) (json : Json) : Except String (Option Value) := do
  let obj ← GoLean.StrictJson.obj path json
  let tag ← GoLean.StrictJson.string s!"{path}.tag" (← GoLean.StrictJson.field path obj "tag")
  match tag with
  | "None" =>
      GoLean.StrictJson.requireExactKeys path obj ["tag"]
      return none
  | "Some" =>
      GoLean.StrictJson.requireExactKeys path obj ["tag", "value"]
      return some (← decodeValue s!"{path}.value" (← GoLean.StrictJson.field path obj "value"))
  | other =>
      throw s!"{path}.tag: expected Option tag, got {repr other}"

private def decodeFunctionMember (path : String) (json : Json) : Except String FunctionMember := do
  let obj ← taggedObj path json "Function" ["args", "backendAnnotations", "body", "name", "posts", "pres", "results", "source", "tag", "terminationMeasures"]
  return {
    source := (← decodeSource s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    name := (← decodeFunctionProxy s!"{path}.name" (← GoLean.StrictJson.field path obj "name")),
    args := (← decodeArrayOf s!"{path}.args" (← GoLean.StrictJson.field path obj "args") decodeParam),
    results := (← decodeArrayOf s!"{path}.results" (← GoLean.StrictJson.field path obj "results") decodeParam),
    pres := (← decodeRawArray s!"{path}.pres" (← GoLean.StrictJson.field path obj "pres")),
    posts := (← decodeRawArray s!"{path}.posts" (← GoLean.StrictJson.field path obj "posts")),
    terminationMeasures := (← decodeRawArray s!"{path}.terminationMeasures" (← GoLean.StrictJson.field path obj "terminationMeasures")),
    backendAnnotations := (← decodeRawArray s!"{path}.backendAnnotations" (← GoLean.StrictJson.field path obj "backendAnnotations")),
    body := (← decodeOptionValue s!"{path}.body" (← GoLean.StrictJson.field path obj "body"))
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
    pres := (← decodeRawArray s!"{path}.pres" (← GoLean.StrictJson.field path obj "pres")),
    posts := (← decodeRawArray s!"{path}.posts" (← GoLean.StrictJson.field path obj "posts")),
    terminationMeasures := (← decodeRawArray s!"{path}.terminationMeasures" (← GoLean.StrictJson.field path obj "terminationMeasures")),
    backendAnnotations := (← decodeRawArray s!"{path}.backendAnnotations" (← GoLean.StrictJson.field path obj "backendAnnotations")),
    body := (← decodeOptionValue s!"{path}.body" (← GoLean.StrictJson.field path obj "body")),
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
    body := (← decodeOptionValue s!"{path}.body" (← GoLean.StrictJson.field path obj "body"))
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

end GoLean.GobraJson
