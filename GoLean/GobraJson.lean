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
  "Initialization", "IntLit", "IntT", "InterfaceT", "ItfTupleTerminationMeasure",
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

structure Document where
  schema : Schema
  inputs : Array String
  program : Value
  deriving Repr, BEq

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

private def decodeInputs (json : Json) : Except String (Array String) := do
  let inputs ← GoLean.StrictJson.array "inputs" json
  GoLean.StrictJson.mapArrayIdx inputs (fun i value => GoLean.StrictJson.string s!"inputs[{i}]" value)

def decode (json : Json) : Except String Document := do
  let obj ← GoLean.StrictJson.obj "document" json
  GoLean.StrictJson.requireExactKeys "document" obj ["inputs", "program", "schema"]
  let schema ← decodeSchema (← GoLean.StrictJson.field "document" obj "schema")
  let inputs ← decodeInputs (← GoLean.StrictJson.field "document" obj "inputs")
  let program ← decodeValue "program" (← GoLean.StrictJson.field "document" obj "program")
  return { schema, inputs, program }

def decodeString (contents : String) : Except String Document := do
  decode (← Json.parse contents)

def decodeFile (path : FilePath) : IO (Except String Document) := do
  return decodeString (← IO.FS.readFile path)

end GoLean.GobraJson
