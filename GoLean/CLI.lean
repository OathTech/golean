import GoLean.GoCore
import GoLean.NativeToIR
import GoLean.StrictJson
import Lean.Data.Json

namespace GoLean.CLI

open System
open Lean

private def observationSchema : String :=
  "golean-observation-v1"

structure RunArgs where
  input : Option FilePath := none
  functionName : Option String := none
  args : Array Int := #[]
  /-- Fuel counts MACHINE STEPS (reshape S3, 2026-07-23; previously
  while-back-edges + call entries only), so the default is retuned upward.
  No corpus case or script pins `--fuel`; the tracked baseline gates the
  retune. -/
  fuel : Nat := 10000000
  /-- Nondeterminism oracle: the choice stream consumed at nondeterministic
  points (map iteration order, append capacity). Empty is the canonical
  default. The harness runs the same program under several sequences to check
  observation invariance. -/
  choices : List Nat := []
  deriving Repr

private def usage : String :=
  "usage:\n" ++
  "  golean native-json-run --input <file> --function <name> [--arg-int <n> ...] [--fuel <n>] [--choices <n,n,...>]\n" ++
  "  golean observation-eq --left <json> --right <json>\n"

private def absoluteFrom (base : FilePath) (path : FilePath) : FilePath :=
  if path.isRelative then (base / path).normalize else path.normalize

private def parseObservationEqArgs : List String → Option String → Option String →
    Except String (String × String)
  | [], some left, some right => .ok (left, right)
  | [], _, _ => .error s!"missing --left <json> or --right <json>\n{usage}"
  | "--left" :: json :: rest, none, right => parseObservationEqArgs rest (some json) right
  | "--left" :: _ :: _, some _, _ => .error s!"duplicate --left\n{usage}"
  | "--right" :: json :: rest, left, none => parseObservationEqArgs rest left (some json)
  | "--right" :: _ :: _, _, some _ => .error s!"duplicate --right\n{usage}"
  | flag :: _, _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def parseJsonInt (path value : String) : Except String Int := do
  GoLean.StrictJson.int path (← Json.parse value)

private def parseJsonNat (path value : String) : Except String Nat := do
  let value ← parseJsonInt path value
  if value < 0 then
    throw s!"{path}: expected nonnegative integer, got {value}"
  return value.toNat

private def parseRunArgs : List String → RunArgs → Except String RunArgs
  | [], cfg => .ok cfg
  | "--input" :: path :: rest, cfg =>
      parseRunArgs rest { cfg with input := some (FilePath.mk path) }
  | "--function" :: name :: rest, cfg =>
      parseRunArgs rest { cfg with functionName := some name }
  | "--arg-int" :: value :: rest, cfg => do
      parseRunArgs rest { cfg with args := cfg.args.push (← parseJsonInt "--arg-int" value) }
  | "--fuel" :: value :: rest, cfg => do
      parseRunArgs rest { cfg with fuel := (← parseJsonNat "--fuel" value) }
  | "--choices" :: value :: rest, cfg => do
      let parts := (value.splitOn ",").filter (fun s => !s.isEmpty)
      let choices ← parts.mapM (fun s => parseJsonNat "--choices" s)
      parseRunArgs rest { cfg with choices }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def locJson : Loc → Json
  | .base addr => Json.mkObj [("tag", Json.str "addr"), ("id", Lean.toJson addr.id)]
  | .field base typeId fieldName =>
      Json.mkObj [
        ("tag", Json.str "fieldAddr"),
        ("base", locJson base),
        ("typeName", Json.str typeId.key),
        ("fieldName", Json.str fieldName)
      ]
  | .index base index =>
      Json.mkObj [
        ("tag", Json.str "indexAddr"),
        ("base", locJson base),
        ("index", Lean.toJson index)
      ]

private partial def goValueJson : GoValue → Json
  | .unit => Json.mkObj [("tag", Json.str "unit")]
  | .bool value => Json.mkObj [("tag", Json.str "bool"), ("value", Lean.toJson value)]
  | .int value _ => Json.mkObj [("tag", Json.str "int"), ("value", Lean.toJson value)]
  | .string value => Json.mkObj [("tag", Json.str "string"), ("bytes", Lean.toJson value.byteNats)]
  | .addr loc => locJson loc
  | .nil => Json.mkObj [("tag", Json.str "nil")]
  -- Func values are not observable in Go (not comparable, not printable),
  -- so the observation channel reports identity only; a case whose OUTPUT
  -- is a func value is outside the differential's comparable surface.
  | .funcVal fid _ =>
      Json.mkObj [("tag", Json.str "func"), ("id", Json.str fid.key)]
  | .interface dynamic value =>
      Json.mkObj [
        ("tag", Json.str "interface"),
        ("dynamic", Json.str dynamic),
        ("value", goValueJson value)
      ]
  | .struct typeId fields =>
      Json.mkObj [
        ("tag", Json.str "struct"),
        ("typeName", Json.str typeId.key),
        ("fields", Json.arr (fields.map (fun (name, value) =>
          Json.mkObj [("name", Json.str name), ("value", goValueJson value)])))
      ]
  | .array values =>
      Json.mkObj [
        ("tag", Json.str "array"),
        ("values", Json.arr (values.map goValueJson))
      ]
  | .slice value =>
      Json.mkObj [
        ("tag", Json.str "slice"),
        ("base", match value.base with
          | some loc => locJson loc
          | none => Json.null),
        ("offset", Lean.toJson value.offset),
        ("len", Lean.toJson value.len),
        ("cap", Lean.toJson value.cap)
      ]
  | .map value =>
      Json.mkObj [
        ("tag", Json.str "map"),
        ("base", match value.base with
          | some loc => locJson loc
          | none => Json.null)
      ]
  | .mapData entries =>
      Json.mkObj [
        ("tag", Json.str "mapData"),
        ("entries", Json.arr (entries.map (fun (key, value) =>
          Json.mkObj [
            ("key", goValueJson key),
            ("value", goValueJson value)
          ])))
      ]

private def runJson : GoLean.GoCore.Result → Json
  | { values } =>
      Json.mkObj [
        ("schema", Json.str observationSchema),
        ("status", Json.str "ok"),
        ("values", Json.arr (values.map goValueJson))
      ]

private def errorJson (error : GoError) : Json :=
  Json.mkObj [
    ("schema", Json.str observationSchema),
    ("status", Json.str error.status),
    ("message", Json.str error.message)
  ]

private def cliErrorJson (message : String) : Json :=
  Json.mkObj [
    ("schema", Json.str observationSchema),
    ("status", Json.str "error"),
    ("message", Json.str message)
  ]

private partial def decodeLocObservation (path : String) (json : Json) : Except String Unit := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.tag" (← StrictJson.field path obj "tag")
  match tag with
  | "addr" =>
      StrictJson.requireExactKeys path obj ["id", "tag"]
      let _ ← StrictJson.nat s!"{path}.id" (← StrictJson.field path obj "id")
      pure ()
  | "fieldAddr" =>
      StrictJson.requireExactKeys path obj ["base", "fieldName", "tag", "typeName"]
      decodeLocObservation s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.string s!"{path}.typeName" (← StrictJson.field path obj "typeName")
      let _ ← StrictJson.string s!"{path}.fieldName" (← StrictJson.field path obj "fieldName")
      pure ()
  | "indexAddr" =>
      StrictJson.requireExactKeys path obj ["base", "index", "tag"]
      decodeLocObservation s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.int s!"{path}.index" (← StrictJson.field path obj "index")
      pure ()
  | other =>
      throw s!"{path}.tag: unknown location tag {repr other}"

private def decodeOptionalLoc (path : String) (json : Json) : Except String Unit :=
  match json with
  | .null => pure ()
  | other => decodeLocObservation path other

private partial def decodeGoValueObservation (path : String) (json : Json) : Except String Unit := do
  let obj ← StrictJson.obj path json
  let tag ← StrictJson.string s!"{path}.tag" (← StrictJson.field path obj "tag")
  match tag with
  | "unit" =>
      StrictJson.requireExactKeys path obj ["tag"]
  | "bool" =>
      StrictJson.requireExactKeys path obj ["tag", "value"]
      let _ ← StrictJson.bool s!"{path}.value" (← StrictJson.field path obj "value")
      pure ()
  | "int" =>
      StrictJson.requireExactKeys path obj ["tag", "value"]
      let _ ← StrictJson.int s!"{path}.value" (← StrictJson.field path obj "value")
      pure ()
  | "string" =>
      StrictJson.requireExactKeys path obj ["bytes", "tag"]
      let bytes ← StrictJson.array s!"{path}.bytes" (← StrictJson.field path obj "bytes")
      let _ ← StrictJson.mapArrayIdx bytes (fun i byte => do
        let _ ← StrictJson.nat s!"{path}.bytes[{i}]" byte
        pure ())
      pure ()
  | "nil" =>
      StrictJson.requireExactKeys path obj ["tag"]
  | "interface" =>
      StrictJson.requireExactKeys path obj ["dynamic", "tag", "value"]
      let _ ← StrictJson.string s!"{path}.dynamic" (← StrictJson.field path obj "dynamic")
      decodeGoValueObservation s!"{path}.value" (← StrictJson.field path obj "value")
  | "addr" | "fieldAddr" | "indexAddr" =>
      decodeLocObservation path json
  | "struct" =>
      StrictJson.requireExactKeys path obj ["fields", "tag", "typeName"]
      let _ ← StrictJson.string s!"{path}.typeName" (← StrictJson.field path obj "typeName")
      let fields ← StrictJson.array s!"{path}.fields" (← StrictJson.field path obj "fields")
      let _ ← StrictJson.mapArrayIdx fields (fun i fieldJson => do
        let fieldObj ← StrictJson.obj s!"{path}.fields[{i}]" fieldJson
        StrictJson.requireExactKeys s!"{path}.fields[{i}]" fieldObj ["name", "value"]
        let _ ← StrictJson.string s!"{path}.fields[{i}].name" (← StrictJson.field s!"{path}.fields[{i}]" fieldObj "name")
        decodeGoValueObservation s!"{path}.fields[{i}].value" (← StrictJson.field s!"{path}.fields[{i}]" fieldObj "value"))
      pure ()
  | "array" =>
      StrictJson.requireExactKeys path obj ["tag", "values"]
      let values ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      let _ ← StrictJson.mapArrayIdx values (fun i value => do
        decodeGoValueObservation s!"{path}.values[{i}]" value)
      pure ()
  | "slice" =>
      StrictJson.requireExactKeys path obj ["base", "cap", "len", "offset", "tag"]
      decodeOptionalLoc s!"{path}.base" (← StrictJson.field path obj "base")
      let _ ← StrictJson.nat s!"{path}.offset" (← StrictJson.field path obj "offset")
      let _ ← StrictJson.nat s!"{path}.len" (← StrictJson.field path obj "len")
      let _ ← StrictJson.nat s!"{path}.cap" (← StrictJson.field path obj "cap")
      pure ()
  | "map" =>
      StrictJson.requireExactKeys path obj ["base", "tag"]
      decodeOptionalLoc s!"{path}.base" (← StrictJson.field path obj "base")
  | "mapData" =>
      StrictJson.requireExactKeys path obj ["entries", "tag"]
      let entries ← StrictJson.array s!"{path}.entries" (← StrictJson.field path obj "entries")
      let _ ← StrictJson.mapArrayIdx entries (fun i entryJson => do
        let entryObj ← StrictJson.obj s!"{path}.entries[{i}]" entryJson
        StrictJson.requireExactKeys s!"{path}.entries[{i}]" entryObj ["key", "value"]
        decodeGoValueObservation s!"{path}.entries[{i}].key" (← StrictJson.field s!"{path}.entries[{i}]" entryObj "key")
        decodeGoValueObservation s!"{path}.entries[{i}].value" (← StrictJson.field s!"{path}.entries[{i}]" entryObj "value"))
      pure ()
  | other =>
      throw s!"{path}.tag: unknown Go observation value tag {repr other}"

private def decodeObservation (path raw : String) : Except String Json := do
  let json ← Json.parse raw
  let obj ← StrictJson.obj path json
  let schema ← StrictJson.string s!"{path}.schema" (← StrictJson.field path obj "schema")
  if schema != observationSchema then
    throw s!"{path}.schema: expected {repr observationSchema}, got {repr schema}"
  let status ← StrictJson.string s!"{path}.status" (← StrictJson.field path obj "status")
  match status with
  | "ok" =>
      StrictJson.requireExactKeys path obj ["schema", "status", "values"]
      let values ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      let _ ← StrictJson.mapArrayIdx values (fun i value => do
        decodeGoValueObservation s!"{path}.values[{i}]" value)
      return json
  | "panic" | "unsupported" | "stuck" | "error" =>
      StrictJson.requireExactKeys path obj ["message", "schema", "status"]
      let _ ← StrictJson.string s!"{path}.message" (← StrictJson.field path obj "message")
      return json
  | other =>
      throw s!"{path}.status: unknown observation status {repr other}"

private def runObservationEq (args : List String) : IO UInt32 := do
  match parseObservationEqArgs args none none with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok (leftRaw, rightRaw) =>
      match decodeObservation "left" leftRaw, decodeObservation "right" rightRaw with
      | .error err, _ =>
          IO.eprintln err
          return 2
      | _, .error err =>
          IO.eprintln err
          return 2
      | .ok left, .ok right =>
          if left == right then
            return 0
          else
            IO.eprintln s!"left:  {left.compress}"
            IO.eprintln s!"right: {right.compress}"
            return 1

private def runNativeJsonRun (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseRunArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      match cfg.input, cfg.functionName with
      | some input, some functionName =>
          let input := absoluteFrom cwd input
          let contents ← IO.FS.readFile input
          match Lean.Json.parse contents with
          | .error err =>
              IO.println (cliErrorJson s!"{input}: JSON parse error: {err}").compress
              return 1
          | .ok json =>
              match GoLean.NativeToIR.decodeProgram json with
              | .error err =>
                  IO.println (cliErrorJson s!"{input}: {err}").compress
                  return 1
              | .ok program =>
                  -- Reshape S3 flip (2026-07-23): the machine interpreter
                  -- (iterated stepFn) is the executable; the big-step
                  -- interpreter is deleted at S4.
                  match GoLean.GoCore.Machine.runNamedFunctionIntsM cfg.fuel program functionName cfg.args cfg.choices with
                  | .ok result =>
                      IO.println (runJson result).compress
                      return 0
                  | .error err =>
                      IO.println (errorJson err).compress
                      return 1
      | _, _ =>
          IO.eprintln s!"provide --input <file> and --function <name>\n{usage}"
          return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | "native-json-run" :: rest => runNativeJsonRun rest
  | "observation-eq" :: rest => runObservationEq rest
  | [] =>
      IO.println usage
      return 0
  | cmd :: _ =>
      IO.eprintln s!"unknown command: {cmd}\n{usage}"
      return 2

end GoLean.CLI
