import GoLean.Artifact.Gobra
import GoLean.GobraEval
import GoLean.GobraJson
import Lean.Data.Json

namespace GoLean.CLI

open System
open Lean
open GoLean.Artifact

structure GobraExportArgs where
  manifest : Option FilePath := none
  input : Option FilePath := none
  id : Option String := none
  outDir : FilePath := "artifacts/gobra-smoke"
  gobraSbt : FilePath := "scripts/gobra-sbt"
  deriving Repr

structure GobraRunArgs where
  input : Option FilePath := none
  functionName : Option String := none
  args : Array Int := #[]
  fuel : Nat := 100000
  deriving Repr

private def usage : String :=
  "usage:\n" ++
  "  golean gobra-export --manifest <file> [--out <dir>] [--gobra-sbt <path>]\n" ++
  "  golean gobra-export --input <file> --id <id> [--out <dir>] [--gobra-sbt <path>]\n" ++
  "  golean gobra-json-check --input <file>\n" ++
  "  golean gobra-json-tags --input <file>\n" ++
  "  golean gobra-json-run --input <file> --function <name> [--arg-int <n> ...] [--fuel <n>]\n"

private def parseGobraExportArgs : List String → GobraExportArgs → Except String GobraExportArgs
  | [], cfg => .ok cfg
  | "--manifest" :: path :: rest, cfg =>
      parseGobraExportArgs rest { cfg with manifest := some (FilePath.mk path) }
  | "--input" :: path :: rest, cfg =>
      parseGobraExportArgs rest { cfg with input := some (FilePath.mk path) }
  | "--id" :: id :: rest, cfg =>
      parseGobraExportArgs rest { cfg with id := some id }
  | "--out" :: path :: rest, cfg =>
      parseGobraExportArgs rest { cfg with outDir := FilePath.mk path }
  | "--gobra-sbt" :: path :: rest, cfg =>
      parseGobraExportArgs rest { cfg with gobraSbt := FilePath.mk path }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def absoluteFrom (base : FilePath) (path : FilePath) : FilePath :=
  if path.isRelative then (base / path).normalize else path.normalize

private def collectEntries (cwd : FilePath) (cfg : GobraExportArgs) :
    IO (Except String (List Gobra.CorpusEntry)) := do
  match cfg.manifest, cfg.input, cfg.id with
  | some manifest, none, none =>
      let manifest := absoluteFrom cwd manifest
      Gobra.readManifest manifest
  | none, some input, some id =>
      return .ok [{ id, source := absoluteFrom cwd input }]
  | _, _, _ =>
      return .error s!"provide either --manifest, or both --input and --id\n{usage}"

private def canonicalizeEntries (entries : List Gobra.CorpusEntry) :
    IO (Except String (List Gobra.CorpusEntry)) := do
  let mut out := []
  for entry in entries do
    if !(← entry.source.pathExists) then
      return .error s!"source file does not exist for '{entry.id}': {entry.source}"
    let source ← IO.FS.realPath entry.source
    out := out.concat { entry with source }
  return .ok out

private def runGobraExport (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseGobraExportArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      match ← collectEntries cwd cfg with
      | .error err =>
          IO.eprintln err
          return 2
      | .ok entries =>
          match ← canonicalizeEntries entries with
          | .error err =>
              IO.eprintln err
              return 2
          | .ok entries =>
              let opts : Gobra.ExportOptions := {
                gobraSbt := absoluteFrom cwd cfg.gobraSbt,
                outDir := absoluteFrom cwd cfg.outDir
              }
              let results ← Gobra.exportMany opts entries
              let failed := results.filter (fun r => !r.success)
              if failed.isEmpty then
                IO.println s!"wrote {results.length} Gobra artifact record(s) to {opts.outDir}"
                return 0
              else
                IO.eprintln s!"{failed.length} Gobra export(s) failed; see {opts.outDir}/manifest.json"
                return 1

private def parseInputOnly : List String → Option FilePath → Except String FilePath
  | [], some input => .ok input
  | [], none => .error s!"missing --input <file>\n{usage}"
  | "--input" :: path :: rest, none => parseInputOnly rest (some (FilePath.mk path))
  | "--input" :: _ :: _, some _ => .error s!"duplicate --input\n{usage}"
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def parseJsonInt (path value : String) : Except String Int := do
  GoLean.StrictJson.int path (← Json.parse value)

private def parseJsonNat (path value : String) : Except String Nat := do
  let value ← parseJsonInt path value
  if value < 0 then
    throw s!"{path}: expected nonnegative integer, got {value}"
  return value.toNat

private def parseGobraRunArgs : List String → GobraRunArgs → Except String GobraRunArgs
  | [], cfg => .ok cfg
  | "--input" :: path :: rest, cfg =>
      parseGobraRunArgs rest { cfg with input := some (FilePath.mk path) }
  | "--function" :: name :: rest, cfg =>
      parseGobraRunArgs rest { cfg with functionName := some name }
  | "--arg-int" :: value :: rest, cfg => do
      parseGobraRunArgs rest { cfg with args := cfg.args.push (← parseJsonInt "--arg-int" value) }
  | "--fuel" :: value :: rest, cfg => do
      parseGobraRunArgs rest { cfg with fuel := (← parseJsonNat "--fuel" value) }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def goValueJson : GoValue → Json
  | .unit => Json.mkObj [("tag", Json.str "unit")]
  | .bool value => Json.mkObj [("tag", Json.str "bool"), ("value", Lean.toJson value)]
  | .int value => Json.mkObj [("tag", Json.str "int"), ("value", Lean.toJson value)]
  | .addr addr => Json.mkObj [("tag", Json.str "addr"), ("id", Lean.toJson addr.id)]
  | .nil => Json.mkObj [("tag", Json.str "nil")]

private def runJson : GoLean.GobraEval.Result → Json
  | { values } =>
      Json.mkObj [
        ("status", Json.str "ok"),
        ("values", Json.arr (values.map goValueJson))
      ]

private def errorJson (message : String) : Json :=
  Json.mkObj [("status", Json.str "error"), ("message", Json.str message)]

private def runGobraJsonCheck (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseInputOnly args none with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok input =>
      let input := absoluteFrom cwd input
      match ← GobraJson.decodeFile input with
      | .ok doc =>
          IO.println s!"ok: {input} ({doc.inputs.size} input(s))"
          return 0
      | .error err =>
          IO.eprintln s!"{input}: {err}"
          return 1

private def runGobraJsonTags (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseInputOnly args none with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok input =>
      let input := absoluteFrom cwd input
      match Json.parse (← IO.FS.readFile input) with
      | .error err =>
          IO.eprintln s!"{input}: {err}"
          return 1
      | .ok json =>
          let tags := GobraJson.uniqueTags (GobraJson.collectTags json)
          let unknown := GobraJson.unknownTags tags
          IO.println s!"{input}: {tags.length} observed tag(s)"
          for tag in tags do
            IO.println s!"  {tag}"
          if unknown.isEmpty then
            return 0
          else
            IO.eprintln s!"unknown tag(s): {unknown}"
            return 1

private def runGobraJsonRun (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseGobraRunArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      match cfg.input, cfg.functionName with
      | some input, some functionName =>
          let input := absoluteFrom cwd input
          match ← GobraJson.decodeFile input with
          | .error err =>
              IO.println (errorJson s!"{input}: {err}").compress
              return 1
          | .ok doc =>
              match GoLean.GobraEval.runFunctionInts cfg.fuel doc functionName cfg.args with
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
  | "gobra-export" :: rest => runGobraExport rest
  | "gobra-json-check" :: rest => runGobraJsonCheck rest
  | "gobra-json-tags" :: rest => runGobraJsonTags rest
  | "gobra-json-run" :: rest => runGobraJsonRun rest
  | [] =>
      IO.println usage
      return 0
  | cmd :: _ =>
      IO.eprintln s!"unknown command: {cmd}\n{usage}"
      return 2

end GoLean.CLI
