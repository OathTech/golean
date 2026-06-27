import GoLean.Artifact.Gobra
import GoLean.GobraEval
import GoLean.GobraJson
import GoLean.StrictJson
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
  ignoreAssertAt : Option (Nat × Nat) := none
  deriving Repr

structure GobraArtifactCheckArgs where
  manifest : Option FilePath := none
  internalJson : Option FilePath := none
  deriving Repr

private def usage : String :=
  "usage:\n" ++
  "  golean gobra-export --manifest <file> [--out <dir>] [--gobra-sbt <path>]\n" ++
  "  golean gobra-export --input <file> --id <id> [--out <dir>] [--gobra-sbt <path>]\n" ++
  "  golean gobra-json-check --input <file>\n" ++
  "  golean gobra-json-tags --input <file>\n" ++
  "  golean gobra-json-run --input <file> --function <name> [--arg-int <n> ...] [--fuel <n>] [--ignore-assert-at <line>:<column>]\n" ++
  "  golean gobra-artifact-check --manifest <file> --internal-json <file>\n" ++
  "  golean observation-eq --left <json> --right <json>\n"

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

private def parseObservationEqArgs : List String → Option String → Option String →
    Except String (String × String)
  | [], some left, some right => .ok (left, right)
  | [], _, _ => .error s!"missing --left <json> or --right <json>\n{usage}"
  | "--left" :: json :: rest, none, right => parseObservationEqArgs rest (some json) right
  | "--left" :: _ :: _, some _, _ => .error s!"duplicate --left\n{usage}"
  | "--right" :: json :: rest, left, none => parseObservationEqArgs rest left (some json)
  | "--right" :: _ :: _, _, some _ => .error s!"duplicate --right\n{usage}"
  | flag :: _, _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def parseGobraArtifactCheckArgs : List String → GobraArtifactCheckArgs →
    Except String GobraArtifactCheckArgs
  | [], cfg => .ok cfg
  | "--manifest" :: path :: rest, cfg =>
      parseGobraArtifactCheckArgs rest { cfg with manifest := some (FilePath.mk path) }
  | "--internal-json" :: path :: rest, cfg =>
      parseGobraArtifactCheckArgs rest { cfg with internalJson := some (FilePath.mk path) }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def parseJsonInt (path value : String) : Except String Int := do
  GoLean.StrictJson.int path (← Json.parse value)

private def parseJsonNat (path value : String) : Except String Nat := do
  let value ← parseJsonInt path value
  if value < 0 then
    throw s!"{path}: expected nonnegative integer, got {value}"
  return value.toNat

private def parseLineColumn (path value : String) : Except String (Nat × Nat) := do
  match value.splitOn ":" with
  | [line, column] =>
      return (← parseJsonNat s!"{path}.line" line, ← parseJsonNat s!"{path}.column" column)
  | _ => throw s!"{path}: expected <line>:<column>, got {value}"

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
  | "--ignore-assert-at" :: value :: rest, cfg => do
      parseGobraRunArgs rest { cfg with ignoreAssertAt := some (← parseLineColumn "--ignore-assert-at" value) }
  | flag :: _, _ => .error s!"unknown or incomplete option: {flag}\n{usage}"

private def sourceStartsAt (source : GobraJson.Source) (line column : Nat) : Bool :=
  match source with
  | .single origin => origin.position.start.line == line && origin.position.start.column == column
  | .internal => false

mutual
  private partial def ignoreAssertAtStmts (line column : Nat) (stmts : Array GobraJson.Stmt) :
      Array GobraJson.Stmt × Nat := Id.run do
    let mut out := #[]
    let mut count := 0
    for stmt in stmts do
      let (stmt, stmtCount) := ignoreAssertAtStmt line column stmt
      out := out.push stmt
      count := count + stmtCount
    return (out, count)

  private partial def ignoreAssertAtStmt (line column : Nat) : GobraJson.Stmt → GobraJson.Stmt × Nat
    | .seqn source stmts =>
        let (stmts, count) := ignoreAssertAtStmts line column stmts
        (.seqn source stmts, count)
    | .block source decls stmts =>
        let (stmts, count) := ignoreAssertAtStmts line column stmts
        (.block source decls stmts, count)
    | .while source cond invs terminationMeasure body =>
        let (body, count) := ignoreAssertAtStmt line column body
        (.while source cond invs terminationMeasure body, count)
    | .assert source assertion =>
        if sourceStartsAt source line column then
          (.assert source (.exprAssertion source (.boolLit source true)), 1)
        else
          (.assert source assertion, 0)
    | stmt => (stmt, 0)

  private partial def ignoreAssertAtMethodBody (line column : Nat)
      (body : GobraJson.MethodBody) : GobraJson.MethodBody × Nat :=
    let (seqnStmts, seqnCount) := ignoreAssertAtStmts line column body.seqn.stmts
    let (postprocessing, postCount) := ignoreAssertAtStmts line column body.postprocessing
    ({ body with
       seqn := { body.seqn with stmts := seqnStmts },
       postprocessing := postprocessing
     },
     seqnCount + postCount)

  private partial def ignoreAssertAtMember (line column : Nat) : GobraJson.Member → GobraJson.Member × Nat
    | .function member =>
        match member.body with
        | some body =>
            let (body, count) := ignoreAssertAtMethodBody line column body
            (.function { member with body := some body }, count)
        | none => (.function member, 0)
    | .method member =>
        match member.body with
        | some body =>
            let (body, count) := ignoreAssertAtMethodBody line column body
            (.method { member with body := some body }, count)
        | none => (.method member, 0)
    | member => (member, 0)
end

private def ignoreAssertAtDocument (line column : Nat) (doc : GobraJson.Document) :
    GobraJson.Document × Nat := Id.run do
  let mut members := #[]
  let mut count := 0
  for member in doc.program.members do
    let (member, memberCount) := ignoreAssertAtMember line column member
    members := members.push member
    count := count + memberCount
  return ({ doc with program := { doc.program with members } }, count)

private def locJson : Loc → Json
  | .base addr => Json.mkObj [("tag", Json.str "addr"), ("id", Lean.toJson addr.id)]
  | .field base typeName fieldName =>
      Json.mkObj [
        ("tag", Json.str "fieldAddr"),
        ("base", locJson base),
        ("typeName", Json.str typeName),
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
  | .int value => Json.mkObj [("tag", Json.str "int"), ("value", Lean.toJson value)]
  | .addr loc => locJson loc
  | .nil => Json.mkObj [("tag", Json.str "nil")]
  | .struct typeName fields =>
      Json.mkObj [
        ("tag", Json.str "struct"),
        ("typeName", Json.str typeName),
        ("fields", Json.arr (fields.map (fun (name, value) =>
          Json.mkObj [("name", Json.str name), ("value", goValueJson value)])))
      ]
  | .array values =>
      Json.mkObj [
        ("tag", Json.str "array"),
        ("values", Json.arr (values.map goValueJson))
      ]

private def runJson : GoLean.GobraEval.Result → Json
  | { values } =>
      Json.mkObj [
        ("status", Json.str "ok"),
        ("values", Json.arr (values.map goValueJson))
      ]

private def errorJson (error : GoError) : Json :=
  Json.mkObj [
    ("status", Json.str error.status),
    ("message", Json.str error.message)
  ]

private def cliErrorJson (message : String) : Json :=
  Json.mkObj [("status", Json.str "error"), ("message", Json.str message)]

private def decodeObservation (path raw : String) : Except String Json := do
  let json ← Json.parse raw
  let obj ← StrictJson.obj path json
  let status ← StrictJson.string s!"{path}.status" (← StrictJson.field path obj "status")
  match status with
  | "ok" =>
      StrictJson.requireExactKeys path obj ["status", "values"]
      let _ ← StrictJson.array s!"{path}.values" (← StrictJson.field path obj "values")
      return json
  | "panic" | "assertion_error" | "unsupported" | "stuck" | "error" =>
      StrictJson.requireExactKeys path obj ["status", "message"]
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

private def artifactRecordMatches (internalJson : FilePath) (path : String) : Bool :=
  (FilePath.mk path).normalize.toString == internalJson.normalize.toString

private def checkArtifactRecord (path : String) (internalJson : FilePath) (json : Json) :
    IO (Except String Bool) := do
  match (do
    let obj ← StrictJson.obj path json
    let recordInternalJson ←
      StrictJson.string s!"{path}.internalJsonPath" (← StrictJson.field path obj "internalJsonPath")
    pure (obj, recordInternalJson)
  ) with
  | .error err => return .error err
  | .ok (obj, recordInternalJson) =>
      if !artifactRecordMatches internalJson recordInternalJson then
        return .ok false
      let parsed := (do
        let success ← StrictJson.bool s!"{path}.success" (← StrictJson.field path obj "success")
        let source ← StrictJson.string s!"{path}.source" (← StrictJson.field path obj "source")
        let sourceSha256 ← StrictJson.string s!"{path}.sourceSha256" (← StrictJson.field path obj "sourceSha256")
        let scratchSource ← StrictJson.string s!"{path}.scratchSource" (← StrictJson.field path obj "scratchSource")
        let scratchSourceSha256 ←
          StrictJson.string s!"{path}.scratchSourceSha256" (← StrictJson.field path obj "scratchSourceSha256")
        pure (success, source, sourceSha256, scratchSource, scratchSourceSha256)
      )
      match parsed with
      | .error err => return .error err
      | .ok (success, source, sourceSha256, scratchSource, scratchSourceSha256) =>
          if !success then
            return .error s!"{path}: artifact record is not successful"
          let sourcePath := FilePath.mk source
          let scratchSourcePath := FilePath.mk scratchSource
          if !(← sourcePath.pathExists) then
            return .error s!"{path}: source does not exist: {sourcePath}"
          if !(← scratchSourcePath.pathExists) then
            return .error s!"{path}: scratch source does not exist: {scratchSourcePath}"
          let actualSourceSha256 ← Artifact.Gobra.sha256File sourcePath
          let actualScratchSourceSha256 ← Artifact.Gobra.sha256File scratchSourcePath
          if actualSourceSha256 != sourceSha256 then
            return .error s!"{path}: source hash changed for {sourcePath}"
          if actualScratchSourceSha256 != scratchSourceSha256 then
            return .error s!"{path}: scratch source hash changed for {scratchSourcePath}"
          if sourceSha256 != scratchSourceSha256 then
            return .error s!"{path}: source and scratch source hashes differ"
          return .ok true

private def checkArtifactManifest (manifest internalJson : FilePath) : IO (Except String Unit) := do
  match Json.parse (← IO.FS.readFile manifest) with
  | .error err => return .error err
  | .ok json =>
      match (do
        let obj ← StrictJson.obj "manifest" json
        StrictJson.array "manifest.results" (← StrictJson.field "manifest" obj "results")
      ) with
      | .error err => return .error err
      | .ok results => do
          let mut matchCount := 0
          for i in [:results.size] do
            match results[i]? with
            | some recordJson =>
                match ← checkArtifactRecord s!"manifest.results[{i}]" internalJson recordJson with
                | .error err => return .error err
                | .ok true => matchCount := matchCount + 1
                | .ok false => pure ()
            | none => return .error s!"manifest.results[{i}]: missing artifact record"
          if matchCount == 1 then
            return .ok ()
          else
            return .error s!"expected exactly one artifact record for {internalJson}, found {matchCount}"

private def runGobraArtifactCheck (args : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  match parseGobraArtifactCheckArgs args {} with
  | .error err =>
      IO.eprintln err
      return 2
  | .ok cfg =>
      match cfg.manifest, cfg.internalJson with
      | some manifest, some internalJson =>
          let manifest := absoluteFrom cwd manifest
          let internalJson := absoluteFrom cwd internalJson
          match ← checkArtifactManifest manifest internalJson with
          | .ok _ =>
              IO.println s!"ok: {internalJson}"
              return 0
          | .error err =>
              IO.eprintln err
              return 1
      | _, _ =>
          IO.eprintln s!"provide --manifest <file> and --internal-json <file>\n{usage}"
          return 2

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
              IO.println (cliErrorJson s!"{input}: {err}").compress
              return 1
          | .ok doc =>
              let doc? : Except String GobraJson.Document :=
                match cfg.ignoreAssertAt with
                | some (line, column) =>
                    let (doc, count) := ignoreAssertAtDocument line column doc
                    if count == 1 then
                      Except.ok doc
                    else
                      Except.error s!"--ignore-assert-at expected exactly one assertion at {line}:{column}, found {count}"
                | none => Except.ok doc
              match doc? with
              | .error err =>
                  IO.println (cliErrorJson err).compress
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
  | "gobra-artifact-check" :: rest => runGobraArtifactCheck rest
  | "observation-eq" :: rest => runObservationEq rest
  | [] =>
      IO.println usage
      return 0
  | cmd :: _ =>
      IO.eprintln s!"unknown command: {cmd}\n{usage}"
      return 2

end GoLean.CLI
