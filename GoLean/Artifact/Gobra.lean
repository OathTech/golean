import GoLean.StrictJson
import Lean.Data.Json

namespace GoLean.Artifact.Gobra

open System
open Lean

structure CorpusEntry where
  id : String
  source : FilePath
  deriving Repr

structure ExportOptions where
  gobraSbt : FilePath
  outDir : FilePath
  deriving Repr

structure ExportResult where
  id : String
  source : FilePath
  sourceSha256 : String
  scratchSource : FilePath
  scratchSourceSha256 : String
  internalPath : FilePath
  internalJsonPath : FilePath
  vprPath : FilePath
  stdoutPath : FilePath
  stderrPath : FilePath
  resultPath : FilePath
  exitCode : UInt32
  internalExists : Bool
  internalJsonExists : Bool
  vprExists : Bool
  deriving Repr

def ExportResult.success (r : ExportResult) : Bool :=
  r.exitCode == 0 && r.internalExists && r.internalJsonExists

private def jsonPath (p : FilePath) : Json :=
  Json.str p.toString

def ExportResult.toJson (r : ExportResult) : Json :=
  Json.mkObj [
    ("id", Json.str r.id),
    ("source", jsonPath r.source),
    ("sourceSha256", Json.str r.sourceSha256),
    ("scratchSource", jsonPath r.scratchSource),
    ("scratchSourceSha256", Json.str r.scratchSourceSha256),
    ("internalPath", jsonPath r.internalPath),
    ("internalJsonPath", jsonPath r.internalJsonPath),
    ("vprPath", jsonPath r.vprPath),
    ("stdoutPath", jsonPath r.stdoutPath),
    ("stderrPath", jsonPath r.stderrPath),
    ("resultPath", jsonPath r.resultPath),
    ("exitCode", Lean.toJson r.exitCode.toNat),
    ("internalExists", Lean.toJson r.internalExists),
    ("internalJsonExists", Lean.toJson r.internalJsonExists),
    ("vprExists", Lean.toJson r.vprExists),
    ("success", Lean.toJson r.success)
  ]

private def decodeExportResult (path : String) (json : Json) : Except String ExportResult := do
  let obj ← GoLean.StrictJson.obj path json
  GoLean.StrictJson.requireExactKeys path obj [
    "exitCode",
    "id",
    "internalExists",
    "internalJsonExists",
    "internalJsonPath",
    "internalPath",
    "resultPath",
    "scratchSource",
    "scratchSourceSha256",
    "source",
    "sourceSha256",
    "stderrPath",
    "stdoutPath",
    "success",
    "vprExists",
    "vprPath"
  ]
  let exitCode ← GoLean.StrictJson.nat s!"{path}.exitCode" (← GoLean.StrictJson.field path obj "exitCode")
  if exitCode > UInt32.size then
    throw s!"{path}.exitCode: expected UInt32 exit code, got {exitCode}"
  return {
    id := (← GoLean.StrictJson.string s!"{path}.id" (← GoLean.StrictJson.field path obj "id")),
    source := FilePath.mk (← GoLean.StrictJson.string s!"{path}.source" (← GoLean.StrictJson.field path obj "source")),
    sourceSha256 := (← GoLean.StrictJson.string s!"{path}.sourceSha256" (← GoLean.StrictJson.field path obj "sourceSha256")),
    scratchSource := FilePath.mk (← GoLean.StrictJson.string s!"{path}.scratchSource" (← GoLean.StrictJson.field path obj "scratchSource")),
    scratchSourceSha256 :=
      (← GoLean.StrictJson.string s!"{path}.scratchSourceSha256" (← GoLean.StrictJson.field path obj "scratchSourceSha256")),
    internalPath := FilePath.mk (← GoLean.StrictJson.string s!"{path}.internalPath" (← GoLean.StrictJson.field path obj "internalPath")),
    internalJsonPath :=
      FilePath.mk (← GoLean.StrictJson.string s!"{path}.internalJsonPath" (← GoLean.StrictJson.field path obj "internalJsonPath")),
    vprPath := FilePath.mk (← GoLean.StrictJson.string s!"{path}.vprPath" (← GoLean.StrictJson.field path obj "vprPath")),
    stdoutPath := FilePath.mk (← GoLean.StrictJson.string s!"{path}.stdoutPath" (← GoLean.StrictJson.field path obj "stdoutPath")),
    stderrPath := FilePath.mk (← GoLean.StrictJson.string s!"{path}.stderrPath" (← GoLean.StrictJson.field path obj "stderrPath")),
    resultPath := FilePath.mk (← GoLean.StrictJson.string s!"{path}.resultPath" (← GoLean.StrictJson.field path obj "resultPath")),
    exitCode := UInt32.ofNat exitCode,
    internalExists := (← GoLean.StrictJson.bool s!"{path}.internalExists" (← GoLean.StrictJson.field path obj "internalExists")),
    internalJsonExists := (← GoLean.StrictJson.bool s!"{path}.internalJsonExists" (← GoLean.StrictJson.field path obj "internalJsonExists")),
    vprExists := (← GoLean.StrictJson.bool s!"{path}.vprExists" (← GoLean.StrictJson.field path obj "vprExists"))
  }

private def absoluteFrom (base : FilePath) (path : FilePath) : FilePath :=
  if path.isRelative then (base / path).normalize else path.normalize

private def ensureParent (path : FilePath) : IO Unit := do
  match path.parent with
  | some parent => IO.FS.createDirAll parent
  | none => pure ()

private def copyTextFile (source dest : FilePath) : IO Unit := do
  ensureParent dest
  let contents ← IO.FS.readFile source
  IO.FS.writeFile dest contents

private def firstField? (text : String) : Option String :=
  text.trimAscii.toString.splitOn " " |>.filter (fun s => !s.isEmpty) |>.head?

def sha256File (path : FilePath) : IO String := do
  let shasum ← IO.Process.output {
    cmd := "shasum",
    args := #["-a", "256", path.toString]
  }
  if shasum.exitCode == 0 then
    match firstField? shasum.stdout with
    | some hash => return hash
    | none => throw <| IO.userError s!"shasum produced no hash for {path}"
  else
    let sha256sum ← IO.Process.output {
      cmd := "sha256sum",
      args := #[path.toString]
    }
    if sha256sum.exitCode == 0 then
      match firstField? sha256sum.stdout with
      | some hash => return hash
      | none => throw <| IO.userError s!"sha256sum produced no hash for {path}"
    else
      throw <| IO.userError s!"could not compute sha256 for {path}: {shasum.stderr}{sha256sum.stderr}"

private def postfixFile (path : FilePath) (suffix : String) : FilePath :=
  let name := path.fileName.getD path.toString
  match path.parent with
  | some parent => parent / s!"{name}.{suffix}"
  | none => FilePath.mk s!"{name}.{suffix}"

private def parseManifestLine (base : FilePath) (lineNo : Nat) (line : String) :
    Except String (Option CorpusEntry) := do
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty || trimmed.startsWith "#" then
    return none
  let fields := trimmed.splitOn " " |>.filter (fun s => !s.isEmpty)
  match fields with
  | [id, source] =>
      return some { id, source := absoluteFrom base (FilePath.mk source) }
  | _ =>
      throw s!"invalid manifest line {lineNo}: expected '<id> <path>'"

def readManifest (manifest : FilePath) : IO (Except String (List CorpusEntry)) := do
  let contents ← IO.FS.readFile manifest
  let base := manifest.parent.getD "."
  let mut entries := []
  let mut lineNo := 1
  for line in contents.splitOn "\n" do
    match parseManifestLine base lineNo line with
    | .ok none => pure ()
    | .ok (some entry) => entries := entries.concat entry
    | .error err => return .error err
    lineNo := lineNo + 1
  return .ok entries

private def writeJsonFile (path : FilePath) (json : Json) : IO Unit := do
  ensureParent path
  IO.FS.writeFile path (json.compress ++ "\n")

private def readExportResult? (path : FilePath) : IO (Option ExportResult) := do
  if !(← path.pathExists) then
    return none
  match Json.parse (← IO.FS.readFile path) with
  | .error _ => return none
  | .ok json =>
      match decodeExportResult path.toString json with
      | .error _ => return none
      | .ok result => return some result

private def samePath (left right : FilePath) : Bool :=
  left.normalize.toString == right.normalize.toString

private def reusableResult? (entry : CorpusEntry) (result : ExportResult) : IO Bool := do
  if result.id != entry.id || !samePath result.source entry.source || !result.success then
    return false
  let sourceSha256 ← sha256File entry.source
  if result.sourceSha256 != sourceSha256 || result.scratchSourceSha256 != sourceSha256 then
    return false
  if !(← result.scratchSource.pathExists) ||
      !(← result.internalPath.pathExists) ||
      !(← result.internalJsonPath.pathExists) ||
      !(← result.stdoutPath.pathExists) ||
      !(← result.stderrPath.pathExists) then
    return false
  let scratchSha256 ← sha256File result.scratchSource
  return scratchSha256 == sourceSha256

private def cachedResult? (opts : ExportOptions) (entry : CorpusEntry) : IO (Option ExportResult) := do
  let resultPath := opts.outDir / "results" / entry.id / "result.json"
  match ← readExportResult? resultPath with
  | none => return none
  | some result =>
      if ← reusableResult? entry result then
        return some result
      else
        return none

def exportOne (opts : ExportOptions) (entry : CorpusEntry) : IO ExportResult := do
  let workDir := opts.outDir / "work" / entry.id
  let resultDir := opts.outDir / "results" / entry.id
  IO.FS.createDirAll workDir
  IO.FS.createDirAll resultDir

  let sourceName := entry.source.fileName.getD "input.gobra"
  let scratchSource := workDir / sourceName
  copyTextFile entry.source scratchSource
  let sourceSha256 ← sha256File entry.source
  let scratchSourceSha256 ← sha256File scratchSource

  let stdoutPath := resultDir / "stdout.txt"
  let stderrPath := resultDir / "stderr.txt"
  let resultPath := resultDir / "result.json"
  let internalPath := postfixFile scratchSource "internal"
  let internalJsonPath := postfixFile scratchSource "internal.json"
  let vprPath := postfixFile scratchSource "vpr"

  let gobraCommand := s!"run --noVerify --printInternal --printInternalJson -i {scratchSource}"
  let output ← IO.Process.output {
    cmd := "bash",
    args := #[opts.gobraSbt.toString, gobraCommand]
  }
  IO.FS.writeFile stdoutPath output.stdout
  IO.FS.writeFile stderrPath output.stderr

  let internalExists ← internalPath.pathExists
  let internalJsonExists ← internalJsonPath.pathExists
  let vprExists ← vprPath.pathExists
  let result : ExportResult := {
    id := entry.id,
    source := entry.source,
    sourceSha256,
    scratchSource,
    scratchSourceSha256,
    internalPath,
    internalJsonPath,
    vprPath,
    stdoutPath,
    stderrPath,
    resultPath,
    exitCode := output.exitCode,
    internalExists,
    internalJsonExists,
    vprExists
  }
  writeJsonFile resultPath result.toJson
  return result

def exportMany (opts : ExportOptions) (entries : List CorpusEntry) : IO (List ExportResult) := do
  let mut results := []
  for entry in entries do
    match ← cachedResult? opts entry with
    | some result =>
        IO.println s!"[gobra] {entry.id}: cached"
        results := results.concat result
    | none =>
        IO.println s!"[gobra] exporting {entry.id}"
        let result ← exportOne opts entry
        let status := if result.success then "ok" else "failed"
        IO.println s!"[gobra] {entry.id}: {status}"
        results := results.concat result
  let manifestJson := Json.mkObj [
    ("results", Json.arr (results.map ExportResult.toJson).toArray)
  ]
  writeJsonFile (opts.outDir / "manifest.json") manifestJson
  return results

end GoLean.Artifact.Gobra
