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
  scratchSource : FilePath
  internalPath : FilePath
  vprPath : FilePath
  stdoutPath : FilePath
  stderrPath : FilePath
  resultPath : FilePath
  exitCode : UInt32
  internalExists : Bool
  vprExists : Bool
  deriving Repr

def ExportResult.success (r : ExportResult) : Bool :=
  r.exitCode == 0 && r.internalExists && r.vprExists

private def jsonPath (p : FilePath) : Json :=
  Json.str p.toString

def ExportResult.toJson (r : ExportResult) : Json :=
  Json.mkObj [
    ("id", Json.str r.id),
    ("source", jsonPath r.source),
    ("scratchSource", jsonPath r.scratchSource),
    ("internalPath", jsonPath r.internalPath),
    ("vprPath", jsonPath r.vprPath),
    ("stdoutPath", jsonPath r.stdoutPath),
    ("stderrPath", jsonPath r.stderrPath),
    ("resultPath", jsonPath r.resultPath),
    ("exitCode", Lean.toJson r.exitCode.toNat),
    ("internalExists", Lean.toJson r.internalExists),
    ("vprExists", Lean.toJson r.vprExists),
    ("success", Lean.toJson r.success)
  ]

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

def exportOne (opts : ExportOptions) (entry : CorpusEntry) : IO ExportResult := do
  let workDir := opts.outDir / "work" / entry.id
  let resultDir := opts.outDir / "results" / entry.id
  IO.FS.createDirAll workDir
  IO.FS.createDirAll resultDir

  let sourceName := entry.source.fileName.getD "input.gobra"
  let scratchSource := workDir / sourceName
  copyTextFile entry.source scratchSource

  let stdoutPath := resultDir / "stdout.txt"
  let stderrPath := resultDir / "stderr.txt"
  let resultPath := resultDir / "result.json"
  let internalPath := postfixFile scratchSource "internal"
  let vprPath := postfixFile scratchSource "vpr"

  let gobraCommand := s!"run --noVerify --printInternal --printVpr -i {scratchSource}"
  let output ← IO.Process.output {
    cmd := "bash",
    args := #[opts.gobraSbt.toString, gobraCommand]
  }
  IO.FS.writeFile stdoutPath output.stdout
  IO.FS.writeFile stderrPath output.stderr

  let internalExists ← internalPath.pathExists
  let vprExists ← vprPath.pathExists
  let result : ExportResult := {
    id := entry.id,
    source := entry.source,
    scratchSource,
    internalPath,
    vprPath,
    stdoutPath,
    stderrPath,
    resultPath,
    exitCode := output.exitCode,
    internalExists,
    vprExists
  }
  writeJsonFile resultPath result.toJson
  return result

def exportMany (opts : ExportOptions) (entries : List CorpusEntry) : IO (List ExportResult) := do
  let mut results := []
  for entry in entries do
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
