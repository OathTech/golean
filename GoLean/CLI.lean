import GoLean.Artifact.Gobra

namespace GoLean.CLI

open System
open GoLean.Artifact

structure GobraExportArgs where
  manifest : Option FilePath := none
  input : Option FilePath := none
  id : Option String := none
  outDir : FilePath := "artifacts/gobra-smoke"
  gobraSbt : FilePath := "scripts/gobra-sbt"
  deriving Repr

private def usage : String :=
  "usage:\n" ++
  "  golean gobra-export --manifest <file> [--out <dir>] [--gobra-sbt <path>]\n" ++
  "  golean gobra-export --input <file> --id <id> [--out <dir>] [--gobra-sbt <path>]\n"

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

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | "gobra-export" :: rest => runGobraExport rest
  | [] =>
      IO.println usage
      return 0
  | cmd :: _ =>
      IO.eprintln s!"unknown command: {cmd}\n{usage}"
      return 2

end GoLean.CLI
