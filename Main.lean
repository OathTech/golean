import GoLean
import Lean.Elab.Term

-- [AGENT] F8: elaboration embeds the inputs, rather than reading current
-- source when an old executable runs. The certified builder checks this
-- value after Lake's content-rehashed build and before any cache reuse.
open Lean Elab Term in
elab "compiledBuildInputs%" : term => do
  let result ← IO.Process.output {
    cmd := "python3", args := #["tools/certification.py", "build-identity"],
    -- Lake supplies the import path for elaboration. Public build/cache
    -- commands refuse caller overrides; this query only hashes the inputs.
    env := #[("LEAN_PATH", none)] }
  if result.exitCode != 0 then
    throwError "cannot bind compiled inputs: {result.stderr}"
  return Lean.mkStrLit result.stdout.trimAscii.toString

private def compiledBuildInputs : String := compiledBuildInputs%

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--build-provenance"] => do
      IO.println compiledBuildInputs
      return 0
  -- Lane tooling (membership-depth lane, 2026-09-01): the labeled
  -- consumption tracer / menu-invariant validator. Dispatched here rather
  -- than in `GoLean.CLI.main` because the module imports CLI (it reuses
  -- the enumerator's accountant and driver copies).
  | "choice-trace" :: rest => GoLean.ChoiceTrace.main rest
  | _ => GoLean.CLI.main args
