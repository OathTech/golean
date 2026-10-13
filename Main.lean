import GoLean

-- The executable's entry point. (The `compiledBuildInputs%` macro that shelled
-- out to tools/certification.py at elaboration time, and the
-- `--build-provenance` arm that printed it, left with the certificate
-- apparatus in the 2026-10-12 gate cull.)
def main (args : List String) : IO UInt32 :=
  match args with
  -- Lane tooling (membership-depth lane, 2026-09-01): the labeled
  -- consumption tracer / menu-invariant validator. Dispatched here rather
  -- than in `GoLean.CLI.main` because the module imports CLI (it reuses
  -- the enumerator's accountant and driver copies).
  | "choice-trace" :: rest => GoLean.ChoiceTrace.main rest
  -- `native-json-run`'s consumption report (F1 of the 2026-10-13 fail-closed pass) is the
  -- tracer's pass, handed to the CLI for the same reason.
  | _ => GoLean.CLI.main GoLean.ChoiceTrace.consumptionReport args
