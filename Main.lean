import GoLean

def main (args : List String) : IO UInt32 :=
  match args with
  -- Lane tooling (membership-depth lane, 2026-09-01): the labeled
  -- consumption tracer / menu-invariant validator. Dispatched here rather
  -- than in `GoLean.CLI.main` because the module imports CLI (it reuses
  -- the enumerator's accountant and driver copies).
  | "choice-trace" :: rest => GoLean.ChoiceTrace.main rest
  | _ => GoLean.CLI.main args
