import GoLean.GoCore.Seed
import GoLean.GoCore.Multi

/-!
# The seeded-heap entry on the POOL driver (slice A, design §6/§4 S6)

`runProgramPoolOutM`'s wiring over the seeded setup — the CLI's driver for `--seed` (slice B).
Separate from `Seed.lean` only because it needs `Multi`; upstream of the proofs (slice B's CLI
driver imports this, not the soundness modules). Its erasure statement (the empty seed with scalar
arguments IS `runProgramPoolOutM`) is `SetupStatement.runProgramPoolSeeded_empty_stmt`, proved in
`SetupSound.lean`.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-- The seeded whole-PROGRAM pool entry: the seeded setup, the subject on the pool, the results
and the final seed cells read from the shared state at main's exit; the output folded before a
`Stop` travels with it, as in `runProgramPoolOutM`. -/
def runProgramPoolSeededOutM (fuel : Nat) (program : Program) (name : String)
    (seed : Array SeedCell) (args : Array SeedArg) (choices : Choices := []) :
    Except (Stop × GoString) SeededReadout :=
  match runProgramSetupSeededM fuel program name seed args choices with
  | .error e => .error (e, GoString.empty)
  | .ok (pctx, c₀, s₀, resultLocs, slots, choices₁) =>
      match execProgLoopOut pctx fuel ⟨#[Thread.running c₀ none], s₀, 0⟩ {} choices₁ GoString.empty with
      | (out, .error e) => .error (e, out)
      | (out, .ok (sF, _)) =>
          match loadMany pctx sF resultLocs with
          | .error e => .error (e, out)
          | .ok vs =>
              match loadMany pctx sF slots.toList with
              | .error e => .error (e, out)
              | .ok fs => .ok { readout := { values := vs.toArray, output := out }, seedFinal := fs.toArray }

end GoLean.GoCore.Machine
