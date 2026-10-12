import GoLean.GoCore.Seed
import GoLean.GoCore.Multi
import GoLean.GoCore.SetupSound

/-!
# The seeded-heap entry on the POOL driver (slice A, design §6/§4 S6)

`runProgramPoolOutM`'s wiring over the seeded setup — the CLI's driver for `--seed` (slice B).
Separate from `Seed.lean` only because it needs `Multi`. Its erasure statement (the empty seed
with scalar arguments IS `runProgramPoolOutM`) is stated and proved here beside the definition.
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

/-- **S6 on the pool: erasure.** With no cells and scalar arguments the seeded pool entry IS
`runProgramPoolOutM` with an empty final seed (one `Except` equation, errors and output included). -/
def runProgramPoolSeeded_empty_stmt : Prop :=
  ∀ (fuel : Nat) (program : Program) (name : String) (args : Array GoValue) (choices : Choices),
    runProgramPoolSeededOutM fuel program name #[] (args.map SeedArg.scalar) choices
      = (fun r : Readout => ({ readout := r, seedFinal := #[] } : SeededReadout)) <$>
          runProgramPoolOutM fuel program name args choices

theorem runProgramPoolSeeded_empty : runProgramPoolSeeded_empty_stmt := by
  intro fuel program name args choices
  unfold runProgramPoolSeededOutM runProgramPoolOutM
  rw [SetupSound.runProgramSetupSeeded_empty]
  cases hs : runProgramSetupM fuel program name args choices with
  | error e => rfl
  | ok r =>
    obtain ⟨pctx, c₀, s₀, resultLocs, choices₁⟩ := r
    dsimp only [Functor.map, Except.map]
    cases hx : execProgLoopOut pctx fuel ⟨#[Thread.running c₀ none], s₀, 0⟩ {} choices₁ GoString.empty with
    | mk out res =>
      cases res with
      | error e => rfl
      | ok r' =>
        obtain ⟨sF, ch⟩ := r'
        dsimp only
        cases hl : loadMany pctx sF resultLocs with
        | error e => rfl
        | ok vs => rfl

end GoLean.GoCore.Machine
