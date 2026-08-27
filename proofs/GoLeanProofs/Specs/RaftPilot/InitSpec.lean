import GoLeanProofs.RunGlue
import GoLeanProofs.Specs.TwinProgram
import GoLeanProofs.Sym.KernelRfl

/-!
# W2 unit 3, stage A: THE INIT SPEC at the `runProgramSetupM`
boundary (the machine's own setup: `seedGlobals` + `$pkginit` + the
entry frame)

**What this replaces and how (the killed-seed-pins successor):** the
W0-killed `StaticCells` pinned raw heap literals by replaying init in
the kernel per fact. Here the conclusion is a SPEC-shaped, composable
statement over `runProgramSetupM` (RunGlue's unfolding boundary — the
exact hypothesis `FastEval/Transfer` and `ChoiceInv.anchorRunProg`
already consume), concluded in reader vocabulary (the statics the
handlers read; every static materialized; the stream untouched), with
fuel ∃-quantified and monotone (no subject-run counts in the export).
The ∃-discharge is ONE kernel replay (`initFacts_true` — the
charter's carve-out: exhibiting a run is how existentials are
proved), shared by every exported conjunct: the derivations below it
are symbolic case analyses of the same opaque computation, so the
1,382-step init is evaluated exactly once, at OPEN stream (the init
phase is choice-free, so reduction never inspects `ch` — the
open-tail principle at the stream).

**Scoping fact (recorded in the W2 log, derivation: the wire walk):**
`$pkginit` is LOOP-FREE (44 straight-line statements) — the plan's
"init's loops" (the 3-node `newTwin` build) live inside the SUBJECT's
entry function, past this boundary; proving that prefix needs
W3-class library CallSpecs (`NewMemoryStorage`/`ApplySnapshot`/
`NewRawNode`) and is the recorded stage-B gap, not silently absorbed.

The exported conclusion is the future invariant's base clause at this
boundary (W2.5 consumes it): the machine is at the entry
configuration of `twinChoiceVerdict` with pinned result cells, every
static root `⟨0⟩…⟨30⟩` is materialized (wire declaration order —
`seedGlobals`' address pin), `loggerInstalled ⟨30⟩` is `false`, and
the choice stream is UNTOUCHED (init is stream-transparent).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.Examples.RaftTwin (twinLowered)

/-- Stage-A fuel (private scaffolding; the export ∃-quantifies it and
`runProgramSetupM_mono` lifts to every larger fuel). -/
private def initFuel : Nat := 1500

/-- ONE Bool over the whole setup computation at the EMPTY stream: it
succeeds, at the entry-frame shape, with the stream untouched, every
static materialized, and `loggerInstalled = false`. -/
private def initFacts : Bool :=
  match runProgramSetupM initFuel twinLowered "twinChoiceVerdict" #[] [] with
  | .ok (c₀, s₃, rls, chOut) =>
      (match c₀ with
        | .exec _ _ (.frame [] [] [] [] .stop false) => true
        | _ => false)
      && chOut.isEmpty
      && (List.range 31).all (fun g =>
          match loadLoc s₃ (.base ⟨g⟩) with
          | .ok _ => true
          | _ => false)
      && (match loadLoc s₃ (.base ⟨30⟩) with
          | .ok (.bool false) => true
          | _ => false)
  | .error _ => false

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 1024000000 in
/-- THE ∃-DISCHARGE, half 1: one kernel replay at the empty stream. -/
private theorem initFacts_true : initFacts = true := by
  kernel_rfl

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 1024000000 in
/-- THE ∃-DISCHARGE, half 2: the setup is STREAM-TRANSPARENT — at any
stream it computes the empty-stream result with the stream threaded
through untouched (the init phase is choice-free; kernel reduction at
the OPEN stream never inspects it — the open-tail principle at the
stream). Stated in the map form so no literal appears. -/
private theorem setup_stream_transparent (ch : Choices) :
    runProgramSetupM initFuel twinLowered "twinChoiceVerdict" #[] ch
      = (runProgramSetupM initFuel twinLowered "twinChoiceVerdict" #[] []).map
          (fun r => (r.1, r.2.1, r.2.2.1, ch)) := by
  kernel_rfl

/-- **THE INIT SPEC (stage A)**: at every sufficient fuel and EVERY
choice stream, the machine's setup reaches `twinChoiceVerdict`'s
entry configuration — the entry frame over `.stop` with pinned result
cells — in a state where every static root `⟨0⟩…⟨30⟩` is
materialized and `loggerInstalled ⟨30⟩` reads `false`, with the
stream UNTOUCHED. Fuel is existential/monotone; no subject-run count
appears in this statement. -/
theorem initSetup_establishes :
    ∃ F₀ : Nat, ∀ fuel : Nat, F₀ ≤ fuel → ∀ ch : Choices,
    ∃ (stmt : Stmt) (env : LocalEnv) (rls : List Loc) (s₃ : ExecState),
      runProgramSetupM fuel twinLowered "twinChoiceVerdict" #[] ch
        = .ok (.exec stmt env (.frame [] [] [] [] .stop false), s₃, rls, ch)
      ∧ (∀ g : Nat, g < 31 → ∃ v, loadLoc s₃ (.base ⟨g⟩) = .ok v)
      ∧ loadLoc s₃ (.base ⟨30⟩) = .ok (.bool false) := by
  refine ⟨initFuel, fun fuel hfuel ch => ?_⟩
  have hfacts := initFacts_true
  unfold initFacts at hfacts
  revert hfacts
  cases hrun : runProgramSetupM initFuel twinLowered "twinChoiceVerdict"
      #[] [] with
  | error e => intro hfacts; cases hfacts
  | ok r =>
      obtain ⟨c₀, s₃, rls₀, chOut⟩ := r
      intro hfacts
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hfacts
      obtain ⟨⟨⟨hshape, hch⟩, hall⟩, hlog⟩ := hfacts
      -- the run at ch, lifted to fuel
      have hstream := setup_stream_transparent ch
      rw [hrun] at hstream
      simp only [Except.map] at hstream
      have hrunFuel := runProgramSetupM_mono hfuel hstream
      -- the entry shape: dismiss every non-matching constructor by
      -- Bool-reduction, leaving the entry-frame branch
      revert hshape
      cases c₀ <;> try (intro h; exact Bool.noConfusion h)
      rename_i stmt env k
      cases k <;> try (intro h; exact Bool.noConfusion h)
      rename_i t te rls' ds k₂ w
      cases t <;> try (intro h; exact Bool.noConfusion h)
      cases te <;> try (intro h; exact Bool.noConfusion h)
      cases rls' <;> try (intro h; exact Bool.noConfusion h)
      cases ds <;> try (intro h; exact Bool.noConfusion h)
      cases k₂ <;> try (intro h; exact Bool.noConfusion h)
      cases w <;> try (intro h; exact Bool.noConfusion h)
      intro _
      refine ⟨stmt, env, rls₀, s₃, hrunFuel, ?_, ?_⟩
      · intro g hg
        have hg31 : g ∈ List.range 31 := List.mem_range.mpr hg
        have hgo := (List.all_eq_true.mp hall) g hg31
        revert hgo
        cases hload : loadLoc s₃ (.base ⟨g⟩) with
        | ok v => exact fun _ => ⟨v, rfl⟩
        | error e => intro h; cases h
      · revert hlog
        cases hload : loadLoc s₃ (.base ⟨30⟩) with
        | error e => intro h; cases h
        | ok v =>
            cases v <;> intro hlog <;>
              first
              | cases hlog
              | (rename_i b
                 cases b with
                 | true => cases hlog
                 | false => rfl)

end GoLean.RaftSeam
