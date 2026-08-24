import GoLeanProofs.FastEval.Step
import GoLeanProofs.FuelMeasure
import GoLean.GoCore.MachineEqb

/-!
# FastEval — the run-level transfer theorem (campaign Arc 2, unit P2R)

The certified-computation composition for a WHOLE `runProgramM` run
(lineage: data refinement / certified computation — the γ-simulation
story of `FastEval/Step.lean`, widened from the twin's per-checkpoint
kernel walk to a single generic theorem):

    slow setup .ok  +  γ-anchor  +  completed fast body run  +  fast readout
        ⇒  `runProgramM fuel program name args ch = .ok result`

The intended discharge mode is COMPILED evaluation (the `fastreplay`
driver, `GoLeanProofs/FastReplay.lean`): the driver runs each premise's
computation natively and the pinned theorem carries the verdict to the
interpreter-level equation. The trust class of a verdict so obtained is
exactly the trust class of running the interpreter itself compiled
(what `golean native-json-run` does), because every premise is a closed
Boolean-checkable computation — nothing here weakens the model; the
theorem only moves WHICH compiled program one must trust from `stepFn`'s
iteration to `stepFast`'s (whose per-step agreement is `stepFast_ok`).

`absState` (slow state → fast state) is UNTRUSTED METHOD like all of
FastEval — never in any statement closure; the driver never trusts it:
the γ-anchor premise is checked at run time via `ExecState.eqb`
(`fastRun_transfer_eqb`), whose soundness is `ExecState.eqb_sound`.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-- Slow heap → trie, by re-inserting every cell at its base address.
Non-`.base` heap keys are skipped (the machine's allocator never
creates one); any discrepancy is caught by the runtime γ-anchor check,
never silently absorbed. -/
def absHeap : Heap → HeapT
  | [] => .leaf
  | (loc, cell) :: rest =>
      match loc with
      | .base a => (absHeap rest).set a.id cell
      | _ => absHeap rest

/-- Slow state → fast state (untrusted; anchor-checked at run time). -/
def absState (s : ExecState) : ExecStateF :=
  { types := s.types, functions := s.functions, methods := s.methods
    methodSets := s.methodSets, heapT := absHeap s.heap
    nextAddr := s.nextAddr }

/-- **THE RUN-LEVEL TRANSFER** (unit P2R): a completed fast body run
between a successful slow setup and a fast readout IS the whole-program
interpreter verdict. `n ≤ fuel` lets the driver run the body on the
same fuel budget the setup was given. -/
theorem fastRun_transfer {fuel n : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {c₀ : Config} {s₃ : ExecState}
    {locs : List Loc} {ch₁ : Choices} {σF₀ σF' : ExecStateF} {ch' : Choices}
    {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch = .ok (c₀, s₃, locs, ch₁))
    (hanchor : γF σF₀ = s₃)
    (hn : n ≤ fuel)
    (hrun : iterF stepFast n σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch'))
    (hload : loadManyF σF' locs = .ok vs) :
    runProgramM fuel program name args ch = .ok { values := vs.toArray } := by
  have hiter : stepFnIter n (γF σF₀) c₀ ch₁ = .ok (.next .stop, γF σF', ch') :=
    iterF_ok (fun _ _ _ _ _ _ h => stepFast_ok h) hrun
  rw [hanchor] at hiter
  have hfe : n + (fuel - n) = fuel := by omega
  have hrc : runConfig fuel s₃ c₀ ch₁ = .ok (γF σF', ch') := by
    have h := runConfig_of_stepFnIter hiter (fuel - n)
    rw [hfe] at h
    rw [h, runConfig_next_stop]
  have hloadS : loadMany (γF σF') locs = .ok vs := loadManyF_ok hload
  unfold runProgramM
  rw [hsetup]
  simp only [Bind.bind, Except.bind]
  rw [hrc]
  simp only []
  rw [hloadS]
  rfl

/-- The driver-facing corollary: the γ-anchor as the RUN-TIME Boolean
check the `fastreplay` driver actually performs (`ExecState.eqb`,
sound by `ExecState.eqb_sound`). -/
theorem fastRun_transfer_eqb {fuel n : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {c₀ : Config} {s₃ : ExecState}
    {locs : List Loc} {ch₁ : Choices} {σF₀ σF' : ExecStateF} {ch' : Choices}
    {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch = .ok (c₀, s₃, locs, ch₁))
    (hanchor : ExecState.eqb (γF σF₀) s₃ = true)
    (hn : n ≤ fuel)
    (hrun : iterF stepFast n σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch'))
    (hload : loadManyF σF' locs = .ok vs) :
    runProgramM fuel program name args ch = .ok { values := vs.toArray } :=
  fastRun_transfer hsetup (ExecState.eqb_sound _ _ hanchor) hn hrun hload

end GoLean.FastEval
