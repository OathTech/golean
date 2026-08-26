import GoLeanProofs.FastEval.Step
import GoLeanProofs.FuelMeasure
import GoLean.GoCore.MachineEqb
import GoLean.GoCore.MultiSound

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
that of trusting a compiled interpreter entry, because every premise is
a closed Boolean-checkable computation; the theorem moves WHICH
compiled program one must trust from `stepFn`'s iteration to
`stepFast`'s (whose per-step agreement is `stepFast_ok`). ENTRIES
(audit fix round 2, 2026-08-25): `fastRun_transfer` concludes about
`runProgramM`, the SEQUENTIAL entry; `fastRun_transfer_pool` concludes
about `runProgramPoolM`, the THREAD-POOL entry that `golean
native-json-run` computes (via its `runProgramPoolIntsM` wrapper); and
`runProgram_pool_seq_bridge` makes the agreement itself a theorem on
the accepted class — an ok verdict certifies BOTH entries. All four
pool/bridge theorems are Audit-pinned; the load-bearing conservation
step is `execProgLoop_single` (MultiSound), itself pinned via
`execProg_single_eq_execStmt`.

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

/-- **The pool-side run-level transfer** (audit fix round 2,
2026-08-25): the SAME premises the driver checks also certify the
THREAD-POOL whole-program entry `runProgramPoolM` (of which
`runProgramPoolIntsM`, the `native-json-run` entry, is a thin
`args.map GoValue.int` wrapper). Composition: the completed fast run
is a `stepFnIter` prefix (`iterF_ok`), which folds into the sequential
outcome loop (`execStmtLoop_of_stepFnIter` + `execStmtLoop_next_stop`);
a completed `.ok` sequential result is `transferable`, so the
singleton-pool conservation theorem `execProgLoop_single` (MultiSound)
makes it the pool driver's result verbatim. Note this rests on
conservation, NOT on stub enumeration: the operative fact is that an
accepted run COMPLETED sequentially (no spawn ever executed, nothing
blocked), which puts its result in `transferable`'s `.ok` class —
where the sequential and pool drivers provably coincide. -/
theorem fastRun_transfer_pool {fuel n : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {c₀ : Config} {s₃ : ExecState}
    {locs : List Loc} {ch₁ : Choices} {σF₀ σF' : ExecStateF} {ch' : Choices}
    {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch = .ok (c₀, s₃, locs, ch₁))
    (hanchor : γF σF₀ = s₃)
    (hn : n ≤ fuel)
    (hrun : iterF stepFast n σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch'))
    (hload : loadManyF σF' locs = .ok vs) :
    runProgramPoolM fuel program name args ch = .ok { values := vs.toArray } := by
  have hiter : stepFnIter n (γF σF₀) c₀ ch₁ = .ok (.next .stop, γF σF', ch') :=
    iterF_ok (fun _ _ _ _ _ _ h => stepFast_ok h) hrun
  rw [hanchor] at hiter
  have hfe : n + (fuel - n) = fuel := by omega
  have hseq : execStmtLoop fuel s₃ c₀ ch₁ = .ok (.normal (γF σF'), ch') := by
    have h := execStmtLoop_of_stepFnIter hiter (fuel - n)
    rw [hfe] at h
    rw [h, execStmtLoop_next_stop]
  have hpool : execProgLoop fuel ⟨#[c₀], s₃, 0⟩ {} ch₁ =
      .ok (.normal (γF σF'), ch') :=
    execProgLoop_single hseq (by simp [transferable])
  have hloadS : loadMany (γF σF') locs = .ok vs := loadManyF_ok hload
  unfold runProgramPoolM
  rw [hsetup]
  simp only [Bind.bind, Except.bind]
  rw [hpool]
  simp only []
  rw [hloadS]
  rfl

/-- The driver-facing corollary of the pool transfer (`ExecState.eqb`
anchor, as the driver actually checks it). -/
theorem fastRun_transfer_pool_eqb {fuel n : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {c₀ : Config} {s₃ : ExecState}
    {locs : List Loc} {ch₁ : Choices} {σF₀ σF' : ExecStateF} {ch' : Choices}
    {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch = .ok (c₀, s₃, locs, ch₁))
    (hanchor : ExecState.eqb (γF σF₀) s₃ = true)
    (hn : n ≤ fuel)
    (hrun : iterF stepFast n σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch'))
    (hload : loadManyF σF' locs = .ok vs) :
    runProgramPoolM fuel program name args ch = .ok { values := vs.toArray } :=
  fastRun_transfer_pool hsetup (ExecState.eqb_sound _ _ hanchor) hn hrun hload

/-- **`runProgram_pool_seq_bridge`** (audit fix round 2, 2026-08-25 —
resolving the round-1 queued follow-on): on the class the driver
accepts (the checked premises), the SEQUENTIAL and THREAD-POOL
whole-program entries AGREE — both are the same `.ok` verdict, by the
two transfer theorems. An ok verdict from the `fastreplay` driver
therefore certifies BOTH entries. -/
theorem runProgram_pool_seq_bridge {fuel n : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {c₀ : Config} {s₃ : ExecState}
    {locs : List Loc} {ch₁ : Choices} {σF₀ σF' : ExecStateF} {ch' : Choices}
    {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch = .ok (c₀, s₃, locs, ch₁))
    (hanchor : γF σF₀ = s₃)
    (hn : n ≤ fuel)
    (hrun : iterF stepFast n σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch'))
    (hload : loadManyF σF' locs = .ok vs) :
    runProgramM fuel program name args ch =
      runProgramPoolM fuel program name args ch :=
  (fastRun_transfer hsetup hanchor hn hrun hload).trans
    (fastRun_transfer_pool hsetup hanchor hn hrun hload).symm

/-- The driver-facing bridge corollary (`ExecState.eqb` anchor). -/
theorem runProgram_pool_seq_bridge_eqb {fuel n : Nat} {program : Program} {name : String}
    {args : Array GoValue} {ch : Choices} {c₀ : Config} {s₃ : ExecState}
    {locs : List Loc} {ch₁ : Choices} {σF₀ σF' : ExecStateF} {ch' : Choices}
    {vs : List GoValue}
    (hsetup : runProgramSetupM fuel program name args ch = .ok (c₀, s₃, locs, ch₁))
    (hanchor : ExecState.eqb (γF σF₀) s₃ = true)
    (hn : n ≤ fuel)
    (hrun : iterF stepFast n σF₀ c₀ ch₁ = .ok (.next .stop, σF', ch'))
    (hload : loadManyF σF' locs = .ok vs) :
    runProgramM fuel program name args ch =
      runProgramPoolM fuel program name args ch :=
  runProgram_pool_seq_bridge hsetup (ExecState.eqb_sound _ _ hanchor) hn hrun hload

end GoLean.FastEval
