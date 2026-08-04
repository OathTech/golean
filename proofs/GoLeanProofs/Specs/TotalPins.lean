import GoLeanProofs.Specs.GoldenSurface
import GoLeanProofs.Specs.GoldenRecover
import GoLeanProofs.Specs.GoldenQuorumWP
import GoLeanProofs.Specs.GoldenQuorumThree
import GoLeanProofs.Specs.Statements

/-!
# Total-correctness pins (sem-adequacy arc slice 5, 2026-08-04)

The concrete pinned programs' TERMINATION, kernel-checked — ∀-streams
quantifier included — plus the two now-payable UNCONDITIONAL negative
twins.

**How the ∀-streams quantifier is discharged** (`Surface.Terminates`
quantifies every choice stream at one uniform fuel bound, but a kernel
run exhibits one stream): `Machine.allStreamsOk` explores the run once,
using the machine's choices discipline — every arm that is not the
`mapIterK` pick or an `appendSlice` apply is provably stream-oblivious
(`stepFn_oblivious`), the pick is BRANCHED over every possible index, and
an `appendSlice` apply position fails the checker closed. One
`decide +kernel` of the checker at fuel `N` plus
`execStmtLoop_ok_of_allStreamsOk` and `execStmtLoop_mono` yields
`Terminates` outright. Measured cost (2026-08-04): all four pins ≈ 6 s
total under the 16 GiB kernel cap — the slice-1 spike's tractability
verdict carries over to the branched exploration (threeAll explores all
3! = 6 pick orders).

**Scope honesty**: these are PER-SEED total results (`Terminates` at the
pinned initial state, conjoined with the proven run-conditioned readout
as `<pin>TotalReadout`). The ∀-config statements stay at `GoSpec`
strength — symbolic termination over every admissible state (full
`GoSpecT`) is recorded as owed in the arc doc, not attempted.

**The unconditional twins**: `quorumOneKnownNotEleven_statement` /
`quorumThreeAllNotTwelve_statement` (targets since phase 4, then
provably out of reach: a `GoTriple` is vacuous on a diverging program,
so refuting a wrong `GoFuncSpec` needs a terminating run EXHIBITED).
The kernel-exhibited `.normal` run plus the run-conditioned readout at
the true value contradicts the wrong spec's triple — discharged below,
names `quorumOneKnownNotEleven` / `quorumThreeAllNotTwelve` (the
run-conditioned twins keep their content under `*Run` names).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum GoLean.Iris.GoldenRecover
open GoLean.Iris.GoldenSlice

namespace GoLean.Surface

set_option maxRecDepth 1000000

/-! ## Per-pin termination (∀ fuel ≥ N, ∀ streams) -/

/-- The golden pin (inc-via-call) terminates from its seeded state, at
every choice stream, past fuel 300. -/
theorem goldenTerminates : Terminates outEnv goldenOut goldenDriver := by
  refine ⟨300, fun fuel hfuel ch => ?_⟩
  have hall : allStreamsOk 300 goldenOut (.exec goldenDriver outEnv .stop)
      = true := by decide +kernel
  obtain ⟨out, ch', hrun⟩ := execStmtLoop_ok_of_allStreamsOk hall ch
  exact ⟨out, ch', execStmtLoop_mono 300 fuel _ _ _ _ hfuel hrun⟩

/-- The recover pin (panic/recover through defer) terminates from its
seeded state, at every choice stream, past fuel 1000. -/
theorem recoverTerminates :
    Terminates recoverOutEnv
      { types := recoverLowered.typeDefs.toList,
        functions := recoverLowered.funcs, methods := recoverLowered.methods,
        heap := recoverOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[]) := by
  refine ⟨1000, fun fuel hfuel ch => ?_⟩
  have hall : allStreamsOk 1000
      { types := recoverLowered.typeDefs.toList,
        functions := recoverLowered.funcs, methods := recoverLowered.methods,
        heap := recoverOut, nextAddr := 1 }
      (.exec (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
        recoverOutEnv .stop) = true := by decide +kernel
  obtain ⟨out, ch', hrun⟩ := execStmtLoop_ok_of_allStreamsOk hall ch
  exact ⟨out, ch', execStmtLoop_mono 1000 fuel _ _ _ _ hfuel hrun⟩

/-- The one-voter quorum pin (`committedOneKnown`, the real etcd-io/raft
lowering) terminates from its seeded state, at every choice stream, past
fuel 4000. -/
theorem quorumOneKnownTerminates :
    Terminates quorumOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[]) := by
  refine ⟨4000, fun fuel hfuel ch => ?_⟩
  have hall : allStreamsOk 4000
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.exec (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
        quorumOutEnv .stop) = true := by decide +kernel
  obtain ⟨out, ch', hrun⟩ := execStmtLoop_ok_of_allStreamsOk hall ch
  exact ⟨out, ch', execStmtLoop_mono 4000 fuel _ _ _ _ hfuel hrun⟩

/-- The three-voter quorum pin (`committedThreeAll`) terminates from its
seeded state, at EVERY choice stream — all `3! = 6` map-iteration orders
explored by the checker — past fuel 4000. -/
theorem quorumThreeAllTerminates :
    Terminates threeOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[]) := by
  refine ⟨4000, fun fuel hfuel ch => ?_⟩
  have hall : allStreamsOk 4000
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.exec (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
        threeOutEnv .stop) = true := by decide +kernel
  obtain ⟨out, ch', hrun⟩ := execStmtLoop_ok_of_allStreamsOk hall ch
  exact ⟨out, ch', execStmtLoop_mono 4000 fuel _ _ _ _ hfuel hrun⟩

/-! ## The per-seed total forms: termination ∧ readout

The honest per-seed total-correctness statement (the mission's
`<pin>TotalReadout` shape): the seeded run COMPLETES at every stream past
the bound, and every `.normal` completion delivers the pinned value.
NOT full `GoSpecT` — that quantifies all admissible states and needs
symbolic termination (recorded as owed). -/

theorem goldenTotalReadout :
    Terminates outEnv goldenOut goldenDriver ∧ goldenReturnsTwo_statement :=
  ⟨goldenTerminates, goldenReturnsTwo⟩

theorem recoverTotalReadout :
    Terminates recoverOutEnv
      { types := recoverLowered.typeDefs.toList,
        functions := recoverLowered.funcs, methods := recoverLowered.methods,
        heap := recoverOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
    ∧ ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
        execStmt fuel recoverOutEnv
            { types := recoverLowered.typeDefs.toList,
              functions := recoverLowered.funcs,
              methods := recoverLowered.methods,
              heap := recoverOut, nextAddr := 1 } ch
            (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
          = .ok (.normal σf, ch') →
        loadLoc σf (.base ⟨0⟩) = .ok (.int 7 .int) :=
  ⟨recoverTerminates, fun fuel ch σf ch' h =>
    recoverReturnsSeven fuel ch σf ch' h⟩

theorem quorumOneKnownTotalReadout :
    Terminates quorumOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
    ∧ ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
        execStmt fuel quorumOutEnv
            { types := quorumLowered.typeDefs.toList,
              functions := quorumLowered.funcs,
              methods := quorumLowered.methods,
              heap := quorumOut, nextAddr := 1 } ch
            (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
          = .ok (.normal σf, ch') →
        loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) :=
  ⟨quorumOneKnownTerminates, fun fuel ch σf ch' h =>
    quorumOneKnownReturnsTwelve fuel ch σf ch' h⟩

theorem quorumThreeAllTotalReadout :
    Terminates threeOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
    ∧ ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
        execStmt fuel threeOutEnv
            { types := quorumLowered.typeDefs.toList,
              functions := quorumLowered.funcs,
              methods := quorumLowered.methods,
              heap := quorumOut, nextAddr := 1 } ch
            (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
          = .ok (.normal σf, ch') →
        loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) :=
  ⟨quorumThreeAllTerminates, fun fuel ch σf ch' h =>
    quorumThreeAllReturnsSix fuel ch σf ch' h⟩

/-! ## The UNCONDITIONAL negative twins -/

/-- **The unconditional one-voter negative twin** — discharges the
phase-4 target `quorumOneKnownNotEleven_statement`: it is REFUTABLE, with
no run hypothesis, that `committedOneKnown()` meets the `= 11` spec.
Proof shape: the kernel-exhibited terminating `.normal` run ends with
`12` in the target cell (`quorumOneKnownReturnsTwelve`); the assumed
wrong spec's triple applied to that same run forces `11` — `.ok`
injectivity refutes. This is what a `GoTriple`'s vacuity on diverging
programs made impossible before termination was exhibited. -/
theorem quorumOneKnownNotEleven : quorumOneKnownNotEleven_statement := by
  unfold quorumOneKnownNotEleven_statement
  intro hspec
  -- the exhibited terminating run
  have hnorm : (match execStmt 4000 quorumOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 } []
      (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[]) with
    | .ok (.normal _, _) => true
    | _ => false) = true := by decide +kernel
  obtain ⟨σf, chf, hrun⟩ :
      ∃ σf chf, execStmt 4000 quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } []
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, chf) := by
    cases hx : execStmt 4000 quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } []
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[]) with
      | error e => rw [hx] at hnorm; simp at hnorm
      | ok p =>
        obtain ⟨out, chf⟩ := p
        cases out with
        | normal σf => exact ⟨σf, chf, rfl⟩
        | returned σf => rw [hx] at hnorm; simp at hnorm
        | broke σf => rw [hx] at hnorm; simp at hnorm
        | continued σf => rw [hx] at hnorm; simp at hnorm
  -- the true readout at that run
  have h12 := quorumOneKnownReturnsTwelve 4000 [] σf chf hrun
  -- the wrong spec's triple at the same run
  have htriple := (hspec 0 (.int 0 .uint64)).1
  have hres := htriple quorumOut 1 (heapletOf quorumOut) (∅ : Heaplet)
    { disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty
          (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty
                (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := ⟨heapletOf quorumOut, ∅, rfl, rfl,
        fun k => .inr (by
          rw [heaplet_get?_eq]
          exact LawfulPartialMap.get?_empty
            (M := GoHeapF) (k := k)),
        fun k c => ⟨fun h => .inl h, fun h => h.elim id (fun h0 => by
          rw [heaplet_get?_eq,
            LawfulPartialMap.get?_empty
              (M := GoHeapF) (k := k)] at h0
          cases h0)⟩⟩
      wf := by decide +kernel }
    4000 [] σf chf hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨hn11, rfl⟩ := hp2
  subst hn11
  have hget : h.get? 0 = some ⟨some (.int .uint64), .int 11 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have h11 := hsub 0 ⟨some (.int .uint64), .int 11 .uint64⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at h11
  have h11' := loadLoc_base_of_lookup h11
  have := h12.symm.trans h11'
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

/-- **The unconditional three-voter negative twin** — discharges the
phase-4 target `quorumThreeAllNotTwelve_statement` by the same shape:
the exhibited terminating run delivers `6`
(`quorumThreeAllReturnsSix`); the assumed `= 12` spec forces `12` at the
same cell — refuted. `12` is the largest acked index, the answer a
"returns something a voter acked" bug would give. -/
theorem quorumThreeAllNotTwelve : quorumThreeAllNotTwelve_statement := by
  unfold quorumThreeAllNotTwelve_statement
  intro hspec
  have hnorm : (match execStmt 4000 threeOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 } []
      (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[]) with
    | .ok (.normal _, _) => true
    | _ => false) = true := by decide +kernel
  obtain ⟨σf, chf, hrun⟩ :
      ∃ σf chf, execStmt 4000 threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } []
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, chf) := by
    cases hx : execStmt 4000 threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } []
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[]) with
      | error e => rw [hx] at hnorm; simp at hnorm
      | ok p =>
        obtain ⟨out, chf⟩ := p
        cases out with
        | normal σf => exact ⟨σf, chf, rfl⟩
        | returned σf => rw [hx] at hnorm; simp at hnorm
        | broke σf => rw [hx] at hnorm; simp at hnorm
        | continued σf => rw [hx] at hnorm; simp at hnorm
  have h6 := quorumThreeAllReturnsSix 4000 [] σf chf hrun
  have htriple := (hspec 0 (.int 0 .uint64)).1
  have hres := htriple quorumOut 1 (heapletOf quorumOut) (∅ : Heaplet)
    { disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty
          (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty
                (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := ⟨heapletOf quorumOut, ∅, rfl, rfl,
        fun k => .inr (by
          rw [heaplet_get?_eq]
          exact LawfulPartialMap.get?_empty
            (M := GoHeapF) (k := k)),
        fun k c => ⟨fun h => .inl h, fun h => h.elim id (fun h0 => by
          rw [heaplet_get?_eq,
            LawfulPartialMap.get?_empty
              (M := GoHeapF) (k := k)] at h0
          cases h0)⟩⟩
      wf := by decide +kernel }
    4000 [] σf chf hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨hn12, rfl⟩ := hp2
  subst hn12
  have hget : h.get? 0 = some ⟨some (.int .uint64), .int 12 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have h12 := hsub 0 ⟨some (.int .uint64), .int 12 .uint64⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at h12
  have h12' := loadLoc_base_of_lookup h12
  have := h6.symm.trans h12'
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

end GoLean.Surface
