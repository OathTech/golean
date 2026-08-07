import GoLeanProofs

/-!
# The Solution — the real proofs, offered to the judge

Restates every Challenge theorem (statement texts kept in lockstep with
`Challenge.lean` — Comparator rejects on any mismatch, so drift fails
closed) and proves each by direct reference to the theorem in
`GoLeanProofs`. Nothing here is trusted: Comparator re-elaborates, exports,
and kernel-replays this module in a sandbox.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Quorum
open GoLean.Iris.GoldenQuorum GoLean.Iris.GoldenRecover

namespace Judge

/-! ## The golden pin (inc-via-call) -/

theorem goldenTriple : goldenTriple_statement := GoLean.Surface.goldenTriple

theorem goldenSpec : goldenSpec_statement := GoLean.Surface.goldenSpec

theorem goldenFuncSpec : goldenFuncSpec_statement := GoLean.Surface.goldenFuncSpec

theorem goldenInvariant : goldenInvariant_statement := GoLean.Surface.goldenInvariant

theorem goldenReturnsTwo : goldenReturnsTwo_statement := GoLean.Surface.goldenReturnsTwo

theorem goldenNotThree : goldenNotThree_statement := GoLean.Surface.goldenNotThree

/-! ## The recover pin -/

theorem recoverFuncSpec : recoverFuncSpec_statement := GoLean.Surface.recoverFuncSpec

theorem recoverReturnsSeven
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel recoverOutEnv
        { types := recoverLowered.typeDefs.toList,
          functions := recoverLowered.funcs, methods := recoverLowered.methods,
          heap := recoverOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 7 .int) :=
  GoLean.Surface.recoverReturnsSeven fuel ch σf ch' hrun

/-! ## The quorum pilot, one voter -/

theorem quorumOneKnownFuncSpec : quorumOneKnownFuncSpec_statement :=
  GoLean.Surface.quorumOneKnownFuncSpec

theorem quorumOneKnownMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1] GoLean.Quorum.ackedOneKnown
          n.toNat)) :=
  GoLean.Surface.quorumOneKnownMeetsSpec

theorem quorumOneKnownReturnsTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) :=
  GoLean.Surface.quorumOneKnownReturnsTwelve fuel ch σf ch' hrun

theorem quorumOneKnownNotEleven : quorumOneKnownNotEleven_statement :=
  GoLean.Surface.quorumOneKnownNotEleven

theorem quorumOneKnownNotElevenRun
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 11 .uint64) :=
  GoLean.Surface.quorumOneKnownNotElevenRun fuel ch σf ch' hrun

/-! ## The comma-ok method -/

theorem quorumAckedIndexFuncSpec2 : quorumAckedIndexFuncSpec2_statement :=
  GoLean.Surface.quorumAckedIndexFuncSpec2

theorem quorumAckedIndexReturnsTwelveTrue
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel ackedIndexOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := ackedIndexOut, nextAddr := 4 } ch
        (.call #[.var "$callres0", .var "$callres1"]
          ⟨"main.mapAckIndexer.AckedIndex"⟩ #[.var "m", .intLit 3 .uint64])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64)
      ∧ loadLoc σf (.base ⟨1⟩) = .ok (.bool true) :=
  GoLean.Surface.quorumAckedIndexReturnsTwelveTrue fuel ch σf ch' hrun

/-! ## The 3-voter instance -/

theorem quorumThreeAllFuncSpec : quorumThreeAllFuncSpec_statement :=
  GoLean.Surface.quorumThreeAllFuncSpec

theorem quorumThreeAllMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedThreeAll"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1, 2, 3] GoLean.Quorum.ackedThreeAll
          n.toNat)) :=
  GoLean.Surface.quorumThreeAllMeetsSpec

theorem quorumThreeAllReturnsSix
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) :=
  GoLean.Surface.quorumThreeAllReturnsSix fuel ch σf ch' hrun

theorem quorumThreeAllNotTwelve : quorumThreeAllNotTwelve_statement :=
  GoLean.Surface.quorumThreeAllNotTwelve

theorem quorumThreeAllNotTwelveRun
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 12 .uint64) :=
  GoLean.Surface.quorumThreeAllNotTwelveRun fuel ch σf ch' hrun

/-! ## The per-seed total pins -/

theorem goldenTerminates : Terminates outEnv goldenOut goldenDriver :=
  GoLean.Surface.goldenTerminates

theorem recoverTerminates :
    Terminates recoverOutEnv
      { types := recoverLowered.typeDefs.toList,
        functions := recoverLowered.funcs, methods := recoverLowered.methods,
        heap := recoverOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[]) :=
  GoLean.Surface.recoverTerminates

theorem quorumOneKnownTerminates :
    Terminates quorumOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[]) :=
  GoLean.Surface.quorumOneKnownTerminates

theorem quorumThreeAllTerminates :
    Terminates threeOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[]) :=
  GoLean.Surface.quorumThreeAllTerminates

theorem goldenTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel outEnv goldenOut ch goldenDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int) :=
  GoLean.Surface.goldenTotalReadout

theorem recoverTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel recoverOutEnv
            { types := recoverLowered.typeDefs.toList,
              functions := recoverLowered.funcs,
              methods := recoverLowered.methods,
              heap := recoverOut, nextAddr := 1 } ch
            (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 7 .int) :=
  GoLean.Surface.recoverTotalReadout

theorem quorumOneKnownTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel quorumOutEnv
            { types := quorumLowered.typeDefs.toList,
              functions := quorumLowered.funcs,
              methods := quorumLowered.methods,
              heap := quorumOut, nextAddr := 1 } ch
            (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) :=
  GoLean.Surface.quorumOneKnownTotalReadout

theorem quorumThreeAllTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel threeOutEnv
            { types := quorumLowered.typeDefs.toList,
              functions := quorumLowered.funcs,
              methods := quorumLowered.methods,
              heap := quorumOut, nextAddr := 1 } ch
            (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) :=
  GoLean.Surface.quorumThreeAllTotalReadout

/-! ## The ∀-config summit -/

theorem committedIndexAllConfigs : committedIndexAllConfigs_statement :=
  GoLean.Surface.committedIndexAllConfigs

theorem committedIndexAllReturnsSix
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel allOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := allOut, nextAddr := 5 } ch
        (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
          #[.var "c", .var "l"])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) :=
  GoLean.Surface.committedIndexAllReturnsSix fuel ch σf ch' hrun

theorem committedIndexAllNotTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel allOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := allOut, nextAddr := 5 } ch
        (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
          #[.var "c", .var "l"])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 12 .uint64) :=
  GoLean.Surface.committedIndexAllNotTwelve fuel ch σf ch' hrun

theorem committedIndexAll_refutes_wrong (c : List Nat)
    (acked : Nat → Option Nat) (r : Nat) (hne : r ≠ committedIndexRef c acked) :
    ¬ GoLean.Quorum.IsCommittedIndex c acked r :=
  GoLean.Surface.committedIndexAll_refutes_wrong c acked r hne

/-! ## The math bridge -/

theorem committedIndexRef_meets_spec : committedIndexRef_meets_spec_statement :=
  GoLean.Quorum.committedIndexRef_meets_spec


/-! ## The fork/join pool kernel witnesses (channels arc slice 2) -/

theorem forkJoinStreamCanonical : fjRunGives42 400 [] = true :=
  GoLean.Surface.forkJoinStreamCanonical

theorem forkJoinStreamAdversarial :
    fjRunGives42 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true :=
  GoLean.Surface.forkJoinStreamAdversarial

theorem forkJoinStreamAlternating :
    fjRunGives42 400 [1, 0, 1, 0, 1, 0, 1, 0] = true :=
  GoLean.Surface.forkJoinStreamAlternating

theorem forkJoinDeadlockCanonical : fjRunDeadlocks 400 [] = true :=
  GoLean.Surface.forkJoinDeadlockCanonical

theorem forkJoinDeadlockAdversarial :
    fjRunDeadlocks 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true :=
  GoLean.Surface.forkJoinDeadlockAdversarial

end Judge
