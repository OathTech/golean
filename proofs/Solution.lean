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


/-! ## (The five slice-2 pinned-stream fork/join rows were
RECLASSIFIED to non-designated witnesses at the triage landing,
2026-08-27 — see Challenge.lean's record; proofs remain in
`Specs/GoldenForkJoin.lean`.) -/

/-! ## The slice-5 ∀-schedule fork/join witnesses + GoSpecC witness -/

theorem forkJoinAllSchedules42 : ∀ ch : Choices, fjRunGives42 400 ch = true :=
  GoLean.Surface.forkJoinAllSchedules42

theorem forkJoinNoDeadlock : ∀ ch : Choices,
    execProg 400 fjEnv fjSeed ch forkJoinDriver ≠ .error .deadlock :=
  GoLean.Surface.forkJoinNoDeadlock

theorem forkJoinNoRace : ∀ ch : Choices,
    execProg 400 fjEnv fjSeed ch forkJoinDriver ≠ .error .raceDetected :=
  GoLean.Surface.forkJoinNoRace

theorem forkJoinTerminatesNormallyC :
    TerminatesNormallyC fjEnv fjSeed forkJoinDriver :=
  GoLean.Surface.forkJoinTerminatesNormallyC

open GoLean.Iris.GoldenSlice in
theorem goldenSpecC :
    GoSpecC sliceLowered.typeDefs.toList sliceLowered.funcs
      sliceLowered.methods outEnv outCell0 goldenDriver outCell2 :=
  GoLean.Surface.goldenSpecC

theorem goldenReturnsTwoC
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execProg fuel outEnv goldenOut ch goldenDriver
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int) :=
  GoLean.Surface.goldenReturnsTwoC fuel ch σf ch' hrun

/-! ## The spec-parity designated pairs (D3 user ruling 2026-08-10) -/

open GoLean.ImportedGoose GoLean.ImportedGoose.SemanticsNil in
theorem compareNilToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareNilDriver (importedCellV 1) :=
  GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC

open GoLean.ImportedGoose GoLean.ImportedGoose.SemanticsNil in
theorem compareNilToNilReadoutC
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execProg fuel importedEnv (importedSeed nilLowered) ch
      compareNilDriver = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) :=
  GoLean.ImportedGoose.SemanticsNil.compareNilToNilReadoutC
    fuel ch σf ch' hrun

open GoLean.ImportedGoose GoLean.ImportedGoose.ChannelActris in
theorem dspCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsInt 42) fuel
        ⟨#[.exec dspDriver dspEnv .stop], dspSeed, 0⟩ {} = true :=
  GoLean.ImportedGoose.ChannelActris.dspCert

open GoLean.ImportedGoose GoLean.ImportedGoose.ChannelActris in
theorem dspAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel dspEnv dspSeed ch dspDriver = .ok (.normal σf, ch')
          ∧ cellIsInt 42 σf = true :=
  GoLean.ImportedGoose.ChannelActris.dspAllSchedules

/-! ## The verified-examples gallery — the seven headline claims

`docs/verified-examples.md` is the project's public object of agreement:
seven Go programs, each with one theorem a non-Lean-expert can read.
Those headlines joined the designated set on 2026-08-14 (user ruling:
the specification functions are *definitionally* part of the TCB, so
hoisting them into the Comparator set is exactly right). The
designated set is the eight statements the gallery quotes VERBATIM —
`fib_ok`/`fib_total` and the six other `<example>_ok`, the last three
in their post-swap S3 forms. Supporting material the gallery only
NAMES in prose (the `_readout` twins, `_v1` pairs, `_framed`
companions, `maxCount_total_canonical`, `wordcount_empty_ok`) is
deliberately NOT designated: it is not quoted as a headline, and
`maxCount_total_canonical` is additionally stated in run-internal
vocabulary (`wcEnv`/`wcSeed`/`wcCall`), which designation would drag
into this trusted closure against the layering doctrine.

The statement vocabulary lives in the def-only
`GoLeanProofs/Examples/Targets.lean` (see its docstring for why it
sits under `Examples/` rather than `Specs/`). -/

open GoLean.Examples.Fib in
theorem fib_ok (n : Nat) (hn : n ≤ 93) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int (fibSpec n) .uint64] } :=
  GoLean.Examples.Fib.fib_ok n hn

open GoLean.Examples.Fib in
theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } :=
  GoLean.Examples.Fib.fib_total n hn

open GoLean.Examples.Gcd in
theorem gcd_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel gcdLowered.typeDefs.toList
          gcdLowered.funcs gcdHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          gcdLowered.methods ch
        = .ok { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } :=
  GoLean.Examples.Gcd.gcd_ok a b ha hb

open GoLean.Examples.Reverse in
theorem reverse_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessVFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } :=
  GoLean.Examples.Reverse.reverse_ok n seed hn hseed

open GoLean.Examples.MinMax in
theorem minmax_ok (n seed : Nat) (h1 : 1 ≤ n) (hcap : n ≤ 8)
    (hseed : seed < 2 ^ 64) :
    ∃ pre : List Int, pre.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel minMaxLowered.typeDefs.toList
            minMaxLowered.funcs mmHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            minMaxLowered.methods ch
          = .ok { values := #[goArr8 pre,
                              .int (minSpec pre) .uint64,
                              .int (maxSpec pre) .uint64] } :=
  GoLean.Examples.MinMax.minmax_ok n seed h1 hcap hseed

open GoLean.Examples.BinSearch in
theorem search_ok (n seed : Nat) (t : Int)
    (hn : n < 2 ^ 62) (hnowrap : seed + 2 * n < 2 ^ 64)
    (ht : 0 ≤ t ∧ t < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel searchLowered.typeDefs.toList
          searchLowered.funcs searchHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64,
            .int t .uint64]
          searchLowered.methods ch
        = .ok { values := #[.int (findSpec (bsFamily n seed) t) .int] } :=
  GoLean.Examples.BinSearch.search_ok n seed t hn hnowrap ht

open GoLean.Examples.InsertionSort in
theorem isort_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } :=
  GoLean.Examples.InsertionSort.isort_ok n seed hn hseed

open GoLean.Examples.WordCount in
theorem wordcount_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ words : List Int, words.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
            wordCountLowered.funcs wcHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            wordCountLowered.methods ch
          = .ok { values := #[goArr8 words,
                              .int (maxMultiplicity words : Nat) .uint64] } :=
  GoLean.Examples.WordCount.wordcount_ok n seed hcap hseed

end Judge
