import GoLeanProofs.Specs.Statements
import GoLeanProofs.Specs.GoldenTargets
import GoLeanProofs.Specs.ForkJoinTargets
import GoLeanProofs.Specs.GooseParityTargets
import GoLeanProofs.Examples.Targets

/-!
# The Challenge — the judge's trusted statement of what GoLean claims

This file IS the claim. A Comparator run
(`deps/comparator`, invoked by `scripts/comparator-judge`) certifies that the
`Solution` module proves every theorem below — same statement, axioms within
the allowlist, accepted by a kernel replaying the exported environment — so a
skeptic auditing GoLean's headline results needs to read exactly: this file,
its import closure, and nothing else. Everything here is `sorry`-bodied by
design; the proofs live in `GoLeanProofs` and reach the judge only through
`Solution`. The direct imports are DEF-ONLY statement modules (zero
theorems); the closure does contain proof modules of the semantic core
(`MachineSound`/`StateWf` ride in with the interpreter), but NO designated
theorem is declared anywhere in it — restored at the channels-arc final
audit (F4, 2026-08-07: the slice-2 `GoldenForkJoin` import had brought nine
designated `decide +kernel` proofs into the closure; its defs now live in
`Specs/ForkJoinTargets.lean`) and enforced by ci's statement-TCB closure
gate (step 1c3).

The import closure is the deletion-test doctrine
(`docs/2026-08-01_tcb-and-layering-doctrine.md`) made operational: `GoLean`
core (the interpreter — the semantic TCB), the Iris-free surface
(`GoTriple`/`GoSpec`/`GoFuncSpec` over `execStmt`), the declarative quorum
spec, the pinned lowerings of the real etcd-io/raft source, and the statement
layer (`Specs/Statements.lean`). No `Iris.*` module is importable from here —
enforced by scripts/ci's surface-purity walk and re-checked by the judge
wrapper before every run.

The theorem list is EXACTLY the statement-TCB gate's designated list
(`proofs/Audit.lean`); the wrapper cross-checks the two and fails closed on
drift. Statements that the repo phrases via a `_statement : Prop` def use the
same def here (the def is in the trusted closure — read it); readout
statements are written out in full.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface GoLean.Quorum
open GoLean.Iris.GoldenQuorum GoLean.Iris.GoldenRecover

namespace Judge

/-! ## The golden pin (inc-via-call) — the first machine-checked surface -/

theorem goldenTriple : goldenTriple_statement := sorry

theorem goldenSpec : goldenSpec_statement := sorry

theorem goldenFuncSpec : goldenFuncSpec_statement := sorry

theorem goldenInvariant : goldenInvariant_statement := sorry

theorem goldenReturnsTwo : goldenReturnsTwo_statement := sorry

theorem goldenNotThree : goldenNotThree_statement := sorry

/-! ## The recover pin (panic/recover through defer) -/

theorem recoverFuncSpec : recoverFuncSpec_statement := sorry

theorem recoverReturnsSeven
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel recoverOutEnv
        { types := recoverLowered.typeDefs.toList,
          functions := recoverLowered.funcs, methods := recoverLowered.methods,
          heap := recoverOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 7 .int) := sorry

/-! ## The quorum pilot — etcd-io/raft's real `CommittedIndex`, one voter -/

theorem quorumOneKnownFuncSpec : quorumOneKnownFuncSpec_statement := sorry

theorem quorumOneKnownMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1] GoLean.Quorum.ackedOneKnown
          n.toNat)) := sorry

theorem quorumOneKnownReturnsTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) := sorry

theorem quorumOneKnownNotEleven : quorumOneKnownNotEleven_statement := sorry

theorem quorumOneKnownNotElevenRun
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 11 .uint64) := sorry

/-! ## The comma-ok method (`AckedIndex`), two results -/

theorem quorumAckedIndexFuncSpec2 : quorumAckedIndexFuncSpec2_statement := sorry

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
      ∧ loadLoc σf (.base ⟨1⟩) = .ok (.bool true) := sorry

/-! ## The 3-voter instance -/

theorem quorumThreeAllFuncSpec : quorumThreeAllFuncSpec_statement := sorry

theorem quorumThreeAllMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedThreeAll"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1, 2, 3] GoLean.Quorum.ackedThreeAll
          n.toNat)) := sorry

theorem quorumThreeAllReturnsSix
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) := sorry

theorem quorumThreeAllNotTwelve : quorumThreeAllNotTwelve_statement := sorry

theorem quorumThreeAllNotTwelveRun
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 12 .uint64) := sorry

/-! ## The per-seed total pins (sem-adequacy slice 5; designated at the
2026-08-04 audit response)

`Terminates` quantifies EVERY choice stream at one uniform fuel bound;
the `TotalReadout` forms additionally pin the completion terminal to
`.normal` and read the pinned value out of the final state. All four
seeds and programs are the readouts' own (above); `Terminates` is the
Iris-free, relation-free `execStmt` notion from the surface layer. -/

theorem goldenTerminates : Terminates outEnv goldenOut goldenDriver := sorry

theorem recoverTerminates :
    Terminates recoverOutEnv
      { types := recoverLowered.typeDefs.toList,
        functions := recoverLowered.funcs, methods := recoverLowered.methods,
        heap := recoverOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"recoverDirect"⟩ #[]) := sorry

theorem quorumOneKnownTerminates :
    Terminates quorumOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[]) := sorry

theorem quorumThreeAllTerminates :
    Terminates threeOutEnv
      { types := quorumLowered.typeDefs.toList,
        functions := quorumLowered.funcs, methods := quorumLowered.methods,
        heap := quorumOut, nextAddr := 1 }
      (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[]) := sorry

theorem goldenTotalReadout :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel outEnv goldenOut ch goldenDriver = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int) := sorry

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
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 7 .int) := sorry

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
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) := sorry

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
        ∧ loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) := sorry

/-! ## The ∀-config summit -/

theorem committedIndexAllConfigs : committedIndexAllConfigs_statement := sorry

theorem committedIndexAllReturnsSix
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel allOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := allOut, nextAddr := 5 } ch
        (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
          #[.var "c", .var "l"])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) := sorry

theorem committedIndexAllNotTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel allOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := allOut, nextAddr := 5 } ch
        (.call #[.var "$callres"] ⟨"main.MajorityConfig.CommittedIndex"⟩
          #[.var "c", .var "l"])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 12 .uint64) := sorry

theorem committedIndexAll_refutes_wrong (c : List Nat)
    (acked : Nat → Option Nat) (r : Nat) (hne : r ≠ committedIndexRef c acked) :
    ¬ GoLean.Quorum.IsCommittedIndex c acked r := sorry

/-! ## The math bridge — the reference meets the declarative spec -/

theorem committedIndexRef_meets_spec : committedIndexRef_meets_spec_statement :=
  sorry


/-! ## The fork/join pool kernel witnesses (channels arc slice 2):
pinned-stream `execProg` runs over the ThreadPool carrier — the
canonical/adversarial/alternating schedules complete `.normal` with the
pinned 42 readout; the all-asleep program classifies `.deadlock`. The
defs (`fjRunGives42`/`fjRunDeadlocks`, seeds, drivers) are in the
trusted closure — `Specs/ForkJoinTargets.lean` (def-only; the proofs
live outside the closure, in `Specs/GoldenForkJoin.lean`). -/

theorem forkJoinStreamCanonical : fjRunGives42 400 [] = true := sorry

theorem forkJoinStreamAdversarial :
    fjRunGives42 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true := sorry

theorem forkJoinStreamAlternating :
    fjRunGives42 400 [1, 1, 1, 1, 1, 1, 1, 1] = true := sorry

theorem forkJoinDeadlockCanonical : fjRunDeadlocks 400 [] = true := sorry

theorem forkJoinDeadlockAdversarial :
    fjRunDeadlocks 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true := sorry

/-! ## The slice-5 ∀-SCHEDULE fork/join witnesses: the `∀ ch`
quantifier discharged — EVERY choice stream (schedules + latitude,
D8's single stream) completes the fork/join rendezvous at main's
`.normal` terminal with the 42 readout; deadlock-freedom and
RACE-REFUSAL-freedom (the detector never refuses — scoped by the
detector's recorded under-approximations, Race.lean U1–U2; U3 closed
by BUG-045's chan-object rule, 2026-08-08) on every
modeled schedule as first-order corollaries; and the
`TerminatesNormallyC` instance (one fuel bound, every stream). Plus
`goldenSpecC`: the full concurrent surface judgment `GoSpecC`,
inhabited on the golden program via the sequential-conservation lane. -/

theorem forkJoinAllSchedules42 : ∀ ch : Choices, fjRunGives42 400 ch = true :=
  sorry

theorem forkJoinNoDeadlock : ∀ ch : Choices,
    execProg 400 fjEnv fjSeed ch forkJoinDriver ≠ .error .deadlock := sorry

theorem forkJoinNoRace : ∀ ch : Choices,
    execProg 400 fjEnv fjSeed ch forkJoinDriver ≠ .error .raceDetected := sorry

theorem forkJoinTerminatesNormallyC :
    TerminatesNormallyC fjEnv fjSeed forkJoinDriver := sorry

open GoLean.Iris.GoldenSlice in
theorem goldenSpecC :
    GoSpecC sliceLowered.typeDefs.toList sliceLowered.funcs
      sliceLowered.methods outEnv outCell0 goldenDriver outCell2 := sorry

theorem goldenReturnsTwoC
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execProg fuel outEnv goldenOut ch goldenDriver
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 2 .int) := sorry

/-! ## The spec-parity designated pairs (D3 curation, USER RULING
2026-08-10 — the arc's designated-set change, 44 → 48; fuel-free forms
ONLY, per the ruling: the `decide +kernel` evidence siblings
(`dspCert400` &c.) stay UNDESIGNATED proof evidence).

Class 1 — the imported sequential exemplar (`testCompareNilToNil`,
upstream `wp_testCompareNilToNil` Qed): the internal `GoSpecC` triple
at full `InitialSplit` strength over the frontend's ACTUAL pinned
lowering (`nilLowered`, staleness-guarded by ci's imported-pins step),
plus the first-order pool-carrier readout twin. Class 3 — the flagship
channel exemplar (dsp, Actris 2.0 prog3, upstream `wp_DSPExample`
Qed): the fuel-general `∃N, ∀ fuel ≥ N` kernel certificate over the
pool ∀-streams checker, plus the ∀-schedule verdict readout (every
choice stream completes at main's `.normal` with 42). All defs in the
trusted closure — `Specs/GooseParityTargets.lean` (def-only) and the
already-def-only `Specs/ImportedGooseActris.lean`. -/

open GoLean.ImportedGoose GoLean.ImportedGoose.SemanticsNil in
theorem compareNilToNilSpecC :
    GoSpecC nilLowered.typeDefs.toList nilLowered.funcs nilLowered.methods
      importedEnv importedCell0 compareNilDriver (importedCellV 1) := sorry

open GoLean.ImportedGoose GoLean.ImportedGoose.SemanticsNil in
theorem compareNilToNilReadoutC
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execProg fuel importedEnv (importedSeed nilLowered) ch
      compareNilDriver = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int) := sorry

open GoLean.ImportedGoose GoLean.ImportedGoose.ChannelActris in
theorem dspCert :
    ∃ N, ∀ fuel, N ≤ fuel →
      allStreamsOkPool (cellIsInt 42) fuel
        ⟨#[.exec dspDriver dspEnv .stop], dspSeed, 0⟩ {} = true := sorry

open GoLean.ImportedGoose GoLean.ImportedGoose.ChannelActris in
theorem dspAllSchedules :
    ∃ N, ∀ fuel, N ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execProg fuel dspEnv dspSeed ch dspDriver = .ok (.normal σf, ch')
          ∧ cellIsInt 42 σf = true := sorry

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
        = .ok { values := #[.int (fibSpec n) .uint64] } := sorry

open GoLean.Examples.Fib in
theorem fib_total (n : Nat) (hn : n < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel fibLowered.typeDefs.toList
          fibLowered.funcs fibHarnessFunc #[.int (n : Int) .uint64]
          fibLowered.methods ch
        = .ok { values := #[.int ((fibSpec n % 2 ^ 64 : Nat) : Int) .uint64] } := sorry

open GoLean.Examples.Gcd in
theorem gcd_ok (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel gcdLowered.typeDefs.toList
          gcdLowered.funcs gcdHarnessFunc
          #[.int (a : Int) .uint64, .int (b : Int) .uint64]
          gcdLowered.methods ch
        = .ok { values := #[.int ((Nat.gcd a b : Nat) : Int) .uint64] } := sorry

open GoLean.Examples.Reverse in
theorem reverse_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel reverseLowered.typeDefs.toList
          reverseLowered.funcs reverseHarnessVFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          reverseLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := sorry

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
                              .int (maxSpec pre) .uint64] } := sorry

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
        = .ok { values := #[.int (findSpec (bsFamily n seed) t) .int] } := sorry

open GoLean.Examples.InsertionSort in
theorem isort_ok (n seed : Nat) (hn : n < 2 ^ 63) (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel isortLowered.typeDefs.toList
          isortLowered.funcs isortHarnessFunc
          #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
          isortLowered.methods ch
        = .ok { values := #[.int 1 .uint64] } := sorry

open GoLean.Examples.WordCount in
theorem wordcount_ok (n seed : Nat) (hcap : n ≤ 8) (hseed : seed < 2 ^ 64) :
    ∃ words : List Int, words.length = n ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
            wordCountLowered.funcs wcHarnessRFunc
            #[.int (n : Int) .uint64, .int (seed : Int) .uint64]
            wordCountLowered.methods ch
          = .ok { values := #[goArr8 words,
                              .int (maxMultiplicity words : Nat) .uint64] } := sorry

end Judge
