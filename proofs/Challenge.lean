import GoLeanProofs.Specs.Statements
import GoLeanProofs.Specs.GoldenTargets

/-!
# The Challenge — the judge's trusted statement of what GoLean claims

This file IS the claim. A Comparator run
(`deps/comparator`, invoked by `scripts/comparator-judge`) certifies that the
`Solution` module proves every theorem below — same statement, axioms within
the allowlist, accepted by a kernel replaying the exported environment — so a
skeptic auditing GoLean's headline results needs to read exactly: this file,
its import closure, and nothing else. Everything here is `sorry`-bodied by
design; the proofs live in `GoLeanProofs` and reach the judge only through
`Solution`.

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

end Judge
