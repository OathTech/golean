import Lean
import GoLeanProofs.FastEval.Step
import GoLeanProofs.FastEval.Transfer
import GoLeanProofs.Specs.TwinPrelude

/-!
# In-build axiom gate — the FastEval surface (campaign Arc 2, U4)

Exact `#print axioms` pins for the fast-twin evaluator's public
refinement surface (the `Audit/Kit.lean` pattern; template rule 4 of
`docs/campaign-arc2-log.md`). FastEval is UNTRUSTED METHOD — never in
any statement closure — and these pins keep its axiom footprint a
visible diff. Re-baseline only with the reason, in the same commit.
-/

/-- info: 'GoLean.FastEval.stepFast_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.stepFast_ok
/-- info: 'GoLean.FastEval.iterF_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.iterF_ok
/-- info: 'GoLean.FastEval.iterF_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.iterF_add
/-- info: 'GoLean.FastEval.list_forIn_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.list_forIn_sim
/-- info: 'GoLean.FastEval.loadLocF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.loadLocF_ok
/-- info: 'GoLean.FastEval.storeLocF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.storeLocF_ok
/-- info: 'GoLean.FastEval.allocF_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.allocF_state
/-- info: 'GoLean.FastEval.γH_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.γH_set
/-- info: 'GoLean.FastEval.γH_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.γH_alloc
/-- info: 'GoLean.FastEval.applyStrictOpF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.applyStrictOpF_ok
/-- info: 'GoLean.FastEval.storeTargetF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.storeTargetF_ok
/-- info: 'GoLean.FastEval.applyStmtOpF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.applyStmtOpF_ok
/-- info: 'GoLean.FastEval.enterFrameF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.enterFrameF_ok
/-- info: 'GoLean.FastEval.applySyncOpF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.applySyncOpF_ok
/-- info: 'GoLean.Examples.RaftTwin.twin_prelude_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Examples.RaftTwin.twin_prelude_eq

/-! Unit P2R (the verified fast replay engine): the run-level transfer
theorems the `fastreplay` driver's verdict rests on. The
`Classical.choice` in the footprint is inherited from `stepFast_ok`
(pinned above) — no new axiom enters here. -/

/-- info: 'GoLean.FastEval.fastRun_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.fastRun_transfer
/-- info: 'GoLean.FastEval.fastRun_transfer_eqb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.FastEval.fastRun_transfer_eqb
