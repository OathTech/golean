import Lean
import GoLeanProofs.RunGlue
import GoLeanProofs.SpecJudgment
import GoLeanProofs.Pilot.BecomeFollowerSpec

/-!
# In-build axiom gate — the W1 surface (judgment layer + runProgramM glue)

W1 (clean-proof plan §W1; design note
`docs/2026-08-27_w1-judgment-design.md`): exact-axiom pins for the
glue family and the judgment layer's rules, in the `Audit/Kit.lean`
format (the exhaustive root sweep bounds everything; these pins add
EXACTNESS). A new public W1 lemma lands with its pin here in the same
commit.
-/

/-! ## RunGlue — the runProgramM glue family (plan §W1: gates both
sentences; audit-pinned by charter) -/

/-- info: 'GoLean.Surface.loadMany_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.loadMany_nil
/-- info: 'GoLean.Surface.loadMany_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.loadMany_cons
/-- info: 'GoLean.Surface.loadMany_ok_of_loads' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Surface.loadMany_ok_of_loads
/-- info: 'GoLean.Surface.runConfig_zero_fuelOut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_zero_fuelOut
/-- info: 'GoLean.Surface.runConfig_prefix_classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runConfig_prefix_classify
/-- info: 'GoLean.Surface.runPkgInitM_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runPkgInitM_eq
/-- info: 'GoLean.Surface.runPkgInitM_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runPkgInitM_none
/-- info: 'GoLean.Surface.runPkgInitM_some_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runPkgInitM_some_ok
/-- info: 'GoLean.Surface.runPkgInitM_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runPkgInitM_mono
/-- info: 'GoLean.Surface.runPkgInitM_prefix_classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runPkgInitM_prefix_classify
/-- info: 'GoLean.Surface.runProgramSetupM_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramSetupM_eq
/-- info: 'GoLean.Surface.runProgramSetupM_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramSetupM_mono
/-- info: 'GoLean.Surface.runProgramSetupM_prefix_classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramSetupM_prefix_classify
/-- info: 'GoLean.Surface.runProgramM_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramM_eq
/-- info: 'GoLean.Surface.runProgramM_of_setup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramM_of_setup
/-- info: 'GoLean.Surface.runProgramM_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramM_mono
/-- info: 'GoLean.Surface.runProgramM_classify_of_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramM_classify_of_total
/-- info: 'GoLean.Surface.runProgramM_readout_of_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.runProgramM_readout_of_total

/-! ## SpecJudgment — the judgment layer (plan §W1: the spec former
+ composition rules) -/

/-- info: 'GoLean.Spec.StmtSpecB.toSpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.StmtSpecB.toSpec
/-- info: 'GoLean.Spec.CallSpecB.toSpec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.CallSpecB.toSpec
/-- info: 'GoLean.Spec.StmtSpecB.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.StmtSpecB.mono
/-- info: 'GoLean.Spec.CallSpecB.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.CallSpecB.mono
/-- info: 'GoLean.Spec.StmtSpec.conseq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.StmtSpec.conseq
/-- info: 'GoLean.Spec.CallSpec.conseq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.CallSpec.conseq
/-- info: 'GoLean.Spec.seqCont_pair_decomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.seqCont_pair_decomp
/-- info: 'GoLean.Spec.StmtSpec.seqn_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.StmtSpec.seqn_pair
/-- info: 'GoLean.Spec.CallSpec.consume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.CallSpec.consume
/-- info: 'GoLean.Spec.stmtSpec_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Spec.stmtSpec_call
/-- info: 'GoLean.Spec.Choices.consume_suffix' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Spec.Choices.consume_suffix
/-- info: 'GoLean.Spec.Choices.consumeAt_suffix' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Spec.Choices.consumeAt_suffix
/-- info: 'GoLean.Spec.Refusal.not' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.Spec.Refusal.not

/-! ## The W1 pilot — Leg A (judgment instances + the reflection
retraction; the judgment's non-vacuity per the charter's carve-out) -/

/-- info: 'GoLean.Sym.reflectV_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.reflectV_conc
/-- info: 'GoLean.Sym.reflectK_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.reflectK_conc
/-- info: 'GoLean.RaftSeam.bfPre_reader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.bfPre_reader
/-- info: 'GoLean.RaftSeam.becomeFollower_callSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.becomeFollower_callSpec
/-- info: 'GoLean.RaftSeam.bfPre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.bfPre_inhabited
