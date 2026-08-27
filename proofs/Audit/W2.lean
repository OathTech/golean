import GoLeanProofs.CondFor
import GoLeanProofs.MapLoops
import GoLeanProofs.Frame.PlugRule
import GoLeanProofs.Specs.RaftPilot.W2Gate

/-!
# Audit pins: W2 — the loop-rule family, the plug rule, the init spec

Exact-axiom pins for the W2 units (clean-proof plan §W2; the W2 log
`docs/w2-prover-log.md`). Grown section-by-section as the units land;
imported by `Audit.lean` in the same commit as each landing (the
in-build gate convention, as `Audit/W1.lean`).
-/

/-! ## CondFor — the plain-for (cond-only) head schema (harvested
verbatim from campaign-arc4d @ 7fa0e04d; provenance banner in the
module). The schema, its countdown discharge witness, and the
witness's kernel cross-check at a concrete state. -/

/-- info: 'GoLean.CondFor.condFor_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.condFor_loop

/-- info: 'GoLean.CondFor.countdown_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.countdown_span

/-- info: 'GoLean.CondFor.cd_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.cd_concrete

/-! ## THE PLUG RULE (W2 unit 1 — design note §7-§8): the per-step
commutation walk, its iteration, and the call-span corollary (the
frame's control half; wp_bind lineage). -/

/-- info: 'GoLean.Frame.stepFn_plug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFn_plug

/-- info: 'GoLean.Frame.stepFnIter_plug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFnIter_plug

/-- info: 'GoLean.Frame.callSpan_plug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.callSpan_plug

/-! ## The compliant pilot + THE W2 GATE (unit 4 + the Leg-B-full
measurement): the re-laid becomeFollower CallSpec and its consumption
at the real stepCandidate site with state framing. -/

/-- info: 'GoLean.RaftSeam.cBecomeFollower_callSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.cBecomeFollower_callSpec

/-- info: 'GoLean.RaftSeam.cBfPre_inhabited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.cBfPre_inhabited

/-- info: 'GoLean.RaftSeam.frameSimG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.frameSimG

/-- info: 'GoLean.RaftSeam.w2_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.w2_gate

/-! ## The loop-family additions (unit 2 / professor delta 5): the
element-type-generic pick loop keeps its Kit pin
(`Audit/Kit.lean` § MapLoops); the no-stop family pins here. -/

/-- info: 'GoLean.MapLoops.filterCandidateList_sublist' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.filterCandidateList_sublist

/-- info: 'GoLean.MapLoops.mapIter_no_stop_of_unmutated' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapIter_no_stop_of_unmutated

/-- info: 'GoLean.MapLoops.mapIter_width_of_unmutated' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapIter_width_of_unmutated
