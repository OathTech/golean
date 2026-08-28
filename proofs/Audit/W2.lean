import GoLeanProofs.CondFor
import GoLeanProofs.MapLoops
import GoLeanProofs.Frame.PlugRule
import GoLeanProofs.Specs.RaftPilot.InitSpec

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
frame's control half; wp_bind lineage). Discharge witnesses
(status split at the G-BIND landing, audit fix round F2):
`stepFn_plug`'s live consumer is now the BIND CHAIN itself
(`Laws/Bind.lean`'s `wp_plug_bind` via `Frame/PlugInv.lean`,
exercised by the C-05 quartet, `Specs/Callchain.lean`);
`stepFn_plug_witness` (`Frame/PlugWitness.lean`, pinned in
`Audit/Landing.lean`) is re-pointed there. The SPAN rules
(`stepFnIter_plug`/`callSpan_plug`) are not on the bind chain —
`callSpan_plug_witness` remains their live application (kept; the
prior `W2Gate` instantiation died with the CallSpec calculus,
triage amendment A4). -/

/-- info: 'GoLean.Frame.stepFn_plug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFn_plug

/-- info: 'GoLean.Frame.stepFnIter_plug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFnIter_plug

/-- info: 'GoLean.Frame.callSpan_plug' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.callSpan_plug

/-! ## (Triage landing 2026-08-27, plan L-10/K-1c): the compliant-pilot
+ W2-gate pins (`cBecomeFollower_callSpec`/`cBfPre_inhabited`/
`frameSimG`/`w2_gate`) were PRUNED in the same commit that deleted
their subjects with the CallSpec calculus (archived at
`archive/callspec-era`); the plug family's live instantiation is now
`Frame/PlugWitness.lean` (pins: `Audit/Landing.lean`). -/

/-! ## The loop-family additions (unit 2 / professor delta 5): the
element-type-generic pick loop keeps its Kit pin
(`Audit/Kit.lean` § MapLoops); the no-stop family pins here. -/

/-- info: 'GoLean.MapLoops.filterCandidateList_sublist' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.filterCandidateList_sublist

/-- info: 'GoLean.MapLoops.mapIter_no_stop_of_unmutated' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapIter_no_stop_of_unmutated

/-- info: 'GoLean.MapLoops.mapIter_width_of_unmutated' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.MapLoops.mapIter_width_of_unmutated

/-! ## THE INIT SPEC, stage A (unit 3): the setup boundary
established — entry configuration + statics materialized +
stream-transparent, fuel ∃-quantified. -/

/-- info: 'GoLean.RaftSeam.initSetup_establishes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.initSetup_establishes
