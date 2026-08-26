import GoLeanProofs.Specs.Raft.SpanS1Witness
import GoLeanProofs.Specs.Raft.SpanApplyGetters

/-!
# Audit pins: the span-computes-model arc (A4d-SM1)

The plain-for head schema (`CondFor`) + its countdown discharge
witness, the `utoa` weak span stack (whole-`Func` kernel pin, frame
entry, digit-loop/body/call spans in the banked ∃-string form), the
checker cell machinery (`twinDecl` pin, struct normalization, the
`viol` pin + span), and the S1 headline: `s1Block` pinned verbatim
into `main.twin.harvest`, the projection bridge
(`lookupTerm`/`setk`/`s1Fires` commutation + the `LookupEq` fold
congruence), `s1_span_computes` with its fire/clean witnesses.
Axiom readouts verbatim from `artifacts/probe/axspan.out`.

NOT imported by `Audit.lean` yet — NEW FILES ONLY (arc4b precedent);
the landing manifest names the one-line import the operator adds.
-/

/-- info: 'GoLean.CondFor.condFor_loop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.condFor_loop

/-- info: 'GoLean.CondFor.countdown_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.countdown_span

/-- info: 'GoLean.CondFor.cd_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.CondFor.cd_concrete

/-- info: 'GoLean.RaftSeam.UtoaSpan.utoa_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.UtoaSpan.utoa_pinned

/-- info: 'GoLean.RaftSeam.UtoaSpan.utoa_enterFrame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.UtoaSpan.utoa_enterFrame

/-- info: 'GoLean.RaftSeam.UtoaSpan.dig10_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.UtoaSpan.dig10_iff

/-- info: 'GoLean.RaftSeam.UtoaSpan.utoa_loop_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.UtoaSpan.utoa_loop_span

/-- info: 'GoLean.RaftSeam.UtoaSpan.utoa_body_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.UtoaSpan.utoa_body_span

/-- info: 'GoLean.RaftSeam.UtoaSpan.utoa_call_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.UtoaSpan.utoa_call_span

/-- info: 'GoLean.RaftSeam.SpanCells.twinDecl_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanCells.twinDecl_pinned

/-- info: 'GoLean.RaftSeam.SpanCells.normalize_twinFs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanCells.normalize_twinFs

/-- info: 'GoLean.RaftSeam.SpanCells.viol_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanCells.viol_pinned

/-- info: 'GoLean.RaftSeam.SpanCells.viol_call_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanCells.viol_call_span

/-- info: 'GoLean.RaftSeam.SpanS1.s1Block_pinned' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1Block_pinned

/-- info: 'GoLean.RaftSeam.SpanS1.lookupTerm_projLOf_setk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.lookupTerm_projLOf_setk

/-- info: 'GoLean.RaftSeam.SpanS1.s1Fires_projLOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1Fires_projLOf

/-- info: 'GoLean.RaftSeam.SpanS1.s1Fold_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1Fold_congr

/-- info: 'GoLean.RaftSeam.SpanS1.s1_abs_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1_abs_step

/-- info: 'GoLean.RaftSeam.SpanS1.s1_span_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1_span_computes

/-- info: 'GoLean.RaftSeam.SpanS1.s1w_span_fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1w_span_fire

/-- info: 'GoLean.RaftSeam.SpanS1.s1w_span_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1w_span_clean

/-- info: 'GoLean.RaftSeam.SpanS1.s1w_span_fire_fires' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS1.s1w_span_fire_fires

/-! The pb-getter spans (A4d-SM1 item 4's banked piece). -/

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getIndex_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getIndex_pinned

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getTerm_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getTerm_pinned

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getType_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getType_pinned

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getData_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getData_pinned

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getIndex_call_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getIndex_call_span

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getTerm_call_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getTerm_call_span

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getType_call_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getType_call_span

/-- info: 'GoLean.RaftSeam.SpanApplyGetters.getData_call_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanApplyGetters.getData_call_span
