import GoLeanProofs.Specs.Raft.SpanS23Witness

/-!
# Audit pins: the S23 span-computes-model arc (A4d-SM2)

The two map fragments (the string-keyed MapMem sibling for `nd.got`,
the slot-valued `byIndex` fragment with the `slotFs` table-footprint
identities), the injective `encGS` data code, the apply walk's
engines (`utoaUnit_walk`, the generic concat spine, the S3/S2 branch
walks), the whole-`Func` `apply` pin + the three declaration pins,
the projection bridge, and the headline `s23_span_computes` +
`s23_abs_step` with the fire/clean witnesses AT THE U23 BRIDGE'S OWN
EVENTS (the 7/8 data codes). Axiom readouts verbatim from
`artifacts/probe/axs23.out`.

NOT imported by `Audit.lean` yet — NEW FILES ONLY (the lane's
standing rule); the landing manifest names the one-line import the
operator adds.
-/

/-- info: 'GoLean.RaftSeam.SpanS23.s23_span_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23_span_computes

/-- info: 'GoLean.RaftSeam.SpanS23.s23_abs_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23_abs_step

/-- info: 'GoLean.RaftSeam.SpanS23.s23w_span_s2fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23w_span_s2fire

/-- info: 'GoLean.RaftSeam.SpanS23.s23w_span_s3fire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23w_span_s3fire

/-- info: 'GoLean.RaftSeam.SpanS23.s23w_span_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23w_span_clean

/-- info: 'GoLean.RaftSeam.SpanS23.s23w_s2hit_model' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23w_s2hit_model

/-- info: 'GoLean.RaftSeam.SpanS23.s23w_data_codes' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23w_data_codes

/-- info: 'GoLean.RaftSeam.SpanS23.apply_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.apply_pinned

/-- info: 'GoLean.RaftSeam.SpanS23.slotDecl_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.slotDecl_pinned

/-- info: 'GoLean.RaftSeam.SpanS23.nodeDecl_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.nodeDecl_pinned

/-- info: 'GoLean.RaftSeam.SpanS23.stateTypeDecl_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.stateTypeDecl_pinned

/-- info: 'GoLean.RaftSeam.SpanS23.entryTypeResolve_pinned' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.entryTypeResolve_pinned

/-- info: 'GoLean.RaftSeam.SpanS23.mapAssignValue_toEntriesS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.mapAssignValue_toEntriesS

/-- info: 'GoLean.RaftSeam.SpanS23.applyRhsOp_mapLookup_toEntriesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.applyRhsOp_mapLookup_toEntriesB

/-- info: 'GoLean.RaftSeam.SpanS23.mapAssignValue_toEntriesB_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.mapAssignValue_toEntriesB_insert

/-- info: 'GoLean.RaftSeam.SpanS23.encGS_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.encGS_inj

/-- info: 'GoLean.RaftSeam.SpanS23.encGS_eq_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.encGS_eq_zero_iff

/-- info: 'GoLean.RaftSeam.SpanS23.gsBeq_encGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.gsBeq_encGS

/-- info: 'GoLean.RaftSeam.SpanS23.s23Fold_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23Fold_congr

/-- info: 'GoLean.RaftSeam.SpanS23.lookupIdx_projBy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.lookupIdx_projBy

/-- info: 'GoLean.RaftSeam.SpanS23.lookupIdx_projBy_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.lookupIdx_projBy_append

/-- info: 'GoLean.RaftSeam.SpanS23.s2guard_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s2guard_proj

/-- info: 'GoLean.RaftSeam.SpanS23.utoaUnit_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.utoaUnit_walk

/-- info: 'GoLean.RaftSeam.SpanS23.spine_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.spine_eval

/-- info: 'GoLean.RaftSeam.SpanS23.sliceVisibleValues_of_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.sliceVisibleValues_of_array

/-- info: 'GoLean.RaftSeam.SpanS23.s23_getters_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23_getters_seg

/-- info: 'GoLean.RaftSeam.SpanS23.s3Branch_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s3Branch_walk

/-- info: 'GoLean.RaftSeam.SpanS23.s2Branch_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s2Branch_walk

/-- info: 'GoLean.RaftSeam.SpanS23.s23_len_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23_len_ret

/-- info: 'GoLean.RaftSeam.SpanS23.s23_tail_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23_tail_seg

/-- info: 'GoLean.RaftSeam.SpanS23.s23_byidx_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.SpanS23.s23_byidx_seg
