import GoLeanProofs.Specs.Raft.DriverNetWitness

/-!
# Audit pins: the driver-loop symbolic-net lemmas (C2b)

The SliceWalk loop schema, the two symbolic-net driver-glue spans
(|net|- and payload-symbolic, bounded-completion — compositional mode
I2), their non-vacuity witnesses, and the shape pins that tie the
proved statements to the PINNED lowering. LINEAGE: Floyd/Hoare loop
invariant (`GoLeanProofs/SliceWalk.lean`'s module docstring).
-/

/-- info: 'GoLean.SliceWalk.sliceWalk_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceWalk.sliceWalk_loop

/-- info: 'GoLean.RaftSeam.DriverNet.rebuildLoop_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.rebuildLoop_span

/-- info: 'GoLean.RaftSeam.DriverNet.liveCountLoop_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.liveCountLoop_span

/-- info: 'GoLean.RaftSeam.DriverNet.rebuild_span_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.rebuild_span_witness

/-- info: 'GoLean.RaftSeam.DriverNet.liveCount_span_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.liveCount_span_witness

/-- info: 'GoLean.RaftSeam.DriverNet.drvRebuild_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.drvRebuild_pinned_prop

/-- info: 'GoLean.RaftSeam.DriverNet.lc_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.lc_pinned_prop

/-- info: 'GoLean.RaftSeam.DriverNet.rebuild_census_link' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.rebuild_census_link

/-- info: 'GoLean.RaftSeam.DriverNet.liveCount_census_link' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.liveCount_census_link
