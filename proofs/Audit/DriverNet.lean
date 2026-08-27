import GoLeanProofs.Specs.Raft.DriverNet

/-!
# Audit pins: the driver-loop symbolic-net lemmas (C2b)

The SliceWalk loop schema, the two symbolic-net driver-glue spans
(|net|- and payload-symbolic, bounded-completion — compositional mode
I2), and the shape pins that tie the proved statements to the PINNED
lowering. LINEAGE: Floyd/Hoare loop invariant
(`GoLeanProofs/SliceWalk.lean`'s module docstring).

W0 reset (kill-list K-D prune, applied at K-B when the witness module
died): `DriverNetWitness` was a fixture-constant witness module
(kill-list K-B — ALL witnesses); its four pins (the two span
witnesses and the two census links) went with it. The ∀-span and
`_pinned` certificate pins below stay — the kept rule half.
-/

/-- info: 'GoLean.SliceWalk.sliceWalk_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.SliceWalk.sliceWalk_loop

/-- info: 'GoLean.RaftSeam.DriverNet.rebuildLoop_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.rebuildLoop_span

/-- info: 'GoLean.RaftSeam.DriverNet.liveCountLoop_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.liveCountLoop_span

/-- info: 'GoLean.RaftSeam.DriverNet.drvRebuild_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.drvRebuild_pinned_prop

/-- info: 'GoLean.RaftSeam.DriverNet.lc_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.DriverNet.lc_pinned_prop
