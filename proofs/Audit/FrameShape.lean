import GoLeanProofs.Specs.Raft.ShapeWitness

/-!
# Audit pins: the completeness-strengthened frame simulation (C2a)

The `FrameSimS` instrument's headline theorems, axiom-pinned (the
commissioning terms' "Audit-pinned"): the strengthened per-step/
per-span transport, the MID-WALK CONSUMPTION theorem, and the
discharge witness (a landed handler equation consumed at a concrete
non-identity placement, with a frame-cell-writing literal resume —
the U15 wall's blocked operation). LINEAGE: Yang–O'Hearn locality,
completeness half (`GoLeanProofs/Frame/ShapeSim.lean`).
-/

/-- info: 'GoLean.Frame.stepFn_simS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFn_simS

/-- info: 'GoLean.Frame.stepFnIter_simS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFnIter_simS

/-- info: 'GoLean.Frame.span_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.span_consume

/-- info: 'GoLean.Frame.span_relocateS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.span_relocateS

/-- info: 'GoLean.Frame.frameSimS_extend' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.frameSimS_extend

/-- info: 'GoLean.RaftSeam.sw_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.sw_consume

/-- info: 'GoLean.RaftSeam.sw_consume_and_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.sw_consume_and_resume

/-- info: 'GoLean.RaftSeam.sw_readout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.sw_readout
