import GoLeanProofs.Specs.Raft.RingWitness

/-!
# Audit pins: the storage-resp sub-ring spans (C2c)

The five per-arm harvest-ring spans at the MsgApp append-family round
fixture (mirror-chain form, ∀ρ/∀σ/∀stream-tail), the composed
13,870-step ring, the storage-resp payload readouts, and the witness
(the concrete run + the `span_consume` composition at a non-identity
placement with a frame-writing resume). LINEAGE: the handler-equation
mirror-chain spine (HhEquation) one ring up; Yang–O'Hearn locality
consumed via the C2a instrument (`RingEquation.lean` /
`RingWitness.lean` module docstrings).
-/

/-- info: 'GoLean.RaftSeam.Ring.ring_w1_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_w1_span

/-- info: 'GoLean.RaftSeam.Ring.ring_w2_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_w2_span

/-- info: 'GoLean.RaftSeam.Ring.ring_w3_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_w3_span

/-- info: 'GoLean.RaftSeam.Ring.ring_w4_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_w4_span

/-- info: 'GoLean.RaftSeam.Ring.ring_w5_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_w5_span

/-- info: 'GoLean.RaftSeam.Ring.ring_full_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_full_span

/-- info: 'GoLean.RaftSeam.Ring.ring_witness_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_witness_run

/-- info: 'GoLean.RaftSeam.Ring.rw_consume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.rw_consume

/-- info: 'GoLean.RaftSeam.Ring.rw_consume_and_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.rw_consume_and_resume

/-- info: 'GoLean.RaftSeam.Ring.rw_readout' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.rw_readout

/-- info: 'GoLean.RaftSeam.Ring.ring_post_storage_ents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_post_storage_ents

/-- info: 'GoLean.RaftSeam.Ring.ring_post_applied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.Ring.ring_post_applied
