import GoLeanProofs.Specs.Raft.RoundInductionWitness

/-!
# Audit pins: the round induction's WITNESSES (A4-U26 slice 2,
live layer — title corrected, delta-review F-4)

The shared loop-head configuration (the four proved kinds' `C0`s
kernel-pinned equal — cross-kind chaining is config-compatible), the
genuine `EStep` abstract witness chain from the discharged seed
(campaign → grant → self-poll → the winning MsgVoteResp), safety at
its end net non-vacuously (`absN4` has a real leader), and the
induction discharged at the identity placement on the Vr/Vote/Mar
1-link chains, the trivial++Ma 2-link chain (chaining mechanics), and
the trivial seeded chain (non-vacuity of the seeded statement).

This module is LIVE (default target, imported by `Audit.lean`) since
the arc-4 landing fix round — the witness ships in the same gated
build as its law (`round_induction` is live; the U25 split had
deferred these pins to landmark corpus builds). -/

/-- info: 'GoLean.RaftSeam.RoundInd.c0_vote_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.c0_vote_shared

/-- info: 'GoLean.RaftSeam.RoundInd.c0_mar_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.c0_mar_shared

/-- info: 'GoLean.RaftSeam.RoundInd.c0_vr_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.c0_vr_shared

/-- info: 'GoLean.RaftSeam.RoundInd.abs_step01' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.abs_step01

/-- info: 'GoLean.RaftSeam.RoundInd.abs_step12' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.abs_step12

/-- info: 'GoLean.RaftSeam.RoundInd.abs_step23' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.abs_step23

/-- info: 'GoLean.RaftSeam.RoundInd.abs_step34' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.abs_step34

/-- info: 'GoLean.RaftSeam.RoundInd.abs_reach04' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.abs_reach04

/-- info: 'GoLean.RaftSeam.RoundInd.abs_safety' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.abs_safety

/-- info: 'GoLean.RaftSeam.RoundInd.absN4_leader' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.absN4_leader

/-- info: 'GoLean.RaftSeam.RoundInd.vr_chain_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.vr_chain_witness

/-- info: 'GoLean.RaftSeam.RoundInd.vote_chain_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.vote_chain_witness

/-- info: 'GoLean.RaftSeam.RoundInd.mar_chain_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.mar_chain_witness

/-- info: 'GoLean.RaftSeam.RoundInd.ma_chain2_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.ma_chain2_witness

/-- info: 'GoLean.RaftSeam.RoundInd.seeded_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundInd.seeded_witness
