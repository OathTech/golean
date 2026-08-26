import GoLeanProofs.Specs.Raft.RoundVrLemma

/-!
# Audit pins: the MsgVoteResp ELECTION-COMPLETION round lemma — the
R-form's fourth proved instance (A4-U25)

Candidate → leader at the real run's anchor 2→3 transition — the
round-kind matrix's LAST structural ring shape, and the round where
THE S1 LEADERSHIP CLAIM IS BORN (claims 0→1 through `absTwinRead`;
see `RoundVrLemma.lean`'s docstring). The canonical 33,274-step run
(39 windows + 30 crossings at the auto-discovered schedule, including
FIVE choice-free Visit exhaustion-exits), the R-form instance,
witness + closure, and the state/lead/claims/commit readouts.

This module is swept by the CORPUS audit target (`AuditCorpus.lean`)
— the A4-U25 validation-corpus split. -/

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_run

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_x1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_x1

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_x5free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_x5free

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_x30free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_x30free

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_run_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_run_conc

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_selfReturn_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_selfReturn_conc

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_lemma

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_witness_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_witness_identity

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_closure

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_pre_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_pre_read

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_post_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_post_read

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_pre_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_pre_state

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_post_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_post_state

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_post_lead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_post_lead

/-- info: 'GoLean.RaftSeam.RoundVr.roundVr_post_committed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVr.roundVr_post_committed
