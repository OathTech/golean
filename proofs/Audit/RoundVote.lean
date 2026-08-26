import GoLeanProofs.Specs.Raft.RoundVoteLemma

/-!
# Audit pins: the MsgVote round lemma — the R-form's second proved
instance (A4-U23)

The canonical 19,291-step vote-round run (16 mirror windows + 10
crossings, auto-discovered boundary schedule — including the
choice-FREE Visit mapIterK exhaustion-exit crossing the choice census
cannot see), the R-form instance via the weak `stepFnIter_sim`
transport, the semantic-pick and exit crossings, the
identity-placement witness + family closure, and the vote round's
hardstate-delta readouts (Term/Vote 0 → 1, no storage-resp arms).
LINEAGE: Abadi–Lamport refinement mapping over the mirror-chain
spine (`RoundVoteLemma.lean`'s docstring).
-/

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_run

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_pick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_pick

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_visitExit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_visitExit

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_run_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_run_conc

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_selfReturn_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_selfReturn_conc

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_lemma

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_witness_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_witness_identity

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_closure

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_pre_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_pre_read

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_post_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_post_read

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_post_term' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_post_term

/-- info: 'GoLean.RaftSeam.RoundVote.roundVote_post_vote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundVote.roundVote_post_vote
