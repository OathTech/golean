import GoLeanProofs.Specs.Raft.RoundMaLemma

/-!
# Audit pins: the MsgApp round lemma — the R-form's first proved
instance (C2d)

The canonical 23,488-step round run (12 mirror windows + 8 crossings,
tree-propagation template), the R-form instance (`RoundLemmaShape`'s
scaffold obligation discharged via the weak `stepFnIter_sim`
transport), the semantic-pick crossing, the identity-placement
witness + family closure, and the round-delta readouts. LINEAGE:
Abadi–Lamport refinement mapping (the R-form docstring's pin) over
the HhEquation mirror-chain spine (`RoundMaLemma.lean`'s docstring).
-/

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_run

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_pick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_pick

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_run_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_run_conc

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_selfReturn_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_selfReturn_conc

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_lemma

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_witness_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_witness_identity

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_closure

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_pre_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_pre_read

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_post_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_post_read

/-- info: 'GoLean.RaftSeam.RoundMa.roundMa_post_applied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMa.roundMa_post_applied
