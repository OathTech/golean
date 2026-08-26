import GoLeanProofs.Specs.Raft.RoundMarLemma

/-!
# Audit pins: the MsgAppResp maybeCommit round lemma — the R-form's
third proved instance (A4-U24)

Commit movement WITHOUT append — the round-kind matrix's untested
row and the etcd-dialect commit story at the interpreter level (the
A4 mismatch axis; see `RoundMarLemma.lean`'s docstring). The
canonical 26,224-step run (21 windows + 12 crossings at the
auto-discovered schedule, including TWO choice-free Visit
exhaustion-exits), the R-form instance, witness + closure, the
commit/apply readouts, and the PROMOTED table pin
(`SymTables.Agrees.concS_eq` — the U23 ledger row's second-consumer
trigger, executed this unit). -/

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_run

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_x1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_x1

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_x5free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_x5free

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_x9free' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_x9free

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_run_conc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_run_conc

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_selfReturn_conc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_selfReturn_conc

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_lemma

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_witness_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_witness_identity

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_closure

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_pre_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_pre_read

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_post_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_post_read

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_post_committed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_post_committed

/-- info: 'GoLean.RaftSeam.RoundMar.roundMar_post_applied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundMar.roundMar_post_applied

/-- info: 'GoLean.Sym.SymTables.Agrees.concS_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Sym.SymTables.Agrees.concS_eq
