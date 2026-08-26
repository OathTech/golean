import GoLeanProofs.Specs.Raft.RoundInduction

/-!
# Audit pins: THE ROUND INDUCTION (A4-U26 slice 2, generic layer)

The simulation induction over round chains — the R-form instances
composed at absState level (layer-C design §3): `round_induction`
(trace-long Fam membership + the abstract `ReachRel` trace), the
trace corollaries (`reach`/`flat`/`safety`/`fullInv` — the native
`one_leader_per_term` carried to any trace end from a seeded start),
and the seeded form over the arc4c seed pin (`seedσ`/`seedN₀`,
`Seed` discharged by `seed_N₀`). Witnesses live in the corpus target
(`RoundInductionWitness.lean`, pinned by `Audit/RoundIndWitness.lean`).

This module is LIVE (default target) — imported by `Audit.lean`. -/

/-- info: 'GoLean.RaftSeam.RoundLemmaShape.refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.RoundLemmaShape.refl

/-- info: 'GoLean.RaftSeam.round_induction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.round_induction

/-- info: 'GoLean.RaftSeam.FamTrace.reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.FamTrace.reach

/-- info: 'GoLean.RaftSeam.FamTrace.flat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.FamTrace.flat

/-- info: 'GoLean.RaftSeam.FamTrace.safety' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.FamTrace.safety

/-- info: 'GoLean.RaftSeam.FamTrace.fullInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.FamTrace.fullInv

/-- info: 'GoLean.RaftSeam.seeded_round_induction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.seeded_round_induction
