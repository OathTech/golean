import GoLeanProofs.Specs.Raft.RoundInduction

/-!
# Audit pins: THE ROUND INDUCTION (A4-U26 slice 2, generic layer)

The simulation induction over round chains — the concrete Fam-chain
half of the layer-C §3 carry: `round_induction` (trace-long Fam
membership + an INDEPENDENT abstract `ReachRel` trace — the
per-boundary abs-pairing is open obligation O5b; the module header
states the claim strength exactly), the trace corollaries
(`reach`/`flat`/`safety`/`fullInv` — the native `one_leader_per_term`
carried to the SUPPLIED abstract chain's end from a seeded start),
and the seeded form over the arc4c seed pin (`seedσ`/`seedN₀`,
`Seed` discharged by `seed_N₀`). Witnesses are LIVE beside the law
since the landing fix round (`RoundInductionWitness.lean`, pinned by
`Audit/RoundIndWitness.lean`, both default-target).

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
