import GoLeanProofs.Specs.Raft.SeedLitVar
import GoLeanProofs.Specs.Raft.SeedPin

/-! # THE SEED-PIN WITNESS (SP1) — a NON-canonical init stream landing
`~ₘ`-equal to the representative (the equivalence's occupation proof)

The variant literal (`SeedLitVar.lean`, same generator) is the
anchored init run under the stream perturbed at positions
`[(0,97),(12,97),(41,97)]` (zeros elsewhere) — ONE deviation on each
latitude axis at once:

- position 0 (`appendSpill` @ newTwin): a DIFFERENT REALIZED
  CAPACITY on the run's first spill backing (the charter's named
  witness axis — different capacities);
- position 12 (`mapIter` @ raft.NewRawNode): an iteration-order pick
  the sweep measured raw-state-VISIBLE (layout/relocation exercised);
- position 41 (`mapIter` @ becomeFollower): node 1's
  `randomizedElectionTimeout` value draw — the probe's refutation
  axis, absorbed by the DECLARED mask (and shown genuinely different
  below, so the mask is occupied, not decorative).

What the kernel checks here, on every build:
- the variant reaches the SAME anchor configuration
  (`seedVar_config` — the probe measured cfgEq at 171/171 positions;
  this pins one non-canonical instance kernel-grade);
- **`seedVar_equiv`** — the masked canonical forms are EQUAL: the
  choice-invariance equivalence between two genuinely different
  81,261-step init runs, kernel-checked;
- `seedVar_clean` — the variant's form is fail-closed-clean;
- `seedVar_absRead` — the abstract readout agrees LITERALLY (the
  reader-invariance corollary at the instance);
- `seedVar_rand_differs` (+ the canonical side) — the masked field
  REALLY differs (10 vs 17): the strict `~` would refuse (the probe's
  refutation, pinned kernel-grade), so the masked equivalence is
  doing exactly the declared work and nothing more.

GENERATOR-VERIFIED ONLY (stated bluntly, the SeedPin split): that
`svarHeap`/`svarC` IS the perturbed stream's anchor state — the
81,261-step walk is the compiled generator's (the same compiled
`stepFn` the differential validates); its kernel completion rides the
same route of record as the canonical run's (SeedPin docstring). -/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Frame.ChoiceErase

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-- The variant post-init state (perturbed stream; generator
provenance in the module docstring). -/
def seedVarσ : ExecState := { wBase with heap := svarHeap, nextAddr := svarNa }

/-- The variant reaches the SAME anchor configuration. -/
theorem seedVar_config : svarC = seedC := by kernel_rfl

/-- The variant's canonical-form pin: the SAME pinned literal the
representative lands on (`SeedCFormLit`; the shared-pin route — the
U21 representation-asymmetry lesson: never compare two computed forms
head-on). -/
theorem seedVar_cform_pin :
    canonStateM twinLatMask seedVarσ seedRoots = seedCForm := by
  kernel_rfl

/-- **THE EQUIVALENCE WITNESS**: the two init runs' states are
`~ₘ`-equal at the declared one-field mask — different capacities,
different iteration order, different rand draw; same choice-erased
state. Composed from the two pins over the shared literal. -/
theorem seedVar_equiv :
    CEquivM twinLatMask seedVarσ seedRoots seedσ seedRoots :=
  seedVar_cform_pin.trans seed_cform_pin.symm

/-- The variant's canonicalization is clean (no fail-closed flags). -/
theorem seedVar_clean :
    (canonStateM twinLatMask seedVarσ seedRoots).flags = [] := by
  rw [seedVar_cform_pin]; rfl

/-- The variant's abstract readout, pinned against the literal (the
shared-pin route again — the head-on computed-vs-computed comparison
of the two readouts was measured >10 min kernel while each
against-the-literal check is seconds). -/
theorem seedVar_absRead_pin :
    absTwinRead seedVarσ seedTwinLoc
      = some { violations := 0, claims := 0, committed := 0,
               nodes := [(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)],
               net := [] } := by kernel_rfl

/-- Reader agreement at the instance: the abstract twin readout of
the variant equals the representative's — via the shared literal. -/
theorem seedVar_absRead :
    absTwinRead seedVarσ seedTwinLoc = absTwinRead seedσ seedTwinLoc :=
  seedVar_absRead_pin.trans seed_absRead.symm

/-- The masked field genuinely DIFFERS between the witnesses (node
1's raft cell, address 389 in both runs — allocation structure is
draw-independent, the probe's dNa=0 finding): the strict `~` would
refuse this pair, so the mask is occupied. -/
theorem seedVar_rand_differs :
    GoLean.Lens.fieldRead seedVarσ ⟨389⟩ ⟨"raft.raft"⟩
      "randomizedElectionTimeout" = some (.int 17 .int) := by kernel_rfl

/-- The canonical side of the same field (electionTimeout 10 + draw
0). -/
theorem seed_rand_canonical :
    GoLean.Lens.fieldRead seedσ ⟨389⟩ ⟨"raft.raft"⟩
      "randomizedElectionTimeout" = some (.int 10 .int) := by kernel_rfl

end GoLean.RaftSeam
