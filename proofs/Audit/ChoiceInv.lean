import GoLeanProofs.Frame.ChoiceCanon
import GoLeanProofs.Frame.ChoiceInv

/-!
# Audit pins: the SP1 choice-erasure layer (curated at the arc-4
landing fix round, 2026-08-26)

The landing audit found this the only arc-4 mechanism layer with no
curated pin module (the exhaustive sweep still covered axiom
cleanliness; this closes the pinning/consumer gap). Pinned here:

- the `~`/`~ₘ` carrier's interface theorems (`ChoiceCanon`):
  equivalence laws + reader invariance by construction;
- the choice-invariance statement layer (`ChoiceInv`): the instance
  projection and the consumer-facing read corollary — the two
  theorems that make `ChoiceInvariantToM` consumable as a named
  premise.

W0 reset (kill-list K-D prune, applied phase-by-phase as the subjects
died): the seed-pin discharge surface and the occupation-witness pins
went with `SeedPin`/`SeedWitness` (K-A, fixture-anchored literals);
the view-fixpoint regression pins went with `ChoiceCanonWitness`
(K-B — ALL witnesses). Archived — docs/ARCHIVE.md. The carrier and
statement-layer pins stay: general choice-erasure machinery, kept off
the critical path.

This module is LIVE (default target) — imported by `Audit.lean`. -/

/-! ## The carrier (ChoiceCanon) -/

/-- info: 'GoLean.Frame.ChoiceErase.CEquivM.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.CEquivM.trans

/-- info: 'GoLean.Frame.ChoiceErase.CEquivM.symm' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.CEquivM.symm

/-- info: 'GoLean.Frame.ChoiceErase.read_invariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.read_invariant

/-- info: 'GoLean.Frame.ChoiceErase.readM_invariant' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.readM_invariant

/-! ## The statement layer (ChoiceInv) -/

/-- info: 'GoLean.Frame.ChoiceErase.choiceInvariant_instance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.choiceInvariant_instance

/-- info: 'GoLean.Frame.ChoiceErase.choiceInvariant_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.choiceInvariant_read
