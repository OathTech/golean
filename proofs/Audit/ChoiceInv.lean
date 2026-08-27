import GoLeanProofs.Frame.ChoiceCanon
import GoLeanProofs.Frame.ChoiceCanonWitness
import GoLeanProofs.Frame.ChoiceInv

/-!
# Audit pins: the SP1 choice-erasure layer (curated at the arc-4
landing fix round, 2026-08-26)

The landing audit found this the only arc-4 mechanism layer with no
curated pin module (the exhaustive sweep still covered axiom
cleanliness; this closes the pinning/consumer gap). Pinned here:

- the `~`/`~ₘ` carrier's interface theorems (`ChoiceCanon`):
  equivalence laws + reader invariance by construction;
- the view-fixpoint regression witness (`ChoiceCanonWitness` —
  fix-round F2a: the case the pre-fix `collectFix` silently dropped,
  now refused; deleting the witness or the fix breaks this build);
- the choice-invariance statement layer (`ChoiceInv`): the instance
  projection and the consumer-facing read corollary — the two
  theorems that make `ChoiceInvariantToM` consumable as a named
  premise.

W0 reset (kill-list K-D prune, applied in the K-A commit since the
seed literals die there): the seed-pin discharge surface and the
occupation-witness pins are gone with `SeedPin`/`SeedWitness`
(fixture-anchored; archived — docs/ARCHIVE.md). The carrier and
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

/-! ## The view-fixpoint regression witness (fix-round F2a) -/

/-- info: 'GoLean.Frame.ChoiceErase.ViewFixWitness.viewfix_d3_read' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.ViewFixWitness.viewfix_d3_read

/-- info: 'GoLean.Frame.ChoiceErase.ViewFixWitness.viewfix_not_equiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.ViewFixWitness.viewfix_not_equiv

/-! ## The statement layer (ChoiceInv) -/

/-- info: 'GoLean.Frame.ChoiceErase.choiceInvariant_instance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.choiceInvariant_instance

/-- info: 'GoLean.Frame.ChoiceErase.choiceInvariant_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.ChoiceErase.choiceInvariant_read
