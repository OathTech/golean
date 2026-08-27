import GoLeanProofs.Frame.ChoiceCanon

/-!
# Audit pins: the SP1 choice-erasure layer (curated at the arc-4
landing fix round, 2026-08-26)

The landing audit found this the only arc-4 mechanism layer with no
curated pin module (the exhaustive sweep still covered axiom
cleanliness; this closes the pinning/consumer gap). Pinned here:

- the `~`/`~ₘ` carrier's interface theorems (`ChoiceCanon`):
  equivalence laws + reader invariance by construction;
- (the `ChoiceInv` statement-layer pins were pruned at the triage
  landing — see the tombstone section below).

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

/-! ## The statement layer (triage kill K-3, 2026-08-27):
`Frame/ChoiceInv.lean` and its two pins are DELETED —
`ChoiceInvariantToM` had zero inhabitants and zero consumers, and
both pinned theorems took it as a premise; the spec route discharges
∀-stream directly. Archived at archive/callspec-era. The ChoiceCanon
carrier pins above stay (general choice-erasure machinery, K-E). -/
