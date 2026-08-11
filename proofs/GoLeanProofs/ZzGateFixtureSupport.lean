import GoLeanProofs.Surface

/-!
# Completion-pin gate: OUT-OF-SPECS fixture support (S1 audit round 3)

Two round-3 verifier probe shapes need declarations OUTSIDE the
`GoLeanProofs.Specs.*` module family (this module's name is the
point):

- the P2 STRUCTURE WRAPPER: a `Prop` structure whose field carries the
  triple, declared here so that the classification walk can only see
  through it via the `.inductInfo → ctors` arm — the arm whose absence
  was the round-3 CRITICAL (the `| _ => pure ()` wildcard, the
  repo's twice-grown fail-open walk bug; see the gate's comment);
- the P8 OUT-OF-SPECS EXPORT: an unpinned triple in a non-`Specs`
  module, provable only because the gate's enforcement scope is now
  ENV-WIDE over the proofs package (`GoLeanProofs` and everything
  under it) — this fixture flags, structurally proving the widening.

Both are honest vacuous-by-unsatisfiable-pre proofs, fixture-private
programs (no pin anywhere, by construction, forever).
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-- Fixture-private program for the structure-wrapper shape. -/
def zzStructProg : Stmt := .seqn #[.seqn #[]]

/-- P2: a `Prop` STRUCTURE wrapping a triple — visible to the
classification walk only through the `.inductInfo → ctors` arm. -/
structure ZzStructWrappedTriple : Prop where
  triple : GoTripleC [] #[] #[] [] (.pure False) zzStructProg .emp

/-- Fixture-private program for the out-of-Specs shape. -/
def zzOutOfSpecsProg : Stmt := .seqn #[.seqn #[], .seqn #[]]

/-- P8: an unpinned triple export OUTSIDE `Specs.*` — flagged by the
env-wide gate (the scope fixture). -/
theorem fixtureOutOfSpecsTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzOutOfSpecsProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

end GoLean.Surface
