import GoLeanProofs.Surface

/-!
# Completion-pin gate: the ESCAPE-SHAPE fixtures (S1 audit round 2)

Negative-test fixtures for the REBUILT (semantic) completion-pin gate
in `Audit.lean` — one tracked instance of each escape shape the round-2
delta review proved against the first gate, each of which the rebuilt
gate must FLAG (its negative tests assert so by constant name) while
enforcement excludes exactly this module and the warning fixture:

- `fixtureSpecCUnpinned` — a `GoSpecC`-typed export: the first gate's
  one-level type scan never saw `GoTripleC` through the `GoSpecC`
  definition (the review's MAJOR). The rebuilt gate's deep
  `defnInfo`-unfolding closure walk classifies it.
- `fixtureDefTriple` — a `def`-exported triple: the first gate's
  `theorem`-only filter dropped it.
- `fixtureWrappedTriple` — a theorem stated at a definitional wrapper
  type: classified by the deep walk, but its stated type carries NO
  extractable `GoTripleC`/`GoSpecC` application — the gate FAILS
  CLOSED on such exports (state the triple directly), and this
  fixture pins that arm.
- The MODULE's own name (`Specs.Zz…`, outside the first gate's
  `Specs.Chan*` glob) is the out-of-glob scope fixture: the rebuilt
  gate's scope is ALL of `GoLeanProofs.Specs.*`.

The fixtures are HONEST theorems (no `sorry` — the axiom sweep forbids
it; the delta review's own `.tmp` probe used `sorry` for the
`ProgressExecC` half, which cannot be committed): each is a triple
over the unsatisfiable precondition `.pure False`, provable outright —
and thereby also a permanent reminder that a `GoTripleC`/`GoSpecC`
with an unsatisfiable pre is vacuously true, exactly the class the
non-vacuity doctrine's witnesses exist to exclude. `zzFixtureProg` is
a fixture-private program constant, so no completion pin for it exists
anywhere (the pairing is per-PROGRAM) and the fixtures stay flagged
forever.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

/-- Fixture-private program: nothing else states anything about it. -/
def zzFixtureProg : Stmt := .seqn #[]

/-- ESCAPE SHAPE 1 — `GoSpecC`-typed, no completion pin (vacuous over
the unsatisfiable pre; module docstring). -/
theorem fixtureSpecCUnpinned :
    GoSpecC [] #[] #[] [] (.pure False) zzFixtureProg .emp :=
  ⟨fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim,
   fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim⟩

/-- ESCAPE SHAPE 2 — a `def`-exported triple type. -/
def fixtureDefTriple :
    GoTripleC [] #[] #[] [] (.pure False) zzFixtureProg .emp :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

/-- The definitional wrapper for escape shape 3. -/
def ZzWrappedTriple : Prop :=
  GoTripleC [] #[] #[] [] (.pure False) zzFixtureProg .emp

/-- ESCAPE SHAPE 3 — a theorem stated at the wrapper type: the deep
walk classifies it, and the gate fails closed on the missing
extractable application (this fixture pins that arm). -/
theorem fixtureWrappedTriple : ZzWrappedTriple :=
  fun _hp _na _hP _F hinit => (hinit.sat_pre.1).elim

end GoLean.Surface
