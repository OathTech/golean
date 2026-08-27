import Lean
import GoLeanProofs.Frame.PlugWitness
import GoLeanProofs.Sym.CrossingWitness

/-!
# Audit pins: the triage landing (2026-08-27)

Exact-axiom pins for the theorems landed by the triage-execution
wave (plan: `docs/2026-08-27_triage-plan.md`; execution record:
`docs/triage-execution-log.md`):

- the plug family's discharge witnesses (amendment A4 — the named
  replacement for the killed `W2Gate` instantiation);
- the crossing kit's mini-witnesses (amendment A5);
- the F-6 pin-restoration wave for the previously unpinned LAND
  items (MapPerm representatives incl. `mapPickLoop_perm`, crossing
  representatives, the reader vocabulary, the ghost-acks lemmas).

In-build (imported by `Audit.lean`); a new public landing theorem
lands with its pin here in the same commit.
-/

/-! ## The plug discharge witnesses (A4) -/

/-- info: 'GoLean.Frame.callSpan_plug_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.callSpan_plug_witness

/-- info: 'GoLean.Frame.stepFn_plug_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Frame.stepFn_plug_witness

/-! ## The crossing kit mini-witnesses (A5) -/

/-- info: 'GoLean.Surface.crossing_witness_lenNeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.crossing_witness_lenNeg

/-- info: 'GoLean.Surface.crossing_witness_ifSplit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.crossing_witness_ifSplit

/-- info: 'GoLean.Surface.crossing_witness_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.crossing_witness_read
