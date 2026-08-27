import Lean
import GoLeanProofs.Frame.PlugWitness
import GoLeanProofs.Sym.CrossingWitness
import GoLeanProofs.MapPerm
import GoLeanProofs.Specs.Raft.MapPermRead
import GoLeanProofs.Specs.Raft.AbsTwinCheckerRead
import GoLeanProofs.Specs.Raft.NativeS1Witness

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

/-! ## The F-6 pin-restoration wave (previously unpinned LAND items;
the Invariant sanity-lemma pins were DROPPED with the module's
archival — A6) -/

/-! ### MapPerm — the (M) carrier (layer-1 quotient crossing, decode
transports, the unique sorted representative, the scaffold-labeled
Perm-collect loop, and the salvaged readback consumer class) -/

/-- info: 'GoLean.MapPerm.lookupP_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.lookupP_perm

/-- info: 'GoLean.MapPerm.mapPairs_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.mapPairs_perm

/-- info: 'GoLean.MapPerm.mapPairsD_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.mapPairsD_perm

/-- info: 'GoLean.MapPerm.sortedLT_eq_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.sortedLT_eq_of_perm

/-- info: 'GoLean.MapPerm.mapPickLoop_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.mapPickLoop_perm

/-- info: 'GoLean.MapPerm.idsFam_population' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.idsFam_population

/-- info: 'GoLean.MapPerm.idsFam_lookup_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.idsFam_lookup_agree

/-- info: 'GoLean.MapPerm.idsFam_sorted_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.MapPerm.idsFam_sorted_collapse

/-! ### The crossing kit — representatives (Class A split, Class 1
normalize, Class 2 slice validation/reads) -/

/-- info: 'GoLean.Surface.stepFn_ifK_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.stepFn_ifK_true

/-- info: 'GoLean.Surface.normalize_int_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.normalize_int_eq

/-- info: 'GoLean.Surface.validateSlice_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.validateSlice_ok

/-- info: 'GoLean.Surface.applyStrict_length_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.applyStrict_length_slice

/-- info: 'GoLean.Surface.applyStrict_indexGet_slice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.Surface.applyStrict_indexGet_slice

/-! ### The reader vocabulary — AbsTwinCheckerRead representatives
(the mini-witnesses; the reader family's non-vacuity) -/

/-- info: 'GoLean.RaftSeam.wTwin_leaderOf' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.wTwin_leaderOf

/-- info: 'GoLean.RaftSeam.wTwin_cursors' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.wTwin_cursors

/-- info: 'GoLean.RaftSeam.wTwin_leaderOfShaped' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.wTwin_leaderOfShaped

/-! ### The ghost-acks interface (L-7): monotonicity, EStep
transparency, and the two non-vacuity witnesses -/

/-- info: 'GoLean.RaftSeam.NativeSpec.ackCertified_mono' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.ackCertified_mono

/-- info: 'GoLean.RaftSeam.NativeSpec.EStep_acks_eq' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.EStep_acks_eq

/-- info: 'GoLean.RaftSeam.NativeSpec.ackCertified_estep' does not depend on any axioms -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.ackCertified_estep

/-- info: 'GoLean.RaftSeam.NativeSpec.witness_ackCertified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.witness_ackCertified

/-- info: 'GoLean.RaftSeam.NativeSpec.witness_acks_transparent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.witness_acks_transparent
