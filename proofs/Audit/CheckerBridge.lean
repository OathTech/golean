import GoLeanProofs.Specs.Raft.NativeCheckerBridge

/-!
# Audit pins: the checker-interface I2 bridges (A4-U23)

The S1/S2/S3 checker fold models, the violation→delta bridges, the
interface instantiations (`S1CheckerInterface` closed up to
`ClaimTrace`; `S23CheckerInterface` closed up to the appliedLog
projection), the composed model-silent corollaries through the arc4b
leaves, and the four verbatim guard shape-pins against the pinned
lowering. The honest residual (the symbolic span-computes-model
theorem) is priced in the module docstring — these pins guard what IS
proved.

W0 reset (kill-list K-D prune, applied at K-C when the bridge's
witness section died): the fire/clean witness pins (s1w_delta,
s23w_iface, s23w_clean) went with it. The retained interface
non-vacuity demonstrations are NativeS1Witness/NativeS23Witness.
-/

/-- info: 'GoLean.RaftSeam.NativeSpec.s1_viol_delta' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s1_viol_delta

/-- info: 'GoLean.RaftSeam.NativeSpec.s1_interface_of_trace' depends on axioms: [propext] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s1_interface_of_trace

/-- info: 'GoLean.RaftSeam.NativeSpec.s1_model_silent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s1_model_silent

/-- info: 'GoLean.RaftSeam.NativeSpec.s23_viol_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s23_viol_delta

/-- info: 'GoLean.RaftSeam.NativeSpec.s23_interface_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s23_interface_of_run

/-- info: 'GoLean.RaftSeam.NativeSpec.s23_model_silent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s23_model_silent

/-- info: 'GoLean.RaftSeam.NativeSpec.s1Guard_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s1Guard_pinned_prop

/-- info: 'GoLean.RaftSeam.NativeSpec.s2Guard_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s2Guard_pinned_prop

/-- info: 'GoLean.RaftSeam.NativeSpec.s3IdxGuard_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s3IdxGuard_pinned_prop

/-- info: 'GoLean.RaftSeam.NativeSpec.s3TermGuard_pinned_prop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms GoLean.RaftSeam.NativeSpec.s3TermGuard_pinned_prop

