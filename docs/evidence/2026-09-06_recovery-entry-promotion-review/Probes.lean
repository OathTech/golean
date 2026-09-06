import GoLean.Interface

-- The experimental facade alone exposes each promoted existing theorem.
#check GoLean.GoCore.RecoveryRuntime.setup_typed
#check GoLean.GoCore.RecoveryRuntime.setup_typed_wf
#check GoLean.GoCore.RecoveryRuntime.enterFrame_typed
#check GoLean.GoCore.RecoveryRuntime.enterFramePick_typed
#check GoLean.GoCore.RecoveryRuntime.ResultRoots.load
#check GoLean.GoCore.RecoveryRuntime.pinResultLocs_typed
#check GoLean.GoCore.RecoveryRuntime.EnvTyped.pushedDecls
#check GoLean.GoCore.RecoveryRuntime.initialState_argument
#check GoLean.GoCore.RecoveryRuntime.initialState_result
#check GoLean.GoCore.RecoveryRuntime.initialState_readout
#check GoLean.GoCore.RecoveryRuntime.typedEntry_wf
#check GoLean.GoCore.RecoveryRuntime.ZeroValues.unique

#print axioms GoLean.GoCore.RecoveryRuntime.setup_typed_wf
#print axioms GoLean.GoCore.RecoveryRuntime.enterFramePick_typed
#print axioms GoLean.GoCore.RecoveryRuntime.initialState_readout
