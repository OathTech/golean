import Tests.GoCoreContract
import Tests.PanicRendering
import Tests.StringPanicMembers
import GoLean.GoCore.PanicText
import GoLean.GoCore.Admission
import GoLean.GoCore.Prefix
import GoLean.GoCore.BridgeSet
import Lean

/-! The core totality audit (2026-09-16, lane `park-lane/typed-profiles-0916`,
`docs/2026-09-16_typed-profiles-parked.md` §3): the post-import axiom audit re-homed from
the parked `semantic interface` step (`Tests/InterfaceAudit.lean` at `62fc8073`), restated
over the CORE alone. Run from an external harness (`tools/core-audit.py`) that imports every
`GoLean/*.lean` and `GoLean/GoCore/*.lean` found on disk and passes that list in, so that:

* every module on disk is in the audited closure and every `GoLean.*` module in the closure
  is on disk (two-way; a module that fails to import fails the harness first);
* no module root outside `Init`/`Std`/`Lean`/`GoLean`/`Tests` is in the closure
  (`lake-manifest.json` declares no packages — a new dependency is refused by name);
* the load-bearing core modules and the required core theorems exist (the trace/run
  bridges, the abort observer, the string-panic members, the contract regressions);
* the abort-text helpers stay CONSTRUCTIVE (`propext`/`Quot.sound` only, no choice) —
  landing chunk L3's boundary (`docs/2026-09-07_land-panic-text-tape.md`);
* every declaration of every `GoLean.*`/`Tests.*` module — private, generated and trailing
  declarations included — depends on the classical trio only: no `sorry`, no axiom, no
  native decision. This is the charter's «no sorry, no native_decide, no axioms anywhere in
  `GoLean/`» as a MACHINE check, beside the text scans of `scripts/ci` steps 1/1a2/1a3. -/

open Lean

namespace Tests.GoCoreAudit

def allowedRoots : List Name := [`Init, `Std, `Lean, `GoLean, `Tests]

def requiredModules : List Name := [
    `GoLean.GoCore.PoolErrorFacts, `GoLean.GoCore.PoolReplayFacts, `GoLean.GoCore.PoolSound,
    `GoLean.GoCore, `GoLean.GoCore.Machine, `GoLean.GoCore.StepFn, `GoLean.GoCore.StateWf,
    `GoLean.GoCore.MachineSound, `GoLean.GoCore.UnseqSound, `GoLean.GoCore.Multi,
    `GoLean.GoCore.MultiSound, `GoLean.GoCore.Trace, `GoLean.GoCore.PoolTrace,
    `GoLean.GoCore.ProgramTrace, `GoLean.GoCore.AbortObservation, `GoLean.GoCore.StringPanic,
    `GoLean.GoCore.PanicText, `GoLean.GoCore.AdmissionIndices, `GoLean.GoCore.AdmissionPolicy,
    `GoLean.GoCore.Admission, `GoLean.CLI, `GoLean.NativeToIR, `GoLean.ChoiceTrace,
    `GoLean.GoCore.ExecutionStatement, `GoLean.GoCore.Prefix, `GoLean.GoCore.BridgeSet,
    `GoLean.GoCore.PrefixFacts, `GoLean.GoCore.StepErrors, `GoLean.GoCore.Locals,
    `GoLean.GoCore.EquationsAttr, `GoLean.GoCore.Equations, `GoLean.GoCore.PoolProjection,
    `Tests.GoCoreContract, `Tests.PanicRendering, `Tests.StringPanicMembers,
    `Tests.GoCoreAudit]

/-- Required core theorems (the `semantic interface` audit's CORE exports, plus the
re-homed regressions). Each must exist as a theorem. -/
def exports : List Name := [
    -- Pool grind M1: the nine frozen statements, BridgeSet rows 503–511.
    ``GoLean.GoCore.PoolSound.raceUpdate_error,
    ``GoLean.GoCore.PoolSound.stepMulti_error_cases,
    ``GoLean.GoCore.PoolSound.schedSlot_iff,
    ``GoLean.GoCore.PoolSound.stepML_erase,
    ``GoLean.GoCore.PoolSound.stepML_sound,
    ``GoLean.GoCore.PoolSound.stepML_complete,
    ``GoLean.GoCore.PoolSound.stepM_lift,
    ``GoLean.GoCore.PoolSound.stepsML_erase,
    ``GoLean.GoCore.PoolSound.stepMulti_replay,

    -- Window packet D (2026-10-03): the per-arm `stepFn` EQUATIONS and their helper laws (every
    -- theorem of `GoLean/GoCore/Equations.lean`; BridgeSet rows 174–402, 437–499 and 502) and the sequential-to-pool
    -- PROJECTIONS (`GoLean/GoCore/PoolProjection.lean`; rows 403–436 and 500–501) — the re-pin offer's interface
    ``GoLean.GoCore.Equations.storeTarget_inv_panic, ``GoLean.GoCore.Equations.applyStmtOp_inv_panic,
    ``GoLean.GoCore.Equations.toResult_of_error, ``GoLean.GoCore.Equations.valueAsBool_bool,
    ``GoLean.GoCore.Equations.valueAsLoc_addr, ``GoLean.GoCore.Equations.valueAsLoc_nil,
    ``GoLean.GoCore.Equations.targetPlan_var, ``GoLean.GoCore.Equations.completeTargetRef_var,
    ``GoLean.GoCore.Equations.resolveChain_nil, ``GoLean.GoCore.Equations.applyRhsOp_vals,
    ``GoLean.GoCore.Equations.applyStrictOp_toInterface_string,
    ``GoLean.GoCore.Equations.loadRoot_base, ``GoLean.GoCore.Equations.storeLoc_root,
    ``GoLean.GoCore.Equations.Heap.lookup_set_self, ``GoLean.GoCore.Equations.Heap.lookup_push_self,
    ``GoLean.GoCore.Equations.exec_seqn, ``GoLean.GoCore.Equations.exec_ifThenElse,
    ``GoLean.GoCore.Equations.exec_while, ``GoLean.GoCore.Equations.exec_returnStmt,
    ``GoLean.GoCore.Equations.exec_breakStmt, ``GoLean.GoCore.Equations.exec_continueStmt,
    ``GoLean.GoCore.Equations.exec_inertLabel, ``GoLean.GoCore.Equations.exec_labeled,
    ``GoLean.GoCore.Equations.exec_breakTo, ``GoLean.GoCore.Equations.exec_continueTo,
    ``GoLean.GoCore.Equations.exec_breakable, ``GoLean.GoCore.Equations.exec_unsupported,
    ``GoLean.GoCore.Equations.exec_call_args, ``GoLean.GoCore.Equations.exec_call_nullary,
    ``GoLean.GoCore.Equations.exec_call_nullary_panic, ``GoLean.GoCore.Equations.exec_call_unsupported,
    ``GoLean.GoCore.Equations.exec_callValue, ``GoLean.GoCore.Equations.exec_callValue_unsupported,
    ``GoLean.GoCore.Equations.retV_callArgsK_more, ``GoLean.GoCore.Equations.retV_callArgsK_enter,
    ``GoLean.GoCore.Equations.retV_callArgsK_enter_panic, ``GoLean.GoCore.Equations.retV_callValCalleeK_enter,
    ``GoLean.GoCore.Equations.retV_callValCalleeK_enter_panic,
    ``GoLean.GoCore.Equations.retV_callValCalleeK_nil, ``GoLean.GoCore.Equations.retV_callValCalleeK_args,
    ``GoLean.GoCore.Equations.retV_callValArgsK_more, ``GoLean.GoCore.Equations.retV_callValArgsK_enter,
    ``GoLean.GoCore.Equations.retV_callValArgsK_enter_panic, ``GoLean.GoCore.Equations.retV_callValArgsK_nil,
    ``GoLean.GoCore.Equations.exec_deferCall, ``GoLean.GoCore.Equations.retV_deferCalleeK_args,
    ``GoLean.GoCore.Equations.retV_deferCalleeK_push, ``GoLean.GoCore.Equations.retV_deferCalleeK_push_frame,
    ``GoLean.GoCore.Equations.retV_deferCalleeK_outside, ``GoLean.GoCore.Equations.retV_deferArgsK_more,
    ``GoLean.GoCore.Equations.retV_deferArgsK_push, ``GoLean.GoCore.Equations.retV_deferArgsK_push_frame,
    ``GoLean.GoCore.Equations.retV_deferArgsK_outside, ``GoLean.GoCore.Equations.exec_panicStmt,
    ``GoLean.GoCore.Equations.retV_panicArgK, ``GoLean.GoCore.Equations.evalE_recoverCall,
    ``GoLean.GoCore.Equations.panicking_frame_empty, ``GoLean.GoCore.Equations.panicking_frame_defer,
    ``GoLean.GoCore.Equations.panicking_frame_defer_run,
    ``GoLean.GoCore.Equations.panicking_frame_defer_panic,
    ``GoLean.GoCore.Equations.panicking_frame_defer_nil, ``GoLean.GoCore.Equations.panicking_panicResumeK,
    ``GoLean.GoCore.Equations.next_panicResumeK_unrecovered,
    ``GoLean.GoCore.Equations.next_panicResumeK_recovered, ``GoLean.GoCore.Equations.panicking_glue,
    ``GoLean.GoCore.Equations.panicking_seq, ``GoLean.GoCore.Equations.panicking_loop,
    ``GoLean.GoCore.Equations.panicking_breakableK, ``GoLean.GoCore.Equations.panicking_labelK,
    ``GoLean.GoCore.Equations.panicking_strictK, ``GoLean.GoCore.Equations.panicking_storeK,
    ``GoLean.GoCore.Equations.panicking_probeK, ``GoLean.GoCore.Equations.panicking_stop_settled,
    ``GoLean.GoCore.Equations.panicking_stop_pending, ``GoLean.GoCore.Equations.panicking_nil_stop,
    ``GoLean.GoCore.Equations.next_preprintK, ``GoLean.GoCore.Equations.next_preprintK_panic,
    ``GoLean.GoCore.Equations.retV_preprintK_string, ``GoLean.GoCore.Equations.panicking_preprintK,
    ``GoLean.GoCore.Equations.next_frame, ``GoLean.GoCore.Equations.signal_ret_frame,
    ``GoLean.GoCore.Equations.frameExit_nil, ``GoLean.GoCore.Equations.frameExit_targets,
    ``GoLean.GoCore.Equations.frameExit_defer, ``GoLean.GoCore.Equations.frameExit_defer_run,
    ``GoLean.GoCore.Equations.frameExit_defer_panic, ``GoLean.GoCore.Equations.frameExit_defer_nil,
    ``GoLean.GoCore.Equations.frameExit_preprint, ``GoLean.GoCore.Equations.frameExit_extra_results,
    ``GoLean.GoCore.Equations.frameExit_malformed, ``GoLean.GoCore.Equations.loadResults_nil,
    ``GoLean.GoCore.Equations.loadResults_cons, ``GoLean.GoCore.Equations.signal_table,
    ``GoLean.GoCore.Equations.signal_stop, ``GoLean.GoCore.Equations.signal_frame_escape,
    ``GoLean.GoCore.Equations.signalStep_seq, ``GoLean.GoCore.Equations.signalStep_breakableK_brk,
    ``GoLean.GoCore.Equations.signalStep_breakableK_ret, ``GoLean.GoCore.Equations.signalStep_breakableK_cont,
    ``GoLean.GoCore.Equations.signalStep_loop_brk, ``GoLean.GoCore.Equations.signalStep_loop_cont,
    ``GoLean.GoCore.Equations.signalStep_loop_ret, ``GoLean.GoCore.Equations.signalStep_labelK_ret,
    ``GoLean.GoCore.Equations.signalStep_labelK_brkTo_self, ``GoLean.GoCore.Equations.next_stop,
    ``GoLean.GoCore.Equations.next_seq_cons, ``GoLean.GoCore.Equations.next_seq_nil,
    ``GoLean.GoCore.Equations.next_loop, ``GoLean.GoCore.Equations.next_breakableK,
    ``GoLean.GoCore.Equations.next_labelK, ``GoLean.GoCore.Equations.next_strictK,
    ``GoLean.GoCore.Equations.next_ifK, ``GoLean.GoCore.Equations.next_callArgsK,
    ``GoLean.GoCore.Equations.retV_seq, ``GoLean.GoCore.Equations.retV_frame,
    ``GoLean.GoCore.Equations.retV_storeK, ``GoLean.GoCore.Equations.retV_stop,
    ``GoLean.GoCore.Equations.evalE_var, ``GoLean.GoCore.Equations.evalE_var_unbound,
    ``GoLean.GoCore.Equations.evalE_ref, ``GoLean.GoCore.Equations.evalE_ref_unbound,
    ``GoLean.GoCore.Equations.evalE_global, ``GoLean.GoCore.Equations.evalE_global_oob,
    ``GoLean.GoCore.Equations.exec_assign, ``GoLean.GoCore.Equations.exec_assign_var,
    ``GoLean.GoCore.Equations.exec_assign_unsupported, ``GoLean.GoCore.Equations.retV_tgtOpK_more,
    ``GoLean.GoCore.Equations.retV_tgtOpK_next_target, ``GoLean.GoCore.Equations.retV_tgtOpK_rhs,
    ``GoLean.GoCore.Equations.retV_tgtOpK_store, ``GoLean.GoCore.Equations.retV_tgtOpK_malformed,
    ``GoLean.GoCore.Equations.retV_rhsK_more, ``GoLean.GoCore.Equations.retV_rhsK_apply,
    ``GoLean.GoCore.Equations.retV_rhsK_apply_panic, ``GoLean.GoCore.Equations.next_storeK_store,
    ``GoLean.GoCore.Equations.next_storeK_chain, ``GoLean.GoCore.Equations.next_storeK_var,
    ``GoLean.GoCore.Equations.next_storeK_panic, ``GoLean.GoCore.Equations.next_storeK_done,
    ``GoLean.GoCore.Equations.exec_block, ``GoLean.GoCore.Equations.allocDecls_nil,
    ``GoLean.GoCore.Equations.allocDecls_cons, ``GoLean.GoCore.Equations.bindParams_nil,
    ``GoLean.GoCore.Equations.bindParams_cons, ``GoLean.GoCore.Equations.retV_ifK_true,
    ``GoLean.GoCore.Equations.retV_ifK_false, ``GoLean.GoCore.Equations.retV_whileK_true,
    ``GoLean.GoCore.Equations.retV_whileK_false, ``GoLean.GoCore.Equations.evalE_and,
    ``GoLean.GoCore.Equations.evalE_or, ``GoLean.GoCore.Equations.retV_andK_true,
    ``GoLean.GoCore.Equations.retV_andK_false, ``GoLean.GoCore.Equations.retV_orK_true,
    ``GoLean.GoCore.Equations.retV_orK_false, ``GoLean.GoCore.Equations.retV_boolK,
    ``GoLean.GoCore.Equations.evalE_intLit, ``GoLean.GoCore.Equations.evalE_boolLit,
    ``GoLean.GoCore.Equations.evalE_stringLit, ``GoLean.GoCore.Equations.evalE_unsupported,
    ``GoLean.GoCore.Equations.evalE_strict_more, ``GoLean.GoCore.Equations.evalE_strict_nullary,
    ``GoLean.GoCore.Equations.retV_strictK_more, ``GoLean.GoCore.Equations.retV_strictK_apply,
    ``GoLean.GoCore.Equations.retV_strictK_apply_panic, ``GoLean.GoCore.Equations.retV_strictK_apply_error,
    ``GoLean.GoCore.Equations.exec_wide, ``GoLean.GoCore.Equations.exec_allocNew,
    ``GoLean.GoCore.Equations.exec_mapAssign, ``GoLean.GoCore.Equations.exec_appendSlice,
    ``GoLean.GoCore.Equations.exec_print, ``GoLean.GoCore.Equations.retV_stmtOpK_more_target,
    ``GoLean.GoCore.Equations.retV_stmtOpK_more_target_nil,
    ``GoLean.GoCore.Equations.retV_stmtOpK_more_operand, ``GoLean.GoCore.Equations.retV_stmtOpK_apply,
    ``GoLean.GoCore.Equations.retV_stmtOpK_apply_panic, ``GoLean.GoCore.Equations.exec_mapRange,
    ``GoLean.GoCore.Equations.retV_mapRangeK, ``GoLean.GoCore.Equations.next_mapIterK_done,
    ``GoLean.GoCore.Equations.next_mapIterK_pick, ``GoLean.GoCore.Equations.next_mapIterK_stop,
    ``GoLean.GoCore.Equations.exec_mapLookup, ``GoLean.GoCore.Equations.exec_typeAssert,
    ``GoLean.GoCore.Equations.exec_assignMany, ``GoLean.GoCore.Equations.exec_assignMany_arity,
    ``GoLean.GoCore.Equations.exec_chanSend, ``GoLean.GoCore.Equations.exec_closeChan,
    ``GoLean.GoCore.Equations.exec_chanRecv, ``GoLean.GoCore.Equations.retV_chanStK_more,
    ``GoLean.GoCore.Equations.retV_chanStK_apply, ``GoLean.GoCore.Equations.retV_chanStK_apply_panic,
    ``GoLean.GoCore.Equations.exec_selectStmt, ``GoLean.GoCore.Equations.exec_selectStmt_default,
    ``GoLean.GoCore.Equations.exec_selectStmt_block, ``GoLean.GoCore.Equations.retV_selectOpsK_more,
    ``GoLean.GoCore.Equations.retV_selectOpsK_apply, ``GoLean.GoCore.Equations.exec_goStmt,
    ``GoLean.GoCore.Equations.retV_goCalleeK_args, ``GoLean.GoCore.Equations.retV_goCalleeK_spawn,
    ``GoLean.GoCore.Equations.retV_goArgsK_more, ``GoLean.GoCore.Equations.retV_goArgsK_spawn,
    ``GoLean.GoCore.Equations.exec_syncStmt, ``GoLean.GoCore.Equations.exec_atomicStmt,
    ``GoLean.GoCore.Equations.retV_syncStK_more, ``GoLean.GoCore.Equations.retV_syncStK_apply,
    ``GoLean.GoCore.Equations.retV_syncStK_apply_error, ``GoLean.GoCore.Equations.retV_atomicStK_more,
    ``GoLean.GoCore.Equations.retV_atomicStK_apply, ``GoLean.GoCore.Equations.retV_atomicStK_apply_panic,
    ``GoLean.GoCore.Equations.blockedSend, ``GoLean.GoCore.Equations.blockedRecv,
    ``GoLean.GoCore.Equations.blockedSelect, ``GoLean.GoCore.Equations.blockedSync,
    ``GoLean.GoCore.Equations.exec_unseqProbe, ``GoLean.GoCore.Equations.retV_probeK,
    ``GoLean.GoCore.Equations.exec_unseq, ``GoLean.GoCore.Equations.next_unseqK,
    ``GoLean.GoCore.Equations.retV_unseqK, ``GoLean.GoCore.Equations.unseqEnter,
    ``GoLean.GoCore.Equations.unseqValue, ``GoLean.GoCore.Equations.unseqRun_eval,
    ``GoLean.GoCore.Equations.unseqWait_invoke, ``GoLean.GoCore.Equations.stateWf_empty,
    ``GoLean.GoCore.Equations.seedGlobals_nil, ``GoLean.GoCore.Equations.runPkgInitM_none,
    ``GoLean.GoCore.Equations.runProgramSetup_noInit, ``GoLean.GoCore.Equations.pinResultLocs_eq_of_lookup,
    ``GoLean.GoCore.Equations.setup_lookup_arg, ``GoLean.GoCore.Equations.setup_lookup_result,
    ``GoLean.GoCore.Equations.setup_resultLocs, ``GoLean.GoCore.Equations.setup_heap_size,
    ``GoLean.GoCore.Equations.bind_eq_error, ``GoLean.GoCore.Equations.runCommit_error,
    ``GoLean.GoCore.Equations.enterFramePickV_of_plan_error, ``GoLean.GoCore.Equations.enterFrame_inv_error,
    ``GoLean.GoCore.Equations.retV_syncStK_apply_panic, ``GoLean.GoCore.Equations.evalE_strict_nullary_error,
    ``GoLean.GoCore.Equations.retV_chanStK_apply_error, ``GoLean.GoCore.Equations.retV_selectOpsK_apply_panic,
    ``GoLean.GoCore.Equations.retV_selectOpsK_apply_error, ``GoLean.GoCore.Equations.retV_rhsK_apply_error,
    ``GoLean.GoCore.Equations.retV_atomicStK_apply_error, ``GoLean.GoCore.Equations.next_preprintK_error,
    ``GoLean.GoCore.Equations.retV_stmtOpK_apply_error, ``GoLean.GoCore.Equations.next_storeK_error,
    ``GoLean.GoCore.Equations.exec_call_nullary_error, ``GoLean.GoCore.Equations.retV_callArgsK_enter_error,
    ``GoLean.GoCore.Equations.retV_callValCalleeK_enter_error,
    ``GoLean.GoCore.Equations.retV_callValArgsK_enter_error,
    ``GoLean.GoCore.Equations.panicking_frame_defer_error, ``GoLean.GoCore.Equations.frameExit_defer_error,
    ``GoLean.GoCore.Equations.exec_block_error, ``GoLean.GoCore.Equations.evalE_var_error,
    ``GoLean.GoCore.Equations.retV_mapRangeK_error, ``GoLean.GoCore.Equations.next_mapIterK_error,
    ``GoLean.GoCore.Equations.frameExit_targets_error, ``GoLean.GoCore.Equations.frameExit_preprint_error,
    ``GoLean.GoCore.Equations.unseqEnter_error, ``GoLean.GoCore.Equations.unseqValue_error,
    ``GoLean.GoCore.Equations.retV_ifK_error, ``GoLean.GoCore.Equations.retV_whileK_error,
    ``GoLean.GoCore.Equations.retV_andK_error, ``GoLean.GoCore.Equations.retV_orK_error,
    ``GoLean.GoCore.Equations.retV_boolK_error, ``GoLean.GoCore.Equations.valueAsBool_nonbool,
    ``GoLean.GoCore.Equations.retV_callValCalleeK_args_notfunc,
    ``GoLean.GoCore.Equations.retV_deferCalleeK_notfunc, ``GoLean.GoCore.Equations.retV_goCalleeK_notfunc,
    ``GoLean.GoCore.Equations.deferrableCallee_false, ``GoLean.GoCore.Equations.panicking_frame_defer_notfunc,
    ``GoLean.GoCore.Equations.frameExit_defer_notfunc, ``GoLean.GoCore.Equations.retV_preprintK_nonstring,
    ``GoLean.GoCore.Equations.next_storeK_arity_refs, ``GoLean.GoCore.Equations.next_storeK_arity_vals,
    ``GoLean.GoCore.Equations.contHeadLabel_labelK, ``GoLean.GoCore.Equations.contHeadLabel_stop,
    ``GoLean.GoCore.Equations.contHeadLabel_frame, ``GoLean.GoCore.Equations.signalStep_breakableK_brkTo,
    ``GoLean.GoCore.Equations.signalStep_breakableK_contTo, ``GoLean.GoCore.Equations.signalStep_labelK_brk,
    ``GoLean.GoCore.Equations.signalStep_labelK_cont, ``GoLean.GoCore.Equations.signalStep_labelK_brkTo_ne,
    ``GoLean.GoCore.Equations.signalStep_labelK_contTo_self,
    ``GoLean.GoCore.Equations.signalStep_labelK_contTo_ne, ``GoLean.GoCore.Equations.signalStep_loop_brkTo,
    ``GoLean.GoCore.Equations.signalStep_loop_contTo_self,
    ``GoLean.GoCore.Equations.signalStep_loop_contTo_ne, ``GoLean.GoCore.Equations.signalStep_mapIterK_brk,
    ``GoLean.GoCore.Equations.signalStep_mapIterK_cont, ``GoLean.GoCore.Equations.signalStep_mapIterK_ret,
    ``GoLean.GoCore.Equations.signalStep_mapIterK_brkTo,
    ``GoLean.GoCore.Equations.signalStep_mapIterK_contTo_self,
    ``GoLean.GoCore.Equations.signalStep_mapIterK_contTo_ne,
    ``GoLean.GoCore.Equations.signal_labelK_contTo_self,
    ``GoLean.GoCore.Machine.transferable_wide, ``GoLean.GoCore.Machine.transferableWide_ok,
    ``GoLean.GoCore.Machine.transferableWide_fuelOut, ``GoLean.GoCore.Machine.transferableWide_terminal,
    ``GoLean.GoCore.Machine.not_transferableWide_deadlock,
    ``GoLean.GoCore.Machine.not_transferableWide_refusal, ``GoLean.GoCore.Machine.seqOut_zero,
    ``GoLean.GoCore.Machine.seqOut_succ, ``GoLean.GoCore.Machine.outFold_nil,
    ``GoLean.GoCore.Machine.outFold_cons, ``GoLean.GoCore.Machine.outFold_eq_fold,
    ``GoLean.GoCore.Machine.runnableIdxs_singleton_none, ``GoLean.GoCore.Machine.mainOutcome?_single_none,
    ``GoLean.GoCore.Machine.front_single_step, ``GoLean.GoCore.Machine.front_single_flagged,
    ``GoLean.GoCore.Machine.front_terminal, ``GoLean.GoCore.Machine.front_aborted,
    ``GoLean.GoCore.Machine.stepThread_single_out, ``GoLean.GoCore.Machine.stepMulti_single_out,
    ``GoLean.GoCore.Machine.execProgLoopOut_single_wide, ``GoLean.GoCore.Machine.execProgLoopOut_single,
    ``GoLean.GoCore.Machine.execProgLoop_single_wide, ``GoLean.GoCore.Machine.execProgLoop_single_terminal,
    ``GoLean.GoCore.Machine.execProgLoopOut_single_terminal,
    ``GoLean.GoCore.Machine.isTerminal_false_of_stepFn_ok,
    ``GoLean.GoCore.Machine.isBlockedConfig_false_of_stepFn_ok, ``GoLean.GoCore.Machine.zeroCost_stops,
    ``GoLean.GoCore.Machine.seqOut_stop, ``GoLean.GoCore.Machine.seqOut_of_prefix,
    ``GoLean.GoCore.Machine.execProgLoopOut_single_prefix, ``GoLean.GoCore.Machine.pool_run_single_prefix,
    ``GoLean.GoCore.Machine.afterStepFlag_none_of_noRegistry, ``GoLean.GoCore.Machine.seqOpCount_eq_zero,
    ``GoLean.GoCore.Machine.execProgLoop_single_noBoundary,
    ``GoLean.GoCore.Machine.execProgLoop_single_noBoundary_wide,
    ``GoLean.GoCore.Machine.execProgLoopOut_single_noBoundary_wide,
    -- Unit 6b, BUG-004 item 4 — the preprint phase (2026-10-03; design
    -- docs/2026-09-30_bug004-item4-design.md §2 (i), RULED [USER] 2026-09-30 relayed): the
    -- abort's characterization over the settled chain, the split's two facts, the rendering
    -- equations the logic side asked for (`*_text`, the `StringPanic` string lemmas' twins),
    -- the helper arms' soundness and the relation-side elimination facts
    ``GoLean.GoCore.Machine.Config.abort?_some_iff, ``GoLean.GoCore.Machine.Config.abort?_of_settled,
    ``GoLean.GoCore.Machine.Config.abort?_of_pending,
    ``GoLean.GoCore.Machine.splitNewestPending?_eq, ``GoLean.GoCore.Machine.splitNewestPending?_pending,
    ``GoLean.GoCore.Machine.renderPanicHead_text, ``GoLean.GoCore.Machine.abortMsg_text,
    ``GoLean.GoCore.Machine.abortMsg_text_refused, ``GoLean.GoCore.Machine.abortMsg_text_ok,
    ``GoLean.GoCore.Machine.stepFn_text_abort, ``GoLean.GoCore.Machine.stepFn_text_abort_refused,
    ``GoLean.GoCore.Machine.runConfig_text_abort, ``GoLean.GoCore.Machine.runConfig_text_abort_refused,
    ``GoLean.GoCore.Machine.stepPanicStop_sound, ``GoLean.GoCore.Machine.stepRetOther_sound,
    ``GoLean.GoCore.Machine.stepNextOther_sound,
    ``GoLean.GoCore.Machine.step_abort_elim, ``GoLean.GoCore.Machine.step_stop_unsettled,
    ``GoLean.GoCore.Machine.stepPanicStop_strict, ``GoLean.GoCore.Machine.preprintFatalStop_strict,
    -- C4, block-entry allocation (2026-10-01; design docs/2026-10-01_gc4-block-allocation-design.md D8 —
    -- the layout function's lemma set, the lane's acceptance list; BridgeSet rows 136–154)
    ``GoLean.GoCore.Machine.entrySlot_def, ``GoLean.GoCore.Machine.entrySlot_inj,
    ``GoLean.GoCore.Machine.entrySlot_not_allocated,
    ``GoLean.GoCore.Machine.blockEntry_shift, ``GoLean.GoCore.Machine.blockEntry_lookup,
    ``GoLean.GoCore.Machine.blockEntry_lookup_outer, ``GoLean.GoCore.Machine.blockEntry_zero,
    ``GoLean.GoCore.Machine.allocDecls_zero, ``GoLean.GoCore.Machine.allocDecls_heap_get_lt,
    ``GoLean.GoCore.Machine.Store.alloc_cell,
    ``GoLean.GoCore.Machine.blockEntry_fresh, ``GoLean.GoCore.Machine.blockExit_store_eq,
    ``GoLean.GoCore.Machine.heap_size_mono, ``GoLean.GoCore.Machine.enterFrame_shift,
    ``GoLean.GoCore.Machine.frameEntry_lookup_arg, ``GoLean.GoCore.Machine.frameEntry_lookup_result,
    ``GoLean.GoCore.Machine.frameEntry_fresh,
    ``GoLean.GoCore.Machine.pushDefer_saves_values, ``GoLean.GoCore.Machine.funcVal_captures_locs,
    -- window unit 5b, the `intn` pick site (2026-09-30; design docs/2026-09-30_intn-pick-design.md D7):
    -- the draw's apply equation, its derived step rule, the pick-lifted / oblivious plans, the
    -- generalized wide-op pick lemma, the two-way consult characterization, and the int-store
    -- class congruence behind the ∀-streams kit; BridgeSet rows 133–135
    ``GoLean.GoCore.Machine.applyStmtOp_randIntn_eq, ``GoLean.GoCore.Machine.Step_randIntn_draw,
    ``GoLean.GoCore.Machine.applyStmtOp_plan_randIntn_draw,
    ``GoLean.GoCore.Machine.applyStmtOp_plan_randIntn_nodraw,
    ``GoLean.GoCore.Machine.stepFn_stmtOp_pick, ``GoLean.GoCore.Machine.stmtConsult?_some,
    ``GoLean.GoCore.Machine.intnBound?_some, ``GoLean.GoCore.Machine.intnBound?_gt_one,
    ``GoLean.GoCore.Machine.Mem.store_int_congr, ``GoLean.GoCore.Machine.applyStmtOp_randIntn_congr,
    -- B6, numeric locals (2026-09-30): the name-table interface (the logic team's request 3)
    ``GoLean.GoCore.Func.localsOk_covers, ``GoLean.GoCore.Func.localsOk_sigDistinct,
    ``GoLean.GoCore.Func.localsOk_named, ``GoLean.GoCore.Func.localsOk_argKind,
    ``GoLean.GoCore.Func.localsOk_resultKind, ``GoLean.GoCore.Func.localsOk_recvFirst,
    ``GoLean.GoCore.Func.localsOk_bodyKind,
    ``GoLean.GoCore.LocalEnv.lookup_declare_self, ``GoLean.GoCore.LocalEnv.lookup_declare_ne,
    ``GoLean.GoCore.LocalEnv.lookup_pushScope,
    ``GoLean.GoCore.Machine.bindParams_lookup, ``GoLean.GoCore.Machine.allocDecls_lookup,
    ``GoLean.GoCore.Machine.enterFrame_lookup_arg, ``GoLean.GoCore.Machine.enterFrame_lookup_result,
    -- the trace/run correspondence (`Trace`, `PoolTrace`, `ProgramTrace`)
    ``GoLean.Semantics.iter_iff_trace, ``GoLean.Semantics.Trace.erase,
    ``GoLean.Semantics.run_ok_iff, ``GoLean.Semantics.exists_run_ok_iff,
    ``GoLean.Semantics.Pool.run_iff, ``GoLean.Semantics.Pool.Run.success_reaches,
    ``GoLean.Semantics.Pool.program_run_iff,
    ``GoLean.Semantics.Pool.exists_program_run_iff,
    ``GoLean.Semantics.Pool.observation_iff,
    ``GoLean.Semantics.Pool.fuel_is_not_observation,
    ``GoLean.Semantics.Pool.refusal_is_not_observation,
    -- the full step label (row-2 reshape, 2026-09-28): the silent projection and the
    -- pool projection (a goroutine step's event label IS `stepFn`'s)
    ``GoLean.GoCore.StepLabel.fold_silent,
    ``GoLean.GoCore.Machine.stepThread_privateStep_label,
    ``GoLean.GoCore.Machine.printOut?_toList,
    ``GoLean.GoCore.Choices.consumeAtE_eq,
    -- the execution bridges (window row 2b, packet B, 2026-09-28; packet B audit F6,
    -- [AGENT] coordinator disposition): the 23 proved `_stmt` theorems and their supports
    ``GoLean.GoCore.ExecutionStatement.prefix_refl, ``GoLean.GoCore.ExecutionStatement.prefix_comp,
    ``GoLean.GoCore.ExecutionStatement.prefix_split, ``GoLean.GoCore.ExecutionStatement.prefix_erase_steps,
    ``GoLean.GoCore.ExecutionStatement.prefix_erase_trace, ``GoLean.GoCore.ExecutionStatement.prefix_iter,
    ``GoLean.GoCore.ExecutionStatement.finish_abort_step, ``GoLean.GoCore.ExecutionStatement.finish_refused_step,
    ``GoLean.GoCore.ExecutionStatement.finish_replay, ``GoLean.GoCore.ExecutionStatement.run_ok_iff,
    ``GoLean.GoCore.ExecutionStatement.run_panic_iff, ``GoLean.GoCore.ExecutionStatement.run_deadlock_iff,
    ``GoLean.GoCore.ExecutionStatement.run_fuelOut_iff, ``GoLean.GoCore.ExecutionStatement.replay_coverage,
    ``GoLean.GoCore.ExecutionStatement.silent_projection, ``GoLean.GoCore.ExecutionStatement.single_embedding,
    ``GoLean.GoCore.ExecutionStatement.program_bridge, ``GoLean.GoCore.ExecutionStatement.classification,
    ``GoLean.GoCore.ExecutionStatement.classification_wf, ``GoLean.GoCore.ExecutionStatement.boundary_abort_one,
    ``GoLean.GoCore.ExecutionStatement.boundary_blocked_zero, ``GoLean.GoCore.ExecutionStatement.boundary_refused_one,
    ``GoLean.GoCore.ExecutionStatement.boundary_refused_zero,
    ``GoLean.GoCore.Machine.stepFn_strict, ``GoLean.GoCore.ExecutionStatement.stepFn_no_stray_panic,
    ``GoLean.GoCore.ExecutionStatement.stepFn_error_cases,
    ``GoLean.GoCore.ExecutionStatement.execStmtLoop_error,
    ``GoLean.GoCore.ExecutionStatement.noRefusal_step,
    ``GoLean.GoCore.Machine.stepFn_picks_none, ``GoLean.GoCore.Machine.stepFn_picks_some,
    -- native method promotion (window row 3, G-P S2, 2026-09-28; [USER] «Agree on (1)», relayed):
    -- the frame names the function it runs at entry and at exit, and the direct path is the
    -- function-call rule
    ``GoLean.GoCore.Machine.Entry.callConfig_run, ``GoLean.GoCore.Machine.frame_exit_returns,
    ``GoLean.GoCore.Machine.enterFrame_declared,
    -- G-P S3 (2026-09-29): the §3 equation lemmas — the lookups, the resolution, the path
    -- walk, the recover rule — and the `findFunctionIn?` domain-narrowing bridge (the logic
    -- team's request 5, relayed; [AGENT] coordinator disposition); BridgeSet rows 68–89
    ``GoLean.GoCore.findFunctionIn?_filter, ``GoLean.GoCore.findFunctionIn?_filter_none,
    ``GoLean.GoCore.methodDecl?_some, ``GoLean.GoCore.promotion?_some,
    ``GoLean.GoCore.resolveMethod?_declared, ``GoLean.GoCore.resolveMethod?_ptrDeclared,
    ``GoLean.GoCore.resolveMethod?_promoted, ``GoLean.GoCore.resolveMethod?_promotedPtr,
    ``GoLean.GoCore.receiverAt_nil_path, ``GoLean.GoCore.receiverAt_nil_path_deref,
    ``GoLean.GoCore.receiverAt_nil_path_deref_nil, ``GoLean.GoCore.receiverAt_nil_panic,
    ``GoLean.GoCore.receiverAt_field, ``GoLean.GoCore.receiverAt_field_proj,
    ``GoLean.GoCore.receiverAt_field_addr,
    ``GoLean.GoCore.receiverAt_ptr, ``GoLean.GoCore.receiverAt_ptr_deref,
    ``GoLean.GoCore.receiverAt_ptr_nil, ``GoLean.GoCore.receiverAt_ptr_nil_deref,
    ``GoLean.GoCore.Machine.recoverResult_eq, ``GoLean.GoCore.Machine.recoverResult_frame,
    ``GoLean.GoCore.Machine.recoverResult_glue,
    -- G-C3, `Cont := List Frame` (window row 4, packet C, 2026-09-29; [USER] «Agree with 1-4»,
    -- relayed; design D6): the walks as list laws, and the B3 algebra re-proved by list
    -- induction under its old names; BridgeSet rows 90–107
    ``GoLean.GoCore.Machine.Cont.sizeOf_tail_lt, ``GoLean.GoCore.Machine.Cont.withTail_tail,
    ``GoLean.GoCore.Machine.Cont.tail_withTail, ``GoLean.GoCore.Machine.Cont.rebuild_descend,
    ``GoLean.GoCore.Machine.Cont.rebuild_act, ``GoLean.GoCore.Machine.Cont.rebuild_stop,
    ``GoLean.GoCore.Machine.Cont.rebuild_cons, ``GoLean.GoCore.Machine.Cont.rebuild_nil,
    ``GoLean.GoCore.Machine.Cont.rebuild_locSup,
    ``GoLean.GoCore.Machine.Cont.tail_nil, ``GoLean.GoCore.Machine.Cont.tail_cons,
    ``GoLean.GoCore.Machine.Cont.withTail_nil, ``GoLean.GoCore.Machine.Cont.withTail_cons,
    ``GoLean.GoCore.Machine.Cont.class_nil, ``GoLean.GoCore.Machine.Cont.class_cons,
    ``GoLean.GoCore.Machine.pushDefer_nil, ``GoLean.GoCore.Machine.pushDefer_frame,
    ``GoLean.GoCore.Machine.pushDefer_glue, ``GoLean.GoCore.Machine.pushDefer_other,
    ``GoLean.GoCore.Machine.pushDefer_eq, ``GoLean.GoCore.Machine.pushDefer_some,
    ``GoLean.GoCore.Machine.seqCont_seq, ``GoLean.GoCore.Machine.seqCont_seq_ne,
    ``GoLean.GoCore.Machine.seqCont_eq,
    ``GoLean.GoCore.Machine.panicPassthrough_nil, ``GoLean.GoCore.Machine.panicPassthrough_eq,
    ``GoLean.GoCore.Machine.recoverAtDeferred_nil, ``GoLean.GoCore.Machine.recoverResult_nil,
    ``GoLean.GoCore.Machine.recoverResult_cons_glue,
    ``GoLean.GoCore.Machine.stepFn_next_frame, ``GoLean.GoCore.Machine.stepFrameExit_nil,
    ``GoLean.GoCore.Machine.Cont.locSup_cons, ``GoLean.GoCore.Machine.Cont.locSup_nil,
    ``GoLean.GoCore.Machine.Cont.ownSup_cons,
    -- the A3a admission checker (core `Admission`; the admission step audits the rest)
    ``GoLean.GoCore.Admission.checkBoolean_iff,
    ``GoLean.GoCore.Admission.admitted_index_bound,
    ``GoLean.GoCore.Admission.admitted_all_bodies,
    -- the config-level abort observer (`AbortObservation`)
    ``GoLean.GoCore.RecoveryRuntime.runConfigWithAbort_erasure,
    ``GoLean.GoCore.RecoveryRuntime.stringPanicEntry?_some,
    ``GoLean.GoCore.RecoveryRuntime.stringPanicEntries?_some,
    ``GoLean.GoCore.RecoveryRuntime.stringPanicEntries?_typed,
    ``GoLean.GoCore.RecoveryRuntime.abortRecord?_some,
    ``GoLean.GoCore.RecoveryRuntime.runConfigWithAbort_witness,
    -- the string-panic members at the machine's abort (`StringPanic`)
    ``GoLean.GoCore.Machine.renderPanicHead_string,
    ``GoLean.GoCore.Machine.stringPanicHead_none_iff,
    ``GoLean.GoCore.Machine.stringFirstLine?_bytes,
    ``GoLean.GoCore.Machine.stepFn_string_abort,
    ``GoLean.GoCore.Machine.stepFn_string_abort_refused,
    ``GoLean.GoCore.Machine.runConfig_string_abort,
    ``GoLean.GoCore.Machine.runConfig_string_abort_refused,
    -- the first-line renderer's byte facts (`PanicText`, `Machine`)
    ``GoLean.GoCore.PanicText.lfPrefix_valid,
    ``GoLean.GoCore.PanicText.firstLine_bytes,
    ``GoLean.GoCore.Machine.utf8String?_bytes,
    -- the contract regressions (`Tests/GoCoreContract.lean` §A/§B/§C)
    ``GoLean.GoCore.ContractTests.recover_step_does_not_transport,
    ``GoLean.GoCore.ContractTests.fixed_stream_not_existential_path,
    ``GoLean.GoCore.ContractTests.address_bound_admits_ill_typed,
    ``GoLean.GoCore.ContractTests.both_pool_traces,
    ``GoLean.GoCore.ContractTests.print_before_panic,
    ``GoLean.GoCore.ContractTests.Interpreter.terminal_at_zero_fuel,
    ``GoLean.GoCore.ContractTests.Interpreter.actual_scope_restoration,
    ``GoLean.GoCore.ContractTests.Interpreter.actual_new_local_zero,
    ``GoLean.GoCore.ContractTests.Interpreter.registration_is_lifo,
    ``GoLean.GoCore.ContractTests.Interpreter.equal_repanic_keeps_history,
    ``GoLean.GoCore.ContractTests.Interpreter.scope_and_zero_execution,
    ``GoLean.GoCore.ContractTests.Interpreter.write_keeps_both_actual_aliases,
    ``GoLean.GoCore.ContractTests.AbortObserver.complete_chain_bytes_and_flags,
    ``GoLean.GoCore.ContractTests.AbortObserver.stringPanicEntries?_map_entry,
    -- the renderer and member regressions (`Tests/PanicRendering.lean`, `Tests/StringPanicMembers.lean`)
    ``GoLean.PanicRenderingTests.equal_repanic_members,
    ``GoLean.PanicRenderingTests.invalid_utf8_first_line_refused,
    ``GoLean.PanicRenderingTests.refusal_names_the_cause,
    ``GoLean.StringPanicMembersTests.member_is_renderer,
    ``GoLean.StringPanicMembersTests.generic_actual_abort,
    ``GoLean.StringPanicMembersTests.actual_abort_pin_collapse,
    ``GoLean.StringPanicMembersTests.actual_abort_refused]

/-- The abort-text helpers keep the constructive machine-helper boundary (no
`Classical.choice`), although the correspondence layer admits the classical trio. -/
def constructiveHelpers : List Name := [
    ``GoLean.GoCore.PanicText.firstLine, ``GoLean.GoCore.Machine.utf8String?,
    ``GoLean.GoCore.Machine.stringFirstLine?, ``GoLean.GoCore.Machine.renderPanicHead,
    ``GoLean.GoCore.Machine.abortMsg]

/-- `onDisk` is the harness's listing of every `GoLean/*.lean` and `GoLean/GoCore/*.lean`
module (plus the aggregator `GoLean.GoCore`); the audit refuses any mismatch with the
closure in either direction. -/
def run (onDisk : List String) : CoreM Unit := do
  let env ← getEnv
  let header := env.header.moduleNames
  for m in header do
    unless allowedRoots.contains m.getRoot do
      throwError "Core totality audit: foreign module root in the closure: {m} (lake-manifest.json declares no packages; fail closed)"
  let ourModules := header.filter fun m => m.getRoot == `GoLean
  if onDisk.isEmpty then
    throwError "Core totality audit: the harness passed an empty on-disk module list (vacuous audit refused)"
  for name in onDisk do
    unless header.contains name.toName do
      throwError "Core totality audit: module on disk but not in the audited closure: {name}"
  for m in ourModules do
    unless onDisk.contains m.toString do
      throwError "Core totality audit: module in the closure but absent from the harness's on-disk list: {m}"
  for m in requiredModules do
    unless header.contains m do
      throwError "Core totality audit: missing module {m}"
  for n in exports do
    let some (.thmInfo _) := env.find? n
      | throwError "Core totality audit: missing theorem {n}"
  for n in constructiveHelpers do
    for ax in (← collectAxioms n) do
      unless [``propext, ``Quot.sound].contains ax do
        throwError "Core totality audit: constructive abort-text helper {n} depends on forbidden axiom {ax}"
  let ours := header.map fun n => [`GoLean, `Tests].contains n.getRoot
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let localModule := match env.getModuleIdxFor? n with
      | some i => ours[i.toNat]!
      | none => true
    unless localModule do continue
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "Core totality audit: {n} depends on forbidden axiom {ax}"
    checked := checked + 1
  let goCore := ourModules.filter fun m => m.toString.startsWith "GoLean.GoCore."
  logInfo s!"Core totality audit: {ourModules.size} GoLean modules in the closure ({goCore.size} under GoLean.GoCore), all on disk; {exports.length} required theorems present; {checked} declarations across all imported local modules; classical trio only"

end Tests.GoCoreAudit
