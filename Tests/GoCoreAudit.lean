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
    `GoLean.GoCore, `GoLean.GoCore.Machine, `GoLean.GoCore.StepFn, `GoLean.GoCore.StateWf,
    `GoLean.GoCore.MachineSound, `GoLean.GoCore.UnseqSound, `GoLean.GoCore.Multi,
    `GoLean.GoCore.MultiSound, `GoLean.GoCore.Trace, `GoLean.GoCore.PoolTrace,
    `GoLean.GoCore.ProgramTrace, `GoLean.GoCore.AbortObservation, `GoLean.GoCore.StringPanic,
    `GoLean.GoCore.PanicText, `GoLean.GoCore.AdmissionIndices, `GoLean.GoCore.AdmissionPolicy,
    `GoLean.GoCore.Admission, `GoLean.CLI, `GoLean.NativeToIR, `GoLean.ChoiceTrace,
    `GoLean.GoCore.ExecutionStatement, `GoLean.GoCore.Prefix, `GoLean.GoCore.BridgeSet,
    `GoLean.GoCore.PrefixFacts, `GoLean.GoCore.StepErrors, `GoLean.GoCore.Locals,
    `Tests.GoCoreContract, `Tests.PanicRendering, `Tests.StringPanicMembers,
    `Tests.GoCoreAudit]

/-- Required core theorems (the `semantic interface` audit's CORE exports, plus the
re-homed regressions). Each must exist as a theorem. -/
def exports : List Name := [
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
