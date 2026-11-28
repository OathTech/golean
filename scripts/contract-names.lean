/-
scripts/contract-names.lean — the KEPT SURFACE of the comparator contract, enumerated from the
built environment (lane gate/comparator-1023, 2026-10-23; release-readiness row 43,
[USER]-ruled 2026-10-23). Run from the checkout root, after `lake build GoLean`:

    lake env lean scripts/contract-names.lean

Prints one line per kept theorem — `KEPT<TAB><family><TAB><full name><TAB><module>` — in a
fixed family order, names sorted within a family, plus `COUNT<TAB><what><TAB><n>` lines for the
counts the records quote (today: the `stepFn_eqns` simp set's membership), and nothing else on
stdout. scripts/gen-contract
turns the list into `comparator.json` and `GoLean/Contract/Solution.lean`. Every family is read
from the ENVIRONMENT, not from text, so a lemma that gains or loses the `stepFn_eqns` attribute,
or a theorem added to or removed from `InitDriverFacts.lean`, changes the list (and
`scripts/gen-contract --check` then names the drift). The families, as ruled:

  dedup       checkCert_slowObs and checkCertM_slowObs: accepted certificates equal SlowObs.
  prefix      `Prefix`/`Finish`'s laws kept for the customer: prefix_comp, prefix_split,
              run_ok_iff, run_panic_iff, replay_coverage (`Prefix.lean`; `replays` is a
              DEFINITION, reached by replay_coverage's statement, not a theorem — see the note in
              Contract/Challenge.lean).
  enterFrame  `enterFrame_declared` (`Machine.lean`).
  recover     `recoverAtDeferred_none` (`Machine.lean`): below anything but the panic marker there
              is nothing to recover (raft-proofs' G23, 2026-11-10, relayed by the [USER] the same
              day: the customer proves a recover rule against it and asked for a contracted
              statement). An EXPLICIT one-name list ([AGENT] 2026-11-10): its neighbours
              (`recoverAtDeferred_marker`, `recoverResult_frame`, `recoverResult_eq`,
              `recoverResult_frame_none`, `recoverResult_glue`, `recoverResult_cons_glue`) were
              not asked for and are not kept; the reply names them.
  iface       `isNormalForTy_interface` (`StateWf.lean`): a value is normal at an interface type
              exactly when it is the nil interface or a box whose payload's head agrees with
              its dynamic type (raft-proofs' G23 (1) in the one-level form ruled by the [USER]
              2026-11-25; the customer named this characterisation as the statement it would
              consume). One name ([AGENT] 2026-11-25): the walk's other lemmas are its proof's.
  widevalue   the wide operators' value-form surface (`WideValue.lean`, `WideValueFacts.lean`;
              raft-proofs' request of 2026-11-27, widened the same day on the [USER]'s direction
              that the surface be a principled set others might target, not the two equations
              asked for): the equations at an address target and for untargeted `randIntn`, the
              no-value refusal and the lowering's target count (`stmtPlan_targets`); the
              validate-phase transfer and the success characterisation
              (`applyStmtOp_plan_ok_iff_value`); the value forms' own invariants (no panic in a
              commit, strictness, `NoDead`, the effect statement `applyStmtOpValue_effect` with
              its shape, size, frame and well-formedness clauses, normality of the value at its
              type, agreement under table slices); the memory frame laws those rest on
              (`Store.updateCell_frame` … `Store.allocCell_frame`); the four step equations at the
              apply position; and, from the second audit's fix round (2026-11-28), the effect's
              clauses each as its own statement (`applyStmtOpValue_shape`, `_size`, `_frame`,
              `_frame_of_growth`, `_wf` — so each is frozen as text, not only through
              `WideEffect`), the stream statements (`_no_draw`, `_appendSlice_stream`,
              `_randIntn`), `applyStmtOp_plan_error_of_target`, and the un-split and step forms of
              untargeted `randIntn`. An EXPLICIT list ([AGENT] 2026-11-27/28: the [USER] directed
              the surface and approved contracting the equations; WHICH further statements are
              kept is the lane's choice): the per-operator lemmas beneath each are the proofs'
              cases. The definitions the statements reach — new: `applyStmtOpValue`,
              `applyStmtOpValue.plan`, `storeValue`, `storeValueInto`, `dropValue`,
              `StmtOp.hasValueForm`, `StmtOp.valueShape`, `wideWrittenRoot?`, `WideEffect`,
              `CommitEffect`; existing: `Post`, `Commit.NoDead`, `StmtOpPres`, `StateWf`,
              `goValueListSup`, `GoValue.locSup`, `PlanNoPanic`, `ErrP`, `Stop.Tame` — are compared
              whole, as every definition is.
  widemachine the machine-side theorems the value-form surface rests on or points to, kept so that
              a consumer reading a value-form fact through them reads a frozen statement (the
              [USER]'s agreement of 2026-11-28 to the second audit's finding 7): the wide apply's
              strictness and commit facts (`applyStmtOp_plan_tame`, `_plan_commitOk`,
              `_commit_noPanic`, `_inv_ok`), its well-formedness (`applyStmtOp_wf`), its stream
              consumption (`applyStmtOp_plan_appendSlice_nospill`, `_spill`,
              `_plan_randIntn_nodraw`, `_draw`, `applyStmtOp_plan_of_stmtConsult?_none`),
              `Mem.store_noPanic`, and `isNormalForTy_sound` (the `valueShape_*_normal` lemmas'
              companion). An EXPLICIT list ([AGENT] 2026-11-28); `applyStmtOp_noDead` is already
              kept, in family `deadcell`.
  consumeAt   every theorem `…Choices.consumeAt*` — the `consumeAt_*` and `consumeAtE_*` laws of
              `State.lean` and `Machine.lean` (the customer's G9 list names both spellings).
  eqns        every public theorem of the module `GoLean.GoCore.Equations` — the customer's
              rewriting library is the MODULE (its `signalStep_*` rows, `runProgramSetup_noInit`,
              the `allocDecls_*`/`bindParams_*`/`setup_*` facts, … are plain theorems there,
              not simp-set members), widened from the `@[stepFn_eqns]` simp set's membership at
              the fix round of 2026-10-23 (review F1; the owner's confirmation asked at the
              merge ask). The simp set's membership is printed as a COUNT line beside it, and
              every member must be a theorem of the module (fail closed otherwise).
  g11         every public theorem of `GoLean/GoCore/InitDriverFacts.lean` (the G11 family:
              `runInitConfig_*`, `runPkgInitM_*`, `prefix_det`/`prefix_det_le`, the
              `*_of_prefix_silent` converses, the one-step helpers), minus the toolchain's
              realized equation lemmas (`*.eq_N`, `*.eq_def`) that happen to be minted there.
  pool        the output-fold bridge: execProgLoopOut_snd (`Multi.lean`), execProgLoopOut_single,
              execProgLoopOut_single_prefix, seqOut_of_prefix (`PoolProjection.lean`),
              execProgLoopOut_eq_execProgLoop, execProgLoopOut_acc (`PoolFacts.lean`).
  g16         the thirteen table-monotonicity statements of `TableMonotonicity.lean` (raft-proofs
              G16, backlog row 48; moved into the contract 2026-10-25, lane gate/contract-pins-1025, on
              the [USER] ruling that the per-key relation of train 17 is final): the lifts `stepFn_mono`,
              `prefix_mono`, `finish_aborted_mono`, `execStmtLoop_ok_mono`, `execStmtLoop_panic_mono`,
              the first-match lookups `findFunctionIn?_mono`, `methodInfoByFuncId?_mono`,
              `methodDecl?_mono`, `promotion?_mono`, `methodSetCoverage?_mono` (added at the fix round
              of 2026-10-25, the coordinator's decision relayed: a public lookup lemma of the same kind,
              and the customer's ask names `methodSetCoverage?` among the lookups it wants monotone),
              `resolveMethod?_mono`, `callee?_mono` and the frame-entry funnel `enterFramePickV_mono` —
              all in namespace `ProgramCtx.SubTables`. An EXPLICIT list, like `prefix` and `pool`, not
              the module's theorem set ([AGENT] 2026-10-25): the module's other theorems are the lift's scaffolding — the
              `tablesFree` congruence sweep in `TableMono`, the per-arm `*_mono`/`*_eq_of_recorded`
              helpers — named for the proof's shape, not the customer's use (the reply
              docs/2026-10-23_reply-to-raft-proofs-g16-g18.md names these twelve, as do the §D pins
              and the core audit's required list); freezing the scaffolding would make a refactor
              of the sweep a contract change. The relation's DEFINITIONS (`SubTables`, `TablesKeyed`,
              `SliceClosed`) are reached by the statements and compared whole, as every definition is.

  deadcell    the dead cell's customer-facing statements (raft-proofs' rung-2 request, backlog row
              63; into the contract on the [USER] ruling of 2026-11-24): refusal at a dead root
              (`IsStuck`'s three laws, the readers/writers, the `Mem.*` operations, the strict and
              sync heads, the dispatch receiver read), the `markDead` frame, `NoDead` (the empty
              store, the two cell primitives, `stepFn_noDead`, `Prefix.noDead`, the frame-entry,
              memory and wide operations), `HeapCell.isDead_iff`, and beside them the three
              `Ty.eqb` laws and `applyStrictOp_leafOf_irrel` asked for in the same message; and,
              from the pre-merge audit's fix round the same day, `NoDead` through the fuel
              drivers, setup, the seeded entry and the pool, `syncCell_dead`/`chanCell_dead`,
              and `HeapNormal`/`StateWf` kept by `markDead` (fifteen; ninety in all). An
              EXPLICIT list, like `g16` ([AGENT] 2026-11-24): `DeadCell.lean`'s other theorems
              are the sweep's scaffolding — the `Post` combinators, the per-constructor
              `stepFn_noDead_*` and `applyStmtOpCore.plan_noDead_*` cases, the `.plan`, delivery
              and step-helper lemmas — and freezing them would make a refactor of the sweep a
              contract change. The definitions the statements reach (`HeapCell.dead`,
              `Store.markDead`, `Store.NoDead`, `Store.DeadAt`, `IsStuck`, `Post`) are compared
              whole, as every definition is.

Fails closed (a Lean error, exit 1) when a named theorem is missing, is not a theorem, carries
universe parameters, lies outside the `GoLean` namespace, or when a family is empty.
-/
import GoLean
import Lean

namespace ContractNames
open Lean

/-- The toolchain's realized names (`eq_1`, `eq_def`, `proof_1`, `match_1`…) and auxiliary names. -/
def isReservedSuffix (n : Name) : Bool :=
  match n with
  | .str _ s => s == "eq_def" || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit)
      || s.startsWith "proof_" || s.startsWith "match_"
  | _ => true

/-- The public theorems the module `m` declares, sorted by name. -/
def moduleTheorems (env : Environment) (m : Name) : Array Name := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if !isPrivateName n && !n.isInternal && !isReservedSuffix n then
        if let some idx := env.getModuleIdxFor? n then
          if env.header.moduleNames[idx.toNat]! == m then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

/-- Every theorem whose name is `….Choices.consumeAt…` — outside the contract's own alias
namespace `GoLean.Contract` (the generated Solution is in the `GoLean` library, so its aliases
are in this environment too; an alias is never a kept theorem). -/
def consumeAtTheorems (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .thmInfo _ := ci then
      if let .str (.str _ "Choices") s := n then
        if s.startsWith "consumeAt" && !(`GoLean.Contract).isPrefixOf n then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

def check (env : Environment) (family : String) (n : Name) : Except String Unit := do
  let some ci := env.find? n | throw s!"{family}: {n} is not in the environment"
  unless ci matches .thmInfo _ do throw s!"{family}: {n} is not a theorem"
  unless ci.levelParams.isEmpty do throw s!"{family}: {n} has universe parameters {ci.levelParams}"
  unless (`GoLean).isPrefixOf n do throw s!"{family}: {n} is outside the GoLean namespace"
  if (`GoLean.Contract).isPrefixOf n then throw s!"{family}: {n} is a contract alias, not a kept theorem"
  if (`GoLean.Contract).isPrefixOf (moduleOf env n) then throw s!"{family}: {n} is declared in a contract module"

end ContractNames

open ContractNames in
#eval show Lean.Elab.TermElabM Unit from do
  let env ← Lean.getEnv
  let some ext ← Lean.Meta.getSimpExtension? `stepFn_eqns
    | throwError "contract-names: the stepFn_eqns simp attribute is not registered"
  let thms ← ext.getTheorems
  let mut tagged : Array Lean.Name := #[]
  for o in thms.lemmaNames.toList do
    if let .decl n _ _ := o then tagged := tagged.push n
  let eqns := tagged.qsort (fun a b => a.toString < b.toString)
  let eqnsModule := moduleTheorems env `GoLean.GoCore.Equations
  for n in eqns do
    unless eqnsModule.contains n do
      throwError "contract-names: the stepFn_eqns member {n} is not a public theorem of GoLean.GoCore.Equations"
  IO.println s!"COUNT\tstepFn_eqns simp-set members (all of them theorems of GoLean.GoCore.Equations)\t{eqns.size}"
  let families : Array (String × Array Lean.Name) := #[
    ("dedup", #[`GoLean.GoCore.Machine.checkCert_slowObs, `GoLean.GoCore.Machine.checkCertM_slowObs]),
    ("prefix", #[`GoLean.GoCore.ExecutionStatement.prefix_comp, `GoLean.GoCore.ExecutionStatement.prefix_split,
      `GoLean.GoCore.ExecutionStatement.run_ok_iff, `GoLean.GoCore.ExecutionStatement.run_panic_iff,
      `GoLean.GoCore.ExecutionStatement.replay_coverage]),
    ("enterFrame", #[`GoLean.GoCore.Machine.enterFrame_declared]),
    ("recover", #[`GoLean.GoCore.Machine.recoverAtDeferred_none]),
    ("iface", #[`GoLean.GoCore.isNormalForTy_interface]),
    ("widevalue", #[
      `GoLean.GoCore.Machine.applyStmtOp_plan_eq_value,
      `GoLean.GoCore.Machine.applyStmtOp_eq_value,
      `GoLean.GoCore.Machine.applyStmtOp_plan_randIntn_untargeted,
      `GoLean.GoCore.Machine.applyStmtOpValue_plan_of_not_hasValueForm,
      `GoLean.GoCore.Machine.stmtPlan_targets,
      `GoLean.GoCore.Machine.applyStmtOpValue_plan_error_iff,
      `GoLean.GoCore.Machine.applyStmtOpValue_plan_ok_iff,
      `GoLean.GoCore.Machine.applyStmtOp_plan_target,
      `GoLean.GoCore.Machine.applyStmtOp_plan_ok_iff_value,
      `GoLean.GoCore.Machine.applyStmtOpValue_commit_noPanic,
      `GoLean.GoCore.Machine.applyStmtOpValue_plan_tame,
      `GoLean.GoCore.Machine.applyStmtOpValue_commit_tame,
      `GoLean.GoCore.Machine.applyStmtOpValue.plan_noDead,
      `GoLean.GoCore.Machine.applyStmtOpValue_noDead,
      `GoLean.GoCore.Machine.applyStmtOpValue_plan_effect,
      `GoLean.GoCore.Machine.applyStmtOpValue_effect,
      `GoLean.GoCore.Machine.valueShape_allocNew_normal,
      `GoLean.GoCore.Machine.valueShape_makeSlice_normal,
      `GoLean.GoCore.Machine.valueShape_appendSlice_normal,
      `GoLean.GoCore.Machine.valueShape_makeMap_normal,
      `GoLean.GoCore.Machine.valueShape_makeChan_normal,
      `GoLean.GoCore.Machine.Store.updateCell_frame,
      `GoLean.GoCore.Machine.storeLoc_frame,
      `GoLean.GoCore.Machine.Mem.store_frame,
      `GoLean.GoCore.Machine.Mem.storeElems_frame,
      `GoLean.GoCore.Machine.Mem.storeRun_frame,
      `GoLean.GoCore.Machine.Store.alloc_frame,
      `GoLean.GoCore.Machine.Store.allocCell_frame,
      `GoLean.GoCore.Machine.stmtOpOut_of_hasValueForm,
      `GoLean.GoCore.Machine.retV_stmtOpK_apply_value,
      `GoLean.GoCore.Machine.retV_stmtOpK_apply_value_panic,
      `GoLean.GoCore.Machine.retV_stmtOpK_apply_value_error,
      `GoLean.GoCore.Machine.retV_stmtOpK_apply_value_store_error,
`GoLean.GoCore.Machine.applyStmtOp_randIntn_untargeted,
      `GoLean.GoCore.Machine.applyStmtOp_plan_error_of_target,
      `GoLean.GoCore.Machine.applyStmtOpValue_shape,
      `GoLean.GoCore.Machine.applyStmtOpValue_size,
      `GoLean.GoCore.Machine.applyStmtOpValue_frame,
      `GoLean.GoCore.Machine.applyStmtOpValue_frame_of_growth,
      `GoLean.GoCore.Machine.applyStmtOpValue_wf,
      `GoLean.GoCore.Machine.applyStmtOpValue_no_draw,
      `GoLean.GoCore.Machine.applyStmtOpValue_appendSlice_stream,
      `GoLean.GoCore.Machine.applyStmtOpValue_randIntn,
      `GoLean.GoCore.Machine.retV_stmtOpK_apply_randIntn_untargeted,
      `GoLean.GoCore.TableMono.applyStmtOpValue_plan_eq,
      `GoLean.GoCore.TableMono.applyStmtOpValue_eq,
      `GoLean.GoCore.TableMono.storeValue_eq]),
    ("widemachine", #[
      `GoLean.GoCore.Machine.applyStmtOp_plan_tame,
      `GoLean.GoCore.Machine.applyStmtOp_plan_commitOk,
      `GoLean.GoCore.Machine.applyStmtOp_commit_noPanic,
      `GoLean.GoCore.Machine.applyStmtOp_wf,
      `GoLean.GoCore.Machine.applyStmtOp_inv_ok,
      `GoLean.GoCore.Machine.applyStmtOp_plan_appendSlice_nospill,
      `GoLean.GoCore.Machine.applyStmtOp_plan_appendSlice_spill,
      `GoLean.GoCore.Machine.applyStmtOp_plan_randIntn_nodraw,
      `GoLean.GoCore.Machine.applyStmtOp_plan_randIntn_draw,
      `GoLean.GoCore.Machine.«applyStmtOp_plan_of_stmtConsult?_none»,
      `GoLean.GoCore.Machine.Mem.store_noPanic,
      `GoLean.GoCore.Machine.isNormalForTy_sound]),
    ("consumeAt", consumeAtTheorems env),
    ("eqns", eqnsModule),
    ("g11", moduleTheorems env `GoLean.GoCore.InitDriverFacts),
    ("pool", #[`GoLean.GoCore.Machine.execProgLoopOut_snd, `GoLean.GoCore.Machine.execProgLoopOut_single,
      `GoLean.GoCore.Machine.execProgLoopOut_single_prefix, `GoLean.GoCore.Machine.seqOut_of_prefix,
      `GoLean.GoCore.Machine.execProgLoopOut_eq_execProgLoop, `GoLean.GoCore.Machine.execProgLoopOut_acc]),
    ("g16", #[`GoLean.GoCore.ProgramCtx.SubTables.stepFn_mono, `GoLean.GoCore.ProgramCtx.SubTables.prefix_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.finish_aborted_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.execStmtLoop_ok_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.execStmtLoop_panic_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.findFunctionIn?_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.methodInfoByFuncId?_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.methodDecl?_mono, `GoLean.GoCore.ProgramCtx.SubTables.promotion?_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.methodSetCoverage?_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.resolveMethod?_mono, `GoLean.GoCore.ProgramCtx.SubTables.callee?_mono,
      `GoLean.GoCore.ProgramCtx.SubTables.enterFramePickV_mono]),
    ("deadcell", #[
      `GoLean.GoCore.IsStuck.not_ok,
      `GoLean.GoCore.IsStuck.not_panic,
      `GoLean.GoCore.IsStuck.bind,
      `GoLean.GoCore.Machine.loadLoc_dead,
      `GoLean.GoCore.Machine.loadRoot_dead,
      `GoLean.GoCore.Machine.storeLoc_dead,
      `GoLean.GoCore.Machine.«mapPayload?_dead»,
      `GoLean.GoCore.Machine.«chanPayload?_dead»,
      `GoLean.GoCore.Machine.storeMapPayload_dead,
      `GoLean.GoCore.Machine.storeChanPayload_dead,
      `GoLean.GoCore.Machine.Mem.load_dead,
      `GoLean.GoCore.Machine.Mem.loadFor_dead,
      `GoLean.GoCore.Machine.Mem.loadBinding_dead,
      `GoLean.GoCore.Machine.Mem.loadBindingFor_dead,
      `GoLean.GoCore.Machine.Mem.store_dead,
      `GoLean.GoCore.Machine.Mem.storeThrough_dead,
      `GoLean.GoCore.Machine.Mem.mapRead_dead,
      `GoLean.GoCore.Machine.Mem.mapWrite_dead,
      `GoLean.GoCore.Machine.loadMany_dead_head,
      `GoLean.GoCore.Machine.loadMany_not_ok_of_dead,
      `GoLean.GoCore.Machine.loadResults_dead_head,
      `GoLean.GoCore.Machine.applyStrictOp_deref_dead,
      `GoLean.GoCore.Machine.applyStrictOp_indexGet_dead,
      `GoLean.GoCore.Machine.applyStrictOp_lengthOf_chan_dead,
      `GoLean.GoCore.Machine.applyStrictOp_lengthOf_map_dead,
      `GoLean.GoCore.Machine.applyStrictOp_lengthOf_addr_dead,
      `GoLean.GoCore.Machine.applyStrictOp_capacityOf_chan_dead,
      `GoLean.GoCore.Machine.applyStrictOp_capacityOf_addr_dead,
      `GoLean.GoCore.Machine.applySyncOpCore_lock_dead,
      `GoLean.GoCore.Machine.applySyncOpCore_unlock_dead,
      `GoLean.GoCore.Machine.applySyncOp_lock_dead,
      `GoLean.GoCore.Machine.applySyncOp_unlock_dead,
      `GoLean.GoCore.Machine.receiverAt_deref_dead,
      `GoLean.GoCore.Store.markDead_size,
      `GoLean.GoCore.Store.markDead_nextAddr,
      `GoLean.GoCore.Store.markDead_lookup_self,
      `GoLean.GoCore.Store.markDead_lookup_ne,
      `GoLean.GoCore.Store.markDead_not_noDead,
      `GoLean.GoCore.Store.updateCell_markDead_ne,
      `GoLean.GoCore.Machine.loadLoc_markDead_ne,
      `GoLean.GoCore.Machine.storeLoc_markDead_ne,
      `GoLean.GoCore.Store.NoDead.empty,
      `GoLean.GoCore.Store.noDead_iff_lookup,
      `GoLean.GoCore.Store.NoDead.allocCell,
      `GoLean.GoCore.Store.NoDead.updateCell,
      `GoLean.GoCore.ExecutionStatement.Prefix.noDead,
      `GoLean.GoCore.Store.alloc_noDead,
      `GoLean.GoCore.storeLoc_noDead,
      `GoLean.GoCore.Mem.store_noDead,
      `GoLean.GoCore.Mem.storeThrough_noDead,
      `GoLean.GoCore.Mem.mapWrite_noDead,
      `GoLean.GoCore.Mem.storeElems_noDead,
      `GoLean.GoCore.Mem.storeRun_noDead,
      `GoLean.GoCore.HeapCell.isDead_iff,
      `GoLean.GoCore.Machine.stepFn_noDead,
      `GoLean.GoCore.Machine.enterFrame_noDead,
      `GoLean.GoCore.Machine.bindParams_noDead,
      `GoLean.GoCore.Machine.allocDecls_noDead,
      `GoLean.GoCore.Machine.applyStrictOp_noDead,
      `GoLean.GoCore.Machine.applyStrictOpPick_noDead,
      `GoLean.GoCore.Machine.applyStmtOp_noDead,
      `GoLean.GoCore.Machine.applyStmtOpCore_noDead,
      `GoLean.GoCore.Machine.storeTarget_noDead,
      `GoLean.GoCore.Machine.mapAssignValue_noDead,
      `GoLean.GoCore.Machine.applySyncOp_noDead,
      `GoLean.GoCore.Machine.applySyncOpCore_noDead,
      `GoLean.GoCore.Machine.applyChanOp_noDead,
      `GoLean.GoCore.Machine.applyAtomicOp_noDead,
      `GoLean.GoCore.Machine.applySelect_noDead,
      `GoLean.GoCore.Machine.commitClause_noDead,
      `GoLean.GoCore.Machine.stepFrameExit_noDead,
      `GoLean.GoCore.Machine.applyStrictOp_leafOf_irrel,
      `GoLean.GoCore.Machine.runConfig_noDead,
      `GoLean.GoCore.Machine.execStmtLoop_noDead,
      `GoLean.GoCore.Machine.stepFnIter_noDead,
      `GoLean.GoCore.Machine.seedGlobals_noDead,
      `GoLean.GoCore.Machine.runInitConfig_noDead,
      `GoLean.GoCore.Machine.runPkgInitM_noDead,
      `GoLean.GoCore.Machine.runProgramSetupM_noDead,
      `GoLean.GoCore.Machine.runProgramSetupSeededM_noDead,
      `GoLean.GoCore.Machine.seedCells_noDead,
      `GoLean.GoCore.Machine.stepMulti_noDead,
      `GoLean.GoCore.Machine.execProgLoop_noDead,
      `GoLean.GoCore.Machine.syncCell_dead,
      `GoLean.GoCore.Machine.chanCell_dead,
      `GoLean.GoCore.Machine.StateWf.markDead,
      `GoLean.GoCore.HeapNormal.markDead,
      `GoLean.Ty.eqb_refl,
      `GoLean.Ty.eqbList_refl,
      `GoLean.Ty.eqb_iff])]
  let mut seen : Std.HashSet Lean.Name := {}
  for (family, names) in families do
    if names.isEmpty then throwError "contract-names: the family {family} is empty"
    for n in names do
      if let .error e := check env family n then throwError "contract-names: {e}"
      if seen.contains n then throwError "contract-names: {n} is listed twice"
      seen := seen.insert n
      IO.println s!"KEPT\t{family}\t{n}\t{moduleOf env n}"
