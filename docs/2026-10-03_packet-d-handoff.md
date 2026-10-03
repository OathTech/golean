# Window packet D — the semantic EQUATIONS, the pool PROJECTIONS, the toy client, the gate: HANDOFF (2026-10-03)

[AGENT packet D worker], branch `window/packet-d-equations-1003` off `main` @ `3bb8f4fc` (train r60 close).
Brief `docs/codex-briefs/2026-09-24_packet-D-equations.md` as amended 2026-09-28 (prompt audit) and 2026-09-30
(coordinator addenda); the coordinator's packet-D specification of 2026-10-03 (five items). The [USER] is the user of
the three teams; the logic team's requests 1, 2, 7 and 9 (`docs/2026-09-28_note-from-logic-team.md`, relayed) are
design input served here. ZERO behaviour change: no runtime definition touched — proofs, lemmas, tests, scripts,
records only. Tip at this handoff: ``5335ee03` (the proofs commit) + the records commit that adds this handoff, the evidence dir and the changelog row`. Changelog row 7a: `docs/changelog/61958f2e-WINDOW.md`.

## 1. State — what landed on the branch

| Item | File(s) | What |
|---|---|---|
| 1 the EQUATION SET | `GoLean/GoCore/Equations.lean` (NEW, 229 theorems), `GoLean/GoCore/EquationsAttr.lean` (NEW: `register_simp_attr stepFn_eqns`) | one lemma per `stepFn` arm over a symbolic store/env/continuation/tape with explicit operation premises; every arm equation tagged `@[stepFn_eqns]`; `simp only [stepFn_eqns, <premises>]` is the use |
| 2 the PROJECTIONS | `GoLean/GoCore/PoolProjection.lean` (NEW, 34 theorems) | the single-goroutine OUTPUT AGREEMENT, the SEQUENTIAL-TO-POOL TERMINAL PROJECTION, the embedding without the `seqOpCount = 0` premise (request 9) |
| 3 the SETUP EQUATION | `Equations.lean` §«The pinned SETUP EQUATION» | `runProgramSetup_noInit` + layout `setup_lookup_arg`/`_result`, `setup_resultLocs`, `setup_heap_size` (request 2) |
| 4 the FOLD-BACK | `MachineSound.lean`, `PrefixFacts.lean`, `MultiStreams.lean`, `Prefix.lean`, `BridgeSet.lean` row 62 | `stepFn_consumption_some` premise-free; the PrefixFacts copy DELETED; row 62 re-targeted, statement unchanged (packet B audit F3) |
| 5 audit F2 | `MachineSound.lean` (`stepFn_sound`, `stepFn_consumption_none`) | the `.retV`/`.next` catch-alls closed by SHAPE (`guard_hyp` tests for a free continuation), not by `case137`/`case152` |
| the CLIENT | `Tests/EquationClient.lean` (NEW; library `EquationTests`) | 7 facts by the equation set + `Prefix`/`Finish`; 229 pins `Pin.<name>` with the statements written out; the in-file `#eval` enrollment check |
| the GATE | `scripts/check-equations` (NEW), `scripts/ci` step `equations`, `scripts/ci-libraries.json`, `lakefile.toml` | builds, runs the client, the no-unfold guard, two fail-closed self-tests |
| the records | `BridgeSet.lean` RE-PIN 10 (rows 174–436), `Tests/GoCoreAudit.lean` (3 modules, 263 theorems required), changelog row 7a, this handoff, `docs/evidence/2026-10-03_packet-d/` | |

## 2. What is PROVED (by group, names)

### 2.1 Priority (1) — control, calls, defer, return, panic/recover, the signal table, frame exit, unwinding
`exec_seqn`, `exec_ifThenElse`, `exec_while`, `exec_returnStmt`, `exec_breakStmt`, `exec_continueStmt`, `exec_inertLabel`,
`exec_labeled`, `exec_breakTo`, `exec_continueTo`, `exec_breakable`, `exec_unsupported`; calls: `exec_call_args`,
`exec_call_nullary` (ENTRY on `enterFrame`), `exec_call_nullary_panic` (the `nilValueMethodText` consult written out),
`exec_call_unsupported`, `exec_callValue`, `exec_callValue_unsupported`, `retV_callArgsK_more`/`_enter`/`_enter_panic`,
`retV_callValCalleeK_enter`/`_enter_panic`/`_nil`/`_args`, `retV_callValArgsK_more`/`_enter`/`_enter_panic`/`_nil`
(request 1's filing correction: these are `.retV v` arms); defer: `exec_deferCall`, `retV_deferCalleeK_args`/`_push`/
`_push_frame`/`_outside`, `retV_deferArgsK_more`/`_push`/`_push_frame`/`_outside`; panic/recover: `exec_panicStmt`,
`retV_panicArgK`, `evalE_recoverCall`; UNWINDING (request 7, over the preprint phase's arms): `panicking_frame_empty`,
`panicking_frame_defer`/`_defer_run`/`_defer_panic`/`_defer_nil` (the `deferPanic` entry), `panicking_panicResumeK`,
`next_panicResumeK_unrecovered`/`_recovered`, `panicking_glue` (the general `panicPassthrough` law) + `panicking_seq`/
`_loop`/`_breakableK`/`_labelK`/`_strictK`/`_storeK`, `panicking_probeK`, `panicking_stop_settled` (THE ABORT),
`panicking_stop_pending` (the PREPRINT PHASE step), `panicking_nil_stop`, `next_preprintK`/`_panic`, `retV_preprintK_string`,
`panicking_preprintK` (the fatal); FRAME EXIT (continuations audit F4): `next_frame`, `signal_ret_frame`, `frameExit_nil`,
`frameExit_targets` (result readback; `loadResults_nil`/`_cons` over `loadRoot`), `frameExit_defer`/`_defer_run`/
`_defer_panic`/`_defer_nil`, `frameExit_preprint`, `frameExit_extra_results`, `frameExit_malformed`; SIGNALS: `signal_table`,
`signal_stop`, `signal_frame_escape`, `signalStep_seq`/`_breakableK_brk`/`_breakableK_ret`/`_breakableK_cont`/`_loop_brk`/
`_loop_cont`/`_loop_ret`/`_labelK_ret`/`_labelK_brkTo_self`; `.next` control: `next_stop`, `next_seq_cons`, `next_seq_nil`,
`next_loop`, `next_breakableK`, `next_labelK`, `next_strictK`/`_ifK`/`_callArgsK` (completion to an expression frame refuses),
`retV_seq`/`_frame`/`_storeK`/`_stop` (a value to a statement frame refuses).

### 2.2 Priority (2) — memory
`evalE_var` (THE read: `loadRoot`, the access at `projChainTarget`'s leaf), `evalE_var_unbound`, `evalE_ref`/`_unbound`,
`evalE_global`/`_oob`; the spine: `exec_assign`, `exec_assign_var`, `exec_assign_unsupported`, `retV_tgtOpK_more`/
`_next_target`/`_rhs`/`_store`/`_malformed`, `retV_rhsK_more`/`_apply`/`_apply_panic`, `next_storeK_store` (composed
`storeTarget`), `next_storeK_chain` (`resolveChain`/`valueAsLoc`/ONE `storeLoc`), `next_storeK_var` (the plain-variable
store), `next_storeK_panic`, `next_storeK_done`; block entry: `exec_block` (C4), `allocDecls_nil`/`_cons`,
`bindParams_nil`/`_cons` (the floor is `Store.alloc`); the ROOT-CELL laws: `loadRoot_base`, `storeLoc_root`,
`Heap.lookup_set_self`, `Heap.lookup_push_self`; helpers: `storeTarget_inv_panic`, `applyStmtOp_inv_panic`,
`toResult_of_error`, `valueAsBool_bool`, `valueAsLoc_addr`/`_nil`, `targetPlan_var`, `completeTargetRef_var`,
`resolveChain_nil`, `applyRhsOp_vals`.

### 2.3 Priority (3) — the rest
`retV_ifK_true`/`_false`, `retV_whileK_true`/`_false`, `evalE_and`/`_or`, `retV_andK_true`/`_false`, `retV_orK_true`/`_false`,
`retV_boolK`; `evalE_intLit`/`_boolLit`/`_stringLit`/`_unsupported`; `evalE_strict_more`/`_nullary`, `retV_strictK_more`/
`_apply`/`_apply_panic`/`_apply_error`; `exec_wide` (over `stmtPlan`), `exec_allocNew`/`_mapAssign`/`_appendSlice`/`_print`,
`retV_stmtOpK_more_target`/`_more_target_nil`/`_more_operand`/`_apply`/`_apply_panic` (the COMPOSED `applyStmtOp`);
`exec_mapRange`, `retV_mapRangeK`, `next_mapIterK_done`/`_pick`/`_stop`; `exec_mapLookup`, `exec_typeAssert`,
`exec_assignMany`/`_arity`; `exec_chanSend`/`_closeChan`/`_chanRecv`, `retV_chanStK_more`/`_apply`/`_apply_panic`;
`exec_selectStmt`/`_default`/`_block`, `retV_selectOpsK_more`/`_apply`; `exec_goStmt`, `retV_goCalleeK_args`/`_spawn`,
`retV_goArgsK_more`/`_spawn`; `exec_syncStmt`, `retV_syncStK_more`/`_apply`/`_apply_error` (the fatal propagates);
`exec_atomicStmt`, `retV_atomicStK_more`/`_apply`/`_apply_panic`; `blockedSend`/`blockedRecv`/`blockedSelect`/`blockedSync`;
`exec_unseqProbe`, `retV_probeK`, `exec_unseq`, `next_unseqK`, `retV_unseqK`, `unseqEnter`, `unseqValue`, `unseqRun_eval`,
`unseqWait_invoke`.

### 2.4 The setup equation (request 2)
`stateWf_empty`, `seedGlobals_nil`, `runPkgInitM_none`, `runProgramSetup_noInit`, `pinResultLocs_eq_of_lookup`,
`setup_lookup_arg` (`args[i] ↦ .base ⟨i⟩`), `setup_lookup_result` (`results[j] ↦ .base ⟨args.size + j⟩`),
`setup_resultLocs` (the pinned list IS those cells in order), `setup_heap_size`.

### 2.5 The projections (packet B audit F5; request 9)
`transferableWide` (+ `transferable_wide`, `transferableWide_ok`/`_fuelOut`/`_terminal`, `not_transferableWide_deadlock`/
`_refusal`), `seqOut` (+ `seqOut_zero`/`_succ`/`_stop`), `outFold` (+ `_nil`/`_cons`/`outFold_eq_fold`);
`runnableIdxs_singleton_none`, `mainOutcome?_single_none`, `front_single_step`/`_single_flagged`/`_terminal`/`_aborted`;
`stepThread_single_out`, `stepMulti_single_out`; **(a) output agreement** `execProgLoopOut_single_wide`,
`execProgLoopOut_single`, `seqOut_of_prefix` (+ `isTerminal_false_of_stepFn_ok`, `isBlockedConfig_false_of_stepFn_ok`,
`zeroCost_stops`), `execProgLoopOut_single_prefix`, `pool_run_single_prefix`; **(b) terminal projection**
`execProgLoop_single_wide`, `execProgLoop_single_terminal`, `execProgLoopOut_single_terminal`; **request 9**
`afterStepFlag_none_of_noRegistry`, `seqOpCount_eq_zero`, `execProgLoop_single_noBoundary`.

## 3. Statements — none changed except the planned row 62 re-target
- Rows 1–173 BYTE-IDENTICAL (checked by `git diff` on `BridgeSet.lean`: the only change above the RE-PIN 10 block is row 62's
  comment and target name). Every `_stmt` of `ExecutionStatement.lean` untouched; `execProgLoop_single`/`transferable` untouched.
- `MachineSound.stepFn_consumption_some`'s TYPE changed (the planned fold-back): the unread `(_hloc : c.appendTargetLocal)`
  dropped and `{tr : StepLabel}` declared explicitly where row 62's statement has it — the theorem now HAS row 62's statement.
  `MultiStreams.stepThread_pick_run` keeps its `hloc` hypothesis (type unchanged; renamed `_hloc`, now unused).
- `Prefix.replay_coverage`/`noRefusal_step` and `MultiStreams.stepThread_pick_run` cite the fold-back; `Tests/UnseqSchedulerAudit`
  names `stepFn_consumption_some` (unchanged name).

## 4. Interpretations ([AGENT packet D worker] INTERPRETED — flagged, not decided)
1. The client's pins are NAMED theorems `Pin.<name>` (not anonymous `example`s) so the exhaustiveness `#eval` can check both
   presence and that the pin's TYPE is the theorem's up to alpha-equivalence (`Expr ==`) — stronger than the brief's textual
   reading; a statement drift fails the client as well as `BridgeSet`.
2. The arm equations' PANIC forms are stated over the COMPOSED applies (`storeTarget`, `applyStmtOp`, `enterFrame`) with the
   `*_inv_panic` helpers (the commit cannot panic — `*_commit_noPanic`), so no premise mentions a `.plan`.
3. Refusal arms are stated where the premise is a clean equation; the `.evalE` catch-all's `"unclassified expression"` is
   UNREACHABLE (every `Expr` constructor is an arm or has a `strictPlan`) and the `.retV` `"expected function value"` refusals
   over an arbitrary non-function value are stated only for `nil`/function values (the general form would enumerate `GoValue`).
4. The `unseq` sweep: the three positions reduce to their helpers (`exec_unseq`, `next_unseqK`, `retV_unseqK`) plus the
   ENTER, the value write, `.run i` on a value head and `.wait i` on an invocation; the other phases are left to the helpers'
   soundness lemmas (MachineSound) — stated as far as the brief's priority (3) asks.
5. `transferableWide`, `seqOut`, `outFold` are proof-layer DEFINITIONS beside `seqOpCount` (no runtime definition touched).
6. Audit F2 is done with `guard_hyp` shape tests (a free continuation under `.retV`/`.next`) — the alternative (a meta tactic)
   would have imported `Lean` into `MachineSound`.
7. The two FRAME-EXIT refusals are stated by shape (`frameExit_extra_results` carries the «not the preprint one-result shape»
   premise as a universally quantified inequality).

## 5. Elaboration (G-C3 stop rule: no module > 1.5×; `maxHeartbeats` never raised)
Measured back to back per module under the lock (`.tmp/elab-ab.sh`; alternating sides, two reps, the module's own artifacts
deleted before each single-target `lake build`; main = a detached worktree at `3bb8f4fc` with a fresh `.lake`; box load from
other projects' builds throughout; `docs/evidence/2026-10-03_packet-d/elaboration-ab.tsv`):

| module | main (s) | lane (s) | ratio |
|---|---|---|---|
| `Machine` | 8.30, 7.60 | 8.40, 8.20 | 1.04× |
| `StateWf` | 26.00, 25.00 | 26.00, 26.00 | 1.02× |
| `StepFn` | 1.20, 1.10 | 1.20, 1.10 | 1.00× |
| `MachineEqb` | 5.50, 5.50 | 5.50, 5.50 | 1.00× |
| `MachineSound` | 90.00, 86.00 | 89.00, 85.00 | 0.99× (the `guard_hyp` closers cost nothing measurable) |
| `MultiSound` | 5.70, 5.20 | 5.30, 5.30 | 0.97× |
| `MultiStreams` | 1.30, 1.30 | 1.20, 1.30 | 0.96× |
| `PrefixFacts` | 23.00, 23.00 | 16.00, 15.00 | **0.67×** (the 240-line copy gone; the preprint audit's 1.48× margin is recovered) |
| `StepErrors` | 272.00, 251.00 | 265.00, 258.00 | 1.00× |
| `Prefix` | 0.98, 0.97 | 0.98, 1.00 | 1.02× |
| `BridgeSet` | 1.00, 1.10 | 1.90, 1.90 | **1.81× — REPORTED** (263 pinned rows added, 173 → 436: the per-row cost is unchanged, the content grew; +0.85 s absolute) |
| `EquationsAttr` | — | 0.21, 0.24 | new |
| `Equations` | — | 2.50, 2.60 | new (229 theorems) |
| `PoolProjection` | — | 1.50, 1.50 | new |

No module's PROOFS got slower; the one ratio over 1.5× is `BridgeSet`'s additive growth (posed in §9 — a split of the
RE-PIN 10 rows into a second pin module would read 1.0× without changing any statement, if the rule is held to the letter).
`maxHeartbeats` was raised nowhere and added nowhere (`Equations.lean`/`PoolProjection.lean` run at the default budget).

## 6. Gates (every EXIT recorded; evidence `docs/evidence/2026-10-03_packet-d/`)
- `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the tree of `5335ee03` (under the lock): **EXIT=1, RED ON EXACTLY THE 5a PAIR** —
  `certificate provenance` (STALE certification: changed dependency `GoLean.lean`; the fresh certifications report «unchanged
  set») and the baseline diff's ONE drift line `imported-goose/channel/google-search PASS/membership → FAIL/membership`
  (the certified row judged stale for that reason). Differential: `cases=3821 pass=3583 fail=238` (237 + the 5a row);
  negative baseline 394 matched; every other step ok — core build WARNING-FREE, core totality audit, admission, declaration
  boundary, wire boundary, method identity, unseq scheduler/wire, **`semantic equations (scripts/check-equations)` ok**,
  frontend pins (twin byte-identical), eval tests 298 ok, executed library coverage (10 libraries, 9 steps, 20 Tests
  modules). Reconciler: 2 findings, both standing (C9 = the 5a STALE; C13 doc versions). 1261 s. Tail:
  `docs/evidence/2026-10-03_packet-d/ci-diff-tail.txt`.
- `GOLEAN_MEM_MAX=48G scripts/capped scripts/check-equations`: **EXIT=0** — `Equation client: enrollment complete — 229 equation
  theorems pinned, 7 facts`; `Equation client: PASS — 7 facts by the equation set only`; `ok [no-unfold]`; `ok [self-test
  unfold] the guard fires on a client that unfolds stepFn`; `ok [self-test pin] deleting Pin.storeTarget_inv_panic fails the
  enrollment check by name`; `Equation gate: PASS`. Tail: `check-equations.txt`.
- `scripts/capped scripts/check-core-audit`: **EXIT=0** — 54 GoLean modules in the closure (45 under `GoLean.GoCore`), all on
  disk; 470 required theorems present (263 added here); 19751 declarations; classical trio only; 5 compiled poison controls
  rejected by name. Tail: `core-audit-tail.txt`.
- `python3 tools/ci_libraries.py check`: PASS (10 libraries, 9 steps, 20 Tests modules); the `selftests` ran green inside `ci`.
- NOT re-run here (unchanged inputs): the whole-corpus choice trace and the raft twin — this packet changes no runtime byte and
  the gate moved no row beyond the 5a line.

## 7. The CLAUDE.md sentence (DRAFT for the [USER]'s approval — not edited here)
Current: «Still OWED, kept in step with the interpreter (priority (c) of the 2026-09-11 ruling): the pool/registry half, the
single-goroutine output agreement and the sequential-to-pool terminal projection. Limits: setup is a premise, init-time
printing is refused, and the domain premise `NoRefusal` covers the sequential driver only (a `go` statement leaves it).»

Proposed: «Still OWED, kept in step with the interpreter (priority (c) of the 2026-09-11 ruling): the pool/registry half —
the labelled pool relation over `StepLabel` with attribution, registry boundaries and the pool deadlock's own condition.
Proved 2026-10-03 (`GoLean/GoCore/PoolProjection.lean`): the single-goroutine output agreement (the pool's output fold is the
sequential labels' fold) and the sequential-to-pool terminal projection (every Go terminal but the sequential deadlock, at the
pool's fuel `fuel + seqOpCount`; at equal fuel when no reachable step opens a registry boundary). Limits: setup is a premise
(its no-globals, no-initializer case is the pinned equation `runProgramSetup_noInit`), init-time printing is refused, and the
domain premise `NoRefusal` covers the sequential driver only (a `go` statement leaves it).»

## 8. The offer's interface summary (what a consumer gets at this tip)
- Three separate checks: STATEMENTS (`BridgeSet.lean`, 436 rows), EQUATIONS (`Equations.lean`, 229 proved; `stepFn_eqns`),
  the CLIENT (`Tests/EquationClient.lean`, 7 facts, 229 pins, `scripts/check-equations`).
- Memory floor: `loadRoot`/`storeLoc`/`Store.alloc` laws (`loadRoot_base`, `storeLoc_root`, `Heap.lookup_set_self`/`_push_self`,
  `allocDecls_cons`/`bindParams_cons` → `Store.alloc_shape`/`_cell`, the C4/B6 slot laws).
- Setup: `runProgramSetup_noInit` + layout.
- Pool: output agreement + terminal projection + the equal-fuel embedding; LIMITS: the deadlock stays excluded (an artificial
  wake-ready blocked seed resumes in the pool); the pool/registry half (multi-goroutine) remains owed.

## 9. What stopped and why — nothing stopped; posed
- None of the five items stopped. POSED for the [USER]/coordinator:
  1. The CLAUDE.md sentence (§7) — a [USER]-approved edit; not made here.
  2. BridgeSet's elaboration ratio (§5): a module whose content grew by 263 pinned rows cannot be «restructured» to stay under
     1.5× — the per-row cost is unchanged; the stop rule's intent (a cost blow-up of existing proofs) is not what moves it.
     Posed: does G-C3 decision 6 apply to additive pin rows? (Absolute cost: ~1 s.)
  3. `transferable` (row 23/50) stays as is; `transferableWide` is offered beside it. A later re-pin could widen
     `single_embedding_stmt` itself to `transferableWide` — a STATEMENT change, so posed, not done.
  4. The brief's `[AGENT Codex, packet D]` commit tag was replaced by `[AGENT packet D worker]` (the coordinator's execution-model
     ruling: packets run as subagents, not Codex).
