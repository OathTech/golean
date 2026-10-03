# Window packet D — the semantic EQUATIONS, the pool PROJECTIONS, the toy client, the gate: HANDOFF (2026-10-03)

[AGENT packet D worker], branch `window/packet-d-equations-1003` off `main` @ `3bb8f4fc` (train r60 close).
Brief `docs/codex-briefs/2026-09-24_packet-D-equations.md` as amended 2026-09-28 (prompt audit) and 2026-09-30
(coordinator addenda); the coordinator's packet-D specification of 2026-10-03 (five items). The [USER] is the user of
the three teams; the logic team's requests 1, 2, 7 and 9 (`docs/2026-09-28_note-from-logic-team.md`, relayed) are
design input served here. ZERO behaviour change: no runtime definition touched — proofs, lemmas, tests, scripts,
records only. Tips: `5335ee03` (the proofs commit), `03779748` (the records commit: this handoff, the evidence dir, changelog row 7a), `556ab207` (a handoff fix) — audited MERGE-CLEAN (`docs/2026-10-03_packet-d-audit.md`, branch `review/packet-d-equations-1003`); then the PRE-LANDING ROUND: `4a4f381f` (proofs/tests/scripts — the new content tip, the changelog's `candidate freeze` line; audit F1–F6, [AGENT] coordinator dispositions 2026-10-03) and the records commit on top. Changelog row 7a: `docs/changelog/61958f2e-WINDOW.md`.

## 1. State — what landed on the branch

| Item | File(s) | What |
|---|---|---|
| 1 the EQUATION SET | `GoLean/GoCore/Equations.lean` (NEW, 292 theorems after the pre-landing round; 293 after the window-review round — the boxing law, §10), `GoLean/GoCore/EquationsAttr.lean` (NEW: `register_simp_attr stepFn_eqns`, the propositional closer `defn_eq`) | one lemma per `stepFn` arm's success and panic forms, the refusal pass-throughs as listed, over a symbolic store/env/continuation/tape with explicit operation premises; every arm equation tagged `@[stepFn_eqns]` as a PROPOSITIONAL rewrite. USE (audit F1): premise-free arms and arms whose premises range over LHS variables close by `simp only [stepFn_eqns]`; an arm whose successor names a premise-bound value (`evalE_var`, the entries, `next_storeK_*`, `exec_block`, `frameExit_targets`, the applies) is applied by INSTANTIATION (`rw [evalE_var env k ch hl hv]`) or under `simp (discharger := assumption) only [stepFn_eqns]` — the plain `simp only [stepFn_eqns, hl, hv]` does NOT fire there; the client tests each idiom (`fact_usage_*`) |
| 2 the PROJECTIONS | `GoLean/GoCore/PoolProjection.lean` (NEW, 36 theorems) | the single-goroutine OUTPUT AGREEMENT, the SEQUENTIAL-TO-POOL TERMINAL PROJECTION, the embedding without the `seqOpCount = 0` premise (request 9) |
| 3 the SETUP EQUATION | `Equations.lean` §«The pinned SETUP EQUATION» | `runProgramSetup_noInit` + layout `setup_lookup_arg`/`_result`, `setup_resultLocs`, `setup_heap_size` (request 2) |
| 4 the FOLD-BACK | `MachineSound.lean`, `PrefixFacts.lean`, `MultiStreams.lean`, `Prefix.lean`, `BridgeSet.lean` row 62 | `stepFn_consumption_some` premise-free; the PrefixFacts copy DELETED; row 62 re-targeted, statement unchanged (packet B audit F3) |
| 5 audit F2 | `MachineSound.lean` (`stepFn_sound`, `stepFn_consumption_none`) | the `.retV`/`.next` catch-alls closed by SHAPE (`guard_hyp` tests for a free continuation), not by `case137`/`case152` |
| the CLIENT | `Tests/EquationClient.lean` (NEW; library `EquationTests`) | 12 facts by the equation set + `Prefix`/`Finish` (7 symbolic runs + the 4 usage idioms + the concrete inhabitation of FACT 3, §10); 293 pins `Pin.<name>` with the statements written out; the in-file `#eval`: the Lean-level NO-UNFOLD check of every fact's proof term (audit F2) and the exhaustive enrollment |
| the GATE | `scripts/check-equations` (NEW), `scripts/ci` step `equations`, `scripts/ci-libraries.json`, `lakefile.toml` | builds, runs the client (its proof-term check and enrollment), the regex pre-filter, ten fail-closed self-tests (the window-review round added the indirect helper, §10) (the regex mutant, the pin deletion, the audit's seven unfolding spellings each REFUSED by name) |
| the records | `BridgeSet.lean` RE-PIN 10 (rows 174–436; the pre-landing round rows 437–501; the window-review round row 502), `Tests/GoCoreAudit.lean` (3 modules, 329 theorems required), changelog row 7a, this handoff, `docs/evidence/2026-10-03_packet-d/` | |

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
`retV_goArgsK_more`/`_spawn`; `exec_syncStmt`, `retV_syncStK_more`/`_apply`/`_apply_panic`/`_apply_error` (the fatal propagates);
`exec_atomicStmt`, `retV_atomicStK_more`/`_apply`/`_apply_panic`; `blockedSend`/`blockedRecv`/`blockedSelect`/`blockedSync`;
`exec_unseqProbe`, `retV_probeK`, `exec_unseq`, `next_unseqK`, `retV_unseqK`, `unseqEnter`, `unseqValue`, `unseqRun_eval`,
`unseqWait_invoke`.

### 2.3b The pre-landing round's additions (audit F3; appended, rows 437–499)
(a) `retV_syncStK_apply_panic`. (b) The composed applies' and entries' NON-PANIC `Stop` pass-through, generically:
`evalE_strict_nullary_error`, `retV_chanStK_apply_error`, `retV_selectOpsK_apply_panic`/`_apply_error`,
`retV_rhsK_apply_error`, `retV_atomicStK_apply_error`, `next_preprintK_error`, `retV_stmtOpK_apply_error`,
`next_storeK_error`, `exec_call_nullary_error`, `retV_callArgsK_enter_error`, `retV_callValCalleeK_enter_error`,
`retV_callValArgsK_enter_error`, `panicking_frame_defer_error`, `frameExit_defer_error`; the plain-bind arms
`exec_block_error`, `evalE_var_error`, `retV_mapRangeK_error`, `next_mapIterK_error`, `frameExit_targets_error`,
`frameExit_preprint_error`, `unseqEnter_error`, `unseqValue_error` (helpers `bind_eq_error`, `runCommit_error`,
`enterFramePickV_of_plan_error`, `enterFrame_inv_error`). (c) The refusal arms by shape: `retV_ifK_error`/
`_whileK_error`/`_andK_error`/`_orK_error`/`_boolK_error` (+ `valueAsBool_nonbool`), `retV_callValCalleeK_args_notfunc`,
`retV_deferCalleeK_notfunc`, `retV_goCalleeK_notfunc` (+ `deferrableCallee_false`), `panicking_frame_defer_notfunc`,
`frameExit_defer_notfunc`, `retV_preprintK_nonstring`, `next_storeK_arity_refs`/`_vals`. (d) The signal table
completed: `signalStep_breakableK_brkTo`/`_contTo`, `signalStep_labelK_brk`/`_cont`/`_brkTo_ne`/`_contTo_self`/
`_contTo_ne`, `signalStep_loop_brkTo`/`_contTo_self`/`_contTo_ne`, the five `signalStep_mapIterK_*` (+ `_contTo_ne`),
`contHeadLabel_labelK`/`_stop`/`_frame`, and the refusal `signal_labelK_contTo_self`. STILL NOT STATED (header
inventory): the `.evalE` catch-all's unreachable `"unclassified expression"`; the `unseq` scheduler's remaining
phases (the sweep reduces to its helpers).

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
`afterStepFlag_none_of_noRegistry`, `seqOpCount_eq_zero`, `execProgLoop_single_noBoundary`; **(audit F4)** the WIDE equal-fuel forms `execProgLoop_single_noBoundary_wide`, `execProgLoopOut_single_noBoundary_wide` (the `fatal`/`raceDetected` terminals included).

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
7. (Pre-landing round, audit F2) The arm equations are PROPOSITIONAL — `defn_eq` closes each definitional
   equation with `Eq.mpr (Eq.refl _) rfl`, not `rfl` — because `simp` uses an `rfl`-theorem as a `dsimp`
   (definitional) rewrite that leaves NO trace in the proof term, which would make the honest `simp only
   [stepFn_eqns]` indistinguishable from `simp [stepFn]`. With the equations propositional, the client's
   proof-term check re-type-checks each fact with `stepFn` IRREDUCIBLE (`Meta.check` itself runs at `.all`,
   so the traversal is its shape at a controlled transparency) — the audit's prescribed constant/`Eq.refl` scan
   alone misses `simp_all [stepFn]`, `simpa [stepFn]` and `simp only [stepFn]; rfl`, whose terms carry neither
   (measured on the audit's witnesses). Statements unchanged; a client that used `dsimp only [stepFn_eqns]`
   must use `simp only`.
8. The two FRAME-EXIT refusals are stated by shape (`frameExit_extra_results` carries the «not the preprint one-result shape»
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

No module's PROOFS got slower; the one ratio over 1.5× is `BridgeSet`'s additive growth (1.0 → 1.9 s; the pre-landing
round adds 65 more rows — `BridgeSet` built in 2.1 s, `Equations` in 2.7 s with 292 theorems). **PENDING [USER]** (audit F6,
[AGENT] coordinator disposition: record, no split): «additive pin rows are EXEMPT from the G-C3 elaboration stop rule —
the ratio measures a hot proof module's cost regressing, not a pin file growing by content; the absolute cost is
reported». Until ruled, the ratio is reported as is and the file is not split.
`maxHeartbeats` was raised nowhere and added nowhere (`Equations.lean`/`PoolProjection.lean` run at the default budget).

## 6. Gates (every EXIT recorded; evidence `docs/evidence/2026-10-03_packet-d/`)
- PRE-LANDING ROUND, at the tree of `4a4f381f`: `ci --diff` **EXIT=1 on exactly the 5a pair** (certificate provenance STALE on `GoLean.lean`; the one certified row), 3821 = 3583/238, negative baseline 394 matched, core build warning-free, `semantic equations` ok, 879 s; `check-equations` **EXIT=0** (292 pinned, 11 facts, «none unfolds stepFn», nine self-tests incl. the seven unfolding spellings REFUSED by name); `check-core-audit` **EXIT=0** (54 modules, 535 required theorems). The first-round figures follow.
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
- `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci` (the fast gate, no `--diff`) at the records tree `03779748`: **EXIT=1 on the same
  5a pair only** (`certificate provenance` STALE on `GoLean.lean`; the cached differential's one drift row), 32 steps ok, 517 s.
- NOT re-run here (unchanged inputs): the whole-corpus choice trace and the raft twin — this packet changes no runtime byte and
  the gate moved no row beyond the 5a line.

## 7. The CLAUDE.md sentence (DRAFT for the [USER]'s approval — not edited here)
Current: «Still OWED, kept in step with the interpreter (priority (c) of the 2026-09-11 ruling): the pool/registry half, the
single-goroutine output agreement and the sequential-to-pool terminal projection. Limits: setup is a premise, init-time
printing is refused, and the domain premise `NoRefusal` covers the sequential driver only (a `go` statement leaves it).»

Proposed: «Still OWED, kept in step with the interpreter (priority (c) of the 2026-09-11 ruling): the pool/registry half —
the labelled pool relation over `StepLabel` with attribution, registry boundaries and the pool deadlock's own condition.
Proved 2026-10-03 (`GoLean/GoCore/PoolProjection.lean`): the single-goroutine output agreement (the pool's output fold is the
sequential labels' fold) and the sequential-to-pool terminal projection — every sequential result but the deadlock and the
refusals, the `fatal` terminal included, is the one-goroutine pool's at the pool's fuel `fuel + seqOpCount`, and at EQUAL fuel
when no reachable step opens a registry boundary. Limits: setup is a premise (its no-globals, no-initializer case is the
pinned equation `runProgramSetup_noInit`), init-time printing is refused, and the domain premise `NoRefusal` covers the
sequential driver only (a `go` statement leaves it).»

Every clause is now backed by a stated theorem (pre-landing round, audit F4): the output fold by `execProgLoopOut_single_prefix`
+ `outFold_eq_fold`; «every sequential result but the deadlock and the refusals» by `execProgLoop_single_wide` over
`transferableWide` (`execProgLoop_single_terminal` for a terminal `t ≠ .deadlock`); the EQUAL-fuel clause by
`execProgLoop_single_noBoundary_wide` (the `fatal`/`raceDetected` terminals included) — the first draft's clause was proved for
`transferable` only.

## 8. The offer's interface summary (what a consumer gets at this tip)
- Three separate checks: STATEMENTS (`BridgeSet.lean`, 502 rows), EQUATIONS (`Equations.lean`, 293 proved; `stepFn_eqns`,
  propositional), the CLIENT (`Tests/EquationClient.lean`, 12 facts — the concrete inhabitation included — 293 pins, the
  Lean-level no-unfold check over the client-owned closure, `scripts/check-equations` with twelve self-tests and the import whitelist; §10–§11). Usage: see §1 item 1 (instantiation / discharger for the premised arms).
- Memory floor, precisely (audit F5): VARIABLE READS (`evalE_var`, the pinned-result readback `frameExit_targets`/
  `loadResults_cons`/`frameExit_preprint`) reach `loadRoot` (= `loadLoc` at a root cell, `loadRoot_base`); PLAIN and CHAIN
  STORES (`next_storeK_var`/`_chain`, `unseqValue`) reach `storeLoc` (`storeLoc_root`, `Heap.lookup_set_self`); BLOCK and
  FRAME ENTRY (`exec_block`, the entries via `enterFrame_declared`) reach `Store.alloc` through `allocDecls_cons`/
  `bindParams_cons` (`Store.alloc_shape`/`_cell`, `Heap.lookup_push_self`, the C4/B6 slot laws). NOT at the floor: a pointer
  read `*p`, a field read `x.f`, an index read `a[i]`, a map get / comma-ok — these stop at the COMPOSED `applyStrictOp`/
  `applyRhsOp` (`retV_strictK_apply`, `retV_rhsK_apply`); their inner `loadLoc`/`Mem.loadFor` laws are not stated here.
- Setup: `runProgramSetup_noInit` + layout.
- Pool: output agreement + terminal projection (wide: every result but the deadlock and the refusals) + the equal-fuel
  embedding (wide); LIMITS: the deadlock stays excluded (an artificial wake-ready blocked seed resumes in the pool); the
  pool/registry half (multi-goroutine) remains owed.

## 9. What stopped and why — nothing stopped; posed
- None of the five items stopped. POSED for the [USER]/coordinator:
  1. The CLAUDE.md sentence (§7) — a [USER]-approved edit; not made here.
  2. BridgeSet's elaboration ratio (§5): PENDING [USER] — «additive pin rows are exempt from the G-C3 elaboration stop rule»
     (audit F6; the coordinator's disposition: record, no split). Absolute cost ~1 s; 328 pinned rows now.
  3. `transferable` (row 23/50) stays as is; `transferableWide` is offered beside it with the wide equal-fuel embedding (F4
     done). A later re-pin could widen `single_embedding_stmt` itself to `transferableWide` — a STATEMENT change, so posed.
  4. The brief's `[AGENT Codex, packet D]` commit tag was replaced by `[AGENT packet D worker]` (the coordinator's execution-model
     ruling: packets run as subagents, not Codex).

## 10. The WINDOW-REVIEW round (`docs/2026-10-03_window-review.md` F1/F2/F4; [AGENT packet D worker] 2026-10-03) — before → after

Commits: the code group `43624b55` (`Equations.lean` +1 law, `BridgeSet.lean` row 502, `Tests/GoCoreAudit.lean` +1 export,
`Tests/EquationClient.lean`, `scripts/check-equations`), the records group `the commit after it (this records commit)` (this section, the changelog's F4
table and row 7a, the evidence tails). No pinned statement changed (row 502 and the export are ADDITIONS); no runtime
definition touched; `maxHeartbeats` never raised.

### F1 (P2) — `fact_write_survives_panic` had an unsatisfiable premise and entered no callee
- BEFORE: the fact raised `.panicStmt (.stringLit txt)` — an UNBOXED `.string` payload, which is not a Go interface value;
  `renderPanicPayload` has no arm for it, so the premise `hmsg : abortMsg ctx (panicEntryOf ctx (.string txt)) [] 0 = .ok t`
  held for NO `ctx`/`txt`/`t` and the fact was vacuous; and nothing was called — the «callee» was the sequence glue.
- AFTER: the caller runs `x = y` then the nullary declared call `f()`; the callee's body is `panic(any(txt))` — the string
  BOXED by `Expr.toInterface ty .string` (`applyStrictOp_toInterface_string`, the NEW helper law: the apply is read-only,
  trace-free, the interface value at the canonical dynamic type `string`; row 502, pinned and exported). Twenty steps: the
  assignment's spine (7), the call's entry (`exec_call_nullary`, trace `tr`), `exec_panicStmt`, `evalE_strict_more`,
  `evalE_stringLit`, `retV_strictK_apply`, `retV_panicArgK`, then the unwinding `panicking_frame_empty` (the callee's frame),
  `panicking_seq` (the caller's glue), `panicking_frame_empty` (the barrier); `Finish.aborted` at the empty continuation.
  Premises: `hlx hly hy hst` (the memory floor), `he : enterFrame ctx s' f [] = .ok (.run func fenv [], s', tr)` (store-
  preserving for a parameterless, resultless callee), `hbody`, `hsettled : splitNewestPending? [strEntry ctx txt] = none`
  (`string` carries no `Error`/`String` method — no preprint phase), `hmsg : abortMsg ctx (strEntry ctx txt) [] 0 = .ok t`,
  with `strEntry ctx txt := panicEntryOf ctx (.interface .string (.string txt))`. Endpoint `.aborted t s' ch` with `s'` the
  WRITTEN store.
- INHABITATION: `fact_inhabit_write_survives_panic` (a named `fact_*` theorem rather than an `example`, so the enrollment
  check verifies it too): context `boomCtx := ProgramCtx.ofTables TypeEnv.reserved #[boomFunc]`, callee `boom()` with body
  `panic(any("boom"))`, two root `int` cells (`x ↦ 0 holding 0`, `y ↦ 1 holding 7`), environment `[[(0, .base 0), (1, .base 1)]]`;
  conclusion `LRun boomCtx boomStore₀ … [] [silent, …, readOf (.base 1), silent, writeOf (.base 0), …] [] (.aborted "boom"
  boomStore₁ [])` with `boomStore₁` = the heap after the write. Every premise discharged by computation: seven `rfl`
  (lookups, read, write, entry, body, settled) and `with_unfolding_all rfl` for `hmsg` (the abort's UTF-8 decoding is
  well-founded recursion). Verified by `#eval` first (the choice of values), then the kernel.
- THE REVIEW'S WITNESSES, now theorems of the client (`section Witnesses`): `witness_unboxed_payload_unrenderable (ctx) (txt) :
  renderPanicPayload ctx (panicEntryOf ctx (.string txt)) = none := rfl` and `witness_unboxed_premise_false (ctx) (txt) (t)
  (hmsg : abortMsg ctx (panicEntryOf ctx (.string txt)) [] 0 = .ok t) : False := by cases hmsg` — both elaborate at the
  round's tip (the gate's client run): the old premise refutes itself for every context, text and `t`.

### F2 (P2) — the no-unfold check visited the facts' proof terms only
- BEFORE: `checkEnrollment` ran (1)–(4) on each `fact_*` value; a `private theorem … := by rfl` on a `stepFn`-headed equation,
  `exact`ed from a fact, passed (the review's reproducer) — the unfolding sat in a constant the fact merely named.
- AFTER: the check runs over the proof-dependency CLOSURE of the CLIENT-OWNED declarations (constants of the current
  module, `env.getModuleIdxFor? = none`) reachable from each fact through `getUsedConstants` of the values; the published API
  (`GoLean.GoCore.Equations`, `Prefix`, `ExecutionStatement`, the interpreter — everything imported) is the boundary and is
  not traversed. Each reached declaration with a value (theorem proof, definition body, opaque) gets (1) no `stepFn.*`
  constant, (2) no reflexivity on a `stepFn`-headed term, (3) the irreducible-`stepFn` re-type-check; (4) axioms at the root
  (transitive already). A refusal names the fact AND the helper: «fact <root> REFUSED — its proof unfolds stepFn in its
  helper <helper> (…)».
- THE OBLIGATION FILTER ([AGENT] design, flagged): (3) re-runs a defeq obligation only when one of its two sides names a
  constant whose definitional unfolding REACHES `stepFn` (`reachesStepFn`: memoized reachability through constant VALUES;
  `mayUnfoldStepFn`: the sides' constants after zeta-expansion, the free locals' types included). Why: the kernel's check of
  an obligation can only unfold what its sides name, so an obligation naming nothing that reaches `stepFn` never meets it —
  re-running it proves nothing about `stepFn` and may be arbitrarily expensive (the inhabitation's
  `abortMsg … = .ok "boom"` is well-founded UTF-8 decoding; re-run at `.all` with a `canUnfold?` override it blew the
  heartbeat budget — the override disables the whnf cache — and at `.default` it is stuck on the irreducible well-founded
  helper, a FALSE refusal). Every obligation that can reach `stepFn` is re-run exactly as before; the seven bypass spellings
  and the indirect helper are all refused (gate self-tests 3–10).
- NEGATIVE CONTROL #10 (`scripts/check-equations`, step e4): the client with `private theorem returnViaReduction … := by rfl`
  inserted before FACT 8 and the anchor replaced by `exact returnViaReduction s env k ch` must fail with «fact
  Tests.EquationClient.fact_usage_simp_set REFUSED — its proof unfolds stepFn in its helper …returnViaReduction». Gate
  output: «ok [self-test indirect] …»; the gate now counts 10 self-tests.
- Witness re-run (the review's reproducer at the round's tip): REFUSED — see the gate tail `check-equations.txt`
  (`ok [self-test indirect]`), and the mutant's log line quoted in the evidence README.

### F4 (P3) — the cumulative tool-interface table
- BEFORE: the changelog's per-lane «flags unchanged» lines, true of their lanes, missed the frontend's additive
  `-unseq-census` flag (`tools/nativefrontend/main.go:87`) in the pin-to-offer record.
- AFTER: `docs/changelog/61958f2e-WINDOW.md` §«Cumulative tool-interface table» — computed from `git diff 61958f2e 43624b55`
  over request 8's interfaces: frontend flags 8 → 9 (`-unseq-census` ADDED; emits a TSV census, no wire; no gate/baseline/
  corpus path reads it), the wire schema v1 → v3 (already recorded), the `scripts/diff-coverage` manifest schema UNCHANGED,
  `decodeProgram : Json → Except String Program` UNCHANGED (its accepted input moved with the schema), `RunResult :=
  Except (Stop × GoString) Readout` and `runProgramM : … → Except Stop Readout` UNCHANGED, Lean `v4.32.2` UNCHANGED, the
  `deps/go` pin go1.26.5 UNCHANGED; each cell with its derivation command.

### Gates of the round (every EXIT; tails in `docs/evidence/2026-10-03_packet-d/`)
- `GOLEAN_MEM_MAX=48G scripts/capped scripts/check-equations` (under the lock): **EXIT=0** — client PASS, «293 equation theorems
  pinned, 12 facts and 15 client-owned helpers, none unfolds stepFn», the regex pre-filter, **10 self-tests** (the regex
  mutant, the pin deletion, the seven bypass spellings, the NEW indirect helper). Tail: `check-equations.txt`.
- `scripts/capped scripts/check-core-audit`: **EXIT=0** — 54 modules in the closure, **536 required theorems present** (+1:
  `applyStrictOp_toInterface_string`), 20100 declarations, classical trio only, 5 poison controls rejected by name. Tail:
  `core-audit-tail.txt`.
- `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (under the lock, at the tree of `43624b55`): **EXIT=1, RED ON EXACTLY THE
  5a PAIR** — `certificate provenance` (STALE: changed dependency `GoLean.lean`) and `baseline diff` (the one drift row
  `imported-goose/channel/google-search PASS/membership → FAIL/membership`); `cases=3821 pass=3583 fail=238`; negative
  baseline 394 matched; every other step ok (core build warning-free, `semantic equations` ok, eval tests 298 ok, executed
  library coverage); 1215 s. Tail: `ci-diff-tail.txt`. The run BEFORE the law's proof was switched to `rfl` (below) had
  the same verdict (920 s).
- The REVIEW'S WITNESSES re-run: `witness_unboxed_payload_unrenderable`/`witness_unboxed_premise_false` elaborate in the
  client (the gate's build); the F2 reproducer, rebuilt outside the gate from the same recipe, fails with
  «`Equation client: fact Tests.EquationClient.fact_usage_simp_set REFUSED — its proof unfolds stepFn in its helper
  Tests.EquationClient.returnViaReduction (it closes Eq.refl …`» (README).

### Elaboration of the round
Standalone `lake env lean` of the module, two reps, one lock session (`elaboration-roundc.txt`): `Equations.lean` NEW
2.40–2.41 s vs the file at `9c14fef1` 2.38–2.45 s — **1.00×**; `BridgeSet.lean` (+1 row) 1.86–1.88 s (the pre-landing round's
1.9 s). HONEST NOTE: the law's FIRST proof, `simp [applyStrictOp, checkedDynamicTy, …]`, cost 5.02–5.11 s (2.1× — the simp
set over the whole `applyStrictOp` match); the gates' first full run (all green on the same lines) was on that proof; it was
replaced by `rfl` (0 ms; the arm reduces definitionally) and every gate re-run on the final tree. No other module changed;
`PrefixFacts` untouched (0.67× stands); `maxHeartbeats` never raised. The client's `#eval` now checks 12 facts + 15
helpers in ~1 s (the obligation filter skips what cannot reach `stepFn`).

## 11. The audit's RE-VERIFICATION, R1 (`docs/2026-10-03_packet-d-audit.md` §«Re-verification (`7a976448`)»; [AGENT] coordinator disposition: close both witnesses before landing; [AGENT packet D worker] 2026-10-03)

Commits: the code group `6fb3ac16` (`Tests/EquationClient.lean`, `scripts/check-equations` only), the records commit after it (this
section, the changelog's row 7a addendum and candidate freeze, the evidence tails). No statement, pin, export or runtime byte
touched; no module of `GoLean/` changed (no elaboration measurement owed).

### R1 — the closure stopped at ANY imported constant, and the imports were unconstrained
- BEFORE: `checkEnrollment` traversed the CLIENT-OWNED closure (`getModuleIdxFor? = none`); two witnesses passed the gate —
  (A) a new fact proved by the imported `rfl`-theorem `GoLean.GoCore.Machine.stepFn_next_frame` (`StepFn.lean`, outside the
  equation set); (B) the anchored fact proved by `AuditSupport.helper`, a `rfl`-on-`stepFn` theorem in a FOREIGN test-support
  module compiled to an olean and imported on an extended `LEAN_PATH`.
- AFTER (1) — the IMPORT WHITELIST: `importWhitelist := [Init, Std, Lean] ++ apiModules` with `apiModules := [Equations,
  EquationsAttr, Prefix, ExecutionStatement, PoolProjection, BridgeSet]` (all `GoLean.GoCore.*`); `checkEnrollment` reads
  `env.header.imports` FIRST and refuses a non-whitelisted import BY NAME («import AuditSupport is NOT WHITELISTED — the client
  may import only […]»); the gate pre-filters the client's `import` lines against the same list (`ok [imports]`).
- AFTER (2) — the boundary is the PUBLISHED API: `ownerOf` classifies every constant the closure meets by its module —
  `.boundary` (an API module, or a toolchain module `Init`/`Std`/`Lean`/`Lake`, which predate `stepFn` and cannot reach it):
  cited, not traversed; `.client` (this module, or any non-`GoLean` module): every value traversed; `.core` (a non-API
  `GoLean` module — `StepFn`, `Machine`, `Ops`, …): its THEOREMS and Prop-typed constants traversed, never `stepFn` itself and
  not its definitions (they are the SUBJECT — what a proof may or may not unfold, which check (3) measures at the use site;
  the core's own gates exclude a proof hidden in a core definition — RECORDED LIMIT). Check (1) no longer counts `stepFn`'s
  MATCHERS `match_N` (Lean reuses matchers across declarations; a matcher cannot unfold `stepFn`, and a proof through one
  still meets check (3)) — otherwise a traversed core theorem could be refused for a reused matcher. The reachability filter
  of check (3) is unchanged. The traversal now reaches 23 helpers (15 client-owned + the core theorems the facts cite:
  `Config.abort?_of_settled`, `Choices.consumeAtE_le_one`, … and their proof dependencies up to the API/toolchain).
- AFTER (3) — gate self-tests 11–12 (`scripts/check-equations` e5/e6), each REFUSED by name: witness A rebuilt as
  `fact_via_imported_rfl` (factCount 13) → «fact Tests.EquationClient.fact_via_imported_rfl REFUSED — its proof unfolds
  stepFn in its helper GoLean.GoCore.Machine.stepFn_next_frame (it closes rfl by reflexivity)»; witness B rebuilt from the
  audit's `AuditSupport.lean` (compiled with `lake env lean -o` into the gate's scratch, `LEAN_PATH` extended, plain `lean`
  through `scripts/capped`) → «Equation client: import AuditSupport is NOT WHITELISTED — the client may import only [Init,
  Std, Lean, GoLean.GoCore.Equations, …]». Both lines reproduced outside the gate from the same recipes (`.tmp`, deleted).
- AFTER (4) — the PASS line: «Equation client: PASS — 12 facts by the equation set and the published API».
- Gates of the round: `check-equations` **EXIT=0** (293 pinned, 12 facts, 23 traversed helpers, **12 self-tests**);
  `check-core-audit` **EXIT=0** (536 required); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` on the CLEAN committed
  tree `6fb3ac16` (no writes during the run) **EXIT=1 on exactly the 5a pair** (`certificate provenance` STALE on `GoLean.lean`;
  the one drift row `imported-goose/channel/google-search PASS/membership → FAIL/membership`), 3821 = 3583/238, 971 s.
  Tails: `docs/evidence/2026-10-03_packet-d/` (`check-equations.txt`, `core-audit-tail.txt`, `ci-diff-tail.txt` replaced by
  this round's).
- POSED: the `.core` rule (definitions of the semantic core are not traversed) is an [AGENT] boundary choice, justified above
  and recorded as a limit; a stricter variant (traverse every core definition that names `stepFn`) was not taken for its cost
  and its false-refusal risk on the compiled recursion structure.

## Merge train r61 — the 5a record ([AGENT] coordinator, 2026-10-03)

[USER] Mike 2026-10-03 «agree on 1-4» (relayed). Pre-merge main `3bb8f4fc` → `refs/snapshots/r61/main`; train tip `44d99cdb`
fast-forwarded (packet D `d8529ab7`, its audit and re-check, the CL1–CL5 corpus disposition, the window review, the rulings and the
`CLAUDE.md` update); fresh primary build (0 foreign references). `release-check` EXIT=2 (EXPECTED — STALE, `build/files/GoLean.lean`);
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` EXIT=1, 1232 s — red on EXACTLY the 5a pair; 3860 rows, 3622 PASS / 238 FAIL =
the pin 3623 / 237 with the one 5a-class row red. Candidate: `claim` and `observations_sha256` IDENTICAL (receipt `44d99cdb`,
157.072 s) — INSTALLED; a provenance refresh. Tail: `docs/evidence/2026-10-03_packet-d/r61-ci-slow.tail.txt`.

**Green re-run at the records commit `5a1c92f1`** ([AGENT] coordinator, 2026-10-03): `ci --diff` EXIT=0, `RESULT: PASS`, baseline diff FULL 3860/3860, certificate provenance ok, semantic equations ok. Round 61 closed: the batched window's build items are all on main.
