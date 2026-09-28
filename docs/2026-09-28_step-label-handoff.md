# Handoff — lane `core/step-label-0928` (window row 2a, the label reshape)

[AGENT worker, lane `core/step-label-0928`] 2026-09-28. Worktree `.claude/worktrees/step-label`, branch
`core/step-label-0928` off `main` @ `84f0a9e4`. Design note: `docs/2026-09-28_step-label.md`. Evidence:
`docs/evidence/2026-09-28_step-label/`. Nothing merged, pushed or committed on `main`; the root `HANDOFF.md` untouched.

## 1. State — BRANCH COMPLETE (first half of the combined candidate «label + execution bridges»)

- `e61b4212` — the reshape (all Lean: core, pool, proofs, packet A's re-statement, BridgeSet re-pin, tracer, tests)
  + the changelog label row (same commit, as the window plan requires for a pinned-statement change).
- The records commit on top (this file, the design note, the evidence dir; two BridgeSet/changelog line-number
  comment fixes — `Step` `:5374`, `Steps` `:6220` — rebuilt green). Its hash is the branch tip (`git log -1`).
- Shape as ruled, NO deviation: `StepLabel := { trace, picks, out }` as `Step`'s fifth index, `stepFn`'s fourth
  component and `StepEvent.label`; pure step `⟨[], [], []⟩`; observation = per-field fold. No design gate hit.

## 2. Gates (every exit captured; box-wide lock held for the full runs)

| Command | Result |
|---|---|
| `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (08:57–09:14 UTC, 1064 s) | EXIT=1, RED ON EXACTLY THE 5a PAIR: `certificate provenance` (STALE — compiled inputs changed) and the baseline line `imported-goose/channel/google-search PASS → FAIL` (its cached certified record judged stale for that reason). 3768 cases = 3531 / 237; NO other row moved; negative baseline 394 matched; eval tests 295 ok; core build warning-free; core audit, unseq scheduler, unseq wire, wire boundary, method identity, frontend pins (raft twin wire byte-identical) all ok. Reconciler: 2 findings, both standing (C9 = the 5a STALE; C13 doc versions). |
| `scripts/capped scripts/check-core-audit` | PASS — 55 required theorems (51 + `StepLabel.fold_silent`, `stepThread_privateStep_label`, `printOut?_toList`, `Choices.consumeAtE_eq`), classical trio only |
| `scripts/capped scripts/check-unseq-scheduler` | PASS |
| `scripts/capped scripts/check-mem-callsites` | PASS, 73 rows (no raw site moved; not edited) |
| whole-corpus choice trace, main's binary vs the lane's | dumps BYTE-IDENTICAL (26 313 records, sha256 `c3f14c50…`); results identical but for one pre-existing ERROR row's artifact path; 0 alarms under the WIDENED cross-check (c) (every step-level site, pool and init phase) |
| raft twin | byte-identical (`check-frontend-pins` inside the gate; frontend and wire schema untouched) |
| escape hatches | no `sorry`/`axiom`/`native_decide`/`partial` added (ci preflight + the audit) |

## 3. The refreshed inputs packet B's brief needs (coordinator: §3 input commit, §4 item 1, line numbers)

INPUT COMMIT: the branch tip (records commit on `e61b4212`). Reshaped signatures (line numbers at the tip):

- `StepLabel` (`Ops.lean:1878`), `StepLabel.fold` (`:1889`), `StepLabel.fold_silent` (`:1895`, PROVED — `silent_projection`
  is a one-liner from it). `PickRecord.ofPick` (`State.lean:478`), `Choices.consumeAtE_eq` (`:482`), `_inv` (`:491`),
  `_le_one` (`:512`), `_of_lt` (`:519`).
- `Step : Config → Store → Config → Store → StepLabel → Prop` (`Machine.lean:5374`); `Steps` (`:6220`) erases labels.
  `deliver … (chain := []) (panicPicks := []) : Config × Store × StepLabel` (`:4148`), `deliver_panic_eq` (`:4173`).
  `seqConsumption` (`:5245`), `repanicCollapseWidth` (`:3211`), `abortConsult` (`:3221`, still `consumeAt`, the
  terminal draw is `Finish`'s), `abortMsg` (`:3926`), `abortLeftover` (`:3937`), `stmtOpOut` (`:4105`),
  `printOut?_toList` (`:4114`), `enterFramePick` (`:901`, `… × Choices × List PickRecord`).
- `stepFn : ProgramCtx → Store → Config → Choices → Except Stop (Config × Store × Choices × StepLabel)`
  (`StepFn.lean:329`); `deliverS` (`:74`), `deliverV` (`:117`, `panicPicks`), `execStmtLoop` (`:1018`), `stepFnIter`
  (`:1048`), `initPrintRefusal?` (`:1131`, RETAINED), `runProgramSetupM` (`:1194`).
- `stepFn_sound` / `step_complete` over `tr : StepLabel` (`MachineSound.lean:1685` / `:2103`);
  `stepFn_consumption_none` (`:5829`), `stepFn_consumption_some` (`:6219`, still with `c.appendTargetLocal`),
  `stepFn_oblivious` (`:6556`), `applyStmtOp_plan_appendSlice_spill` (`:5319`, `NoPanic (g pick)`),
  `applyStmtOp_commit_noPanic` (`:864`); `step_preserves_wf` (`StateWf.lean:8107`, over `MachineWf`).
- Pool: `StepEvent := { who, action, label }` (`Multi.lean:1029`; `ev.picks/out/trace` reducible projections),
  `spawnStep` (`:617`, `… × Choices × List PickRecord × AccessTrace`), `stepThread` (`:1483`), `stepMulti` (`:1659`),
  `execProgLoopOut` (`:1933`), `StepE` (`:2094`, over `StepLabel`), `StepM` (`:2134`, KEEPS `AccessTrace`, `l.trace`).
  `stepFn_selectApply_inv` (`MultiSound.lean:288`, now `… = .ok (c', σ', ch', tr.picks, cl?, tr.trace) ∧ tr.out = []`),
  `stepThread_single` (`:327`), `stepMulti_abort_single` (`:510`), `seqOpCount` (`:640`), `transferable` (`:594`),
  `stepThread_privateStep_label` (`:1707`, the pool projection); `stepThread_stepFn_path` (`MultiStreams.lean:235`).
- `ExecutionStatement.lean`: `Prefix` (`:70`, `List StepLabel`), `Finish` (`:118`, unchanged), `replays` (`:156`, NEW
  signature `List PickRecord → Choices → Choices → Prop`, by record), `replay_coverage_stmt` (`:287`, over `l.picks`),
  `silent_projection_stmt` (`:295`, over `StepLabel.fold`). The boundary `rfl` controls still pass (file builds).
- `BridgeSet.lean`: 34 pins (1, 2, 13, 15, 22 re-pinned; 25–34 added); its diff IS the interface diff.
- Brief text to correct: §4 item 1 «re-state over StepLabel» is DONE for `ExecutionStatement.lean` (B proves; B may still
  refine `replays`' form under its ambiguity policy); §4 item 8's lemma exists (`StepLabel.fold_silent`).

## 4. Flags for packet B / the coordinator (decided nothing beyond the ruled shape)

1. [AGENT] `replay_coverage_stmt` premise-free vs `stepFn_consumption_some`'s `appendTargetLocal`: records are dropped
   on a tape-restoring panic, so coverage at `appendSpill` needs the post-consult tail panic-free — which
   `applyStmtOp_plan_appendSlice_spill` (`NoPanic (g pick)`) and `applyStmtOp_commit_noPanic` state. B's first question.
2. [AGENT] disclosure: the pool event's `picks` now also carry the sequential sites and the spawn's child-entry pick
   (both previously unrecorded in the event); no observation reads them (the tracer's cross-check was widened to match).
3. [AGENT] `StepM`/`StepMFine` keep `AccessTrace` labels — the labelled pool relation is after the window (charter §2).

## 5. PENDING [USER] items

- (11) of the 2026-09-24 rulings: the CLAUDE.md owed-simulation sentence — POSED at the COMBINED candidate's landing
  (after packet B), not by this lane. The merge sign-off and the audit ask are the combined candidate's.
