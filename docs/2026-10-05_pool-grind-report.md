# Pool grind — M1, 2026-10-05

[AGENT Codex, pool grind] M1 proofs complete; acceptance BLOCKED. Stop here; M2 not started.
Proof/integration tip: `16cdd1431a6c76e5416e14c0f0424692c3c1ffea`; the subsequent report commit changes records only.
Input: `72e309c22b0869c142f7f28b628a2dba43a1a939`; branch `core/pool-grind-2026-10-05`; worktree `.claude/worktrees/pool-grind`.
All nine declarations below are in `GoLean/GoCore/PoolSound.lean`, exactly `theorem <name> : <name>_stmt`:

| Theorem | Frozen statement discharged |
|---|---|
| `raceUpdate_error` | `raceUpdate_error_stmt` |
| `stepMulti_error_cases` | `stepMulti_error_cases_stmt` |
| `schedSlot_iff` | `schedSlot_iff_stmt` |
| `stepML_erase` | `stepML_erase_stmt` |
| `stepML_sound` | `stepML_sound_stmt` |
| `stepML_complete` | `stepML_complete_stmt` |
| `stepM_lift` | `stepM_lift_stmt` |
| `stepsML_erase` | `stepsML_erase_stmt` |
| `stepMulti_replay` | `stepMulti_replay_stmt` |

BridgeSet rows 503–511 write out the statements; the core audit requires all nine exports and three new modules.
New proof-only helpers: `PoolErrorFacts.lean`, `PoolReplayFacts.lean`; no helpers added to pre-existing modules, no existing proof changed.
Bounded adjustments: NONE. Frozen definitions, statement bodies, controls and hash lines unchanged; interpreter/scripts/baselines unchanged.
The nine proved Skeleton lines were deleted (39 remain); one additive changelog row records M1.

Acceptance uses `GOLEAN_MEM_MAX=48G`, box-wide lock, `TMPDIR=<worktree>/.tmp`, `LEAN_NUM_THREADS=2`; explicit target builds use the brief's lock exemption.
Evidence: [gate tail](evidence/2026-10-05_pool-grind/m1-ci-tail.log), [core audit](evidence/2026-10-05_pool-grind/m1-core-audit.log), [target builds](evidence/2026-10-05_pool-grind/m1-builds.log), [pool checker](evidence/2026-10-05_pool-grind/m1-pool-spec.log).
`scripts/capped lake build GoLean.GoCore.PoolSound`: EXIT=0, `Build completed successfully (31 jobs).`
`scripts/capped lake build GoLean.GoCore.BridgeSet`: EXIT=0, `Build completed successfully (36 jobs).`
`scripts/capped scripts/ci`: EXIT=1, `RESULT: FAIL`; certificate provenance plus two cached-manifest hash failures; all other summary checks pass, including escape-hatch preflight, warning-free build and 298 eval tests.
`scripts/capped bash scripts/check-core-audit`: EXIT=0, `Core totality audit gate: PASS`; 59 modules / 545 required theorems; all five poison controls rejected.
`python3 scripts/check-pool-spec --statements-only`: EXIT=1; `ok [frozen] both files and 48 statements match docs/specs/pool-relation/FROZEN.sha256`.
`git diff --exit-code <input> --` the frozen files plus `{Multi,MultiSound,PoolTrace,PoolProjection,Prefix,ExecutionStatement}.lean`: EXIT=0, EMPTY; `git diff --check`: EXIT=0, EMPTY.
Final diagnostics below also held the box-wide lock, with `GOLEAN_MEM_MAX=48G` and `LC_ALL=en_US.UTF-8`; combined script EXIT=1 (two known blockers).
`scripts/capped python3 .tmp/m1-locale-check.py`: EXIT=0, `PASS: locale explains both manifest-hash failures; cached results/meta unchanged; no fresh differential run.`
`scripts/capped scripts/coverage-baseline-diff --full`: EXIT=0, `no regression: 3884 case(s) run in latest.tsv match baselines/native-full.tsv`; with `--baseline baselines/negative-full.tsv artifacts/coverage/negative-latest.tsv`: EXIT=0, `no regression: 394 case(s) run in negative-latest.tsv match baselines/negative-full.tsv`.
`scripts/capped python3 tools/certification.py check-records`: EXIT=2, verbatim BLOCKER 2 below; `scripts/capped python3 scripts/check-pool-spec --statements-only`: EXIT=1, same frozen PASS and missing-39 output as above.
`scripts/capped scripts/check-evidence-size`: EXIT=0, `evidence-size gate: PASS`; 2402 tracked files / 32070513 bytes / 151 evidence dirs; 17 pre-existing allowlisted offenders, 0 new (the four new evidence files remain unchanged after this check).
`scripts/capped git diff --exit-code <input> -- <same frozen/existing files above>`, `scripts/capped git diff --check`, `scripts/capped git diff --cached --check`: each EXIT=0, EMPTY.

BLOCKER 1 (verbatim): ``check-pool-spec: FAIL — statements without `theorem <name> : <name>_stmt` in PoolSound.lean:`` (39 names in the linked output).
`scripts/check-pool-spec` uses `--statements-only` only when PoolSound is absent; once present it demands all 48. Brief §§7–8 require staged acceptance, while §6 forbids script edits. No workaround or gate weakening applied; coordinator resolution required.
BLOCKER 2 (verbatim): `certification: STALE certification: changed dependency build/files/GoLean.lean`.
Required imports/new proof sources change the certified build inventory. Brief §6 forbids baseline edits and unrequested differential runs; no record refreshed. Coordinator must resolve the acceptance/boundary conflict. No claim that M1 is mergeable or gate green.
Cached manifest diagnosis: `LC_ALL=en_US.UTF-8` reproduces both recorded hashes; `C.UTF-8` differs only in row order (3884 execution / 394 negative rows). Results/meta were copied unchanged from primary, recorded at `0b072f7d`, go1.26.5, clean; no fresh differential or re-certification performed.
The queued full CI retry was cancelled before acquiring the lock (own waiter PID only, EXIT=143); no second full CI result is claimed.

Still unproved (all deferred to M2–M5, unattempted under the required milestone stop; no residual Lean goal or counterexample asserted):
M2: `stepML_who_runnable_stmt`, `stepML_sched_stmt`, `stepML_switch_boundary_stmt`, `stepML_sched_record_stmt`;
`stepML_frame_stmt`, `stepML_paired_trace_stmt`, `stepML_spawn_stmt`, `asleep_silent_stmt`;
`singleton_deadlock_stmt`, `mainOutcome_not_deadlock_stmt`, `stepMulti_deadlock_elim_stmt`.
M3: `front_continue_stmt`, `front_finish_stmt`, `front_refusal_stmt`, `poolFinish_functional_stmt`, `poolFinish_zero_not_continue_stmt`.
M4: `poolPrefix_comp_stmt`, `poolPrefix_split_stmt`, `poolPrefix_labelled_stmt`, `poolPrefix_erase_stmt`, `poolPrefix_run_stmt`;
`pool_run_ok_iff_stmt`, `pool_run_terminal_iff_stmt`, `pool_run_fuelOut_iff_stmt`, `pool_run_refusal_iff_stmt`, `pool_classification_stmt`;
`run_ok_prefix_stmt`, `continue_replay_stmt`, `poolPrefix_replay_stmt`, `program_prefix_stmt`.
M5: `stepML_single_sound_stmt`, `stepML_single_complete_stmt`, `singleton_prefix_embedding_stmt`;
`singleton_finish_normal_stmt`, `singleton_finish_aborted_stmt`, `singleton_finish_refused_stmt`, `singleton_finish_fatal_stmt`, `singleton_finish_deadlock_stmt`, `singleton_run_stmt`.
No §5 false-statement/unprovability finding surfaced in M1; no material interpretation self-adjudicated.

End state: proved M1 work preserved on the branch; clean after the records commit; primary checkout remains clean on input `main`; nothing merged or pushed.
Audit ask to coordinator (CLAUDE.md, unconditional pre-merge ask; scope/waiver yours): please arrange adversarial review of these nine proofs, helper modules, pins/exports and the two acceptance blockers. No merge sign-off requested.

## M2 — continuous run checkpoint (2026-10-05)

[AGENT Codex, pool grind] Proof tip `74749393ff4f778268e52b892a6db015c91986fc`; new branch `core/pool-grind-m2m5-2026-10-05`, worktree `.claude/worktrees/pool-grind-m2m5`, input `a3e18ff5`.
Authority: [USER] 2026-10-05 continuous-run instruction and amended brief; checkpoints commit and continue, no intermediate review pause.
All eleven frozen statements below are discharged in `PoolSound.lean`:
- `stepML_who_runnable` : `stepML_who_runnable_stmt`.
- `stepML_sched` : `stepML_sched_stmt`.
- `stepML_switch_boundary` : `stepML_switch_boundary_stmt`.
- `stepML_sched_record` : `stepML_sched_record_stmt`.
- `stepML_frame` : `stepML_frame_stmt`.
- `stepML_paired_trace` : `stepML_paired_trace_stmt`.
- `stepML_spawn` : `stepML_spawn_stmt`.
- `asleep_silent` : `asleep_silent_stmt`.
- `singleton_deadlock` : `singleton_deadlock_stmt`.
- `mainOutcome_not_deadlock` : `mainOutcome_not_deadlock_stmt`.
- `stepMulti_deadlock_elim` : `stepMulti_deadlock_elim_stmt`.

BridgeSet rows 528–538; rows 1–527 byte-identical. All eleven exports added; `PoolStructure` enrolled in default imports and the audit.
Helpers in the pre-existing `PoolSound`: private `stepML_slot`. New module helpers: `PoolStructure.applyPairing_shape`, `applyPairing_trace`.
No bounded adjustment, frozen hash change, existing `MultiSound`/`PoolProjection` edit, or repair. Runtime and scripts unchanged.
All following gates ran under the box-wide lock with `GOLEAN_MEM_MAX=48G`, `LC_ALL=en_US.UTF-8`, `LEAN_NUM_THREADS=2`, worktree-local TMPDIR.
`scripts/capped scripts/ci`: EXIT=1, `RESULT: FAIL`; the ONLY non-ok summary step is certificate provenance (expected by the amended brief).
Verbatim cause: `certification: STALE certification: changed dependency build/files/GoLean.lean`. No re-certification, baseline edit, or fresh differential run.
`scripts/capped bash scripts/check-core-audit`: EXIT=0, `Core totality audit gate: PASS`; 62 modules / 572 required theorems / five poison controls rejected.
`scripts/capped python3 scripts/check-pool-spec --landed M2`: EXIT=0; all 20 M1–M2 statements discharged; frozen files and all 48 hashes match; 28 later statements owed.
`scripts/capped lake build GoLean.GoCore.BridgeSet`: EXIT=0, `Build completed successfully (40 jobs).`; earlier PoolSound target EXIT=0 (33 jobs).
`scripts/capped python3 .tmp/check-frozen.py`: EXIT=0; frozen files, existing modules, LANDED/MILESTONES and rows 1–527 byte-identical to input; `git diff --check`: EXIT=0, EMPTY.
Escape-hatch preflight and warning-free build PASS within CI; 298 eval tests pass. Cached comparisons: 3884 execution and 394 negative cases match; records from clean `ab047d0` at go1.26.5, no fresh run.
[CI tail](evidence/2026-10-05_pool-grind/m2-ci-tail.log) · [audit tail](evidence/2026-10-05_pool-grind/m2-audit-tail.log) · [pool checker](evidence/2026-10-05_pool-grind/m2-pool-spec.log) · [exit ledger / checks](evidence/2026-10-05_pool-grind/m2-checks.log).
[AGENT] Record correction: `0827161d` prematurely claimed an evidence-size PASS while that extra check was still queued (not reading this tree); its own waiter was cancelled (EXIT=143). The new evidence awaits the locked check; CI’s earlier evidence-size step passed before these four logs were staged.
[AGENT] Correction resolved 2026-10-05 23:19 UTC: the queued capped, locked `scripts/check-evidence-size` completed EXIT=0 on the four staged M2 logs: 2411 tracked files / 32100991 bytes, 0 new offenders. Actual output retained in `m2-checks.log`.

Still owed at this checkpoint (not attempted yet; no residual goal or counterexample claimed):
M3: `front_continue_stmt`, `front_finish_stmt`, `front_refusal_stmt`, `poolFinish_functional_stmt`.
`poolFinish_zero_not_continue_stmt`.
M4: `poolPrefix_comp_stmt`, `poolPrefix_split_stmt`, `poolPrefix_labelled_stmt`, `poolPrefix_erase_stmt`.
`poolPrefix_run_stmt`, `pool_run_ok_iff_stmt`, `pool_run_terminal_iff_stmt`, `pool_run_fuelOut_iff_stmt`.
`pool_run_refusal_iff_stmt`, `pool_classification_stmt`, `run_ok_prefix_stmt`, `program_prefix_stmt`.
`continue_replay_stmt`, `poolPrefix_replay_stmt`.
M5: `stepML_single_sound_stmt`, `stepML_single_complete_stmt`, `singleton_finish_normal_stmt`, `singleton_finish_aborted_stmt`.
`singleton_finish_refused_stmt`, `singleton_finish_fatal_stmt`, `singleton_finish_deadlock_stmt`, `singleton_prefix_embedding_stmt`.
`singleton_run_stmt`.
M2 complete; acceptance differs from green only by the authorized stale-certificate red. Continue to M3; no review ask, merge or push.

## M3 checkpoint — driver carriers, 2026-10-05

[AGENT Codex, pool grind] Continuous M2–M5 authority; input `a3e18ff5`, branch `core/pool-grind-m2m5-2026-10-05`.
Proof/integration commit: `4b5f0ba884053bb9b51d9be8664efb2f19ba3931`; this checkpoint's subsequent record commit changes documentation only.
Five exact frozen declarations proved in `PoolSound.lean`: `front_continue`, `front_finish`, `front_refusal`, `poolFinish_functional`, `poolFinish_zero_not_continue`.
BridgeSet rows 539–543 added; all old rows retained. Five exports added, `PoolFrontFacts` enrolled in default imports and the audit.
New module helpers characterize the front's continue/normal/aborted/deadlock/refusal cases, with raw-choice iff lemmas.
Finish uniqueness is an exhaustive constructor proof; local development required explicit exit-window records and replacing an unsuccessful repeated tactic search.
No counterexample, residual goal, repair, bounded statement adjustment, frozen hash change, or existing proof-module edit.
All acceptance ran under the box-wide lock, capped at 48G, locale `en_US.UTF-8`, two Lean threads, worktree-local TMPDIR.
`scripts/capped scripts/ci`: EXIT=1, `RESULT: FAIL`; ONLY failing summary step: certificate provenance.
Verbatim expected cause: `certification: STALE certification: changed dependency build/files/GoLean.lean`.
`scripts/capped bash scripts/check-core-audit`: EXIT=0; PASS, 63 modules / 54 core modules / 577 required theorems / 20701 declarations, classical trio only; five poison controls rejected.
`scripts/capped python3 scripts/check-pool-spec --landed M3`: EXIT=0; all 25 M1–M3 statements discharged, 0 early, 23 owed; both frozen files and all 48 statement hashes match.
`scripts/capped lake build GoLean.GoCore.BridgeSet`: EXIT=0, 41 jobs; pre-checkpoint target build also EXIT=0; PoolSound target EXIT=0, 34 jobs.
`scripts/capped python3 .tmp/check-frozen.py`: EXIT=0; frozen files, existing modules, LANDED/MILESTONES and BridgeSet rows 1–527 byte-identical to input.
`git diff --check`: EXIT=0, EMPTY. CI escape-hatch scans and warning-free build pass; 298 eval tests pass.
Cached comparison only: 3884 execution and 394 negative cases match, records from clean `ab047d0` / go1.26.5; no fresh differential or certification refresh.
[CI tail](evidence/2026-10-05_pool-grind/m3-ci-tail.log) · [audit tail](evidence/2026-10-05_pool-grind/m3-audit-tail.log) · [pool checker](evidence/2026-10-05_pool-grind/m3-pool-spec.log) · [exit ledger](evidence/2026-10-05_pool-grind/m3-checks.log).
Still owed (M4/M5 drafts are unverified scratch, no obstruction claimed):
M4: `poolPrefix_comp_stmt`, `poolPrefix_split_stmt`, `poolPrefix_labelled_stmt`, `poolPrefix_erase_stmt`, `poolPrefix_run_stmt`.
`pool_run_ok_iff_stmt`, `pool_run_terminal_iff_stmt`, `pool_run_fuelOut_iff_stmt`, `pool_run_refusal_iff_stmt`, `pool_classification_stmt`.
`run_ok_prefix_stmt`, `program_prefix_stmt`, `continue_replay_stmt`, `poolPrefix_replay_stmt`.
M5: `stepML_single_sound_stmt`, `stepML_single_complete_stmt`, `singleton_finish_normal_stmt`, `singleton_finish_aborted_stmt`.
`singleton_finish_refused_stmt`, `singleton_finish_fatal_stmt`, `singleton_finish_deadlock_stmt`, `singleton_prefix_embedding_stmt`, `singleton_run_stmt`.
M3 complete; acceptance differs from green only by the authorized stale-certificate failure. Continue without review, merge or push.
New M3 evidence is staged; its extra size check was cancelled while waiting for another lane (EXIT=143, never read this tree) and is requeued before M4’s first compiler pass. No size PASS for those new logs is claimed yet.
[AGENT] M3 evidence-size resolution, 2026-10-05 23:54 UTC: the capped, locked check completed EXIT=0 on the four new M3 logs: 2415 tracked files / 32110168 bytes, 0 new offenders. Actual output retained in `m3-checks.log`.

## M4 checkpoint — run lifts, 2026-10-05–06

[AGENT Codex, pool grind] Continuous-run authority; same input, branch and worktree as M2–M3.
Proof/integration commit: `4cefee19b7dc998bcd6063847435460c1446d0c6`; acceptance completed 2026-10-06 UTC.
Fourteen exact frozen declarations proved:
`poolPrefix_comp`, `poolPrefix_split`, `poolPrefix_labelled`, `poolPrefix_erase`, `poolPrefix_run`.
`pool_run_ok_iff`, `pool_run_terminal_iff`, `pool_run_fuelOut_iff`, `pool_run_refusal_iff`, `pool_classification`.
`run_ok_prefix`, `program_prefix`, `continue_replay`, `poolPrefix_replay`.
BridgeSet rows 544–557 and fourteen audit exports added; no new module. Previous rows retained byte-for-byte.
Private helpers in `PoolSound`: `poolOut_cons`, `front_error_cases`, the proof carrier `RunEvidence`, `run_evidence`, `finish_normal_run`, `finish_terminal_run`.
The finite driver trace yields each exact ending witness; prefix execution supplies the converses, preserving output, detector state, tapes and finishing cost.
All development goals discharged. No counterexample, repair, bounded adjustment, frozen hash change, or edit to an existing proof module outside `PoolSound`.
Every acceptance command capped at 48G under the box-wide lock, locale `en_US.UTF-8`, two Lean threads, worktree-local TMPDIR.
`scripts/capped scripts/ci`: EXIT=1, `RESULT: FAIL`; ONLY failing summary step is certificate provenance.
Verbatim expected cause: `certification: STALE certification: changed dependency build/files/GoLean.lean`.
`scripts/capped bash scripts/check-core-audit`: EXIT=0; PASS, 63 modules / 54 core / 591 required theorems / 20756 declarations, classical trio only; five poison controls rejected.
`scripts/capped python3 scripts/check-pool-spec --landed M4`: EXIT=0; 39 M1–M4 statements discharged, 0 early, 9 owed; all frozen files and 48 statement hashes match.
`scripts/capped lake build GoLean.GoCore.BridgeSet`: EXIT=0, 41 jobs; the integrated pre-checkpoint PoolSound/BridgeSet build also EXIT=0.
`scripts/capped python3 .tmp/check-frozen.py`: EXIT=0; frozen surface, existing modules, LANDED/MILESTONES and rows 1–527 byte-identical to input.
`git diff --check`: EXIT=0, EMPTY. CI escape-hatch scans and warning-free build pass; 298 eval tests pass.
Cached comparisons only: 3884 execution / 394 negative cases match; clean `ab047d0` records, go1.26.5. No fresh differential or certification refresh.
[CI tail](evidence/2026-10-05_pool-grind/m4-ci-tail.log) · [audit tail](evidence/2026-10-05_pool-grind/m4-audit-tail.log) · [pool checker](evidence/2026-10-05_pool-grind/m4-pool-spec.log) · [exit ledger](evidence/2026-10-05_pool-grind/m4-checks.log).
An optional interactive-terminal request failed with `failed to openpty` / `Permission denied`; `nono why --path /dev/ptmx --op write` reported `path_not_granted`.
No permission or profile change: ordinary capped commands worked and the run continued. The M3 evidence-size timestamp above is corrected to its log's actual 23:54 UTC minute.
Still owed at this checkpoint: M5 `stepML_single_sound_stmt`, `stepML_single_complete_stmt`, `singleton_finish_normal_stmt`.
`singleton_finish_aborted_stmt`, `singleton_finish_refused_stmt`, `singleton_finish_fatal_stmt`, `singleton_finish_deadlock_stmt`.
`singleton_prefix_embedding_stmt`, `singleton_run_stmt`. No obstruction claimed; M5's first compiler pass follows.
M4 complete; only the authorized stale-certificate red remains in acceptance. Continue without review, merge or push.
M4 staged evidence-size check: capped and locked, EXIT=0; 2419 tracked files / 32118971 bytes in 154 evidence directories, 0 new offenders.
