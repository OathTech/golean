# The pool/registry half — the GRIND BRIEF (draft; launchable only after the design gate)

STATUS: **DRAFT — NOT LAUNCHED.** The spec packet it drives is a NAMED DESIGN GATE awaiting [USER] review
(`docs/2026-10-04_pool-relation-spec.md` §8). Authority for the shape: [USER] Mike 2026-10-04 «Great, launch it»
(relayed) — a Fable spec packet, then a Codex grind «with enough flex it could build successfully, without giving
too much space for drift». Written by the [AGENT] design worker; the coordinator refreshes §2 (the input commit)
and deletes this paragraph at launch. Provenance in the grind's commits: **[AGENT Codex, pool grind]**.
**Ambiguity policy: if two readings of this brief differ materially, STOP, write both in the report, do not choose.**

## 1. Purpose
Prove every `<name>_stmt` of `GoLean/GoCore/PoolStatement.lean` — 45 statements — as `theorem <name> : <name>_stmt`
in a new `GoLean/GoCore/PoolSound.lean`, the statements UNCHANGED; pin them in `BridgeSet.lean`; extend the core
audit's required list; land milestone by milestone. The design note is the specification; this brief is its fence.

## 2. Setup
`git -C /home/dev/projects/golean worktree add .claude/worktrees/pool-grind -b core/pool-grind-<date> <INPUT COMMIT — the
spec packet's landed tip, refreshed by the coordinator>`. Seed the Lean cache from the primary checkout at the same commit
(`cp -a .lake <worktree>/.lake`). Scratch under the worktree's `.tmp/` only (never `/tmp`); every build through
`scripts/capped` with an explicit `GOLEAN_MEM_MAX` (≤ 48G for explicit targets); the box-wide lock
(`mkdir /home/dev/projects/golean/artifacts/build-lock.d` + `owner` file; wait-retry; never take over; release under a
trap) for every full build or gate; `rm` only with `"${var:?}"`; never kill by pattern (own PIDs only); one writer.

## 3. Inputs (read; edit only what §6 allows)
`GoLean/GoCore/PoolStep.lean` (the FROZEN definitions: `MultiConfig.schedMenu?`, `SchedSlot`, `schedRecord`,
`selectAction`, `StepML`, `StepsML`, `PoolDeadlock`, `Continue`, `DriverEvent`, `PoolPrefix`, `PoolOutcome`,
`PoolOutcome.terminal?`, `PoolFinish`); `GoLean/GoCore/PoolStatement.lean` (the FROZEN statements; `poolOut`,
`DriverEvent.events`, `PoolClass*`, the controls); `docs/specs/pool-relation/Skeleton.lean` (the names, in the
suggested order; never imported); `docs/specs/pool-relation/FROZEN.sha256` + `scripts/check-pool-spec`.
The existing kit: `Multi.lean` (`stepThread`, `stepMulti`, `StepM`, `schedPick`, `schedSlots`, `arrivalPlan`,
`applyPairing`, `spawnStep`, `resumeThread`, `execProgLoop(Out)`, `raceUpdate`), `MultiSound.lean` (`stepMulti_sound`,
`stepM_complete`, `stepThreadInto_sound`, `stepMulti_of_inner`, `stepMulti_single`, `stepMulti_flagged_single`,
`stepMulti_abort_single`, `stepThread_privateStep_label`, `stepFn_selectApply_inv`, `arrivalPlan_of_*`,
`arrivalCases_multi_length`, `schedSlots_mem`, `mem_schedSlots_of_runnable`, `schedPick_of_boundary`, `schedPick_cur`,
`spawnStep_shape`, `step_spawnPos_elim`, `abort?_none_of_stepE`, `push_eq_append_running`, `raceUpdate_single`,
`singleton_pool_facts`, `runnableIdxs_singleton`, `schedSlots_singleton`), `MachineSound.lean` (`stepFn_sound`,
`step_complete`, `step_terminal_elim`, `step_abort_elim`, `step_blocked*_elim`), `Prefix.lean` (`stepFn_no_stray_panic`,
`stepFn_error_cases`, `finish_aborted_stepFn`, `finish_aborted_of_stepFn`, `abortLeftover_eq*`, `execStmtLoop_error`,
`Prefix.run_eq`), `PoolTrace.lean` (`front`, `unfold_driver`, `Run`, `run_iff`, `PoolSteps`), `PoolProjection.lean`
(`front_single_step/_flagged/_terminal/_aborted`, `stepThread_single_out`, `stepMulti_single_out`,
`execProgLoopOut_single_wide`, `isTerminal_false_of_stepFn_ok`, `isBlockedConfig_false_of_stepFn_ok`, `outFold_*`),
`State.lean` (`Choices.consumeAtE_eq/_inv/_le_one/_of_lt`, `consumeAt_fst_lt/_fst_singleton`, `PickRecord.ofPick`),
`Machine.lean` (`deliver_ok/_panic`, `toResult_*`, `Config.abort?_some_iff`), `Race.lean` (`RaceState.events/event/accessKey`),
`NPDRF.lean` (`threadDone_atBoundary`, `isBlockedConfig_atBoundary`), `Tests/GoCoreAudit.lean` (`requiredModules`, `exports`).

## 4. The FROZEN surface (`scripts/check-pool-spec` guards it; a drift FAILS by name)
Every definition of `PoolStep.lean` and every `_stmt` body of `PoolStatement.lean`, byte-for-byte up to comments and
whitespace (`docs/specs/pool-relation/FROZEN.sha256`). Also frozen: the interpreter (`stepFn`, `stepThread`, `stepMulti`,
the drivers, `Choices.*`, every helper) and every statement already pinned in `BridgeSet.lean` (rows 1–502).

## 5. The zones
**FREE** — anything that proves the frozen statements without touching them: helper lemmas (private or public) in
`PoolSound.lean` or in NEW proof-only modules it imports; restructuring the proof of an EXISTING theorem of
`MultiSound.lean`/`PoolProjection.lean` provided its statement is byte-identical and `BridgeSet.lean` still compiles;
tactics/macros local to the proof modules; `#eval`-checked `example` controls; the proof order.
**BOUNDED** — permitted statement adjustments, EACH re-frozen (`scripts/check-pool-spec --freeze`) with a written reason
in the report naming the hash line, and ONLY these: (i) adding to a `_stmt` a premise that is PROVED (in the same
landing) to follow from the statement's other premises — never a new free assumption; (ii) weakening a universal
binder's type annotation to a definitionally equal one; (iii) renaming a bound variable; (iv) splitting one `_stmt`
into a conjunction of two `_stmt`s whose conjunction is syntactically the original (the Skeleton gains a line per
part). NOTHING ELSE — in particular no change to a conclusion, no dropped conjunct, no new `∃`, no `transferable`-style
class narrowing, no premise «`m.threads.size ≤ 1`», no `NoRefusal`-style domain premise.
**HARD STOP** — a statement found FALSE or unprovable as written: STOP, write the counterexample (a concrete pool,
tape and the two sides evaluated by `#eval`) or the obstruction (the goal state, the missing lemma, why it does not
hold), in the report; commit what is proved; do NOT weaken the statement, do NOT patch the interpreter, do NOT touch the
frozen definitions. Two statements are flagged as the likeliest to surface a FINDING rather than a proof gap:
`stepMulti_error_cases_stmt` (a pool-level stray `panic` would be a fidelity bug — the pool twin of packet A's audit F1)
and `stepML_frame_stmt` (an `applyPairing` arm writing a third goroutine). A finding is REPORTED, never absorbed.

## 6. Boundaries — what NOT to do
Edit ONLY: the new `GoLean/GoCore/PoolSound.lean` (and new proof-only modules under `GoLean/GoCore/` that it imports),
`GoLean.lean`'s import list (enroll the new modules), `GoLean/GoCore/BridgeSet.lean` (ADD rows only), `Tests/GoCoreAudit.lean`
(`requiredModules`/`exports` — ADD only), `docs/changelog/61958f2e-WINDOW.md` (one row per milestone), your evidence dir
(`docs/evidence/<date>_pool-grind/`, ≤ 256 KiB per file) and your report. NO change to `PoolStep.lean`, to a `_stmt`
outside §5's bounded list, to `stepFn`/`stepThread`/`stepMulti`/the drivers/`Choices.*`/any helper, to any rule of `Step`,
`StepE`, `StepM`, to the frontend, decoder, `Corpus/`, `baselines/`, `scripts/` (except `check-pool-spec`'s re-freeze
output), `tools/`, `CLAUDE.md`, the root `HANDOFF.md`. Totality: no `sorry`/`axiom`/`native_decide`/`partial`/`admit`
(`scripts/ci`'s scans and the core audit police it). No gate weakening. No `/tmp`. No uncapped build. Never take over a
lock. Never edit while a gate reads the tree. No push, merge, tag or rebase onto a moved `main`. Do not run the
differential unless the coordinator asks (nothing here changes runtime behaviour).

## 7. Proof order — five milestones, each mergeable alone (its theorems depend only on earlier ones)
M1 **step correspondence + error classes** — `raceUpdate_error`, `stepMulti_error_cases` (FIRST: it decides whether
the classification theorems are provable as stated), `schedSlot_iff`, `stepML_erase`, `stepMulti_sound` (the existing
`stepMulti_sound`/`stepThreadInto_sound` case tree, with label equalities — reuse `stepThread_privateStep_label`,
`stepFn_selectApply_inv`, `spawnStep_shape`, `arrivalPlan_of_*`, `consumeAtE_eq`), `stepML_complete` (the existing
`stepM_complete`/`stepMulti_of_inner` route, the sched slot realized by `slot :: ch` at bound ≥ 2), `stepM_lift`, `stepsML_erase`.
M2 **attribution, boundaries, deadlock** — `stepML_who_runnable`, `stepML_sched`, `stepML_switch_boundary`,
`stepML_sched_record`, `stepML_frame` (an `applyPairing_frame` helper: the arms' two `setIfInBounds`), `stepML_paired_trace`,
`stepML_spawn`, `asleep_silent`, `singleton_deadlock`, `mainOutcome_not_deadlock`, `stepMulti_deadlock_elim`.
M3 **the driver carriers** — `front_continue`, `front_finish`, `front_refusal`, `poolFinish_functional`, `poolFinish_zero_not_continue`.
M4 **the run lifts + the program seam** — `poolPrefix_comp`, `poolPrefix_split`, `poolPrefix_labelled`, `poolPrefix_erase`,
`poolPrefix_run` (induction with `unfold_driver`), the pool twin of `execStmtLoop_error` as a helper, then `pool_run_ok_iff`,
`pool_run_terminal_iff`, `pool_run_fuelOut_iff`, `pool_run_refusal_iff`, `pool_classification`, `run_ok_prefix`, `program_prefix`.
M5 **the single-goroutine reduction** — `stepML_single_sound`, `stepML_single_complete`, `singleton_finish_normal/_aborted/
_refused/_fatal/_deadlock`, `singleton_prefix_embedding` (mirror `execProgLoopOut_single_wide`'s induction), `singleton_run`.
Each milestone ends with: `scripts/check-pool-spec` (statements intact; discharged so far listed — until M5 lands, run it
with `--statements-only` AND report the undischarged names explicitly), the Skeleton's lines for the proved names deleted
(the Skeleton shrinks to what is still owed; at M5 it is deleted), BridgeSet rows added (`example : <stmt written out>
:= @GoLean.GoCore.PoolSound.<name>`), `exports` extended, a changelog row, and the gate below.

## 8. Acceptance (per milestone; capped; locked; every EXIT code recorded)
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci` green (no `--diff`: no runtime change; the coordinator may ask for it);
`scripts/capped bash scripts/check-core-audit` PASS with the new modules in the closure and the milestone's theorems in
`exports`; `python3 scripts/check-pool-spec` (M5) / `--statements-only` (M1–M4) exit 0; the escape-hatch preflight clean;
`BridgeSet.lean` compiles with the new rows; `git diff --stat <input> -- GoLean/GoCore/PoolStep.lean` EMPTY and
`FROZEN.sha256` unchanged unless a §5 bounded adjustment is reported line by line; no existing theorem's statement changed
(`git diff <input> -- GoLean/GoCore/{Multi,MultiSound,PoolTrace,PoolProjection,Prefix,ExecutionStatement}.lean` shows
proof bodies only, if anything). Evidence: gate tails and the `check-pool-spec` output per milestone.

## 9. Report — `docs/<date>_pool-grind-report.md` (≤ 60 lines per milestone)
Tip commit; the theorems proved with the `_stmt` each discharges; every bounded-zone adjustment with its hash line and
reason; every helper lemma added to a pre-existing module; every acceptance command with EXIT code + tail; every
`[AGENT Codex, pool grind] INTERPRETED: …` (flagged, not decided); every statement left unproved with the obstacle
VERBATIM (the goal state), and every FINDING (§5 HARD STOP) with its witness. End state: branch complete, clean, nothing
merged or pushed; the audit ask posed to the coordinator. Commit message shape: `[AGENT Codex, pool grind] M<k>: <names>;
BridgeSet rows <a–b>; exports extended` with the repo's attribution trailer.
