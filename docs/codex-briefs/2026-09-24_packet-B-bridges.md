# Codex packet B — the BRIDGES (prefix closure, terminal transition, fuel, replay coverage, refusal-separate correspondence)

STATUS: **DRAFT — launchable after the label reshape (charter row 2, first half) lands on its LANE TIP; the coordinator REFRESHES §3 (the
input commit), §4 item 1 (the reshaped signatures) and the line numbers, then deletes this sentence.** [AGENT] planning writer 2026-09-24.
Ruling: decision 6 (ledger 2026-09-24), executed as an Opus 5.5 subagent dispatched by the coordinator ([USER] 2026-09-27, ledger «E6's
shape, train r49 and the execution model»). Executes charter row 2 (second half), §2 and §3; plan `docs/2026-09-24_window-plan.md` row 2b.
Provenance: **[AGENT packet B worker]**.
Packets A and B share names: A STATES (`GoLean/GoCore/ExecutionStatement.lean`, every `<name>_stmt : Prop`), B PROVES (`theorem <name> : <name>_stmt`).
**Ambiguity policy: if two readings of this brief differ materially, STOP, write both in the report, do not choose.**

## 1. Purpose
Prove every `_stmt` of `ExecutionStatement.lean`, re-stated over the RESHAPED `Step`/`stepFn` whose label is `StepLabel := { trace : AccessTrace,
picks : List PickRecord, out : List GoString }`, as theorems in the core; re-pin `BridgeSet.lean`; complete the changelog's label row. ONE
combined candidate with the reshape (response §Recommendation: «dependent changes need a combined candidate») — the coordinator merges both.

## 2. Setup
`git -C /home/dev/projects/golean worktree add .claude/worktrees/codex-packet-b -b codex/packet-b-bridges-<date> <RESHAPE TIP — refreshed>`.
Scratch under the worktree's `.tmp/` only; every build/gate through `scripts/capped`; the box-wide lock for any full build or gate
(`mkdir /home/dev/projects/golean/artifacts/build-lock.d` + `owner` file; wait-retry 120 s; never take over; release under a trap); one writer.

## 3. Inputs (REFRESHED by the coordinator at launch; read, edit only what §6 allows)
The reshape tip `<commit>`; `GoLean/GoCore/ExecutionStatement.lean` and `BridgeSet.lean` (packet A, as re-pinned by the reshape lane);
`Trace.lean` (`Trace`, `iter_iff_trace`, `Trace.erase`, `run_ok_iff`), `ProgramTrace.lean` (`ProgramRun`, `program_run_iff`, `Observation`,
`observation_iff`), `MultiSound.lean` (`execProgLoop_single`, `seqOpCount`, `transferable`), `MachineSound.lean` (`stepFn_sound`,
`step_complete`, `stepFn_consumption_none`, `stepFn_consumption_some`), `State.lean` (`Choices.consume`, `Choices.consumeAt`,
`Choices.consumeAtE` + `consumeAtE_fst_snd`/`_le_one`/`_of_lt`, `PickRecord`), `Machine.lean` (`Config.abort?`, `abortConsult`, `abortMsg`,
`abortLeftover`, `repanicCollapseWidth`, `seqConsumption`, `Steps`, `Step`), `StepFn.lean` (`stepFn`, `execStmtLoop`, `stepFnIter`,
`initPrintRefusal?`, `runProgramSetupM`), `Multi.lean` (`StepEvent`, `execProgLoop`, `execProgLoopOut`, `execProgLoopOut_snd`,
`runProgramPoolOutM`), `StateWf.lean` (`StateWf`, `step_preserves_wf`); the review witness `docs/evidence/2026-09-23_batched-window-review/FuelBoundary.lean`;
charter §2 (the specification), response §2 (the five corrections), `docs/2026-09-24_execution-statement.md` (packet A's note).

## 4. Deliverables — Lean, in a new `GoLean/GoCore/Prefix.lean` (imported by `ExecutionStatement.lean`; reachable from `GoLean.lean`)
1. RE-STATE over `StepLabel`: `Prefix` (labels `List StepLabel`), `ZeroCost`, `Blocked`, `FinishOutcome`, `Finish` (its records = the terminal
   draw's `PickRecord`s), `LRun`, `replays` (now by the label's `picks`: `∀ ch₂, <the recorded picks replay on ch₂> → …`), `NoRefusal`. Keep
   every `_stmt` name; each becomes a `theorem <name> : <name>_stmt`. The old `AccessTrace`-labelled forms are deleted, not kept as aliases.
2. `prefix_refl`, `prefix_comp`, `prefix_split`, `prefix_erase_steps` (via `stepFn_sound`), `prefix_erase_trace`, `prefix_iter` (the labelled
   analogue of `iter_iff_trace`) — for every `n`, INDEPENDENT of termination (response §2 (3): earlier labels survive fuel-out and divergence).
3. `finish_abort_step`: `Finish.aborted` ↔ the abort arm of `stepFn` at `.panicking chain .stop` — `abortConsult` = `Choices.consumeAt
   .repanicCollapse (repanicCollapseWidth first rest)`, then `abortMsg` (response §2 (2)); `finish_refused_step` for the renderer refusal;
   `abortLeftover_eq`: `abortLeftover c ch` is `Finish`'s residual tape.
4. The fuel bridges with `ZeroCost` (F2; convention KEPT): `run_ok_iff` (labelled; the pinned `Semantics.run_ok_iff` stays and is derived
   from it), `run_panic_iff` (`n + 1 ≤ fuel`, cost 1), `run_deadlock_iff`, `run_fuelOut_iff` (`Prefix fuel … ∧ ¬ ZeroCost cf`). CONTROLS as
   `example`s in `Prefix.lean`: `abort? = some _` → `execStmtLoop ctx 0 … = .error .fuelOut` and `execStmtLoop ctx 1 … = .error (.terminal (.panic _))`;
   `.next .stop` at 0 → `.ok`; a blocked form at 0 → `.error (.terminal .deadlock)`; a renderer refusal at 1 → `.error (.refusal _)`, at 0 → `.fuelOut`.
5. `replay_coverage` (response §2 (4)): `stepFn ctx s c ch = .ok (c', s', ch', l) → ∀ ch₂ ch₂', replays … l.picks … → stepFn ctx s c ch₂ = .ok (c', s', ch₂', l)`,
   covering: bound ≤ 1 → no record and no pop (`consumeAtE_le_one`); empty tape → pick 0 (`Choices.consume`); modulo selection (`% max 1 bound`);
   the terminal draw (via `finish_abort_step`). If the proof needs `c.appendTargetLocal` (as `stepFn_consumption_some` does today) PROVE that
   premise from the reshape's invariant or `StateWf`, or STOP and report — never add it to the statement silently. Plus `stepFn_sound` /
   `step_complete` relabelled (fixed-tape soundness/completeness) and the witness direction (`step_complete`'s `∃ ch ch'`).
6. `classification` (unconditional; the four cases DISJOINT, refusal reported — response §2 (5)), then `classification_wf` under
   `StateWf ctx s ∧ NoRefusal ctx s c`; `NoRefusal`'s one-step preservation where `step_preserves_wf` gives it. Fragment domain facts stay theirs.
7. `single_embedding` over `StepLabel`: `execProgLoop_single` restated, the cost relation `seqOpCount` PROVED (never «equal fuel»); the pool's
   `StepEvent := { who, action, label }` fold agrees with the sequential labels' fold (`execProgLoopOut_snd` relabelled).
8. `silent_projection`: `⟨[], [], []⟩` contributes `[]` to each channel's fold; no `[emptyLabel]` element appears where today there is none.
9. `program_bridge`: setup premise `runProgramSetupM … = .ok (pctx, c₀, s₀, locs, ch₁)` (tape `ch → ch₁` INCLUDED), readout `loadMany`,
   output = the `out` fold; init output empty BY REFUSAL (`initPrintRefusal?` RETAINED — decision 10, do not lift). `ProgramRun`,
   `program_run_iff`, `observation_iff` restated over the label and re-proved under their pinned names.
10. `BridgeSet.lean`: every new theorem pinned (`example : <type> := @<name>`); every changed statement re-pinned. `docs/changelog/61958f2e-WINDOW.md`:
    the label row COMPLETED (before/after for `Step`, `stepFn`, `StepEvent`, `Trace.step`, `stepFn_sound`/`step_complete`, the bridges).

## 5. Acceptance (capped; locked; every EXIT code recorded)
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` green — a moved baseline row is the RESHAPE lane's finding: STOP and report, do not
re-pin; `scripts/capped scripts/check-core-audit` PASS (the harness now imports `Prefix.lean`); the escape-hatch preflight clean; every `_stmt`
has its theorem (`git grep -c "_stmt" GoLean/GoCore/ExecutionStatement.lean` equals the theorem count in `Prefix.lean` — record both);
`python3 tools/reconcile-records` findings reported. Evidence `docs/evidence/<date>_packet-b/` (README per `docs/evidence/README.md` + gate
tails, ≤ 256 KiB). The expected `certificate provenance` red of the fast steps is the train's 5a business, not yours.

## 6. Boundaries — what NOT to do
Edit ONLY `GoLean/GoCore/{ExecutionStatement,BridgeSet,Trace,ProgramTrace,MultiSound}.lean`, the new `Prefix.lean`, `GoLean.lean`'s imports,
the changelog, your evidence dir and report. NO change to `stepFn`, `Step`, any rule, `Config`, `Cont`, `StepLabel`, `StepEvent`, the
drivers, `Choices.*`, the frontend, the decoder, `Corpus/`, `baselines/`, `scripts/`, `tools/`, `CLAUDE.md`, the root `HANDOFF.md`.
**If a statement is unprovable as written, STOP and report — do not alter the semantics, the statement or its premises to make it
provable.** Totality doctrine: no `sorry`/`axiom`/`native_decide`/`partial`/`admit`. No gate weakening. No `/tmp`. No uncapped build. Never
take over a lock. Never kill by pattern (own PIDs only). Never edit while a gate reads the tree. No push, merge, tag or rebase onto a moved `main`.

## 7. Report — `docs/<date>_packet-B-report.md` (≤ 60 lines)
Tip commit; the theorem list with the `_stmt` each discharges; the premises each proof ACTUALLY needed (the `appendTargetLocal` question
answered explicitly); every acceptance command with EXIT code + tail; every `[AGENT Codex, packet B] INTERPRETED: …` (flagged, not decided);
every statement left unproved with the obstacle verbatim (the goal state). End state: branch complete, clean, nothing merged or pushed.
Commit: `[AGENT Codex, packet B] bridges: Prefix/Finish proved over StepLabel; BridgeSet re-pinned; changelog label row`.
