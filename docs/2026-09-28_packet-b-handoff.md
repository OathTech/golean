# Handoff — packet B, the execution bridges (window row 2b)

[AGENT packet B worker] 2026-09-28. Worktree `.claude/worktrees/packet-b`, branch `window/packet-b-bridges-0928`
off `core/step-label-0928` @ `61bdc65d` (the label reshape; its audit `docs/2026-09-28_step-label-audit.md` on
`review/step-label-0928` @ `05435724` is MERGE-CLEAN). Brief `docs/codex-briefs/2026-09-24_packet-B-bridges.md` as
refreshed by the [AGENT] coordinator. Evidence `docs/evidence/2026-09-28_packet-b/`. Audit round: §8. Nothing merged, pushed or
committed on `main`; the root `HANDOFF.md` untouched. This file doubles as the brief's §7 report.

## 1. State — BRANCH COMPLETE, nothing stopped

Commits: `f7b15450` (the proofs, the BridgeSet re-pin, the changelog row) and the records commit on top (this file,
the evidence dir, the F3 comment fixes) — its hash is the branch tip (`git log -1`). Both build; the gate ran on the
records commit's Lean content (the two commits differ in Lean only by comments).

Every `<name>_stmt` of `ExecutionStatement.lean` is PROVED as `theorem <name>` in NEW `GoLean/GoCore/Prefix.lean`,
statements unchanged (23 `def … _stmt : Prop` = 23 theorems; `git grep -c "_stmt"
GoLean/GoCore/ExecutionStatement.lean` = 32 matching LINES — comments and uses included). No `sorry`/axiom/
`native_decide`/`partial`; `stepFn`, `Step`, the rules, `Config`, `StepLabel`, `StepEvent`, the drivers untouched.

| Theorem | `_stmt` | Premises the proof actually needs |
|---|---|---|
| `prefix_refl`, `prefix_comp`, `prefix_split`, `prefix_erase_trace`, `prefix_erase_steps` (via `Trace.erase` → `stepFn_sound`), `prefix_iter` | same names | none (every `n`, independent of termination) |
| `finish_abort_step` | same | the NO-STRAY-PANIC lemma (below) for ⇐ |
| `finish_refused_step`, `finish_replay` | same | the statement's `abort? = some` only |
| `run_ok_iff` | same | none (from the pinned `Semantics.run_ok_iff` + `prefix_of_trace`) |
| `run_panic_iff`, `run_deadlock_iff`, `run_fuelOut_iff` | same | `execStmtLoop_error` + `stepFn_error_cases` (no stray panic / deadlock / race / fuel-out) |
| `replay_coverage` | same | **NONE — premise-free** (§2) |
| `classification` | same | unconditional (via `classification_strong`) |
| `classification_wf` | same | `NoRefusal` only — the `StateWf` premise is not used |
| `silent_projection` | same | `StepLabel.fold_silent` |
| `single_embedding` | same | `execProgLoop_single` (definitional, audit F5) |
| `program_bridge` | same | unfolds `runProgramPoolOutM` under the setup premise |
| `boundary_abort_one`, `boundary_blocked_zero`, `boundary_refused_one`, `boundary_refused_zero` | same | the abort arm (`stepFn_abort`) |

Also proved (not `_stmt`s): `abortLeftover_eq` (+ `_refused`), `stepFn_abort`, `abortMsg_error`,
`finish_aborted_stepFn` / `_of_stepFn`, `execStmtLoop_error` (every loop error located on the fixed tape's prefix),
`Prefix.run_eq` / `run_le`, `stepFn_error_cases`, **`stepFn_no_stray_panic`**, `stepFn_any_residual`,
**`noRefusal_step`** (the domain premise's one-step preservation — no `StateWf` needed), and the boundary CONTROLS
as `example`s (abort at 0/1, `.next .stop` at 0, blocked at 0, renderer refusal at 0/1; `#eval`-checked first; the
fuel-1 two by `with_unfolding_all rfl`).

## 2. The two questions put to this packet

1. **No stray panic — TRUE, machine-checked.** `StepErrors.stepFn_strict`: `c.abort? = none → c.blockedB = false →
   ErrP Stop.Strict (stepFn ctx σ c ch)` — away from the abort and the four blocked forms `stepFn` raises ONLY a
   refusal or `fatal`: no Go panic, no deadlock, no race terminal, no fuel-out. Proved over the whole helper
   closure (every raw call, every `toResult`-wrapped apply and every commit phase: `Stop.Tame` lemmas for the
   helpers under `toResult`, `Stop.Strict` for the raw ones, `CommitOk` for every plan's commits). No site the
   stray-panic lane missed. `Prefix.stepFn_no_stray_panic` is the coordinator's form.
2. **`replay_coverage` — premise-free, TRUE.** `MachineSound.stepFn_consumption_some` never reads its
   `appendTargetLocal` binder (`_hloc`); `PrefixFacts.stepFn_consumption_some'` is its case sweep copied with the
   binder dropped (the module is outside this packet's edit boundary). The owed record lemma (label-reshape audit
   F2): `stepFn_picks_none` / `stepFn_picks_some` — a successful step's `l.picks` is `[]` when `seqConsumption` is
   `none`, else exactly `PickRecord.ofPick site b (Choices.consumeAt site b ch).1`. With the two consumption
   theorems these give `replay_coverage` without any premise.

## 3. Coordinator items folded in (label-reshape audit, [AGENT] coordinator disposition)

- **F1**: `stepThread_privateStep_label` strengthened (theorem-only) — the conclusion also states
  `arrivalPlan ctx s threads i c ch = .ok (none, ch₁, ps₁) ∧ selectApplyPlan c = none`; BridgeSet row 34 re-pinned.
- **F2**: answered by §2.2.
- **F3** (records commit): `ExecutionStatement.lean`'s twelve stale `file:line` references refreshed; the print
  arm of `applyStmtOpCore.plan` now says the bytes are the step label's `out` (`stmtOpOut`) — comment only, the line
  count kept so no downstream reference shifts.

## 4. Files

NEW `GoLean/GoCore/Prefix.lean` (the 23 theorems, the controls), NEW `GoLean/GoCore/PrefixFacts.lean` (`OkP`/`okp`,
the record sweeps, the premise-free consumption theorem), NEW `GoLean/GoCore/StepErrors.lean` (`ErrP`/`errp`, the
helper-closure lemmas, `stepFn_strict`). `GoLean.lean` imports `Prefix`. `BridgeSet.lean` re-pinned: row 34
changed, rows 35–64 added. `MultiSound.lean` (F1). `docs/changelog/61958f2e-WINDOW.md`: row «bridges (2b)» added,
the label row points at it. Comments only: `ExecutionStatement.lean`, `Machine.lean` (F3).

## 5. Gates (box-wide lock held for every build/gate)

| Command | Result |
|---|---|
| `scripts/capped lake build` | EXIT=0, 106 jobs, warning-free (also `lake env lean` per new module: no warning) |
| `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (12:14–12:27 UTC, 739 s) | EXIT=1, RED ON EXACTLY THE 5a PAIR: `certificate provenance` (STALE) and the baseline line `imported-goose/channel/google-search PASS → FAIL` (its cached certified record stale for that reason); 3768 cases = 3531 / 237; NO other row moved; negative baseline 394 matched; eval tests 295 ok; core build warning-free; core audit, memory inventory, unseq scheduler/wire, wire boundary, method identity, frontend pins ok. An earlier full run (before `noRefusal_step` was added) gave the same result (947 s). |
| `scripts/capped scripts/check-core-audit` | EXIT=0 PASS — 50 modules (41 under GoCore), 55 required theorems, classical trio only |
| `scripts/capped scripts/check-mem-callsites` | EXIT=0 PASS, 73 rows |
| `python3 tools/reconcile-records` | 2 findings, both standing: C9 (the 5a STALE) and C13 (doc Go versions) |
| escape hatches | none added (ci preflight + the audit) |

## 6. Flags — [AGENT packet B worker] INTERPRETED (flagged, not decided)

1. **Two extra new modules.** The brief puts the Lean in «a new `Prefix.lean`»; the supporting sweeps live in two
   more new modules, `PrefixFacts.lean` and `StepErrors.lean` (build time and readability), imported by
   `Prefix.lean`. The brief's «imported by `ExecutionStatement.lean`» is reversed: the proofs import the statements
   (the statements file cannot import its own proofs' consumers without a cycle).
2. **`stepFn_consumption_some'` is a COPY** of the `MachineSound` sweep minus the unused binder. The better shape —
   drop the premise in `MachineSound` itself and delete the copy — is outside this packet's boundary; proposed as a
   follow-up.
3. **`run_ok_iff` direction.** The brief asks for the pinned `Semantics.run_ok_iff` to be derived FROM the labelled
   one; the dependency order (`Trace.lean` is imported by the statements) makes the reverse the natural one: the
   labelled `run_ok_iff` is derived from the pinned one. Both hold; the pinned statement is untouched.
4. **Brief items not in any `_stmt`, not done**: the pool/sequential fold agreement under `single_embedding`
   (item 7's second half) and restating `ProgramRun`/`program_run_iff`/`observation_iff` over the label (item 9) —
   the statements file (fixed) does not state them; the reshape lane did not re-state them either.
5. **Required-theorem list.** The coordinator's note says to add the new theorems to `check-core-audit`'s required
   list «where the brief says»; the brief says only that the harness imports `Prefix.lean` (it does — the audit
   globs every module on disk), and `Tests/` is outside §6's edit list — so the list is unchanged (55). A
   strengthening the coordinator may want at the landing.
6. **The tactic apparatus is meta-code in the core directory** (`errp_unfold`, `errp_heq`, `errp_commit` elaborators,
   `import Lean`): proof automation only, no definitions the machine runs; `Lean` is an allowed module root.

## 7. What remains

Nothing owed by this packet. For the combined landing: the audit ask (unconditional), the merge sign-off, the train's
5a record (the certificate provenance is STALE by construction: compiled inputs changed), PENDING [USER] item 11
(the CLAUDE.md owed-simulation sentence, posed at the combined landing).

## 8. Audit round (packet B audit MERGE-CLEAN, `docs/2026-09-28_packet-b-audit.md` on `review/packet-b-bridges-0928` @ `801f8479`; [AGENT] coordinator dispositions, disclosed at the merge ask)

Rebased first: `core/step-label-0928` onto `main` @ `fd1135ff` in its worktree (`61bdc65d` → `0a5a7999`), then this
branch onto it (snapshots `refs/snapshots/packet-b-rebase/{step-label,packet-b}` = the old tips). New commit on top:

- **F1**: BridgeSet rows 35–57 write each `_stmt`'s statement out (no longer pinned by name); `open
  GoLean.GoCore.ExecutionStatement (…)` for the statement vocabulary.
- **F2**: BridgeSet header count fixed («rows 35–64 … seven supporting facts»).
- **F6** (authorized `Tests/` edit, gate strengthening only): `Tests/GoCoreAudit.lean` — required modules +
  `ExecutionStatement`, `Prefix`, `BridgeSet`, `PrefixFacts`, `StepErrors` (the audit's module list is a list of
  module names checked against the closure, so all five were added); required theorems + the 23 bridge theorems,
  `stepFn_strict`, `stepFn_no_stray_panic`, `stepFn_error_cases`, `execStmtLoop_error`, `noRefusal_step`,
  `stepFn_picks_none`, `stepFn_picks_some` (55 → 85). Fail-closed confirmed by a scratch mutation (`noRefusal_step`
  renamed, its BridgeSet row dropped, reverted after): `check-core-audit` EXIT=1, «Unknown constant
  `GoLean.GoCore.ExecutionStatement.noRefusal_step`» (`docs/evidence/2026-09-28_packet-b/core-audit-mutation.txt`).
- **F7**: the leftover debug `logInfo` in `errp_unfold` removed.

Recorded, NOT fixed (dispositions):

- **F3**: fold `stepFn_consumption_some'` back into `MachineSound` (drop the unused `appendTargetLocal` premise there,
  delete the copy) — a later core edit.
- **F4**: `NoRefusal` is scoped to the SEQUENTIAL driver: `stepFn` refuses a `go` spawn position (spawning is a pool
  step), so the premise fails on any program that reaches a `go` statement; `classification_wf` is a sequential-run
  corollary only.
- **F5**: owed before the re-pin offer — the single-goroutine OUTPUT agreement (the pool's `out` fold vs the
  sequential labels' fold) and the sequential-to-pool TERMINAL projection.

Gates of this round: `scripts/capped lake build` EXIT=0 (warning-free); `scripts/capped scripts/check-core-audit` EXIT=0 PASS (85 required theorems); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (12:58–13:10 UTC, 738 s) EXIT=1, RED ON EXACTLY THE 5a PAIR (`certificate provenance` STALE; `imported-goose/channel/google-search` PASS → FAIL), 3768 = 3531 / 237, no other row moved, negative baseline 394 matched. The evidence dir's `ci-diff-tail.txt` and `core-audit-tail.txt` are this round's.

## Merge train r52 — the 5a record ([AGENT] coordinator, 2026-09-28)

The label reshape, packet B, both audits and the approved `CLAUDE.md` wording landed ([USER] Mike 2026-09-28 «D1: approved,
D2: approved. Go ahead», relayed). Pre-merge main `fd1135ff` → `refs/snapshots/r52/main`; train tip `d640a5ac` fast-forwarded.
Under the lock: `scripts/build-certified` EXIT=0 (binary `476cd29f…`); `release-check` EXIT=2 (EXPECTED — «STALE
certification: changed dependency build/files/GoLean.lean»); `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` EXIT=1,
983 s — red on EXACTLY the 5a pair (`certificate provenance`; the one drift line `imported-goose/channel/google-search
PASS→FAIL/membership`); 3768 rows run, 3531 PASS / 237 FAIL = the pin 3532 / 236 with the one 5a-class row red; no other
drift. Tail: `docs/evidence/2026-09-28_packet-b/r52-ci-slow.tail.txt`. Candidate vs tracked record: `claim` and
`observations_sha256` IDENTICAL; 20 compiled modules differ (the label reshape and the bridge modules), no tool file, plus the
receipt (`d640a5ac`, 162.964 s) — INSTALLED in this commit; a provenance refresh, not a re-pin.
