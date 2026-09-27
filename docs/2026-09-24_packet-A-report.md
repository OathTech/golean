# Window packet A — report (the CONTRACT)

[AGENT packet A worker] 2026-09-27, Opus 5.5 subagent under the execution-model ruling of 2026-09-27; brief
`docs/codex-briefs/2026-09-24_packet-A-contract.md` + the coordinator's overrides and the [AGENT] coordinator's
2026-09-27 dispositions (below; disclosed at the merge ask). Evidence: `docs/evidence/2026-09-24_packet-a/`.

**Branch** `window/packet-a-contract-0927` (worktree `.claude/worktrees/packet-a`): INPUT `main` @ `5946adfa`
(`git diff --stat 3fb4a0d1 5946adfa -- GoLean/GoCore` empty, verified first), REBASED onto `main` @ `7d2a62e5` (r49
5a records + r50 docs; no `GoLean/` change) at the coordinator's instruction. Commits `fc82f8b0` (the contract),
`c3a351ac` (the dispositions), then this records commit.

**Files** — `GoLean/GoCore/BridgeSet.lean` 157 · `GoLean/GoCore/ExecutionStatement.lean` 397 ·
`docs/2026-09-24_execution-statement.md` 115 · `docs/changelog/61958f2e-WINDOW.md` 90 · `GoLean.lean` +5 (two imports
+ comment) · `scripts/mem-callsites.tsv` +1 row (disposition 2) · the evidence dir (README + 5 files, 36 KiB) · this report.

**The 24 pins.** `#check @<name>` = the brief's table on EVERY row — kind, source line, `ctx` binder (`{ctx}`: 1–6,
24; `(ctx)`: 10, 11, 13, 15, 17, 18, 21–23; none: 7–9, 12, 14, 16, 19, 20); types in `checks.txt`. No row flagged.
A two-row mutant fails the build (`Type mismatch` ×2).

**Dispositions ([AGENT] coordinator, 2026-09-27)** of the two items packet A had STOPPED: (1) Reading A — `Finish`
gains a fifth constructor `fatal` (a `stepFn` call raising `.terminal (.fatal m)`, `Machine.lean:4392`/`:4416`/`:4443`
via `toResult`; cost 1; endpoint store + tape; record `[]`); `classification_stmt` and `classification_wf_stmt`
WRITTEN over five constructors (cases `ClassOk` / `ClassTerminal` / `ClassFuelOut` / `ClassRefusal`, the terminal
linked by `FinishOutcome.terminal?`); two `rfl` fatal boundary controls (one unlocked-mutex cell at `base 0`,
`.retV (.addr (.base ⟨0⟩)) (.syncStK .unlock [] [] [] .stop)`: `.fuelOut` at fuel 0, the fatal at 1). (2) Reading A —
`program_bridge_stmt` WRITTEN; its `loadMany` recorded in `scripts/mem-callsites.tsv` («NO EXECUTION», like line 74).

**Acceptance at `c3a351ac`** (capped; EXIT codes captured):
1. `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean` → EXIT=0, 0 `warning:` lines.
2. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (under the lock) → EXIT=1 in 781 s, red on EXACTLY the 5a
   pair: `certificate provenance` (STALE: `build/files/GoLean.lean`) and `imported-goose/channel/google-search`
   PASS→FAIL/membership (tier=slow certificate, same cause); 3768 = 3531 / 237; negative diff no regression; every
   other step ok, incl. `check-mem-callsites`. `baselines/certified/` untouched — the train's step 5a. (Earlier: fast
   `ci` at `60251b78` red also at `check-mem-callsites` and the two «NO recorded run» baseline steps — both resolved.)
3. `scripts/capped scripts/check-core-audit` → EXIT=0, gate PASS, modules 45 → 47. `scripts/check-mem-callsites` → PASS.
4. `scripts/check-spec-anchors` → EXIT=0 (none cited here). `python3 tools/reconcile-records` → EXIT=0, verbatim:
   «[01] C9 HIGH certificate provenance: STALE certification: changed dependency build/files/GoLean.lean» · «[02] C13
   MEDIUM 79 doc site(s) across 10 file(s) name a patch-level Go version other than the pin …» (full text in
   `controls-and-checks.txt`; re-run at `c3a351ac`: identical findings). Fixed none.
5. `git grep -n -E "sorry|admit|native_decide|axiom|partial" -- <the two files>` → empty.

**`[inf]` cells** (changelog): all «what to touch» cells (eleven rows incl. the new contract-modules row). Verified,
not inferred: `Step` rules 122 → 128 (six added, none removed; the awk command in the file); `Stmt`/`Cont`/
`ChoiceSite`/`Config` = 44/33/10/10, identical in order at both commits.

**INTERPRETED (flagged for the audit, not decided):**
- both new files ALSO `import GoLean.GoCore.Trace` (rows 3, 4, 24 and `prefix_erase_trace_stmt`; `#check` failed without).
- `Finish.abortRefused` and the refusal boundaries match `abortMsg … = .error (.refusal r)` (it throws only `.unsupported`).
- `NoRefusal`'s renderer clause uses the pick the consult draws from the residual, not «any pick».
- the boundary statements' names `boundary_{abort_one,blocked_zero,refused_one,refused_zero}_stmt`; the witness inlined.
- `replay_coverage_stmt` omits `c.appendTargetLocal` (brief-directed; packet B's first question).
- `classification_wf_stmt` uses `StateWf ctx s` as briefed, but `step_preserves_wf` (`StateWf.lean:8106`) is over `MachineWf`.
- `Finish.fatal` records `[]` picks and keeps the pre-call tape: no consultation precedes the three fatal throws.
- `ClassRefusal` bounds the refusing call by `n + 1 ≤ fuel` (the brief's `n ≤ fuel` is implied; F2's cost 1 made explicit).
- the four case predicates `ClassOk`/`ClassTerminal`/`ClassFuelOut`/`ClassRefusal` and `FinishOutcome.terminal?` are
  helper names of mine; «exactly one» is by the pairwise-distinct result shapes they fix.
- the E6e row of «Window rows (PENDING)» is marked OFF the critical path per the [USER] 2026-09-27 re-scoping.

**End state:** branch complete, worktree clean, nothing merged, pushed or tagged; the root `HANDOFF.md` untouched.
