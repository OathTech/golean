# Window packet A — report (the CONTRACT)

[AGENT packet A worker] 2026-09-27 (Opus 5.5 subagent); brief `docs/codex-briefs/2026-09-24_packet-A-contract.md` +
coordinator overrides + [AGENT] coordinator dispositions (disclosed at the merge ask). Evidence: `docs/evidence/2026-09-24_packet-a/`.

**Branch** `window/packet-a-contract-0927`: INPUT `main` @ `5946adfa` (GoCore = `3fb4a0d1`'s), rebased onto `main` @
`7d2a62e5`, then onto `core/stray-panic-refusal-0927` @ `05d0dbd4` (F1's fix, under audit); 6 commits + this one.

**Files** — `GoLean/GoCore/BridgeSet.lean` 157 · `GoLean/GoCore/ExecutionStatement.lean` 453 ·
`docs/2026-09-24_execution-statement.md` 120 · `docs/changelog/61958f2e-WINDOW.md` 96 · `GoLean.lean` +5 (two imports
+ comment) · `scripts/mem-callsites.tsv` +1 row (disposition 2) · the evidence dir (README + 7 files) · this report.

**The 24 pins.** `#check @<name>` = the brief's table on EVERY row (kind, source line, `ctx` binder; types in
`checks.txt`); no row flagged; a two-row mutant fails the build (`Type mismatch` ×2).

**Dispositions ([AGENT] coordinator, 2026-09-27)**: (1) Reading A — `Finish.fatal` (`.terminal (.fatal m)` from a `stepFn`
call, cost 1, record `[]`); both classifications WRITTEN over five constructors (`ClassOk`/`ClassTerminal`/`ClassFuelOut`/
`ClassRefusal`, `FinishOutcome.terminal?`); two `rfl` fatal controls (an unlocked-mutex cell: fuel 0 → `.fuelOut`, 1 →
the fatal). (2) Reading A — `program_bridge_stmt` WRITTEN; one «NO EXECUTION» row in `scripts/mem-callsites.tsv`.

**Audit round** (FIX-FIRST, `docs/2026-09-27_packet-a-audit.md` on `review/packet-a-contract-0927` @ `e750e13c`;
[AGENT] coordinator dispositions, disclosed at the merge ask): **F2 FIXED** — `NoRefusal`'s first clause is
`¬ ZeroCost cf → ∀ r, stepFn ctx sf cf chf ≠ .error (.refusal r)` (`stepFn` refuses at `.next .stop`), with a
positive control (`example`: a one-step completing run from `.next (.seq [] [] .stop)` satisfies it; `#eval` first).
**F3 FIXED** — `finish_replay_stmt`: a tape `ch₂` whose `repanicCollapse` consult emits the same `rec` replays
the `.aborted t` / `.refused r` finish with `ch₂`'s residual. **F4/F5/F6 recorded** (`MachineSound.lean:6243`;
the two DEFINITIONAL statements; the decoder count command). **F1 RESOLVED** by `core/stray-panic-refusal-0927`
(disposition (b), [AGENT] coordinator, disclosed at the merge ask): the four statements refuted as stated
(`finish_abort_step_stmt`, `run_panic_iff_stmt`, both classifications) are UNCHANGED and elaborate; the audit's
witness now `#eval`s to `.refusal (.internal "binding cell is not a root location: …")` and is PROVED `ClassRefusal`,
not `ClassTerminal` (`F1Witness.lean`, classical trio only). The core lane's changelog line is merged.
**Detected gap** (pre-existing; a later tooling lane; untouched): `check-mem-callsites` skips a declaration's HEADER
line — a one-line `def f … := loadMany …` passes.

**Acceptance at `36d8571b`** (same at `92aaab2a`, `c3a351ac`; capped, EXIT codes captured):
1. `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean` → EXIT=0, 0 `warning:` lines.
2. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (under the lock) → EXIT=1 in 948 s, red on EXACTLY the 5a
   pair: `certificate provenance` (STALE: `build/files/GoLean.lean`) and `imported-goose/channel/google-search`
   PASS→FAIL/membership (tier=slow certificate, same cause); 3768 = 3531 / 237; negative diff no regression; every
   other step ok. `baselines/certified/` untouched — the train's step 5a.
3. `check-core-audit` → EXIT=0, PASS, modules 45 → 47. `check-mem-callsites` → PASS. `check-spec-anchors` → EXIT=0.
4. `tools/reconcile-records` → EXIT=0: «[01] C9 HIGH certificate provenance: STALE certification: changed dependency
   build/files/GoLean.lean» · «[02] C13 MEDIUM 79 doc site(s) across 10 file(s) name a patch-level Go version …»
   (verbatim in `controls-and-checks.txt`; identical at `c3a351ac`). Fixed none.
5. `git grep -n -E "sorry|admit|native_decide|axiom|partial" -- <the two files>` → empty.

**`[inf]` cells**: every changelog «what to touch» cell. Verified: `Step` rules 122 → 128; `Stmt`/`Cont`/`ChoiceSite`/
`Config` 44/33/10/10, identical at both commits (commands in the file).

**INTERPRETED (flagged for the audit, not decided):**
- both new files ALSO `import GoLean.GoCore.Trace` (rows 3, 4, 24, `prefix_erase_trace_stmt` need it).
- `Finish.abortRefused` and the refusal boundaries match `abortMsg … = .error (.refusal r)` (it throws only `.unsupported`).
- `NoRefusal`'s renderer clause uses the pick the consult draws from the residual, not «any pick».
- the boundary statements' names `boundary_{abort_one,blocked_zero,refused_one,refused_zero}_stmt`; the witness inlined.
- `replay_coverage_stmt` omits `c.appendTargetLocal` (brief-directed; audit F4: the proof already drops it, `:6243`).
- `classification_wf_stmt` uses `StateWf ctx s` as briefed, but `step_preserves_wf` (`StateWf.lean:8106`) is over `MachineWf`.
- `Finish.fatal` records `[]` picks and keeps the pre-call tape: no consultation precedes the three fatal throws.
- `ClassRefusal` bounds the refusing call by `n + 1 ≤ fuel` (the brief's `n ≤ fuel` is implied; F2's cost 1 made explicit).
- `ClassOk`/`ClassTerminal`/`ClassFuelOut`/`ClassRefusal`, `FinishOutcome.terminal?` are my names; «exactly one» by result shape.
- the E6e row of «Window rows (PENDING)» is marked OFF the critical path per the [USER] 2026-09-27 re-scoping.
**End state:** branch complete, worktree clean, nothing merged, pushed or tagged; the root `HANDOFF.md` untouched.
