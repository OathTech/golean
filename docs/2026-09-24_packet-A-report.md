# Window packet A — report (the CONTRACT)

[AGENT packet A worker] 2026-09-27, Opus 5.5 subagent under the execution-model ruling of 2026-09-27; brief
`docs/codex-briefs/2026-09-24_packet-A-contract.md` + the coordinator's overrides (input = current `main`, branch
name, lock, changelog fold, provenance tag). Evidence: `docs/evidence/2026-09-24_packet-a/`.

**Branch** `window/packet-a-contract-0927` (worktree `.claude/worktrees/packet-a`), one commit over the INPUT
`main` @ `5946adfa`. `git diff --stat 3fb4a0d1 5946adfa -- GoLean/GoCore` empty (verified before starting).
DRIFT: `main` moved to `7d2a62e5` during the packet (r49 5a records + r50 docs; no `GoLean/` change) — NOT rebased.

**Files** — `GoLean/GoCore/BridgeSet.lean` 157 · `GoLean/GoCore/ExecutionStatement.lean` 294 ·
`docs/2026-09-24_execution-statement.md` 120 · `docs/changelog/61958f2e-WINDOW.md` 87 · `GoLean.lean` +5 (two
imports + comment) · the evidence dir (README + 6 files, 40 KiB) · this report.

**The 24 pins.** `#check @<name>` agrees with the brief's table on EVERY row — kind, source line and `ctx` binder
(`{ctx}`: 1–6, 24; `(ctx)`: 10, 11, 13, 15, 17, 18, 21–23; none: 7–9, 12, 14, 16, 19, 20); full types in
`checks.txt`; all 24 source lines re-verified at `5946adfa`. No row flagged. A two-row mutant fails (`Type mismatch` ×2).

**Acceptance** (capped; EXIT codes captured):
1. `GOLEAN_MEM_MAX=48G scripts/capped lake build GoLean` → EXIT=0, 0 `warning:` lines.
2. Fast `scripts/capped scripts/ci` at `60251b78` → EXIT=1: `certificate provenance` (expected) + `check-mem-callsites`
   (mine, below) + `baseline diff` / `negative baseline diff` («NO recorded … run»: a fresh worktree has none; not
   waived via `GOLEAN_ALLOW_NO_DIFF`). Re-run as `scripts/capped scripts/ci --diff` at `0317b64a` → EXIT=1 in 865 s,
   red on EXACTLY the 5a pair: `certificate provenance` (STALE: `build/files/GoLean.lean`) and
   `imported-goose/channel/google-search` PASS→FAIL/membership (tier=slow certificate, same cause); 3768 = 3531 / 237;
   negative diff no regression; every other step ok. `baselines/certified/` untouched — the train's step 5a.
3. `scripts/capped scripts/check-core-audit` → EXIT=0, `Core totality audit gate: PASS`, modules 45 → 47.
4. `scripts/check-spec-anchors` → EXIT=0 (no `spec#`/`mem#` cited by this packet). `python3 tools/reconcile-records` →
   EXIT=0, verbatim: «[01] C9 HIGH certificate provenance: STALE certification: changed dependency
   build/files/GoLean.lean» · «[02] C13 MEDIUM 79 doc site(s) across 10 file(s) name a patch-level Go version other
   than the pin …» (full text in `controls-and-checks.txt`). Fixed none.
5. `git grep -n -E "sorry|admit|native_decide|axiom|partial" -- <the two files>` → empty (EXIT=1).

**`[inf]` cells** (changelog): all ten «what to touch» cells — `Step` arity, `stepFn` result, `stepFn_sound`/
`step_complete`, read/write labels, alloc + `Store.alloc`, `Trace.step`, rule count, constructor lists (none), the
legacy triple, the wire, the decoder refusals. Verified (not inferred): 122 → 128 (six added, none removed; the awk
command in the file); `Stmt`/`Cont`/`ChoiceSite`/`Config` = 44/33/10/10, identical in order at both commits.

**INTERPRETED (flagged, not decided):**
- `[AGENT packet A worker] INTERPRETED:` both new files ALSO `import GoLean.GoCore.Trace` — neither `ProgramTrace` nor
  `MultiSound` reaches it, and rows 3, 4, 24 and `prefix_erase_trace_stmt` need it (`#check` failed without).
- `INTERPRETED:` `Finish.abortRefused` and the refusal boundary statements match `abortMsg … = .error (.refusal r)`:
  `abortMsg` returns `Except Stop String` and throws only `.unsupported` (`Machine.lean:3912`); typing forces the pattern.
- `INTERPRETED:` `NoRefusal`'s renderer clause uses the pick the consult draws from the residual (not «any pick»).
- `INTERPRETED:` the four boundary statements are named `boundary_{abort_one,blocked_zero,refused_one,refused_zero}_stmt`;
  the witness's `ctx`/`abortConfig` are inlined into the three `rfl` examples (no new declarations).
- `INTERPRETED:` `classification_wf_stmt`'s premise was to be `StateWf ctx s`, but `step_preserves_wf`
  (`StateWf.lean:8106`) is over `MachineWf ctx σ c` — moot while the statement is held (below), recorded for packet B.
- The E6e row of «Window rows (PENDING)» is marked OFF the critical path per the [USER] 2026-09-27 re-scoping.

**Readings DECLINED under the ambiguity policy (items STOPPED; both readings in the design note's last section):**
- `classification_stmt` / `classification_wf_stmt` — NOT stated: `stepFn` raises `.terminal (.fatal m)` at a
  non-zero-cost configuration (`Machine.lean:4392`, `:4416`, `:4443`; `toResult` `Value.lean:394`), which no
  four-constructor `Finish` classifies — as briefed both would be false. (A) a fifth `Finish.fatal` (cost 1);
  (B) a fifth classification disjunct like the refusal case.
- `program_bridge_stmt` — HELD (text elaborated; kept verbatim in the evidence dir): its `loadMany` mention is a NEW
  `scripts/check-mem-callsites` row and brief §8 forbids editing `scripts/`. (A) add the tsv row (reason «NO EXECUTION
  — …», as `ProgramRun`'s line 74); (B) restate through `ProgramRun`.

**End state:** branch complete, worktree clean, nothing merged, pushed or tagged; the root `HANDOFF.md` untouched.
