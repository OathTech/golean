# Packet C (G-C3, `Cont := List Frame`) — evidence

[AGENT packet C worker], lane `core/continuations-0929`, 2026-09-29/30. Fork base `main` @ `883ebc36`; the runtime
commit is `3be9a643` (the runs below are at it; later lane commits are records only). Scratch under the worktree's
`.tmp/` (deleted at the end); every build/gate `scripts/capped`, under the box-wide lock.

## Acceptance

1. **Gate.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `3be9a643`: EXIT 1, `RESULT: FAIL` on exactly
   the 5a pair — `certificate provenance` (STALE: changed dependency files, the train's 5a business; reconciler C9
   names `GoLean/GoCore/BridgeSet.lean`) and `baseline diff` with the ONE drift line
   `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]`. Every other step ok,
   incl. core build warning-free, core totality audit (144 required theorems), memory-module call sites, unseq
   scheduler/wire, frontend pins, eval tests (298 ok), negative baseline. `differential coverage summary:
   cases=3791 pass=3553 fail=238` = the baseline's 3554 / 237 with the google-search line. NO `baselines/` edit
   (`git diff main -- baselines` empty). CI total wall seconds 1204. Tail: `ci-diff-tail.txt`.
2. **Choice trace, byte-identical.** Pre binary = `lake build golean` at `883ebc36` (sha256 `697001fc…feb52c`,
   identical to a from-scratch build in `.tmp/pre-c3`); post binary = the lane's (`8e042f19…3b5f4`). Both runs:
   `scripts/choice-trace-corpus --dump --jobs 6 --golean <bin> --exclude goroutines/send-then-spin --exclude
   strings/trimspace-repeat/repeat-bound-refused --out .tmp/ct/<pre|post>` — 3755 wires exported, the same 34
   frontend refusals and the 2 standing exclusions; both exit 1 «FINDINGS present» (the summarizer's standing
   findings). `cmp` of `dump-0..5.tsv`: all six IDENTICAL (26417 consumption rows; sha256 of the concatenation
   `1d621c3a…937a79` both sides). `results-1..5.tsv` IDENTICAL; `results-0.tsv` differs ONLY in one row's
   embedded wire path (`.tmp/ct/pre/wire/…` vs `.tmp/ct/post/wire/…`, row `arrays/materialization-budget/
   over-budget`'s refusal message) and is identical after `sed 's#\.tmp/ct/<side>/#.tmp/ct/SIDE/#g'`; the
   `results-*.log`, `batch.tsv`, `summary.txt` differ only in that out-dir path (the summary's fixed-width
   truncation moves by the one-character length difference). The exported `wire/` directories are identical.
   Additionally, every one of the 3755 wires run once per binary (`native-json-run`, default stream, alternating
   order): stdout + exit code identical for all 3755; total 85.5 s pre / 86.4 s post (ratio 1.010).
3. **Twin.** No file under `tools/nativefrontend`, `GoLean/NativeToIR.lean` or `baselines/` changed, so the wire is
   unchanged by construction; `scripts/check-frontend-pins` ok in (1); the twin and `multipkg/mini-raft-twin` rows
   are not in the drift.
4. **Statements.** `Step`: 128 rules at both commits, the constructor-name list identical in order (run_cmd over
   `Step`'s `InductiveVal.ctors`, output files identical). `fun_cases stepFn`: 162 goals at both commits, the same
   positional tags on the same patterns. No theorem statement edited: in `git diff 883ebc36 3be9a643 -- GoLean Tests` the only
   removed line of an existing theorem's statement is `Cont.rebuild_stop`'s `… = act .stop := by`, re-added
   as `… = act .stop := rfl` (the proof, not the statement); `ExecutionStatement.lean`, `Prefix.lean`, `PrefixFacts.lean`
   unchanged; BridgeSet rows 1–89 byte-identical and elaborating. `set_option maxHeartbeats`/`maxRecDepth`: the
   same 59 settings, none added or raised (sorted listing identical).

## Elaboration (the stop rule: >1.5x or a heartbeat raise stops the lane)

`elaboration.txt` has every run. The FIRST single-side runs were taken hours apart under very different box load
(other projects' jobs: load 5 → 16) and showed up to 2.8x — not comparable. The binding numbers are A/B
INTERLEAVED (pre then post per module, back to back, same load; `.tmp/measure2.sh`), wall / cpu seconds:

| module | pre wall | post wall | ratio | pre cpu | post cpu |
|---|---|---|---|---|---|
| Machine | 4.23 | 4.09 | 0.97 | 7.36 | 7.32 |
| StepFn | 1.03 | 1.04 | 1.01 | 1.33 | 1.34 |
| MachineSound | 67.52 | 71.97 | 1.07 | 104.08 | 111.30 |
| StateWf | 17.49 | 17.37 | 0.99 | 60.60 | 61.57 |
| MachineEqb | 4.74 | 4.85 | 1.02 | 7.88 | 8.23 |
| StepErrors | 229.38 | 217.94 | 0.95 | 272.36 | 257.28 |
| BridgeSet | 0.86 | 0.89 | 1.03 | 0.91 | 0.95 |

Profiler totals (pre → post): MachineSound tactic 28.5 → 32.3 s, simp 58.4 → 61.6 s; StateWf tactic 25.2 → 25.9 s;
StepErrors tactic 246 → 233 s; MachineEqb tactic 5.32 → 5.59 s; Machine elaboration 1.55 → 1.62 s. Whole
`lake build golean` from scratch: 384 s post, 468 s pre (run back to back; an earlier pre run under other load:
369 s). Every module is under 1.5x; no heartbeat setting changed.

Two costs found and removed on the way (proof-local, no definition changed): (a) `stepFn_sound` and
`stepFn_consumption_none` exceeded the default heartbeats at C3 — the generic `simp_all [stepFn]` spent ~9 s (0.5 s
before) on the `.retV` catch-all arm's 26 list-shaped overlap hypotheses; `case140`/`case155` (the `.retV`/`.next`
catch-all refusals) are now closed by `simp only [stepFn] at h; simp [throw, …] at h` (0.5 s / 17 ms); (b) the new
`stepFn_next_frame` first proved by `simp only [stepFn]` generated `stepFn`'s equation lemmas in `StepFn.lean`
(+1.7 s, StepFn 2.8x in the first interleaved run); it is `rfl` now.
