# Evidence — C1 S2c (D9: the synchronization emissions in the module; the one fold), BUG-111 fix (i), S3

Lane `core/c1-memory-module-s2c-0918`, base main `42023bd9`; handoff
`docs/2026-09-18_c1-memory-module-s2c-handoff.md`; charter `docs/2026-09-17_c1-memory-module-charter.md`;
predecessor evidence `docs/evidence/2026-09-18_c1-memory-module/`. Small files only (the caps:
`scripts/check-evidence-size`); bulk stays under `artifacts/` (gitignored) and is described here.

## S2c-i — the ordered event label, both folds live, the fold-equality audit (2026-09-18)

Runtime commit `f1ad88c3` (its message is the content inventory). Binaries: S2c-i `7eb5de44bd99…`
(`.lake/build/bin/golean` at the commit); main `42023bd9`'s certified binary `42b7bf1ab5f2…`
(the primary's `.lake/build/bin/golean`, copied read-only to `.tmp/golean-main` after the train's lock
was released; byte-identical to the fix round's `42b7bf1a…`).

| file | what |
|---|---|
| `fold-audit-s2c1.txt` | the whole-corpus tracer run (`scripts/choice-trace-corpus --dump --jobs 6`, the standing 2 exclusions): 21,835 (row, stream) results, `foldMismatches` column sum 0, statuses census; the sorted-dump byte-identity vs main's binary (23,679 records, sha256 `0df092ee…` both, `cmp` EXIT=0) |
| `twin-audit-s2c1.txt` | the raft twin (`raft-twin/probeTwin{Choice,Single,Elect,Perturb,Ticks}` × 6 streams, fuel 10,000,000) on both binaries: 30/30 ok, 0 fold mismatches, 0 alarms, 14,360 consumptions each; sorted dumps `cmp` EXIT=0, sha256 `3b0b4c0a…` both |
| `probe-FoldOrder.lean` / `.log` | the positive control: two labels differing only in the order of `Mutex.Unlock`'s state Add and its release fold to DIFFERENT shadows; `Acc.auditFold` reports it; equal folds report nothing; a one-goroutine pool is inert |
| `eval-tests-s2c1.txt` | `gocore-eval-tests` at the S2c-i tree: 211 ok, EXIT=0 |
| `gate-tail-s2c1.txt` | the `ci --diff` tail at `f1ad88c3` (EXIT=1, 770 s; red only on the two 5a-class items) |

### The audit — what was compared, and the result

Per pool step (the tracer `GoLean/ChoiceTrace.lean`, `poolStep`): the fold of record
`raceUpdate ctx m.shared m.threads ev m' r` (the registry arms over the pre-step pool, untouched in
S2c-i beyond reading the label's accesses through `dataEvents`) and the one-fold
`raceFold ev m' r` (the LABEL alone, `RaceState.events`) from the SAME pre-state `r`; compared
STRUCTURALLY (`RaceState`'s derived `BEq`: clocks, the sorted shadow, the channel/sync/atomic clock
tables with their insertion order) or by error class + message. A difference is `fold-mismatch: …`
(an alarm, so the corpus run exits 1, and the `foldMismatches`/`firstFoldMismatch` columns). The
tracer continues with the fold of record's result.

RESULT: **0 mismatches** on 21,835 corpus (row, stream) results — 252 of them `race` verdicts, each a
step on which BOTH folds threw `raceDetected` — and on the twin's 30. The positive control shows the
instrument detects an order difference. The choice trace is BYTE-IDENTICAL to main's on the corpus and
the twin (D4: no semantic change on the machine).

### Gate

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (`.tmp/with-lock.sh`; acquired after 0 s, 22:37:12–22:50:02 UTC) on the committed runtime tree `f1ad88c3` (clean for `GoLean`/`Tests`/`scripts`; the evidence dir untracked — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 770 s**; **3676 cases: 3427 PASS / 249 expected FAIL** (`differential coverage summary: cases=3676 pass=3427 fail=249`); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `memory-module raw call-site inventory` ok (78 rows); `unseq scheduler` ok; `method-identity` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/ChoiceTrace.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row, judged stale because compiled semantic inputs changed). ZERO other drift; the negative baseline matched (394). Tail: `gate-tail-s2c1.txt`.

### Inventory

`scripts/check-mem-callsites` EXIT=0, PASS, 78 rows — unchanged at S2c-i (the registry arms exist
until S2c-ii; the emission tables and the moved `chanValueLoc` add no raw site).

## S2c-ii — the switch (2026-09-18)

Runtime commit `fc4e5d6b` (its message is the content inventory). Binary `b3354990efe8…`.

| file | what |
|---|---|
| `choice-trace-s2c2.txt` | the whole-corpus tracer run with the S2c-ii binary (the audit instrument retired: 15 TSV columns): 21,835 (row, stream) results, same census, 0 alarms/violations/driver mismatches; sorted dumps 23,679 records, sha256 `0df092ee…` = main's, `cmp` EXIT=0 |
| `twin-audit-s2c2.txt` | the raft twin with the S2c-ii binary: 30/30 ok, 14,360 consumptions, sorted dumps `cmp` EXIT=0 vs main's (sha256 `3b0b4c0a…`) |
| `gate-tail-s2c2.txt` | the `ci --diff` tail at `fc4e5d6b`: EXIT=1, 768 s, 3676 = 3427/249, red only on the two 5a-class items; the inventory step GREEN at 72 rows |
| `detector-soundness-s2c2.txt` | the official matrix on the S2c-ii binary: EXIT=2 (INCOMPLETE for the 9 `params-omit-sites=` membership refusals, exactly as at the fix round), 1,729 s, worker-pool exit 0, 639 rows: **HOLE 0, possible-HOLE 0**, agree-DRF 502, agree-race 36, over-refusal 6 (`race/free/array-dyn-index-read-write` = BUG-041's O1 residual and the five `race/gomem-only/*` rows of the RULED go_mem-RACY / TSan-GREEN lane), refused 9, uncertified 86 — cell for cell the fix round's official record (`detector-soundness-s2c2.txt`). The one fold reads the label and reproduces the deleted arms' verdicts on every in-scope row. |

### Gate

`GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (`.tmp/with-lock.sh`; acquired after 0 s, 23:02:27–23:15:15 UTC) the committed runtime tree `fc4e5d6b` (clean for `GoLean`/`Tests`/`scripts`; `docs/` dirty with the records edits — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 768 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `memory-module raw call-site inventory` ok (**72 rows**); every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row). ZERO other drift; the negative baseline matched (394). Tail: `gate-tail-s2c2.txt`.

### Inventory

`scripts/check-mem-callsites` EXIT=0, PASS, **72 rows** (78 − the six DETECTOR REGISTRY ARM rows: `raceCommitClauseEvent` chanCell 2,
`racePairEvent` chanCell 3, `raceUpdate` chanCell 3 / loadLoc 1 / syncCell 3, `raceWakeEvent` chanCell 2 — 14 raw memory-operation sites
gone with the arms). The SYNCHRONIZATION rows now name the apply's own emission as the reason the peek/raw write is not a data access.
