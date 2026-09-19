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
| `probe-FoldOrder.lean` / `.log` | the positive control: two labels differing only in the order of `Mutex.Unlock`'s state Add and its release fold to DIFFERENT shadows; `Acc.auditFold` reports it; equal folds report nothing; a one-goroutine pool is inert. COMPILES AT THE S2c-i TREE `f1ad88c3` ONLY (the audit's F9): it imports `GoLean.ChoiceTrace`'s `raceFold`/`Acc.auditFold`, deleted at S2c-ii — historical evidence, not a live probe; the live order guard since the fix round is the label-shape fact set in `Tests/GoCoreEval.lean` (`labelShapeFacts`) |
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

## BUG-111 — fix (i), canonical-path keys (2026-09-18; RULED [USER] 2026-09-18, relayed)

| file | what |
|---|---|
| `bug111-born-state.txt` | the two rows on the S2c-ii binary BEFORE the fix: the alias row ACCEPTED (`ok`, 1 — the missed race, born FAIL), the guard `ok` 12, the control racy row refuses |
| `gate-tail-bug111-rows.txt` | the `ci --diff` tail at the rows' commit `96f2d72d`: EXIT=1, 691 s, 3678 = 3428/250; red on the 5a pair plus the new row's STAGE word (FAIL/racy pinned, FAIL/lean-observation observed — the pin corrected in the following records commit; the verdict FAIL unchanged) |
| `bug111-fixed-state.txt` | the two rows on the fix binary `06e78653…` (default stream): the alias row REFUSES (`race`), the guard `ok 12`, the controls unchanged; eval tests 211 ok |
| `gate-tail-bug111-fix.txt` | the `ci --diff` tail at the fix commit `a8e0cf95`: EXIT=1, 807 s, 3678 = 3428/250; red on the 5a pair plus the alias row's racy-stage line — the enumerator's REFUSAL at the lane's default `sites=8` (depth 9 needed), not a verdict; `re-pin guard` 0 flips, the FAIL→PASS greening noted |
| `bug111-enumerator.txt` | the racy-lane enumerator on the fix binary: refused by name at `--max-sites 8`; at 16 EVERY path refuses (`observations=1`, `race`, 334 leaves); the guard's single `ok 12` member |
| `twin-audit-bug111.txt` | the raft twin with the fix binary: 30/30 ok, 14,360 consumptions, sorted dumps `cmp` EXIT=0 vs main's (sha256 `3b0b4c0a…`) |
| `detector-soundness-bug111-sites8.txt` | INTERMEDIATE: the matrix on the fix binary at the rows' first params — 641 rows, the one `possible-HOLE` is the alias row's enumerator refusal at `sites=8` (gc RACE 5/5 both procs, the single run `race`), the guard agree-DRF, every other cell = the S2c-ii matrix |
| `gate-tail-bug111-params.txt` | the `ci --diff` tail at the params commit `87a3c90b` (`sites=16`): EXIT=1, 709 s, **3678 = 3429/249**, red ONLY on the 5a pair — BUG-111's end state |
| `detector-soundness-bug111.txt` | the FINAL official matrix (fix binary, tree `87a3c90b`): EXIT=2 (the 9 `params-omit-sites=` membership refusals, as always), 1,740 s, worker-pool exit 0, **641 rows** (639 + the two BUG-111 rows): **HOLE 0, possible-HOLE 0**, agree-DRF 503 (the S2c-ii 502 + the guard: gc clean 5/5 at both procs, machine DRF), **agree-race 37** (the S2c-ii 36 + the alias row: gc RACE 5/5 at GOMAXPROCS 1 and 8, machine RACE-ALL 1/1 member at `sites=16`), over-refusal 6 (the same six: BUG-041's O1 residual and the five ruled `race/gomem-only/*` rows), refused 9, uncertified 86 — every pre-existing cell unchanged (`detector-soundness-bug111.txt`; the intermediate matrix at `sites=8`, whose one possible-HOLE was the alias row's enumerator refusal, is `detector-soundness-bug111-sites8.txt`). |
| `choice-trace-bug111.txt` | the whole-corpus choice trace with the fix binary vs main's on the 3,676 pre-existing rows: 23,679 records, sha256 `0df092ee…` = main's, `cmp` EXIT=0 (D4: no other row's consumption moved); the alias row `race` on all six streams, the guard `ok` on all six |

## Audit fix round — the audit's F1–F10 applied (2026-09-19; gated commit `967712a3` + the records commit that follows it)

Audit: `docs/2026-09-19_c1-s2c-audit.md` on `review/c1-memory-module-s2c-0918` @ `41bef7bc` (its litmus sources and
outputs under `docs/evidence/2026-09-19_c1-s2c-audit/` on that branch; the eight corpus rows below reuse six of its
programs verbatim modulo type names, one reshaped — the handoff's fix-round section). Candidate binary at the
transcripts: `06e78653…` (the fix binary — the fix round's Lean edits are docstrings and the test module);
main's certified binary `42b7bf1a…` (`.tmp/golean-main`, read-only copy).

| file | what |
|---|---|
| `fixround-gc-transcript.txt` | gc `go run -race` ×5 at GOMAXPROCS 1 and 8 per new subject (`fixround-run-gc.sh`, the audit's `run-lit.sh` protocol; `GO111MODULE=off`, `GOCACHE` under `.tmp/`): the four racy subjects RACE 5/5 at both procs, the four race-free subjects clean 5/5 at both procs (the atomic handoff samples only its `0` member — the membership row admits both) |
| `fixround-machine-racy.txt` | the four racy subjects on both binaries (default stream) and both enumerators at the rows' `sites=` (`fixround-run-machine.sh`, no `--expect-status`): the candidate RACE-ALL on every one (334 / 11 / 11 / 11 leaves); MAIN `ok` on the three alias rows (HOLEs — its enumerator: DRF on 148 leaves for the nested Mutex copy, `ok`/`panic` members for the wg overwrite, a `sites=16` refusal for the array field), `race` on the no-alias one |
| `fixround-machine-free.txt` | the four race-free subjects: the candidate certifies {1, 2} (3,116 leaves), {2} (3,116), {1} (1,441), {0, 1} (406); MAIN `race` — RACE-ALL on the Mutex and RWMutex handoffs, RACE-SOME on the Once observe and the atomic flag handoff (FALSE races: split clock tables) |
| `fixround-eval-tests.txt` | `gocore-eval-tests` at the fix-round tree, sequential warm build: `lake build` EXIT=0, `lake exe` EXIT=0, **267 ok** (211 + the 56 `LABEL …` facts, listed), 0 FAIL |
| `gate-tail-fixround.txt` | the `ci --diff` tail at `967712a3`: EXIT=1, 741 s, 3686 = 3437/249 (gate count; baseline 3438/248 — the stale-certificate row), red ONLY on the 5a pair (`certificate provenance` STALE on `CLI.lean`; the single `google-search` drift line), eval tests 267 ok, inventory 72 ok, core audit ok, re-pin guard 0 flips, reconciler no C4/C5; the eight rows PASS at their lanes (`mutex-handoff`'s `1` member gc-unexhibited in 32 draws — the machine's, DRF) |
| `choice-trace-fixround.txt` | 542 ids (the audit's subset), 3,252 results per side, sorted dumps 17,052 records each, sha256 `890c2e7a…` both, `cmp` EXIT=0 |
| `detector-soundness-fixround.txt` | 649 rows, EXIT=2 (the 9 standing refusals), HOLE 0 / possible-HOLE 0 / agree-race 41 (37 + 4) / agree-DRF 507 (503 + 4) / over-refusal 6 / refused 9 / uncertified 86 — every pre-existing cell unchanged, 1,748 s |

## Merge train r42 — the 5a record ([AGENT] coordinator, 2026-09-19)

[USER] Mike 2026-09-19, verbatim (relayed): «Great, merge it. Then is the next piece on NaN to just do an
investigatory memo? If so do that». Pre-merge main `42023bd9` → `refs/snapshots/r42/main`; S2c + BUG-111
+ the ratification record (`ad594e0b`) fast-forwarded; the audit branch rebased (`8ca55b17`) and
fast-forwarded; the NaN memo rebased (`3b99f42f`) and fast-forwarded (records). Under the lock at
`3b99f42f`: `scripts/build-certified` EXIT=0, 118 s (binary `da7bb8376164…` — the fix
round's gate binary); `release-check --base refs/snapshots/r42/main` EXIT=2 (EXPECTED — «STALE
certification: changed dependency build/files/GoLean/CLI.lean»); `GOLEAN_MEM_MAX=48G scripts/capped
scripts/ci --slow` EXIT=1, 1003 s — red on EXACTLY the 5a pair (`certificate provenance` STALE; the single
drift line `imported-goose/channel/google-search PASS→FAIL/membership`); 3686 rows otherwise unchanged;
negatives 394 no regression. Tail: `r42-ci-slow.tail.txt`. Candidate vs tracked record: `claim` and
`observations` IDENTICAL; 18 input hashes differ (S2c's core files) and the receipt (clean `3b99f42f`,
binary `da7bb837…`) — INSTALLED in this commit; a provenance refresh, not a re-pin. This commit also
records the NaN ruling ([USER] «NaN: sounds good to me» = [a]+[b]): the rulings-ledger entry, R7's heading
corrected to the memo's pre-implementation text, BUG-094's PLAN.

**Green re-run at the records commit `ede220cb`** ([AGENT] coordinator, 2026-09-19): full
`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` → EXIT=0, `RESULT: PASS`, `baseline diff FULL
(3686/3686, no regression)`, `certificate provenance` ok, negatives 394 no regression; the reconciler at
its single pre-existing finding. Round 42 closed; C1 S2c + BUG-111 + the NaN memo and ruling are on
main; the box-wide lock released.
