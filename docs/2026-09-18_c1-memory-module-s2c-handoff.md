# C1 S2c/S3 handoff — the synchronization emissions move into the module (D9), the one fold, BUG-111, the rollback (lane `core/c1-memory-module-s2c-0918`, opened 2026-09-18)

Successor of `docs/2026-09-18_c1-memory-module-handoff.md` (S0–S2b and the audit fix round, landed on
main at `f901c46c` / train r41 close `42023bd9`). Authority: [USER] Mike, 2026-09-18, verbatim, relayed
by the [AGENT] coordinator — cite as relayed: «(1) agree, (2) agree. Go ahead» — (1) ratifies the C1
charter's D1–D7, D9, D10 (`docs/2026-09-17_c1-memory-module-charter.md` §7), (2) rules BUG-111's fix =
option (i), canonical-path keys at emission (record: `docs/2026-08-31_qrow-rulings.md`, «The C1 charter
ratification and BUG-111 ruling record (2026-09-18)»). Every decision below is [AGENT] unless marked
[USER]. Base: main `42023bd9`. Worktree `.claude/worktrees/c1-successor`.

## 0. Where the lane is (kept current; the park statement is §7)

- **S2c-i** — LANDED on the branch as the gated runtime commit `f1ad88c3` (§1, §2): the label is an
  ORDERED list of memory-model events, the registry applies EMIT their synchronization, BOTH folds live,
  the whole-corpus + raft-twin audit says EQUAL (0 mismatches). Records commit: this file's first
  version + `docs/evidence/2026-09-18_c1-memory-module-s2c/`.
- **S2c-ii** — LANDED on the branch as the gated runtime commit `fc4e5d6b` (§1, §2): the one fold IS
  `raceUpdate` (no `ctx`/`sPre`/`tsPre`); the registry arms and their helpers deleted; the tracer's
  audit retired; the inventory at 72 rows. Choice trace byte-identical to main's (corpus and twin);
  the official detector-soundness run: §3.
- **BUG-111 fix (i)** — DONE on the branch: rows `96f2d72d` (+ records `12e196c7`: the born stage), the fix
  `a8e0cf95` (`Loc.canon` at every emitter; the disclosed FAIL→PASS flip; BUG-111 `Status: fixed`), the
  row-params correction `87a3c90b` (`sites=16`) — the end-state gate green but for the 5a pair (§2a). The
  final detector-soundness matrix: §2a.
- **Audit fix round** — DONE on the branch (2026-09-19; the section «Audit fix round (2026-09-19)» below):
  the adversarial audit `docs/2026-09-19_c1-s2c-audit.md` (branch `review/c1-memory-module-s2c-0918` @
  `41bef7bc`) returned FIX-FIRST, records and coverage class; its F1–F10 dispositions are applied in the
  gated commit `967712a3` (eight scope pins + the BUG-080 field-path pin, the 56 label-shape facts, the
  F5/F7/F10 docstrings, ledger §8) and the records commit that follows it on the branch. The wider-scope ratification
  stays PENDING [USER] (§6), now evidence-backed.
- **S3** (the rollback, cost B(b)/(c)): NEXT — the park statement §7 has the design sketch and the command.

## 1. What landed, per slice (gate lines in §2)

| slice | commit | content |
|---|---|---|
| S2c-ii | `fc4e5d6b` (runtime) | `raceUpdate (ev) (m') (r) := if m'.threads.size ≤ 1 then r else r.events ev.who ev.trace`; DELETED with tombstones: the old fold and its chan/sync/atomic arms, `raceChanEntryReads`, `racePairEvent`, `raceWakeEvent`, `raceCommitClauseEvent`, `raceWgAddEvent`, `chanApplyChan`, `dataEvents` (Multi.lean), `tryLockAcquired` (Machine.lean), `RaceState.chanObjAccess` (Race.lean); the section docstring rewritten («ONE FOLD over the step's LABEL»), `StepAction`'s docstring corrected; call sites in `EnumDedup`, `EnumDedupCheck`, `EnumDedupSound`, `PoolTrace`, `MultiStreams`, `CLI`, the tracer; `raceUpdate_single` restated; the tracer's fold-equality audit RETIRED (the TSV back to 15 columns; the ERROR rows' two stale trailing fields since S2b-ii fixed); the summarizer line removed; `scripts/mem-callsites.tsv` 78 → 72 (the six DETECTOR REGISTRY ARM rows retired — 14 raw sites gone), the SYNCHRONIZATION reasons reworded to the applies' own emissions |
| S2c-i | `f1ad88c3` (runtime) | `HbAction`/`MemEvent`/`AccessTrace := List MemEvent`/`traceAccesses` (Ops.lean); `chanValueLoc` moved up, `chanSendEntry`/`chanCloseWrite`/`selectPoll`/`atomicEvents`, `syncWord`/`syncEntryKinds`/`syncReleaseTailKinds`/`atomicOpKind` moved in from Race.lean (Machine.lean); `applyChanOp`/`commitClause`/`applySelectCore`+`SelectOutcome`/`applySelect`/`applySyncOpCore`/`applyTryLock`/`applySyncOp`/`applyAtomicOp` return their label; the four registry `Step` rules and `stepFn` arms carry it; `resumeThread`/`applyPairing` (+`arrivalPoll`, `pairSendEvents`, `pairRecvEvents`) return theirs; `ArrivalOutcome.commit evs cl env k`; `stepThread` labels the spawn (`.hb (.spawn n) :: tr.map (.attributed n)`), wake, pairing, arrival commit, select interception; `StepE ctx n …`; `StepM`/`StepMFine` `pair`/`pickPair`/`pickCommit`/`wake` labelled; `RaceState.hbAction`/`event`/`events`, `accessKeys` deleted (Race.lean); `raceFold` (the one fold) beside `raceUpdate` (adapted through `dataEvents` only where it read the label); `footprintsConflict` over `traceAccesses`, `RacyFine` with the index (NPDRF.lean); the tracer's fold-equality audit (`Acc.auditFold`, `foldMismatches`/`firstFoldMismatch`; summarizer line). Proofs restated arm-for-arm (the commit message lists them). |

## 2. Gate lines (captured `EXIT=`; tails in the evidence README)

- **S2c-i, `f1ad88c3`**: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock
  (`.tmp/with-lock.sh`: `mkdir artifacts/build-lock.d`, owner file, trap-protected release, wait-retry
  120 s) — (acquired after 0 s, 22:37:12–22:50:02 UTC) the committed runtime tree `f1ad88c3` (clean for `GoLean`/`Tests`/`scripts`; the evidence dir untracked — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 770 s**; **3676 cases: 3427 PASS / 249 expected FAIL** (`differential coverage summary: cases=3676 pass=3427 fail=249`); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `memory-module raw call-site inventory` ok (78 rows); `unseq scheduler` ok; `method-identity` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/ChoiceTrace.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row, judged stale because compiled semantic inputs changed). ZERO other drift; the negative baseline matched (394). Tail: `gate-tail-s2c1.txt`.
- **S2c-ii, `fc4e5d6b`**: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock
  (`.tmp/with-lock.sh`; acquired after 0 s, 23:02:27–23:15:15 UTC) the committed runtime tree `fc4e5d6b` (clean for `GoLean`/`Tests`/`scripts`; `docs/` dirty with the records edits — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 768 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `memory-module raw call-site inventory` ok (**72 rows**); every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row). ZERO other drift; the negative baseline matched (394). Tail: `gate-tail-s2c2.txt`.
- Static checks at S2c-ii: `scripts/check-mem-callsites` EXIT=0 (PASS, 72 rows); `gocore-eval-tests` 211 ok.
- Static checks at S2c-i: `scripts/check-mem-callsites` EXIT=0 (PASS, 78 rows — unchanged: the registry
  arms still exist in this commit; `chanValueLoc`'s move and the new emission tables add no raw site;
  `applyPairing`'s `chanCell` mentions are the same six, now binding the capacity). Eval tests
  (`gocore-eval-tests`) 211 ok, EXIT=0. Records checks at the S2c-i records commit: `scripts/check-bugs.sh`
  EXIT=0; `scripts/check-evidence-size` EXIT=0; `scripts/check-agents-alias` EXIT=0.

## 2a. BUG-111 — the rows' born state and the fix (charter §7 D7: a disclosed `Cases:` flip)

- **Rows** (commit `96f2d72d`, `Corpus/coverage/exec/race/{negative,free}`, `baselines/native-full.tsv`
  re-pinned 3676 → 3678 with the reason, `docs/BUGS.md` BUG-111 `Pinned-by: differential`, `Cases:
  race/negative/struct-tag-alias-field`): the alias row — `type aliasA struct{ f int }; type aliasB struct{ f
  int }`, `q := (*aliasB)(&a)`, goroutine 1 `a.f = 1`, goroutine 2 `_ = q.f`, main joined by two receives on a
  buffered channel (the lane's idiom in place of the entry's WaitGroup: the same HB shape, and the row's ONLY
  race is the pair through the two spellings) — is BORN on the wrong side: the S2c-ii binary ACCEPTS it
  (`status ok, value 1`; the control `raceWriteWrite` refuses `race`), pinned FAIL/racy; the guard (the same
  alias, main writes `c.f`, the child writes `q.g`, readout 12) is PASS/confluent
  (`bug111-born-state.txt`). Gate at the rows' commit: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (acquired after 0 s, 23:48:13–23:59:44 UTC) on the committed tree `96f2d72d`: **EXIT=1, 691 s**; **3678 cases: 3428 PASS / 250 FAIL** (the two new rows: the guard PASS as pinned, the alias row FAIL); `eval tests` 211 ok; `bug-index cross-check` ok; `re-pin guard` ok (0 PASS→non-PASS flips); `memory-module raw call-site inventory` ok (72); every other step ok. RED: the two 5a-class items (`certificate provenance` STALE on `CLI.lean`; the one cached certified row) PLUS ONE drift line on the new row itself — `race/negative/struct-tag-alias-field baseline[FAIL/racy] -> now[FAIL/lean-observation]`: the row IS FAIL as pinned, its born STAGE is `lean-observation` (the machine observes `ok` where `go run -race` reports), not the `racy` word the first pin guessed — the pin corrected to what the gate observed in the records commit that follows (the verdict never changed). ZERO other drift. Tail: `gate-tail-bug111-rows.txt`.
- **The fix** (commit `a8e0cf95`; the fix binary `06e78653…`): `Loc.canon` (Ops.lean) — the `.field` step's static `typeId` erased to
  `TypeId.canon`, the field NAME kept as the position, indices kept — applied by EVERY emitter: the `.data`
  keys (`Mem.*`), the `.syncWord` paths (`syncWord`), the `.chanObj` identities
  (`chanSendEntry`/`chanCloseWrite`/`selectPoll`), and the `HbAction` locations that key the clock tables
  (`atomicEvents`, the applies' `slotOp`/`closeOp`/`closeAcquire`/`syncAcquire`/`syncRelease`, the pairing
  tables). Machine paths untouched. The alias row flips FAIL → PASS (the DISCLOSED flip; the baseline re-pinned
  with the reason; BUG-111 `Status: fixed`, `Cases:` both rows); the guard stays PASS; NO other row changes
  (a change would have been a STOP, not a re-pin). Gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (acquired after 0 s, 00:06:46–00:20:13 UTC 2026-09-19) on the committed tree `a8e0cf95`: **EXIT=1, 807 s**; **3678 cases: 3428 PASS / 250 FAIL**; `eval tests` 211 ok; `bug-index cross-check` ok; `re-pin guard` ok (0 PASS→non-PASS flips; the report-only note `GREENED race/negative/struct-tag-alias-field FAIL -> PASS` — the disclosed flip); `memory-module raw call-site inventory` ok (72); every other step ok. RED: the two 5a-class items PLUS one line on the alias row — `baseline[PASS/racy] -> now[FAIL/racy]`: NOT a verdict but the racy-lane enumerator's REFUSAL by name, «run consumes more than --max-sites 8 choice site(s) — raise the case's sites bound (never truncated silently)» (`artifacts/coverage/latest.tsv`): the row has three goroutines (two children + main) and its enumeration reaches depth 9, beyond the lane's default `sites=8` that the first row line copied. With the harness's own invocation at `--max-sites 16` the fix binary certifies the row — `observations=1`, `status race`, 334 leaves, depth 9: EVERY enumerated path refuses; the guard at 8 certifies its one member `ok 12` (`bug111-enumerator.txt`). The row's `sites=` corrected to 16 in the next commit (a row-params correction, the lane's `map-range-iter` precedent), re-gated. ZERO other drift. Tail: `gate-tail-bug111-fix.txt`. **The row-params commit `87a3c90b`** (`sites=16`): `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (acquired after 0 s, 00:37:14–00:49:03 UTC) — **EXIT=1, 709 s**; **3678 cases: 3429 PASS / 249 FAIL** — the alias row PASS/racy as pinned (the DISCLOSED flip complete), the guard PASS; `eval tests` 211 ok; `bug-index cross-check` ok; `memory-module raw call-site inventory` ok (72); every other step ok. RED: exactly the two 5a-class items (`certificate provenance` STALE on `CLI.lean`; the SINGLE drift line `imported-goose/channel/google-search`). ZERO other drift: BUG-111's end state. Tail: `gate-tail-bug111-params.txt`. NOTE (the audit's F2, added at the fix round): this gate ran on a DIRTY tree — the negative-diff step's line reads «negative baseline diff matched (394 case(s)) but the record was made on a DIRTY tree (git_dirty=true)» (tail :98); the params tail itself does not say WHAT was dirty; by the lane's own pattern (the S2c-i/S2c-ii lines above disclose theirs as records edits under `docs/`) it was the records in progress, and the gated runtime files were committed at `87a3c90b` — a note, not a failure; this line did not disclose it until the audit. ALSO (F2): the REPORT-ONLY cross-ledger reconciler carried, from the rows commit `96f2d72d` onward, «[01] C4 HIGH the language-coverage ledger §8 arithmetic is computed over a STALE baseline: §8 says 3676 cases / 3428 PASS / 248 FAIL; the tracked baseline at this tip is 3678 / 3430 / 248» — in the tails `gate-tail-bug111-rows.txt` (:58), `gate-tail-bug111-fix.txt` (:69) and `gate-tail-bug111-params.txt` (:55); absent at S2c-i/S2c-ii. The lane added two rows and did not refresh §8; the finding was not disclosed here until the audit. Closed at the fix round (ledger §8 refreshed to 3686 = 3438 / 248 with the eight new rows; the reconciler at the fix-round tree reports no C4 and no C5).

**Baseline tally vs gate tally (the audit's F8).** The baseline header says 3678 = 3430 PASS / 248 FAIL; the gate above says 3429 / 249. Both are correct: the gate counts the cached-certified row `imported-goose/channel/google-search` as FAIL (the 5a-class stale certificate — a candidate is judged stale because compiled semantic inputs changed) while the baseline pins it PASS; the same one-row offset exists at every gate on this branch (3676: baseline 3428/248, gate 3427/249) and disappears at the train's step 5a re-certification. Every gate line on this page is the gate's count; every baseline figure is the header's. Detector-soundness after the fix (the FINAL official matrix, tree `87a3c90b`):
  EXIT=2 (the 9 `params-omit-sites=` membership refusals, as always), 1,740 s, worker-pool exit 0, **641 rows** (639 + the two BUG-111 rows): **HOLE 0, possible-HOLE 0**, agree-DRF 503 (the S2c-ii 502 + the guard: gc clean 5/5 at both procs, machine DRF), **agree-race 37** (the S2c-ii 36 + the alias row: gc RACE 5/5 at GOMAXPROCS 1 and 8, machine RACE-ALL 1/1 member at `sites=16`), over-refusal 6 (the same six: BUG-041's O1 residual and the five ruled `race/gomem-only/*` rows), refused 9, uncertified 86 — every pre-existing cell unchanged (`detector-soundness-bug111.txt`; the intermediate matrix at `sites=8`, whose one possible-HOLE was the alias row's enumerator refusal, is `detector-soundness-bug111-sites8.txt`).

## 3. The S2c-i audit — RESULT (the S2a pattern: both accounts in ONE binary, per step)

- **Whole corpus** (`scripts/choice-trace-corpus --dump --jobs 6`, the standing 2 exclusions, 6 streams
  per row; binary `7eb5de44…`): **21,835 (row, stream) results, fold-equality mismatches 0** (the
  `foldMismatches` column sums to 0 over every result line; `alarms` 0; `violations` 0;
  driver-agreement mismatches 0); statuses = S2a's census exactly (ok 17,957 / panic 2,284 / unsupported
  1,095 / **race 252** / deadlock 162 / fatal 54 / stuck 30 / ERROR 1 — the pre-existing
  `arrays/materialization-budget/over-budget` lowering refusal). The 252 race verdicts are steps on
  which BOTH folds threw `raceDetected` (a one-sided verdict is a mismatch by construction). Evidence
  `fold-audit-s2c1.txt`.
- **The raft twin** (`raft-twin/probeTwin{Choice,Single,Elect,Perturb,Ticks}` × 6 streams on the
  pinned `baselines/pins/twin-chdriver.wire.json`, fuel 10,000,000): **30/30 results ok, 0 fold
  mismatches, 0 alarms** (S2c-i binary 1,189 s wall; main's binary 1,157 s). Evidence
  `twin-audit-s2c1.txt`.
- **Choice-trace byte-identity vs main `42023bd9`'s certified binary `42b7bf1a…`** (D4): whole-corpus
  sorted consumption dumps **23,679 records each, sha256 `0df092ee…` both, `cmp` EXIT=0**; the twin's
  sorted dumps `cmp` EXIT=0 (`twin-audit-s2c1.txt`).
- **Positive control** (`probe-FoldOrder.lean`/`.log`): two labels that differ ONLY in the order of
  `Mutex.Unlock`'s state Add and its release action fold to DIFFERENT detector states (the access sits
  at the pre-release epoch in one, the bumped epoch in the other — `shadow false`, clocks equal) and
  `Acc.auditFold` reports `fold-mismatch: … states differ (clocks true, shadow false, …)`; equal folds
  report nothing; a one-goroutine pool is inert for both. So the instrument sees an ORDER difference,
  which is the design point §6b of the predecessor handoff put on the table.

**S2c-ii (the switch) — the regression evidence.** Choice trace vs main `42023bd9`'s certified binary
`42b7bf1a…` with the S2c-ii binary `b3354990…`: whole corpus sorted dumps **23,679 records, sha256
`0df092ee…` = main's, `cmp` EXIT=0**; statuses census identical (ok 17,957 / panic 2,284 / unsupported
1,095 / race 252 / deadlock 162 / fatal 54 / stuck 30 / ERROR 1); the raft twin **30/30 ok, 14,360
consumptions, sorted dumps `cmp` EXIT=0, sha256 `3b0b4c0a…` = main's** (`choice-trace-s2c2.txt`,
`twin-audit-s2c2.txt`). The official detector-soundness matrix (`scripts/detector-soundness --select
in-scope --jobs 6`, the fixed runner) on the S2c-ii binary: EXIT=2 (INCOMPLETE for the 9 `params-omit-sites=` membership refusals, exactly as at the fix round), 1,729 s, worker-pool exit 0, 639 rows: **HOLE 0, possible-HOLE 0**, agree-DRF 502, agree-race 36, over-refusal 6 (`race/free/array-dyn-index-read-write` = BUG-041's O1 residual and the five `race/gomem-only/*` rows of the RULED go_mem-RACY / TSan-GREEN lane), refused 9, uncertified 86 — cell for cell the fix round's official record (`detector-soundness-s2c2.txt`). The one fold reads the label and reproduces the deleted arms' verdicts on every in-scope row.

What the audit does NOT cover: configurations the corpus never reaches (the S2b-i theorem's role for
the data trace); for the synchronization events there is no universal companion theorem in this slice
— the two accounts are compared executably on every traced step, and the old account is deleted at
S2c-ii on that evidence plus inspection (§4). Charter §6's «0 unrowed differences» holds with 0
differences.

## 4. [AGENT] choices with the alternative named

| choice | taken | alternative (not taken) | why |
|---|---|---|---|
| the label's shape (§6b's OPEN design point) | ONE ordered list of memory-model events, `MemEvent := access ∣ hb ∣ attributed`, `raceUpdate` = one fold (`RaceState.events`) | (a) two access lists per event, before/after the HB hook; (b) `ev.action` + carried pre-state facts with the HB arms kept | (a) hard-codes ONE hook per step (Unlock has an access AFTER its release, a close a write BEFORE; a select commit has poll reads then an action) and (b) keeps two accounts, which is the defect D9 removes; the list is what gc's instrumentation IS — a sequence of TSan calls in program order — and the positive control shows the order matters |
| where the HB constructors are interpreted | `RaceState.hbAction` (Race.lean), the ONE place a clock moves | interpret inline in the fold | one table, enumerated, a new constructor is a compile error at the interpreter and at every emitter |
| attribution | `MemEvent.attributed who e` (recursive wrapper) | a `who` field on every event; a `List (Nat × MemEvent)` pool label; `StepE` returning two lists | the sequential `Step` label never needs an actor; the wrapper is used at exactly two pool sites (the child's entry read, the partner's slot transit) and folds under the other id in one line |
| `StepE` learns the child's index | `StepE ctx n c σ c' σ' efs tr`, `n = m.threads.size` at every use (`StepM.thread`, `StepMFine.thread`, `RacyFine`) | a label-lifting function on `StepM.thread` dispatching on `efs`; attribution «to the child of this step» resolved by the fold from `ev.action` | the spawn label must name the child (attributing the dispatch read to the parent changes verdicts: a later parent access to the receiver would be same-goroutine and never conflict); an index on the relation is the honest way to say it, and the fold stays action-blind |
| `ArrivalOutcome.commit` carries `evs` | `.commit evs cl env k` | a poll trace field; re-running `evalClauses` in `stepThread` from the pre-config | the arrival commit's label is the select's poll over ALL clauses plus the commit; the analysis already evaluated them; a re-derivation from the pre-configuration is the footprint-table shape the charter retires |
| the arriving op's entry emission on the pairing path | `arrivalPoll bc` off the would-block shape (`chanSendEntry` for a send, `selectPoll evs` for a select) | emit at `arrivalCases` (the pure analysis); emit from `stepThread`'s `c` | `bc` is the arriving op's own identity built by `chanArrivalPlan`/`selectArrivalCases` for this arrival; the analysis is a relation premise and must not emit |
| the pairing tables | `pairSendEvents loc cap j` (rendezvous at cap 0 else sender-slot then partner-recv-slot) and `pairRecvEvents loc cap bufEmpty j` (rendezvous at an empty buffer else recv-slot then partner-send-slot) | the fold's literal `if cap == 0 … else if buf.size > 0 …` guards | on reachable states identical (a sender parks at an empty buffer only at capacity 0; a nonempty buffer at capacity 0 cannot be constructed — `applyChanOp` pushes only under `buf.size < capacity`); the apply's own branch is the honest condition; the audit's EQUAL on every traced pairing is the evidence |
| `applyTryLock`'s `acquired` | the apply's own outcome (`tryAcquire = some ∧ ¬ spurious`) | `tryLockAcquired op pre post` re-derived from the cells | the apply knows; equal by the case analysis in the S2c-i design notes (the four pre/post shapes) and by the audit |
| the sync tables' home | Machine.lean, beside the applies that emit them (moved from Race.lean, return `AccessTrace`) | leave them in Race.lean and re-export | Race.lean is DOWNSTREAM of Machine.lean (it imports StepFn); the emitter cannot see them there |
| the transitional old fold | `raceUpdate` reads the label only through `dataEvents` (accesses, attribution looked through) on its two label-reading arms; every registry arm untouched | rewrite the old fold to ignore the new events some other way | on a private data step the label has no other kind of event, on a spawn the child's accesses are exactly the S2b account — the old fold is byte-for-byte the detector of record (zero drift by construction), which is what makes the audit's EQUAL meaningful |
| the audit's equality | STRUCTURAL `RaceState` equality (derived `BEq`), incl. the clock tables' insertion order; error class + message on failures | equality up to a semantic quotient | the two folds perform the SAME clock operations in the SAME order or they do not — structural equality is the stricter, cheaper check, and the tracer continues with the fold of record |
| BUG-111's canonical form | `Loc.canon`: the same `Loc` type with the `.field` typeId erased to one canonical `TypeId.canon` (`⟨"$canon"⟩` — not a Go identifier) | a separate `KeyPath := Addr × List (String ⊕ Int)` type for shadow keys (the spike's `pathsDisjoint` shape) | the key stays a `Loc`, so `ShadowKey`, `locPrefix`/`overlap`, the clock tables, `Ord` and every lemma keep their types; on canonical keys structural prefix IS the spike's canonical prefix (`f1_canon`'s relation) |
| what BUG-111's fix canonicalizes | EVERY emitted location — `.data`, `.syncWord`, `.chanObj` keys AND the `HbAction` locs that key the channel / sync / atomic clock tables | (a) the `.data` keys alone (the entry's letter); (b) canonicalize at CONSUMPTION in the fold | (a) would leave the sync words structural, and a canonical data path would then no longer prefix-overlap the primitive's words — the copy-beside-Lock class at FIELD paths (a primitive inside a nested struct; pinned since the audit fix round by `race/negative-sync/nested-mutex-copy`) would silently OPEN; the tracked root-copy BUG-080 pins would NOT have (their `.base` key prefixes every path) — the audit's F3 precision; the clock tables keyed structurally would split on an alias — NOT a residual but FALSE races, the audit's F1 showed (main's binary refuses race-free alias handoffs). One rule at the ONE place the module speaks — emission — is the charter's shape; (b) would put a second account in the fold |
| the rows' join idiom | two receives on a buffered channel (the lane's idiom) | the entry's `sync.WaitGroup` | the same happens-before shape, no `sync` import in `race/negative`, and the row's only race stays the alias pair |
| a delivered panic's label | `[]` (the standing `deliver` convention); a `.panicking` CONFIGURATION returned by an apply keeps the apply's label (a send on a closed channel carries its entry read; `wgAdd`'s negative-counter panic carries its entry pair and its release-merge) | strip the label on every panicking successor | gc records `chansend`'s entry read before the closed-channel panic and `Add`'s ReleaseMerge before the negative-counter check (waitgroup.go:81); the old fold recorded exactly these (`raceChanEntryReads` on every outcome, `raceWgAddEvent` regardless of outcome) and the audit confirms |

## 5. Proved vs owed after S2c-i

Proved (kernel-checked, warning-free core): every coherence and preservation theorem restated over the
event label (the commit message lists them by name): `stepFn_sound`/`step_complete`/
`step_complete_any_wf` with the four registry rules carrying the apply's label; `stepMulti_sound`/
`stepM_complete` with the spawn, wake, pairing and arrival-commit labels; `step_preserves_wf` and the
`*_wf` family with the extra component; `stepFn_consumption` and the stream lemmas; MultiStreams'
obliviousness. S2c-ii and BUG-111 added no theorem and weakened none (`raceUpdate_single` restated; the `Mem.*_eq`
statements say `.data l.canon`). Owed: a universal companion for the synchronization emissions (not
chartered — recorded as a possible later theorem: the one fold on `stepThread`'s event equals the deleted
registry account per action; the executable S2c-i audit stands in for it); the disjoint-path frame law
on the REAL `storeLoc` for the canonical relation (the spike's `f1_canon` on the stub of the same shape —
porting is S3/C3 work); S3's per-arm «panic ⇒ store unchanged» theorems (charter §6).

## 6. PENDING [USER]

PENDING [USER] (evidence-backed since the audit fix round, 2026-09-19): **the ratification of BUG-111 fix
(i)'s WIDER scope.** The ruling's letter (`docs/2026-08-31_qrow-rulings.md`) names the `.data` keys; the
landed fix canonicalizes EVERY emitted location — the `.data` keys AND the sync-word / channel-object keys
and the `HbAction` clock-table locations. The adversarial audit (`docs/2026-09-19_c1-s2c-audit.md` F1, its
table) showed the wider scope is NECESSARY, not a preference: on main's certified binary `42b7bf1a…` six
alias programs are WRONG — three missed races (a nested Mutex's state word, an array-element field, the
WaitGroup `sema` word, each under a struct-tag-compatible alias) and three–four FALSE races (one Mutex /
RWMutex / Once / atomic word under two spellings, whose clock tables split) — and RIGHT on the fix binary,
gc `-race` agreeing on every one; a `.data`-only canonicalization would fix only the landed row and leave
all six. The fix round pinned each key kind with a corpus row (eight rows, BUG-111's and BUG-080's `Cases:`
lines; «Audit fix round (2026-09-19)» below), so a later narrowing to the letter flips them visibly. The
[USER] may still narrow the scope to the `.data` keys, knowing which verdicts reopen (those eight rows go
red). The disclosure's BUG-080 argument, stated precisely (the audit's F3): a `.data`-only canonicalization
would have reopened the copy-beside-Lock class at FIELD paths — e.g. a primitive inside a nested struct,
where the copy's canonical key `.field o $canon "in"` no longer prefix-overlaps a structural sync-word path
`.field (.field o outN "in") inN "mu"` — which NO tracked pin covered until `race/negative-sync/nested-
mutex-copy` (gc RACE 5/5; both binaries refuse); the tracked BUG-080 pins copy ROOT variables (`c := b`),
whose `.base` key prefixes every path whatever the typeIds, and would NOT have opened. No pre-existing
corpus row's verdict changed (the differential, the choice trace on the 3,676 pre-existing rows and the
detector-soundness matrix say so).

## Audit fix round (2026-09-19) — the audit's F1–F10 dispositions, applied

The adversarial audit of this branch (`docs/2026-09-19_c1-s2c-audit.md`, on `review/c1-memory-module-s2c-0918`
@ `41bef7bc`; ordered by [USER] Mike 2026-09-19 «Go ahead with the audit», relayed) returned **FIX-FIRST,
records and coverage class** — no WRONG-VERDICT, no UNSOUND-PROOF / COHERENCE-GAP, no FAIL-OPEN introduced, no
gate weakening, scope clean. Dispositions [AGENT] coordinator, disclosed at the merge ask; applied by the
[AGENT] fix-round worker in ONE gated corpus/tests commit **`967712a3`** and ONE records commit —
the one that follows `967712a3` on the branch. No machine-semantics change (the Lean edits are docstrings, a header comment and the
test module); no theorem touched.

| finding | disposition | where |
|---|---|---|
| **F1** RECORDS-CLAIM/coverage — the fix's necessary scope is wider than the ruling's letter (`.data`), disclosed, and NOTHING pinned the wider half; six wrong verdicts on main's binary | one corpus row per KEY KIND, each born on the RIGHT side under the fix binary `06e78653…` and gc `-race` agreeing (5/5 at GOMAXPROCS 1 and 8; `fixround-gc-transcript.txt`), main's certified binary `42b7bf1a…` WRONG on every alias row (`fixround-machine-{racy,free}.txt`): `race/negative/struct-tag-alias-array-field` (`.data` + `.index`; gc RACE, candidate RACE-ALL 334 leaves, main `ok` — its enumerator cannot even finish at `sites=16`: HOLE), `race/negative-sync/struct-tag-alias-nested-mutex-copy` (`.syncWord` at a nested alias path; gc RACE, candidate RACE-ALL 11 leaves, main `ok` on 148 leaves: HOLE), `race/negative-sync/struct-tag-alias-nested-wg-overwrite` (the wg `sema` word — **reshaped**, below; gc RACE 5/5, candidate RACE-ALL 11 leaves, main `ok`/`panic` members, no refusal: HOLE), `race/free-sync/struct-tag-alias-mutex-handoff` (membership {1, 2}, 3,116 leaves; main RACE-ALL: FALSE race), `race/free-sync/struct-tag-alias-rwmutex-handoff` (singleton 2; main RACE-ALL), `race/free-sync/struct-tag-alias-once-observe` (singleton 1, 1,441 leaves; main RACE-SOME), `race/atomics-free/struct-tag-alias-flag-handoff` (membership {0, 1}; main RACE-SOME). All on BUG-111's `Cases:` line (`Status: fixed` unchanged; `check-bugs.sh` EXIT=0). Baseline 3678 → 3686 = 3438 / 248, header reason; no existing row changed. The ratification of the wider scope stays PENDING [USER] (§6), now with this evidence. | `Corpus/coverage/exec/race/{negative,negative-sync,free-sync,atomics-free}`, `baselines/native-full.tsv`, `docs/BUGS.md` BUG-111 |
| F1 (placement, [AGENT]) | the brief read «racy rows under `race/negative/`, false-race rows under `race/free/`»; the sync-using programs went to `race/negative-sync`, `race/free-sync` and `race/atomics-free` — the packages that already import `sync`/`sync/atomic` — keeping `race/negative` sync-free as the lane chose for the BUG-111 row (§4). The array-field row, sync-free, is in `race/negative`. | `cases.tsv` comments |
| F1 (the WaitGroup row, [AGENT] reshaping) | the audit's litmus `wgAliasNestedCopyBesideWait` (a copy of the nested struct beside a parked Wait's first-waiter `sema` WRITE) is RACE-SOME — racy only where the waiter parks before the Done (gc's sampler 0/5); the racy lane pins «every path refuses» and the membership harness treats a `-race` red draw as a failed draw, so no lane pins a RACE-SOME program honestly. The row races the SAME word on every path instead: the child's `Add(1)` from counter 0 through the alias performs gc's realized `race.Read(&wg.sema)` (waitgroup.go:115 — the `wg-overwrite` pin's access, at a FIELD path), main OVERWRITES the nested struct; both accesses on every path, HB-unordered. gc RACE 5/5 at both procs; the fix binary RACE-ALL; main `ok`/`panic` (the overwrite resets the counter under the child's Done) — the same HOLE, pinned. | `race/negative-sync/struct-tag-alias-nested-wg-overwrite` |
| **F2** RECORDS-CLAIM — an undisclosed reconciler C4 HIGH from the rows commit onward; the params gate's dirty tree undisclosed | ledger §8: ONE current tally «3686 cases, 3438 PASS / 248 FAIL», the 2026-09-15 tally demoted («Previous tally, then current …»); the reconciler at the fix-round tree: no C4, no C5 (C9 = the 5a-class STALE certificate; C13 pre-existing). §2a above now names the params gate's dirty tree (records edits under `docs/`, a note) and lists the three tails that carried the C4 line (`-rows` :58, `-fix` :69, `-params` :55; absent at S2c-i/ii). | `docs/language-coverage-ledger.md` §8; §2a |
| **F3** RECORDS-CLAIM — the disclosure's BUG-080 argument is TRUE for the field-path class, not for the tracked root-copy pins; the class had no pin | wording fixed in §4 and §6 (exactly: holds for the FIELD-PATH class; the tracked pins copy ROOT variables and would not have opened) and in BUG-111's / BUG-080's entries; the class pinned: `race/negative-sync/nested-mutex-copy` (`raceSyncNestedMutexCopy`; gc RACE 5/5; BOTH binaries refuse, 11 leaves each) on BUG-080's `Cases:` line ([AGENT]: the class it pins; BUG-111's entry cites it). | §4, §6; `docs/BUGS.md` BUG-080/BUG-111 |
| **F4** GUARD GAP — after S2c-ii the ORDER inside a label is review-only | `Tests/GoCoreEval.lean` `labelShapeFacts`: **56** per-arm facts on fixture stores (`labelCells`, 16 cells) asserting the EXACT `AccessTrace` each emitting arm emits — `applyChanOp` ×7 (send commit/park/closed, recv buffered/closed-empty/park, close), `commitClause` ×3, select commit/park/wake, Mutex Lock/park/Unlock, RWMutex RLock/RUnlock/Lock/Unlock + TryRLock ×2 + TryLock ×2, WaitGroup Add(+1 from 0)/Done/Wait fast/Wait park, Once fresh/observe/park/complete, Mutex TryLock ×3, atomics Load/Store/Add/Swap/CAS ok/CAS fail, `resumeThread` ×8, `pairSendEvents`/`pairRecvEvents` ×4, the spawn ×3 (a plain function: `[spawn 1]`; a pointer-box value-receiver dispatch: `[spawn n, attributed n (read receiver)]` with `n = threads.size`, from thread 0 and from thread 1). Every fact was `#eval`ed first (`.tmp` scratch, the standing rule) and is asserted with `==` on the derived `DecidableEq`; a permutation or omission fails the eval step BY NAME. The table lives in the test module's docstring. Sequential warm: `lake build gocore-eval-tests` EXIT=0, `lake exe` EXIT=0, **267 ok** (211 + 56), 0 FAIL, warning-free (`fixround-eval-tests.txt`). Two mechanics worth recording: `main`'s do-block is at the elaborator's recursion limit (`set_option maxRecDepth 4096 in` precedes it, and my first draft displaced that option — «maximum recursion depth»), so the facts live in their own `IO Bool` called once from `main`. | `Tests/GoCoreEval.lean` |
| **F5** NIT — Once's completion-observing Do records `@done` BEFORE its acquire; TSan acquires first | recorded, not fixed: a comment at the `syncEntryKinds` row and a line in BUG-111's entry (verdict-neutral at program level — the read's only conflicting partner is a plain overwrite of the Once, racy in some schedule for gc too; per schedule the machine refuses where gc's acquire-first read would be ordered; pre-existing — main's fold had the same order). A reorder is a semantic change and would need its own row; the label-shape fact pins the order as it stands. | `Machine.lean` `syncEntryKinds`; `docs/BUGS.md` BUG-111 |
| **F6** NIT — gc's `racesync` / `elemsize == 0` `racenotify` accumulate HB in ONE sync object; the machine is go_mem-faithful, stricter | documented alignment fact in latitude inventory C10 (no status change; cites the audit and its litmus `chanStructAccum`) | `docs/2026-08-11_latitude-inventory.md` C10 |
| **F7** NIT — `selectPoll` reads EVERY send clause; gc only those reached in its random `pollorder` | `selectPoll`'s docstring now says «every send clause — the UNION over gc's random `pollorder`» with the select.go lines and the litmus (`selectPollVsClose`: gc 2–3/5, the machine on every path); the same fact in C10 | `Machine.lean` `selectPoll`; C10 |
| **F8** NIT — baseline header 3678 = 3430/248 vs gate 3429/249 | reconciled once in §2a («Baseline tally vs gate tally»): the gate counts the cached-certified `imported-goose/channel/google-search` row as FAIL (the 5a-class stale certificate) while the baseline pins it PASS — a one-row offset at every gate on the branch, gone at the train's step 5a | §2a |
| **F9** NIT — `probe-FoldOrder.lean` compiles only at `f1ad88c3` | the evidence README's row says so (historical evidence; the live order guard is `labelShapeFacts`) | evidence README |
| **F10** NIT — `MultiStreams.lean` :41 listed the deleted `raceUpdate_oblivious` as live | header corrected (points at the stage-B tombstone) | `GoLean/GoCore/MultiStreams.lean` |

**Gate (the fix-round commit `967712a3`).** `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (`.tmp/with-lock.sh`; acquired after 0 s, 03:18:14–03:30:35 UTC 2026-09-19) on the committed tree **`967712a3`** (clean for `Corpus`/`GoLean`/`Tests`/`baselines`/`scripts`; three `docs/` files dirty with THIS section's records in progress — `docs/2026-08-11_latitude-inventory.md`, this handoff, the evidence README — so the negative-diff step notes `git_dirty=true`, disclosed here): **EXIT=1, 741 s**; **3686 cases: 3437 PASS / 249 FAIL** (`differential coverage summary: cases=3686 pass=3437 fail=249` — the gate's count; the baseline header says 3438 / 248: the one-row stale-certificate offset of §2a's F8 paragraph). The eight new rows PASS at their lanes as pinned (`artifacts/coverage/latest.tsv`): the four racy rows «every enumerated path refuses» (the array-field row 334 leaves at `sites=16`, the three `negative-sync` rows 11 leaves each), `rwmutex-handoff`/`once-observe` confluent, `flag-handoff` membership `enumerated=2 exhibited=2 draws=8 (stopped at the members=2 pin)`, `mutex-handoff` membership `enumerated=2 exhibited=1 draws=32 (pin members=2 NOT reached — 1 distinct drawn) unexhibited=1` — gc's 32 draws all gave `2` (main's critical section first); the `1` member (the child's first) is the machine's, DRF by mem#locks either way, an ORDER the sampler did not land on at the gate budget (the `rw-tryrlock-acquire` precedent). `eval tests` **267 ok** (211 + the 56 label-shape facts); `core build (warning-free)` ok; `core totality audit` ok; `memory-module raw call-site inventory` ok (72 rows); `bug-index cross-check` ok; `re-pin guard` ok (0 PASS→non-PASS flips); every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row). ZERO other drift; the negative baseline matched (394). The REPORT-ONLY reconciler: 2 findings — C9 (the same stale certificate) and the pre-existing C13 (doc sites naming an off-pin Go patch version); **no C4, no C5**. Tail: `gate-tail-fixround.txt`. The gate rebuilt the binary: `da7bb837…` (the fix binary `06e78653…` plus the fix round's docstring/comment edits; the machine's behaviour is unchanged — the choice trace below is the evidence).

**Choice trace vs main's certified binary `42b7bf1a…`.** `scripts/choice-trace-corpus --dump --jobs 6` on the audit's 543-id multi-goroutine subset (`subset-ids.txt` on the review branch — the ids the audit itself compared; the two standing exclusions and the two BUG-111 rows absent, the fix round's eight rows not in it) with the gate-built fix-round binary `da7bb837…` and main's certified binary `42b7bf1a…` (`.tmp/golean-main`): **542 ids traced per side** (the 543rd is the audit's known frontend export refusal), 3,252 (id, stream) results each, 0 menu-invariant violations, 0 self-check alarms, 0 driver-agreement mismatches; the sorted per-consumption dumps (chunk headers dropped) **17,052 records each, sha256 `890c2e7a…` both, `cmp` EXIT=0** — byte-identical on every pre-existing row traced (the audit's 17,060-record figure counts the eight chunk-header lines). Transcript `choice-trace-fixround.txt`.

**Detector-soundness (official runner, `--select in-scope --jobs 6`), the fix-round binary.** `scripts/detector-soundness --select in-scope --jobs 6 --out artifacts/detector-soundness-fixround` on the gate-built binary `da7bb837…` at `967712a3`, `go run -race` live at the pin (03:33:23–04:02:31 UTC, **1,748 s**): **EXIT=2** (the standing 9 `params-omit-sites=` membership refusals — `sync/trylock/*`, `sync/promoted-mutex/trylock-expr`, `sync/out-of-scope-trylock/trylock-uncontended` — as at every recorded run), worker-pool exit 0, gc-infra 0, unclassified 0; **649 rows** (the 641 of the lane's FINAL matrix + the eight new rows): **HOLE 0, possible-HOLE 0, agree-race 41** (37 + the four racy rows: `struct-tag-alias-array-field`, `struct-tag-alias-nested-mutex-copy`, `struct-tag-alias-nested-wg-overwrite`, `nested-mutex-copy` — each gc RACE 5/5 at GOMAXPROCS 1 and 8, machine RACE-ALL 1/1 members), **agree-DRF 507** (503 + the four race-free rows: `struct-tag-alias-mutex-handoff`, `-rwmutex-handoff`, `-once-observe`, `struct-tag-alias-flag-handoff` — each gc clean 5/5 at both procs, machine DRF), over-refusal 6 (the same six: BUG-041's O1 residual and the five ruled `race/gomem-only/*` rows), refused 9, uncertified 86 — every pre-existing cell unchanged (`detector-soundness-fixround.txt`, with the ten rows' matrix lines).

**Records checks at the records commit.** on the records tree (this section complete): `scripts/check-bugs.sh` EXIT=0 («ok (111 bug(s); pinned cases behave as claimed)» — BUG-111's nine and BUG-080's five `Cases:` ids all PASS under `Status: fixed`, the symmetric rule (3)); `scripts/check-evidence-size` EXIT=0 (PASS — 1,840 tracked files, 0 new offenders; this lane's evidence dir 196 KiB, largest file under the 256 KiB cap); `scripts/check-agents-alias` EXIT=0; `scripts/check-spec-anchors` EXIT=0 (869 spec# + 261 mem# + 26 godoc citations resolve at the pin); `tools/reconcile-records` EXIT=0 with 2 findings — C9 (the 5a-class STALE certificate, `CLI.lean`) and the pre-existing C13 (79 doc sites naming an off-pin Go patch version) — **C4 gone, no C5** (no ledger reds cell backticks a non-existent case id; the eight new ids are cited in prose and in BUGS.md `Cases:` lines only). Static checks on the gated tree are in the gate line above.

## 7. Where the lane stopped; the next command — PARKED 2026-09-19 (UTC)

PARKED (re-parked 2026-09-19 after the audit fix round) at the records commit that follows `967712a3` on the branch, over the
gated fix-round commit **`967712a3`** (the audit's F1–F10 applied — the section above), which sits on the
records commit `2ce323ff` over the gated corpus-params commit **`87a3c90b`** (BUG-111's end state; §2a),
which sits on the BUG-111 fix `a8e0cf95`, the born-stage records `12e196c7`, the red-first rows `96f2d72d`,
S2c-ii `fc4e5d6b` (+ records `91a28366`), S2c-i `f1ad88c3` (+ records `b3bb801f`); branch
`core/c1-memory-module-s2c-0918`, base main `42023bd9`; worktree `.claude/worktrees/c1-successor`, clean;
nothing merged, nothing pushed; main untouched. Every runtime commit is gated (§2, §2a); the last gate is
green but for the 5a pair. D9 DONE (S2c). BUG-111 FIXED (fix (i), disclosed flip). OPEN: **S3**.

THE NEXT COMMAND (S3 — the rollback, cost B(b)/(c); charter §6): the sharing that makes `Array.modify` copy
is now ONLY `deliverS`'s reference to the pre-apply store `s` (the detector's `sPre` is gone with S2c-ii —
`raceUpdate` reads the label — and `execProgLoop` drops `m` after `stepMulti`), plus the enumerator's fork
copies (B(c)). `deliverS s k ch next r` needs `s` only on the `.panic` path, and a thrown panic returns no
store. Plan of record (sketched, [AGENT]): split every store-bearing apply into a VALIDATE phase that
borrows `s` (every panic point: `valueAsLoc`, `arrayGet`, `validateSlice`, the map-key hash, the target
chain checks — reads only) and a COMMIT phase that consumes `s` (writes only, cannot panic — `storeLoc` at
a validated path, `Store.alloc`, the payload writers), so `stepFn`'s arm is `match toResult (validate …)
with | .panic msg => (.panicking …, s, …) | .ok plan => commit s plan …` and `s` is referenced on ONE path
after the validate call; the per-arm theorem «`.panic` ⇒ the store is `s`» (charter §6) is then the
statement that the commit phase is unreachable on a panic. The S0 audit's eight W arms
(`docs/evidence/2026-09-18_c1-memory-module/README.md` «The write-then-panic audit»: `allocNew`,
`makeSlice`, `makeMap`, `makeChan`, `clearSlice`, `copySlice`, `appendSlice`, the dead `storeMany`) are
where the phases must be REORDERED (hoist `valueAsLoc tv` before the alloc in makeMap/makeChan — a pure
reordering; state or prove the header/backing invariant `offset + cap ≤ backing.size` so the element loops
cannot fail after `validateSlice`); the V arms are reorganizations. Targets (charter §6): `alloc_new`
linear, n = 32k < 1 s; the (h) scalar phase within 1.2× of h = 0; the OWED `append_grow` ×2 ratios ≤ 2.2
(MISSED at S1: ×2.5–2.8). Measure BEFORE with main's binary and AFTER with
`docs/evidence/2026-09-11_bug090-rediagnosis/run-probes.py --plan full` (3 runs, medians, net of the empty
probe); a miss is reported as a miss and carried to C4 with the reason. Gate; choice trace byte-identical;
the detector-soundness matrix unchanged. Then the merge ask for the whole branch (S2c + BUG-111 + S3).

The pre-merge adversarial audit is ASKED at this park (charter §8; scope and waiver are the [USER]'s):
the (b)/(c) bar of `docs/2026-09-18_c1-memory-module-audit.md` — (b) the label as an ORDERED list of
events per rule (a rule whose emission order differs from gc's instrumentation order; an emission the fold
attributes to the wrong goroutine; a wake or pairing whose action differs from the deleted arm's); (c) what
guards the emit/peek discipline now (the 72-row inventory) and what guards the ORDER (nothing mechanical
beyond the S2c-i audit's evidence and the positive control); BUG-111's canonical form (`TypeId.canon`
inside a `Loc` — a key that is not a machine path; every emitter covered? the enumerator's `stepNeeds`
mirrors untouched?); the extension of the fix to the HB locations (§6).
