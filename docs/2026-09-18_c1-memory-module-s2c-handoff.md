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
  (a change would have been a STOP, not a re-pin). Gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (acquired after 0 s, 00:06:46–00:20:13 UTC 2026-09-19) on the committed tree `a8e0cf95`: **EXIT=1, 807 s**; **3678 cases: 3428 PASS / 250 FAIL**; `eval tests` 211 ok; `bug-index cross-check` ok; `re-pin guard` ok (0 PASS→non-PASS flips; the report-only note `GREENED race/negative/struct-tag-alias-field FAIL -> PASS` — the disclosed flip); `memory-module raw call-site inventory` ok (72); every other step ok. RED: the two 5a-class items PLUS one line on the alias row — `baseline[PASS/racy] -> now[FAIL/racy]`: NOT a verdict but the racy-lane enumerator's REFUSAL by name, «run consumes more than --max-sites 8 choice site(s) — raise the case's sites bound (never truncated silently)» (`artifacts/coverage/latest.tsv`): the row has three goroutines (two children + main) and its enumeration reaches depth 9, beyond the lane's default `sites=8` that the first row line copied. With the harness's own invocation at `--max-sites 16` the fix binary certifies the row — `observations=1`, `status race`, 334 leaves, depth 9: EVERY enumerated path refuses; the guard at 8 certifies its one member `ok 12` (`bug111-enumerator.txt`). The row's `sites=` corrected to 16 in the next commit (a row-params correction, the lane's `map-range-iter` precedent), re-gated. ZERO other drift. Tail: `gate-tail-bug111-fix.txt`. **The row-params commit `87a3c90b`** (`sites=16`): `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (acquired after 0 s, 00:37:14–00:49:03 UTC) — **EXIT=1, 709 s**; **3678 cases: 3429 PASS / 249 FAIL** — the alias row PASS/racy as pinned (the DISCLOSED flip complete), the guard PASS; `eval tests` 211 ok; `bug-index cross-check` ok; `memory-module raw call-site inventory` ok (72); every other step ok. RED: exactly the two 5a-class items (`certificate provenance` STALE on `CLI.lean`; the SINGLE drift line `imported-goose/channel/google-search`). ZERO other drift: BUG-111's end state. Tail: `gate-tail-bug111-params.txt`. Detector-soundness after the fix (the FINAL official matrix, tree `87a3c90b`):
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
| what BUG-111's fix canonicalizes | EVERY emitted location — `.data`, `.syncWord`, `.chanObj` keys AND the `HbAction` locs that key the channel / sync / atomic clock tables | (a) the `.data` keys alone (the entry's letter); (b) canonicalize at CONSUMPTION in the fold | (a) would leave the sync words structural, and a canonical data path would then no longer prefix-overlap the primitive's words (the BUG-080 copy-beside-Lock refusals would silently OPEN); the clock tables keyed structurally would split on an alias (a fail-closed residual). One rule at the ONE place the module speaks — emission — is the charter's shape; (b) would put a second account in the fold |
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

None new; nothing asked. (The predecessor's §6 items are ruled/withdrawn.) For disclosure at the merge ask,
not a decision: BUG-111's fix canonicalizes EVERY emitted location — the `.data` keys the ruling names AND
the sync-word / channel-object keys and the `HbAction` clock-table locations (§4: the `.data`-only reading
would have reopened the BUG-080 copy-beside-Lock class through a canonical data path that no longer
prefix-overlaps a structural sync-word path, and the clock tables would split on an alias — a fail-closed
residual). No corpus row's verdict changed (the differential, the choice trace on the 3,676 pre-existing rows
and the detector-soundness matrix say so); the [USER] may narrow it to the `.data` keys if the letter of (i)
is preferred — then the sync-word keys must be canonicalized too or the BUG-080 pins re-checked.

## 7. Where the lane stopped; the next command — PARKED 2026-09-19 (UTC)

PARKED at the records commit over the gated corpus-params commit **`87a3c90b`** (BUG-111's end state; §2a),
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
