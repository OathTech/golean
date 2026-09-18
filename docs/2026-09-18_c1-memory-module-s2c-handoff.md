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
- **S2c-ii** — the switch (`raceFold` becomes `raceUpdate`; the registry arms, `raceChanEntryReads`,
  `racePairEvent`, `raceWakeEvent`, `raceCommitClauseEvent`, `raceWgAddEvent`, `tryLockAcquired`'s
  fold use, `dataEvents` deleted; the tracer's audit columns retired; the six DETECTOR REGISTRY ARM
  inventory rows retired): NEXT (§7).
- **BUG-111 fix (i)** and **S3** (the rollback, cost B): after S2c-ii (§7).

## 1. What landed, per slice (gate lines in §2)

| slice | commit | content |
|---|---|---|
| S2c-i | `f1ad88c3` (runtime) | `HbAction`/`MemEvent`/`AccessTrace := List MemEvent`/`traceAccesses` (Ops.lean); `chanValueLoc` moved up, `chanSendEntry`/`chanCloseWrite`/`selectPoll`/`atomicEvents`, `syncWord`/`syncEntryKinds`/`syncReleaseTailKinds`/`atomicOpKind` moved in from Race.lean (Machine.lean); `applyChanOp`/`commitClause`/`applySelectCore`+`SelectOutcome`/`applySelect`/`applySyncOpCore`/`applyTryLock`/`applySyncOp`/`applyAtomicOp` return their label; the four registry `Step` rules and `stepFn` arms carry it; `resumeThread`/`applyPairing` (+`arrivalPoll`, `pairSendEvents`, `pairRecvEvents`) return theirs; `ArrivalOutcome.commit evs cl env k`; `stepThread` labels the spawn (`.hb (.spawn n) :: tr.map (.attributed n)`), wake, pairing, arrival commit, select interception; `StepE ctx n …`; `StepM`/`StepMFine` `pair`/`pickPair`/`pickCommit`/`wake` labelled; `RaceState.hbAction`/`event`/`events`, `accessKeys` deleted (Race.lean); `raceFold` (the one fold) beside `raceUpdate` (adapted through `dataEvents` only where it read the label); `footprintsConflict` over `traceAccesses`, `RacyFine` with the index (NPDRF.lean); the tracer's fold-equality audit (`Acc.auditFold`, `foldMismatches`/`firstFoldMismatch`; summarizer line). Proofs restated arm-for-arm (the commit message lists them). |

## 2. Gate lines (captured `EXIT=`; tails in the evidence README)

- **S2c-i, `f1ad88c3`**: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock
  (`.tmp/with-lock.sh`: `mkdir artifacts/build-lock.d`, owner file, trap-protected release, wait-retry
  120 s) — (acquired after 0 s, 22:37:12–22:50:02 UTC) the committed runtime tree `f1ad88c3` (clean for `GoLean`/`Tests`/`scripts`; the evidence dir untracked — the negative-diff step notes `git_dirty=true` for that reason): **EXIT=1, 770 s**; **3676 cases: 3427 PASS / 249 expected FAIL** (`differential coverage summary: cases=3676 pass=3427 fail=249`); `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `memory-module raw call-site inventory` ok (78 rows); `unseq scheduler` ok; `method-identity` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/ChoiceTrace.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` (the one cached certified row, judged stale because compiled semantic inputs changed). ZERO other drift; the negative baseline matched (394). Tail: `gate-tail-s2c1.txt`.
- Static checks at S2c-i: `scripts/check-mem-callsites` EXIT=0 (PASS, 78 rows — unchanged: the registry
  arms still exist in this commit; `chanValueLoc`'s move and the new emission tables add no raw site;
  `applyPairing`'s `chanCell` mentions are the same six, now binding the capacity). Eval tests
  (`gocore-eval-tests`) 211 ok, EXIT=0. Records checks at the S2c-i records commit: `scripts/check-bugs.sh`
  EXIT=0; `scripts/check-evidence-size` EXIT=0; `scripts/check-agents-alias` EXIT=0.

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
| a delivered panic's label | `[]` (the standing `deliver` convention); a `.panicking` CONFIGURATION returned by an apply keeps the apply's label (a send on a closed channel carries its entry read; `wgAdd`'s negative-counter panic carries its entry pair and its release-merge) | strip the label on every panicking successor | gc records `chansend`'s entry read before the closed-channel panic and `Add`'s ReleaseMerge before the negative-counter check (waitgroup.go:81); the old fold recorded exactly these (`raceChanEntryReads` on every outcome, `raceWgAddEvent` regardless of outcome) and the audit confirms |

## 5. Proved vs owed after S2c-i

Proved (kernel-checked, warning-free core): every coherence and preservation theorem restated over the
event label (the commit message lists them by name): `stepFn_sound`/`step_complete`/
`step_complete_any_wf` with the four registry rules carrying the apply's label; `stepMulti_sound`/
`stepM_complete` with the spawn, wake, pairing and arrival-commit labels; `step_preserves_wf` and the
`*_wf` family with the extra component; `stepFn_consumption` and the stream lemmas; MultiStreams'
obliviousness. Owed: S2c-ii (the switch and the deletions, the inventory rows, the docstrings that
still say «until S2c»/«the registry arm»); a universal companion for the synchronization emissions
(not chartered — recorded as a possible later theorem: `raceFold` on `stepThread`'s event equals the
deleted fold's registry account per action; the executable audit stands in for it now).

## 6. PENDING [USER]

None new. (The predecessor's §6 items are ruled/withdrawn.)

## 7. Where the lane is; the next command

NOT PARKED — the lane continues in the same session. S2c-i is landed on the branch as the gated runtime
commit `f1ad88c3` with this records commit on top. THE NEXT COMMAND (S2c-ii, the switch): make `raceFold`
the `raceUpdate` (`raceUpdate (ev : StepEvent) (m' : MultiConfig) (r : RaceState)` — no `ctx`, no
`sPre`/`tsPre`); update the call sites (`execProgLoop`/`execProgLoopOut`, `EnumDedup`, `EnumDedupCheck`,
`EnumDedupSound`, `PoolTrace`, `MultiStreams`, `MultiSound.raceUpdate_single`, `CLI` ×3, the tracer);
delete the registry arms and their helpers (`raceChanEntryReads`, `racePairEvent`, `raceWakeEvent`,
`raceCommitClauseEvent`, `raceWgAddEvent`, `chanApplyChan`, `tryLockAcquired`, `dataEvents`) with
tombstones; retire the tracer's audit instrument (`Acc.mismatches`, `auditFold`, `labelText`,
`stepActionName`, the two columns, the summarizer line — a column that can no longer be non-zero is a
false witness); retire the six DETECTOR REGISTRY ARM rows of `scripts/mem-callsites.tsv` and reword the
SYNCHRONIZATION rows that say «until S2c»/«the registry arm»; rewrite the docstrings («The registry's
SECOND duty», `StepAction`, `raceUpdate`); gate; choice trace vs main's binary; the official
`scripts/detector-soundness --select in-scope --jobs 6` (HOLE 0 / possible-HOLE 0 / over-refusal 6 expected).
Then BUG-111 (red-first rows FIRST), then S3.
