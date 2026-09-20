# Stage D handoff — exploration economics: the ladder measured, route α landed (2026-09-20)

[AGENT] worker, lane `core/unseq-stage-d-0920` (worktree `.claude/worktrees/unseq-stage-d`; branch off main
`f14a05e5`, rebased onto `10d2f2dc` — the train's records-only r44 close). Design note:
`docs/2026-09-20_unseq-stage-d-design.md`. Evidence: `docs/evidence/2026-09-20_unseq-stage-d/README.md`. The plan's
row D (`docs/2026-09-16_evaluation-order-model-v2.md` §7) and §3.6 (routes α/β) are the authority; no [USER] ruling
was needed and none is posed (§6). Every logged decision below is [AGENT].

## 1. What landed (ONE gated runtime commit + records)

- Runtime commit `95c6c052` (TRUST-SURFACE #2: the dedup engine's certifier — `GoLean/GoCore/EnumDedupCheck.lean`,
  `EnumDedupSound.lean`; and `GoLean/GoCore/Machine.lean` gains a definition): **route α** —
  - `Machine.unseqNextBound : Config → Nat` (= `|ready|` at a pick position, 0 elsewhere; reads no store, no other
    thread) beside `consumesUnseqNext` (docstring updated).
  - `MultiStreams.poolThreadOblivious`: at `consumesUnseqNext c` → `decide (unseqNextBound c ≤ 1)` (was `false`):
    a bound-≤-1 pick pops nothing (G-U) and is oblivious; `stepThread_oblivious` extended for it (via
    `stepFn_consumption_none`). New: `stepThread_stepFn_path` (the goroutine-step on the plain `stepFn` path as an
    equation), `stepThread_pick_run` (the `stepFn`-path pick determinization, the analogue of `stepThread_l4_run`,
    through `stepFn_consumption_some`).
  - `EnumDedupCheck.innerVecs` class **N-PICK**: `consumesUnseqPanic c → some [[0],[1]]`; `consumesUnseqNext c →
    if 2 ≤ unseqNextBound c then some ((List.range (unseqNextBound c)).map ([·])) else none` (the `none` is
    unreachable — the oblivious flag took the ≤ 1 case — kept fail-closed).
  - `EnumDedupSound.stepThread_total_covered`: the two N-PICK cases (`stepThread_pick_run` + the raw pop's bound).
    **`checkCert_slowObs` / `checkCertM_slowObs`: statements UNCHANGED** — the same theorem certifies the wider class.
  - `MachineSound`: `consumesUnseqNext_shape`, `consumesUnseqPanic_shape`, `unseqNextBound_pick`,
    `seqConsumption_unseqNext`, `seqConsumption_unseqPanic`.
  - `EnumDedup.refusalReason`: the two sites' texts now say «certified since Stage D; unreachable refusal».
  - `CLI.dedupSeed` factored out of `runDedupObservations` (byte-identical behaviour; the tests certify from the CLI's
    own seeded pool).
  - Tests: `Tests/UnseqHarness.lean` `expectDedupSet`/`expectDedupRefusal` (the certified set vs the expected members,
    through the UNMODIFIED `checkCert`); `Tests/UnseqScheduler.lean` six α checks (W1/W2/W6/recursion/W4 certified,
    the printing replay graph refused by name); `Tests/UnseqSchedulerAudit.lean` +11 exports (35 required theorems) and
    `import GoLean.GoCore.EnumDedupSound`; `Tests/GoCoreEval.lean` `dedupAlphaFacts` (its own do-block — `main` is at
    the recursion-depth limit; the C1 S2c precedent): the W1 certificate accepted with members exactly [1, 2], the
    widest node branches exactly |ready| = 3, mutations M1–M5 refused (M4 is new: a pick node's last branch dropped).
    Eval tests 267 → 274.
  - Lane move: `spec-examples-stmt/continue-label` strict `depth=128` → `lane=confluent`, `engine=dedup`
    (`width=4,sites=64,work=200000`; the row's comment block carries the reason).
- Records: this handoff, the design note, the evidence README + small tables, `docs/coverage-suite-structure.md`
  (the lane move under the depth guard's standing consequence), v2.1 §3.6 addendum (route α landed),
  `docs/language-coverage-ledger.md` §8 tally paragraph.

Gate: `scripts/capped scripts/ci --slow` at the runtime commit (this tree; the box-wide lock held 21:50–22:06Z),
EXIT=1 in 946 s — RESULT FAIL on EXACTLY the expected red: `certificate provenance` (STALE certification: changed
dependency `build/files/GoLean/CLI.lean`; the fresh re-certification reports the UNCHANGED six-member `google-search`
set, 187 s — the train installs the candidate at step 5a, not a re-pin here) and `baseline diff` DRIFT = exactly
`imported-goose/channel/google-search` PASS/membership → FAIL/membership (the same 5a-class item) + `spec-examples-stmt/
continue-label` PASS/- → PASS/confluent (the named lane move; re-pinned in the runtime commit with the written reason).
Every other step ok: core build warning-free; escape-hatch preflight/addendum/meta-layer; core totality audit (every
GoLean/ module, required core theorems, poison controls); engine-isolation; check-mem-callsites; admission proofs;
declaration + wire boundaries; method identity; unseq scheduler (Stage B; 35 theorems); unseq wire (Stage C); frontend
pins (twin wire = pinned bytes); frontend/lowerdiag/harness unit tests; eval tests 274 ok; differential 3705 rows
3458 PASS / 247 FAIL (= the pin with the one 5a-class row red); lane-validation fixtures incl. the go half; negative
corpus 394 matched; FloatVectors + inittask-std byte-exact; executed library coverage PASS. `beside-loop` (the
baseline's alternation row) did not drift. Gate tail: `docs/evidence/2026-09-20_unseq-stage-d/gate-tail.txt`. Sequential warms before it: `GoLean.GoCore.MachineSound` (67 s, EXIT=0), `MultiStreams` (EXIT=0),
`EnumDedupSound` (EXIT=0), `golean` (96 jobs, EXIT=0), `UnseqSchedulerTests` + `gocore-eval-tests` (EXIT=0);
`scripts/check-unseq-scheduler` PASS (35 theorems, classical trio only); `gocore-eval-tests` 274 ok, EXIT=0.

## 2. The ladder — headline (tables: evidence README §2–§4)

| rung | β (paths / steps / wall) | α (unique states / edges / merges) | closes within budget |
|---|---|---|---|
| `loop N` silent, N = 1..12 | 2^N paths; 585 623 steps and 66–94 s at N = 12 | 154 + 115·(N−1) states — LINEAR; 1 419 / 1 430 / 12 at N = 12 in 0.49 s | β: yes (to N = 12); α: yes |
| `loop N` printing | members = paths; N = 13 REFUSED by name (cap 4096) | α refuses the output event by name (G-OUT) | β: to N = 12; α: not applicable |
| `wide k` silent, k = 2..8 | k! paths; 40 320 / 4.1 M steps / ~4 m 15 s at k = 8 | 21 887 / 22 655 / 769 at k = 8 in 37 s | β: yes to k = 8 (k = 9 would exceed 50 M); α: yes |
| `wide k` printing, k = 2..7 | members = k!; k = 7 REFUSED (5 040 > 4 096) | refused (G-OUT) | β: to k = 6 |
| `nest M` silent, M = 1..5 | 6^M paths; 7 776 / 1.03 M steps / 88 s at M = 5 (printing M = 5 REFUSED, cap) | 372 + 315·(M−1) — linear; 1 632 / 1 656 / 25 at M = 5 in 0.55 s | β: yes; α: yes |
| corpus E13 family + pilot + moved rows (153 rows) | every row's own baseline enumeration (ms each) | 100 CLOSE and certify, sets = DFS 100/100; 42 printing refusals; 8 row-own refusals; 3 pre-existing shapes | both |
| `continue-label` | 32 805 leaves / 39.6 M steps (just under 50 M) | 5 122 / 5 145 / 24 — the singleton certified | β barely; α easily → the lane move |
| raft twin (5 rows) | 569 consumptions, all `appendSpill`; 0 `unseqNext` | — | control: 0 `unseq` nodes, as the census said |

D2: accountant — 0 sentinel alarms on every β path of the ladder, 0 validator alarms on the twin;
`seqConsumption_unseqNext` is the exactness at the new site as a theorem. Reclamation cost for C4: 4 cells per sweep
(2 binder + 2 callee-result cells), none reclaimed — heap 3 + 4N on `loop N` (`heap` rung), i.e. linear memory per
sweep and a strictly growing node key on every engine.

## 3. Route α's coverage — what is certified, what is not

Certified sites in the dedup engine after Stage D: N-OBL (unchanged), N-L4 (unchanged), N-APP non-spilling (unchanged),
**N-PICK: `unseqNext` at every bound (≤ 1 oblivious, ≥ 2 enumerated) and `unseqPanic` (bound 2)**. Still refused by
name (unchanged): L2 `.multi` arrivals, consuming selects, `mapIterK`, spilling appends, `tryLock`,
`nilValueMethodText`, `repanicCollapse`, and — the engine's own rule, not a pick — any output-producing step.
The `unseqPanic` site IS the same shape (a `stepFn`-path pick with a configuration-determined bound), so it is
certified by the same lemma; it retires with the legacy lowering at Stage E.

## 4. Lane moves

Exactly one, named: `spec-examples-stmt/continue-label` (§1). The 41 membership rows the engine closes with their
declared sets reproduced are recorded (`alpha-corpus-rows.tsv`), not moved — the rules license no move for rows the
DFS closes, and switching engines there is not proposed. BUG-065's 16 rows: none closes (they refuse on budget or on
`appendSpill`/scheduling shapes, never on the `unseq` pick); recorded, not forced.

## 5. Where this lane stopped; the next command

Stopped at the records commit on top of the gated runtime commit (branch `core/unseq-stage-d-0920`, worktree clean,
parked; NOT merged, NOT pushed). The records gate (`scripts/capped scripts/ci --diff` on the committed tree) and the
whole-corpus choice-trace comparison against main's binary are recorded in the evidence README §6–§7. Next command for
the train: the audit ask (§8) → on sign-off `git checkout main && git merge --ff-only core/unseq-stage-d-0920`, then
step 5a (`scripts/build-certified` + `tools/certification.py release-check`): the `google-search` record's inputs
changed (`CLI.lean`), the fresh set is unchanged — install the candidate as the round's 5a records commit.

## 6. PENDING [USER]

None. The one open choice (output-keyed dedup nodes for printing sweeps) is [AGENT]'s (b) with (a) recorded
(design note §5) — no claim changes either way.

## 7. What Stage E needs from this lane

- Route α is live for every `unseq` pick: a migrated family whose sweeps are silent can carry `engine=dedup` as its
  rows land (certified membership / confluence); printing families ride β with the per-row budgets recorded here.
- The N3 refusals are real and by name (cap 4096, work 50 M) — Stage E's families should be sized against the β
  tables in the README before emission widens.
- `unseqPanic`'s certification is incidental; delete it with the site.

## 8. The audit ask (posed; scope and waiver the [USER]'s)

Adversarial audit of: (i) `stepThread_pick_run`/`stepThread_stepFn_path` and the two N-PICK cases — is the branch
vector `[p]` for `p < unseqNextBound c` COMPLETE for every stream (the raw pop `Choices.consume ch b` lands in
`[0, b)`) and does the determinization read nothing but the frame; (ii) `poolThreadOblivious`'s new `true` at a
bound-≤-1 pick — is any consumer of the flag (`stepAllBranchesOk`, `allStreamsOkPool`) widened beyond what
`stepThread_oblivious` proves; (iii) the certified sets — 100/100 equal to the DFS's on the corpus rungs, the W1
mutation controls, `continue-label`'s singleton against gc; (iv) the lane move's licence under the depth-guard rules;
(v) the ladder's budgets as the exit criterion (are the refusals by name where claimed; is any number unanchored).
