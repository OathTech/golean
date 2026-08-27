# W0 reset log (2026-08-27) — one writer: the w0-reset worker

Governing docs: the AMENDED kill-list (`docs/2026-08-27_kill-list.md`,
campaign worktree copy read at start), the clean proof plan v2 (§W0),
`docs/ARCHIVE.md` (created this unit). Archive ref
`archive/fixed-trajectory-era` verified pinned @ `c4986b29` = branch
base. Conventions: build-lock for full builds, capped builds only,
zero sorry/native_decide/new axioms in touched files, [AGENT]-tagged
judgment calls.

## Judgment calls and checkpoints

- [AGENT] Build lock: `artifacts/build-lock.d/owner` held a stale
  `coordinator-ceremony` entry (mtime 2026-08-26 16:13; zero lake/lean
  build processes on the box at takeover; the ceremony's landing is in
  main's history at `c4986b29`). Took the lock over for w0-reset with
  a takeover note rather than treating the box as blocked. What this
  taught us: lock releases belong in the ceremony's exit path — a
  completed ceremony left its owner file behind.
- Pre-deletion census reconciliation (derivation: `wc -l`, `ls`,
  python import-graph walk over `proofs/`): K-A = 57 `*Lit*` modules
  (1,184,013 lines) + TwinCheckpoints (40) + TwinCheckpointsF (47)
  = 59 modules / 1,184,100 lines — EXACTLY the census figure.
  Baseline `proofs/` (excl. `.lake`): 449 files, 1,395,056 lines.
- Import-graph verification (before touching anything): the
  transitive dependents of the 59 literals are exactly the K-B
  modules + the four K-C donors (RoundStatement, AllocEq,
  AllocEqWave1, AbsStateV2) + the K-D Audit pin modules + the
  aggregators. NOTHING in the kept set (native chain, DriverNet,
  Frame core, Sym, statement layer, retained witnesses) reaches a
  literal. The census's importer-graph claim HOLDS.
- [AGENT] Phase-greenness sequencing: deleting bottom-up (K-A first)
  breaks upper layers unless their build-root links go in the same
  commit. Resolution: each phase's commit deletes its listed FILES
  and additionally UNLINKS (removes aggregator/Audit import lines
  for) any module doomed by that phase's deletions, leaving later
  phases to delete the unlinked files on their listed schedule. This
  keeps every phase's default-target build green without reordering
  the kill-list. Unlink-early victims at K-A: the doomed K-B/K-C
  modules' aggregator lines, `Audit/{Ring,RoundMa,RoundVote,RoundMar,
  RoundVr,RoundIndWitness,RoundInduction,FrameShape}` imports (files
  deleted at K-D per the list), the `twin_prelude_eq` pin in
  `Audit/FastEval` and the seed-pin sections of `Audit/ChoiceInv`
  (their K-D prunes pulled to the phase their subjects die).

## Discrepancies vs the census (running list)

- D1: `BfSortStep.lean` (99 lines, Specs/Raft) is census class b (the
  Bf fixture chain: imports BfSteps2, sole importer BfEquation — both
  K-B) but matches no literal K-B pattern (`*Steps*` misses
  "SortStep"). [AGENT] deleted with K-B; it cannot survive its chain.
- D2: `AbsStateV2`'s kill-list row deletes only `absV2_witness_L4`,
  but its three sibling witnesses (`absV2_witness_log`,
  `absV2_witness_lastIndex`, `absV2_witness_outbox`) consume `uσ`
  from `BfFixture` (K-B) and `absV2_witness_message` consumes `wBase`
  from `BecomeFollowerWitness` (K-B) — none can survive their
  fixtures, and all four are fixture-constant theorems, the banned
  class the DONE condition sweeps for. [AGENT] deleted the whole
  witness section at the K-C split; the readers + `_ren` half (the
  row's keep column) is exactly what remains.

## Phase record

- Phase 1 (ARCHIVE.md + this log): `353851d9`. Docs only, no build.
- Phase 2 (K-A): `59e05206`. 59 files deleted (1,184,370 lines incl.
  aggregator prunes; module lines 1,184,100 census-exact). Build
  GREEN, COLD, 521 jobs, 12:14 wall (capped 96G, threads 8;
  artifacts/w0/ka-build.log — includes iris-lean + GoLean core; this
  worktree had no prior build dir).
- Phase 3 (K-B): `5dc3551b`. 69 files deleted (18,266 lines);
  NativeS1Witness/NativeS23Witness RETAINED + docstrings. Build
  GREEN, 510 jobs, 5.2s incremental (kb-build.log).
- Phase 4 (K-C): `9608b9da`. Splits verified standalone FIRST
  (42-job focused build, kc-split-build.log); then donors deleted
  (RoundStatement/RoundInduction/AllocEq/AllocEqWave1; −1,527/+336
  incl. NEW RenCongr.lean + AbsTwinRead.lean). Build GREEN, 513
  jobs, 1:12 (kc-build.log).
- Phase 5 (K-D): `cea038b6`. 133 files deleted (29,002 lines: the
  corpus pair + lake targets, 8 Audit pin modules, tools/campaign
  115 files ≈23,000 lines, Frame/Shape* 7 modules, the corpus
  landmark record); scripts/ci coverage step reverted to ONE closure
  + allowlist — fail-closed RE-TESTED both directions (clean rc=0,
  planted orphan rc=1). Build GREEN, 506 jobs, 4.9s (kd-build.log).
- Phase 6 (the gate): `scripts/ci` with GOLEAN_ALLOW_NO_DIFF=1
  (fresh worktree, no recorded differential — the sanctioned hatch,
  visible notes printed), capped 96G. **RESULT: PASS, wall 2:36.14**
  (artifacts/w0/gate.log) vs the ~256s warm baseline (−39%); proofs
  build 506 jobs vs the 627 baseline (−121). Audit sweep: 39,048
  declarations, all axiom-clean. THE EXPECTED LANDMARK NOTE printed:
  "comparator landmark OWED (scope): 2 file(s) in Challenge's
  trusted closure changed" — the two are proofs/Audit.lean and
  proofs/lakefile.toml (the judge's WATCHED set, verified by
  reproducing the check's git diff; the statement layer and
  Challenge's import closure are untouched). The operator owes a
  scripts/comparator-judge run at the merge, per the brief.
- Phase 7 (line-count audit): proofs/ (excl. .lake) BEFORE 449
  files / 1,395,056 lines → AFTER 302 files / 185,412 lines. Net
  −1,209,644 lines (git numstat over proofs/: −1,210,069 +414).
  Census predicted ≈1.20M: reconciled — 1,184,100 (K-A) + ≈17.6k
  (K-B) = 1,201,700 census headline; the ≈8k overage is content the
  kill-list counted OUTSIDE its 1.20M headline number: Frame/Shape*
  (≈6k, K-D), the K-C donors (≈1.4k), the Audit pin modules + corpus
  aggregators (≈0.7k). Outside proofs/: tools/campaign −23,000
  lines, docs/corpus-landmark-record.md deleted.

## End-state confirmations

- Zero `*Lit*` generated modules under proofs/ (find: 0).
- Zero fixture-constant theorems outside the two retained witnesses:
  every remaining `uσ`/`wBase`/`rhb*`/`bfTB`/`uS0`/`uC0` mention is a
  docstring or the Sym layer's ∀-quantified `γS ρ σ S` symbolic
  concretization (general machinery, not a fixture constant). The
  general non-vacuity witnesses of live non-raft laws (the WP law
  witnesses, FastEval's TransferWitness) are K-E keeps, untouched.
- Specs/Raft is now 14 modules: the native chain (8 incl. the two
  retained witnesses), NativeCheckerBridge (rule half), DriverNet,
  AbsState, AbsStateV2, AbsTwinRead, RenCongr.
- [AGENT] Build lock RELEASED at unit end (owner file cleared).

Nothing merged; branch-complete. The merge ceremony (gate + judge +
audit-ask) is the operator's.
