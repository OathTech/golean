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

(appended per phase; commit hashes + build walls)
