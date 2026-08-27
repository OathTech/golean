# ARCHIVE — the fixed-trajectory era (ref: `archive/fixed-trajectory-era`)

The branch ref `archive/fixed-trajectory-era` is pinned at `c4986b29` —
the last pre-reset tip of `main`. Everything the W0 reset (2026-08-27)
deleted is preserved there in full, with its history. This file is the
tracked record of what the ref holds, why it was killed, and where the
harvestable parts live.

**THE RULE: nothing in the archive is ever cited by a proof.** The
archived material is design history and harvest source only. A proof,
witness, or gate that reaches into `archive/fixed-trajectory-era` (or
re-lands its content without a fresh design justification under the
current plan) is a defect by definition.

## What the ref holds

Numbers measured at `c4986b29` (`wc -l` / `ls` over the tree; the
per-phase deletion commits on the `w0-reset` branch carry the same
numbers in their messages):

- **The literal data (kill-list K-A)**: 59 modules, 1,184,100 lines —
  57 generated `*Lit*` modules under `proofs/GoLeanProofs/Specs/Raft/`
  (census class c: `GENERATED — DO NOT EDIT`, zero theorems) plus
  `Specs/TwinCheckpoints.lean` (40) and `Specs/TwinCheckpointsF.lean`
  (47). Fixed-trajectory heap/config literals of the raft twin.
- **The trajectory theorems (K-B)**: ≈66 modules, ≈17,600 lines — the
  handler `*Equation`/`*Fixture`/`*Steps*`/`*Resite`/`*31` chains, the
  four `Round*` equation/lemma chains, `RingEq*`, `HandlerEq(Sym)`,
  `SeedPin`/`SeedWitness`, the fixture-constant witnesses,
  `StaticCells(Ext)`, `LensInst`, `TwinPrelude`, `StateWire`, the
  round induction and its witness. Theorems ABOUT fixed trajectories
  and fixture anchors — the class the bounded-techniques doctrine bans
  from proofs.
- **The corpus apparatus (K-D)**: `GoLeanProofsCorpus.lean`,
  `AuditCorpus.lean`, their lake targets, `scripts/ci`'s two-closure
  coverage step, `docs/corpus-landmark-record.md`.
- **The emitters and campaign tooling (K-D)**: `tools/campaign/` —
  115 files of generators, emitters, doctor/prune tooling, probes,
  census scripts. Enumerative infrastructure, killed irrespective of
  greenness per the [USER] directive.
- **`Frame/Shape*` (K-D)**: 7 modules (≈6,000 lines incl. the
  2,013-line `ShapeStrict` copy) — the splice-clause completeness
  design, layout-dependent and refuted at its one chartered use
  (single-splice cannot place a pruned sub-fixture into an
  interleaved outer frame; campaign log, A4-U22 entry).

## The design lessons (pointers, not restatements)

- `docs/raft-campaign-log.md` — the campaign log of record: the
  per-unit **WHAT THIS TAUGHT US** entries and the owned-mistake
  records (the three kernel walls, the OOM incidents, the witness
  discipline, the fixture-resists-canonicalization verdicts, the
  representation-engineering principle). Read the tail (2026-08-26/27
  entries) for why the era ended.
- The bounded-techniques doctrine: `CLAUDE.md` §"Clever tricks, not
  stupid tricks" (2026-08-24) — representation-level grinding and
  fixture-specialized machinery are tolerated scaffolds at most,
  never load-bearing. The reset is that doctrine enforced by
  deletion.
- The replanning round's governing docs (2026-08-27):
  `docs/2026-08-27_kill-list.md` (the evidence-based census verdicts;
  professor-amended), `docs/2026-08-27_clean-proof-plan.md` (v2 — the
  W0–W5 work breakdown this reset opens),
  `docs/2026-08-27_proof-structure-explained.md` (the clean proof
  path the kept modules serve).

## Harvest pointers (refs kept, never merged as-is)

- **`campaign-arc4d`** — the span-computes-model arc: the checker-span
  content and the reusable projections (`projLOf`/`projBy`/`encGS`)
  with their commutation lemmas. Wrong-shape evidence for the killed
  design; harvest source for the W3 checker specs.
- **`campaign-wave-a`** — a killed worker's partials; its kill
  commits overlap this reset's list (reconcile before harvesting).
- **`campaign-ce`** — the SpanIso start; harvest candidate.

## What survived the reset (for orientation)

The trusted base (GoCore, the frontend, the differential corpus +
scripts, FastEval + transfer theorems + fastreplay), the ∀-shaped rule
set (`Frame/` core, `Sym/`, `Lens`, `SliceWalk`/`MapLoops`/`StepKit`/
`FuelMeasure`, the Iris WP layer), `Frame/ChoiceCanon` + `ChoiceInv`
(minus witnesses/seed pins), the native abstract chain +
`NativeCheckerBridge`'s rule half, the pairing vocabulary (`AbsState`,
`AbsStateV2` readers + `_ren`, `absTwinRead`), and the statement layer
(`WirePin`, `TwinProgram`, `RaftAgreement`). The two retained native
interface witnesses (`NativeS1Witness`, `NativeS23Witness`) stay until
W5 supersedes them — the non-vacuity demonstrations of the interface
premises the abstract leaves consume.
