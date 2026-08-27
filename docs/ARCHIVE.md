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

---

# ARCHIVE — the CallSpec era (ref: `archive/callspec-era`)

The branch ref `archive/callspec-era` is pinned at `20cda772` — the
w1-prover wave tip (W1–W3, 2026-08-27). The triage landing
(`docs/2026-08-27_triage-plan.md`, [USER]-approved 2026-08-27)
deleted the wave's parallel calculus and landed its tier-agnostic
substrate; everything deleted is preserved at the ref in full. THE
RULE above applies unchanged: nothing archived is ever cited by a
proof.

## What lived there

- **The judgment calculus** (`SpecJudgment.lean`, 483): six
  judgment forms (StmtSpec/CallSpec/R/RD/RN + B-forms) with
  conseq/consume/seqn/call rules over `stepFnIter` — a
  continuation-parametric triple calculus beside the real Iris tier
  already on main. [USER] diagnosis: parallel-calculus drift;
  CallSpecV and the R-geometry transport road CANCELLED.
- **~30 CallSpec members** (`LogReadSpecs`, `StorageWalkSpecs`,
  `RaftLogReadSpecs`, `InitCallSpecs`, `MapOrderSpecs`,
  `HarvestSpecs`; ≈8.5k lines): exact readbacks of real etcd raft
  log/storage/harvest/init functions — with fixture-family
  preconditions (literal addresses in statements). The CONCLUSIONS'
  semantic content re-derives as tier-3 FnSpec postconditions at the
  cluster units; the per-member windows, crossing maps, and measured
  costs live in the LANDED w1/w2/w3 prover logs.
- **The pilot/gate chain** (`BecomeFollowerSpec`,
  `CBecomeFollowerSpec`, `CallSiteComposition`, `W2Gate`; 925): the
  W2 end-to-end framed-composition demonstration. Its load-bearing
  content landed judgment-free (the plug family + `absRaftNode_frameSim`);
  the G-BIND unit's gate instance is the named replacement demo.
- **The fixture mass** (`SymBase`, `Bf*`/`CBf*` incl. 15.9k
  generated literal lines, `Reloc` — with the divergent, unconsumed
  `symPlugK`/`symPlugC` plug sibling, deleted with prejudice — plus
  `tools/relayout/CBfLitGen.lean`; ≈18.6k).
- **Main-side removals archived with the tip**: `Frame/Relocate.lean`
  (zero live consumers; cancelled R-geometry vocabulary),
  `Frame/ChoiceInv.lean` (`ChoiceInvariantToM`: zero inhabitants,
  zero consumers), and `Specs/RaftPilot/Invariant.lean` (the
  629-line invariant contract, ARCHIVED rather than landed on an
  [AGENT] coordinator recommendation ratified by [USER] package
  assent at the 2026-08-27 sign-off — provenance corrected by the
  pre-merge audit, gate-dimension M-1, from the flat "[USER]
  decision" this line first carried — incl. the F-1-defective
  `ElectedAt.logBridge`/`commitTie` clause pair; G-INV re-designs
  the clause inventory at the Iris tier under the [USER] gate).

## The lesson

Leaf specs were stated in a bespoke triple calculus over the
executable machine while a real iris-lean tier (heap RA, WP, FnSpec
contracts over real raft code, adequacy) stood on main. The error
was not missing tiers — it was building a fourth, parallel calculus
beside them. Landed survivors (plug, RunGlue, CondFor/MapLoops/
MapPerm, Crossing/ReflectConc, the readers, InitSpec, ghost-acks,
the prover record) are exactly the tier-agnostic substrate.

## Harvest pointers

- Member readback conclusions → tier-3 FnSpec postconditions
  (G-cluster units); windows/crossing maps/costs → the unit pricing
  anchors (w3 logs, landed).
- **The four machine-geometry facts** (pre-merge audit,
  semantics-dimension L6: these are facts about `stepFn` ITSELF, not
  about the killed calculus, so they survive the era wholesale and
  must be routable without reading the dead code. Each is
  probe-anchored in a landed log; the anchors below are the durable
  citations, and the named consumers are the future G-CALLS/G-BIND
  units):
  1. **Two return-arrival geometries.** A defer-free callee ends at
     `.returning (.frame plans env rlocs [] k false)`; that is the
     only terminal such a callee reaches.
     *Anchor:* `docs/w3-init-log.md:160-183`.
  2. **Deferred frames exit via `.next (.frame …)`.** A callee WITH
     defers drains them through the frame's defer arm and arrives at
     `.next (.frame plans env rlocs [] k false)` — it NEVER re-visits
     a `.returning` frame configuration. Both arrival arms perform
     the same next step (loadMany + tgtOpK), so consumers may treat
     the two forms identically, but a span that assumes the
     `.returning` terminal for a deferred callee is kernel-stuck.
     Every `MemoryStorage` method (Lock/defer/Unlock) is in this
     class. *Anchor:* `docs/w3-init-log.md:160-183`; independently
     corroborated from the prover lane at
     `docs/w3-prover-log.md:700-703` (probe `kit-ms3.out`).
  3. **The wrap-per-op normalize rule.** One `normalize` per
     arithmetic op, one per int-cell store, DOUBLE for struct
     literals (`structLit` normalizes each field via
     `normalizeValueForTy` AND the store coerce normalizes again),
     ZERO for `newValue`/interface/pointer stores (`newValue` stores
     the read value RAW, so pointer-copy chains conclude exact
     equality with no range facts). *Anchor:*
     `docs/w3-prover-log.md:1149-1153`; derivation and the
     -1-payload probe convention for wrap discovery at
     `docs/w3-prover-log.md:1025-1034`.
  4. **`postOp`/`opDone` is a PURE STRIP** in the sequential
     `stepFn` — the sync walk consumes NO tape.
     *Anchor:* `docs/w3-prover-log.md:703-705`.
- The prior discharges of now-scaffold-labeled rules, and what did
  (and did NOT) replace them — stated exactly, per the pre-merge
  audit's claim-dimension F2, which found the earlier one-sentence
  version overclaimed:
  * `mapPickLoop_perm` ← `MapOrderSpecs.lean:864`
    (`jointConfigIDs_callSpecR`, the full-permutation-family member
    over the real `quorum.JointConfig.IDs`). **This one has NO live
    replacement.** Its discharge is OWED AT THE G-MAPITER UNIT, per
    the in-tree SCAFFOLD label on the rule itself
    (`proofs/GoLeanProofs/MapPerm.lean`). Neither
    `Frame/PlugWitness.lean` nor `Sym/CrossingWitness.lean`
    discharges it, and nothing else in the tree does either.
  * The crossing kit ← the three `LogReadSpecs` members. These DO
    have live replacements: the judgment-free mini-witnesses in
    `Sym/CrossingWitness.lean`
    (`crossing_witness_lenNeg`/`_ifSplit`/`_read`).
  * `Frame/PlugWitness.lean` (`callSpan_plug_witness`,
    `stepFn_plug_witness`) replaces something else again — the
    `W2Gate` plug-rule INSTANTIATION that died with the CallSpec
    member corpus — not the map-pick discharge.
