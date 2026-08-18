# The WP arc log — INDEX (2026-08-16 … )

Charter: `docs/2026-08-16_wp-arc-charter.md`. One file per slice
(`s1.md` … ) plus this index (per-slice totals + checkpoint summaries).
The log updates IN THE SAME COMMIT as the work it describes.
Checkpoints at least every 5 units; SHAs on unit entries.

**Conventions** (inherited from the campaign,
`docs/gallery-campaign-log/INDEX.md` §What the log is + the trip
report's lesson 15): every summary number DERIVATION-ANCHORED (a
build, a probe, a shown grep/command, or a SHA behind it — or it does
not go in); cross-doc cites UNIT/SECTION-ANCHORED or COMMIT-QUALIFIED,
never bare tip-relative lines; judgment calls one line each
(`JC: <the call> — <the principle applied>.`); honesty beats velocity
beats elegance; honest gaps are legitimate outcomes and never count
toward totals.

## Per-slice totals

| slice | scope (charter §) | status | units done | landed lines deleted | kit pins added |
|---|---|---|---|---|---|
| s1 | lift wave 1 (pure lifts) | **COMPLETE** — all 6 lift families landed (lift-5 stragglers resolved in S1.5b) | 8 / 8 | 2,483 (consumers; net −1,551 with +932 delegation/instantiation lines) | +79 (116 → 195) |
| s2 | lift wave 2 (new shapes) | **COMPLETE** — all 7 chartered items landed | 7 / 7 | 1,103 (consumers; net −633 with +470 delegation/instantiation lines) | +38 (195 → 233) |
| s3 | library regularity | **COMPLETE** — 8 kit modules regularized (the charter's 7 + `EntryEq`) | 5 / 5 | 0 (docstring-only slice; +851/−145 in `/-!` blocks) | +0 (233 → 233; no name moved) |
| s4 | mirror symbolic evaluator | **phases 1–3 DONE** (design gate discharged 2026-08-18; drift + refinement theorems in the default build; matmul acceptance LANDED — gallery entry 25) | 13 (S4.0–S4.12; S4.12 = the cost-story reconciliation, run at the s5 boundary) | — (additive layer; matmul: the withdrawn 2,375-line snapshot lands as 2,486 incl. the mirror fixtures) | Sym surface +6 pins over the lane's fork base (post-merge total recounted at the s5 boundary) |
| s5 | emission + instantiation sugar | **COMPLETE** — 3 units: the option probe (S4.11's flag closed), the storm lint, the sugar assessment (4 tactics trimmed with reasons, 1 lemma shipped) | 3 / 3 | 7 (the guard-bridge retrofit; ~50 more sites available, not swept) | +1 (`decide_natCast_lt_true`, `[propext]`) |
| s6 | discoverability close-out | **COMPLETE** — the Kit Guide (`docs/kit-guide.md`, 819 lines, 23 sections) + 9 module cross-pointers + the dry-run acceptance RUN TWICE (5 guide bugs found, 5 fixed) | 3 / 3 | 0 (docs + docstring-only slice) | +0 (233 → 233; `Audit/Kit.lean` untouched) |

Derivations for the s1 row: per-unit `git diff --numstat` figures in
`s1.md` units S1.1–S1.6 (deleted 256+315+151+1481+63+104+113 = 2,483;
inserted 97+174+20+317+110+172+42 = 932); pin count
`grep -c '^#guard_msgs in #print axioms ' proofs/Audit/Kit.lean` → 195.

## Checkpoints

**Checkpoint 1 — S1 PARK (2026-08-16, ≤5-unit cadence met at 6 units;
tip = the park commit).** Units S1.0–S1.5 landed, one commit each,
`scripts/ci` PASS at every commit. Lift 6 not started. Full park
record: `s1.md` §PARK RECORD.

**Checkpoint 2 — S1 COMPLETE (2026-08-18, tip = the S1.6 commit).**
Resume from the park record: S1.5b (bail stragglers — the
relational/measure-indexed schema `stepFnIter_iterate_bail_rel`;
twosum + bubble retrofitted, rle verified NO-OP) and S1.6 (GAP-RESLICE
+ `stepFn_return_frame`/`stepFn_block` + the queue glue composites),
one commit each, `scripts/ci` PASS at each. P6 sweeps re-verified at
the tip; totals above. Close-out entry: `s1.md` §SLICE 1 CLOSE-OUT.

**Checkpoint 3 — S2 COMPLETE (2026-08-18, tip = the S2.7 commit;
≤5-unit cadence met at units S2.1–S2.5 + this close).** All seven
chartered new-shape items landed, one commit each, `scripts/ci` PASS
at every commit: footprint pack (FreshFrom/DeadFrom unified + the
lookup/set battery + the two docstring signature disciplines),
call-span combinator + loadMany pair, GAP-APPEND
(element-type-generic one-element append with the envelope
existential), `StringMem` (values only, no heap half), growing-heap
front support (`keysBelow` executable front bound +
`storeTarget_live`), the `derive_entry_eq` string arm (zero
hand-written entry dances survive, claim sites updated), GAP-C1b
(`MapLoops` name parameterization). Totals above; close-out entry:
`s2.md` §SLICE 2 CLOSE-OUT. Next per the charter: slice 3 (library
regularity).

**Checkpoint 4 — S3 COMPLETE (2026-08-18, tip = the S3.5 commit;
≤5-unit cadence met at units S3.1–S3.4 + this close).** Five units,
one commit each, `scripts/ci` PASS at every commit: StepKit (the
standard shape + THE FIVE RULES anchored as the kit's single copy of
the storm discipline), SliceMem + StringMem, MapMem + MapLoops,
FuelMeasure + Frame/Threshold + EntryEq, then the convention note.
A DOCSTRING-ONLY slice by construction: 0 aliases, 0 renames, 0 names
added or removed, `proofs/Audit/Kit.lean` untouched throughout
(`git diff --name-only a9c15dcd -- proofs/Audit/` → empty), so the
existing axiom pins are byte-identical and the pin count is unchanged
at 233. Measured outcome: **142 public declarations that were named
NOWHERE in their module docstring at the s2 tip are now in a named
API group; the seven lemma modules' 263 public declarations partition
first-group-wins across their groups with ZERO ungrouped, and
`EntryEq`'s further 15 are all named in its two groups** (parsed at
the S3.4 tip; the per-module sums are in `s3.md`). Close-out entry + the naming convention, the (empty)
alias list, the five recorded near-misses and THE API-GROUP INVENTORY
— slice 6's Kit Guide skeleton, with its twenty guide-section names
fixed: `s3.md`. Next per the charter: slice 5 (slice 4 is in flight on
the `wp-eval` lane).
**Checkpoint 2 — S4 phases 1–3 (2026-08-18; tip = the matmul-landing
commit).** Phase 1 (`085862bd`…`f37b2feb`): Sym/Domain + Mirror + the
kernel-cost spike (gate PASS, S4.3) + commutation leaves. Phase 2
(`f1542dad`, `563b7f41`): the complete helper stratum, THE MASTER WALK,
THE DRIFT THEOREM, THE REFINEMENT THEOREM, the Kadane witness through
it; spike apparatus retired; TCB checks re-run (S4.9). Phase 3 (this
commit): the matmul acceptance in two measured stages — the trio of
measured blocker segments transported through `symEvalWindow_refines'`
(~1.3 s vs 61.4 s raw each), and the GAP-RFL-COST ROOT CAUSE found: a
MetaM smart-unfolding pathology (`set_option smartUnfolding false`
takes the raw 291-step segment from 61.4 s to 1.09 s; whole module
109 s / 2.30 GiB); `matmul_ok`+`matmul_readout` landed, gated, pinned
(gallery 25, all 8 checklist items; `scripts/ci` PASS with the
recorded no-diff hatch note — GoCore and `Corpus/` untouched all
slice). Full records: `s4.md` units S4.0–S4.11. Slice-4 remaining at
phase-3 end: the charter-phrasing integration TODO (OQ3 amendment at
the next arc boundary) and the S4.3-scale smart-unfolding re-probe
(flagged in S4.11).

**Checkpoint 5 — S5 COMPLETE (2026-08-18, tip = the S5.3 commit;
3 units, two commits, `scripts/ci` PASS at each).** The slice the
S4.11 discovery rescoped:
1. **The option probe** (`8cd1f3d1`) — S4.11's flagged open question
   answered at this tree and written up as `s4.md` §S4.12: the
   reconstructed 752-step accumulation baseline is **DNF in 620 s at
   default vs 0.94 s under `set_option smartUnfolding false`**, while
   the evaluator's own `rfl` is 1.03 s / 1.01 s (option-insensitive)
   and the transported route is 2.6 s at default but **DNF in 420 s
   under the option** — the measured REVERSAL. Verdict recorded
   plainly: the option, not the evaluator, buys the raw-window
   collapse on today's corpus; the refinement theorem's value is
   structural + the class the option breaks. S4.3's ratio superseded
   in its own log.
2. **The storm lint** (`8cd1f3d1`) — `scripts/proof-lint`, five rules
   over measured pathologies (L5 is the probe's), report-only,
   DO-NOT-HARDEN, wired into `scripts/ci` as a note-only step. 181
   notes + a 552 L3 census at the tip; nothing changed to satisfy it.
3. **The sugar assessment** (the S5.3 commit) — all four chartered
   tactics (`go_iterate`/`go_bail`/`go_rebase`/`go_run`) TRIMMED with
   one measured reason each (the descriptors are per-example content;
   `Frame/Threshold` and `harness_readout_of_total` already ate the
   rebase/readout work), `derive_seg` mode (a) out of scope and now
   unmotivated. What shipped instead: the one verbatim-repeated idiom
   the assessment found — the loop-guard bridge `decide_natCast_lt_true`
   (79-site census; 7 sites retrofitted, −7 lines, pin `[propext]`).

Slice records: `s5.md` (+ `s4.md` §S4.12). Next per the charter:
slice 6, the discoverability close-out (the Kit Guide + its dry-run
acceptance).

**Checkpoint 6 — S6 COMPLETE (2026-08-18, tip = the S6 commit; 3 units
in one commit, `scripts/ci` PASS).** The arc's last slice, docs-only by
construction (the whole code diff is `/-!` docstring blocks; no
statement, no proof, no pin, no `Audit/Kit.lean` edit, no
`Corpus/`/`baselines/` touch):

1. **`docs/kit-guide.md`** — the situation index, 819 lines, 23 `##`
   sections. All TWENTY section names fixed in `s3.md`'s API-group
   inventory are present verbatim, so every module pointer resolves;
   three sections beyond them, each with a reason (§5 Segments, which
   carries S4.12's per-window guidance table — slice 4 ran on the
   parallel lane and had no inventory row; §22 The disciplines; §23
   Honest limits). All twelve of the charter's named situations
   covered. Every row: kit form · hypothesis shape · the named fixture
   FILE (never a line — the cite-drift rule) · the lint rules that bite.
   Fixture cites re-derived by grep at this tip.
2. **Cross-pointers filled** in 9 modules (the 8 `Future`-marked s3
   slots + a new one in `Sym/Refine.lean`); `grep -rn kit-guide proofs/`
   → 9 hits, 0 `Future`. One factual correction: MapMem's slot named
   two sections ("Map counting", "Map range") that are not among the
   twenty; both now name real sections.
3. **THE DRY-RUN ACCEPTANCE, run TWICE.** Two fresh general-purpose
   agents, no arc context, given only the guide + one example's corpus
   half (`main.go` + `cases.tsv`) and told to plan, not prove, and to
   read nothing. **`tool_uses = 0` in both transcripts** — no example
   module was read, so the measurement is clean. Round 1 (dedup →
   `Examples/DedupAdjacent.lean`): **10 of 13 phases routed correctly**
   — exact on the entry form AND its computed layout, the
   `familyF`-delegation pattern, the array-local store pair, the three
   loop instantiations, the readout twin and its branch reason — with
   **3 guide bugs**, all one defect class: *a section that lists forms
   without saying when the section does not apply* (§18 sent every call
   to the call span; §19 listed `SliceQueue`-only glue and the
   `CompletesIn` algebra flat beside `stepFnIter_chain`; §3 had NO
   applicability test, so a run whose every address is a constant still
   pulled seven heap-algebra forms). Fixed with PRECONDITIONS + a
   negative fixture, not new forms. Round 2 (stein →
   `Examples/Stein/Run.lean`, chosen to exercise every fixed route in
   the OPPOSITE direction): **all four fixes verified** — the footprint
   precondition correctly failed, §18 correctly SPLIT the two calls,
   §19's two tests correctly excluded both — plus **2 new bugs of the
   same class** (§1 stated the program-generic form as a preference
   rather than a condition on the segment spelling; no row existed for
   the MEASURE-driven loop class, which is all four of stein's loops
   and dedup's subject loop). Both fixed; flagged as the one part of
   the guide no dry-run has exercised.

Two tree findings recorded, deliberately NOT acted on (docs-only
slice): `Examples/DedupAdjacent.lean` is an un-retrofitted
`stepFnIter_iterate_bail_rel` consumer (its `sj_loopD` hand-induces
`∃ k ≤ 98·μ`) and re-spells `takePad` locally — both promotion-ledger
candidates. Slice record with both plans and both evaluations
verbatim: `s6.md`. **This closes the arc's chartered slices; next per
the charter is the arc-end gate + the audit ask.**

## FINAL CHECKPOINT — the DONE conjunction at tip 69ef4bda + the boundary commit (2026-08-18)

| clause | requirement | state |
|---|---|---|
| 1 | s1-s2 families lifted, zero survivors, deltas, pins | DONE (s1: 6/6 families, −2,483; s2: 7/7, −1,103; pin trail in the per-slice close-outs) |
| 2 | s3 regularity | DONE (8 modules, 0 renames, 0 pin churn) |
| 3 | s4: gate user-reviewed BEFORE proofs; refinement+witness; outside-TCB walker+deletion; drift in default build; matmul two-stage | DONE (gate discharged 2026-08-18 pre-build; symEvalWindow_refines + Kadane witness same-commit; Sym-deletion full-lib build exit 0; stepFn'_concrete_agrees in default build; matmul = gallery 25 with both stages measured; the S4.12 cost-story reconciliation supersedes S4.3's headline honestly) |
| 4 | s5 shipped or trimmed with reasons | DONE (probe run; lint landed note-only; 4 tactics trimmed with measured reasons, 1 idiom lemma shipped) |
| 5 | s6 guide + dry-run + findings fixed | DONE (two rounds, tool_uses=0 both, 5 guide bugs fixed + verified) |
| 6 | gates green; frozen pins byte-identical; standing record carries (no corpus change on this branch) | DONE (ci PASS at tip; in-build Audit green every commit; corpus untouched — matmul's gallery entry is the chartered acceptance exception) |
| 7 | log current; audit ask POSED | This checkpoint + the operator's ask accompanying it |

Charter integration TODO (OQ3 wording) discharged in this commit.
Open items recorded for the audit/next arc: DedupAdjacent's two
promotion-ledger candidates (s6); the measure-driven-loop guide section
unexercised by any dry-run (s6); the L5 lint's 81 notes as future
option/transport migration candidates (s5).
