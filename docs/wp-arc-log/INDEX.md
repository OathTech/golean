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
| s4 | mirror symbolic evaluator | not started (USER design-note gate) | — | — | — |
| s5 | emission + instantiation sugar | not started | — | — | — |
| s6 | discoverability close-out | not started | — | — | — |

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
