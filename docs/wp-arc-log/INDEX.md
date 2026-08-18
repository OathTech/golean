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
| s1 | lift wave 1 (pure lifts) | **PARKED (orderly pause)** — 5 of 6 lift families landed | 5 / 6 | 2,266 (consumers; net −1,548 with +718 delegation/instantiation lines) | +72 (116 → 188) |
| s2 | lift wave 2 (new shapes) | not started | — | — | — |
| s3 | library regularity | not started | — | — | — |
| s4 | mirror symbolic evaluator | **phases 1–3 DONE** (design gate discharged 2026-08-18; drift + refinement theorems in the default build; matmul acceptance LANDED — gallery entry 25) | 12 (S4.0–S4.11) | — (additive layer; matmul: the withdrawn 2,375-line snapshot lands as 2,486 incl. the mirror fixtures) | +6 (Sym surface, incl. `symEvalWindow_refines'`) |
| s5 | emission + instantiation sugar | not started | — | — | — |
| s6 | discoverability close-out | not started | — | — | — |

Derivations for the s1 row: per-unit `git diff --numstat` figures in
`s1.md` units S1.1–S1.5 (deleted 256+315+151+1481+63 = 2,266; inserted
97+174+20+317+110 = 718); pin count
`grep -c '^#guard_msgs in #print axioms ' proofs/Audit/Kit.lean` → 188.

## Checkpoints

**Checkpoint 1 — S1 PARK (2026-08-16, ≤5-unit cadence met at 6 units;
tip = the park commit).** Units S1.0–S1.5 landed, one commit each,
`scripts/ci` PASS at every commit. Lift 6 not started. Full park
record: `s1.md` §PARK RECORD.

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
