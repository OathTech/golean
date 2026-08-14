# Brick-wp promotion-wave review — the G0 mapping (2026-08-15)

Status: the Gallery Campaign G0 unit 2 deliverable (charter
`docs/2026-08-15_gallery-campaign.md` §G0 item 1). Source read
2026-08-15: `deps/brick-wp` @ `52f8a6e` (READ-ONLY, trust-tools rule),
commits `944c555..52f8a6e` — the PROMOTION WAVE that followed the
W1–W7 ergonomics arc — plus its charter,
`docs/2026-08-15_promotion_wave_meta_review.md` (the findings F1–F7
and the P1–P6 wave), and the wave's diffs (P5 `770dc4e`/`b7335b9`,
P6 `f711c70`, outcome `52f8a6e`). Extends the slice-2 mapping
(`docs/2026-08-14_phase2-slice2-proof-library.md` §1) in its format;
the W1–W7 rows there stand unchanged and are not repeated.

Context reminder for the transfer (unchanged from slice 2): brick-wp
is an Iris/Rocq WP stack over C++; our shipped examples use the DIRECT
segment method (conditioned `stepFn` facts + `with_unfolding_all rfl`
segments + fuel measures). Analogues land in the direct-method kit.
The campaign-specific difference from slice 2: G0 is PREEMPTIVE by
user direction — the §12 consumer rule is satisfied by SCHEDULED
consumers (G1's chartered candidate list) plus mandatory retrofits of
≥2 landed ones, so patterns slice 2 closed as "no current demand" are
re-examined against a 13-example pipeline.

| pattern | what brick-wp did | our analogue | status |
|---|---|---|---|
| **F1/P3 — the generic shape catalog** (`BaseUnits.v`: the library held the ALGEBRA while every example re-proved the generic SHAPES — locals, ref params, literals — so the catalog was promoted, parameterized over TU/class/identifier) | Same split, same drift: `StepKit`/`SliceMem`/`FuelMeasure` hold the step-glue and op-fact ALGEBRA, while every array example re-proves the same two SHAPES locally — (a) the setup-loop strong induction (8 instances: `hIsetup_loop`, `wcH_setup_loop`, `hsetup_loop`, `su_loop`, `sh_loop`, `su_loopV`, `su_loopR` ×2 — the same `Nat.strongRecOn` on `n − i` with the same chain/arith/exit boilerplate every time), and (b) WordCount's map executable-fact family (`Examples/WordCount/Pure.lean`), which is `map[uint64]uint64` machinery, not wordcount machinery. | **BUILD-NOW** — G0 item 3a (the P5 setup-iteration schema, reopened: slice 2 §4 closed it "reopenable on the repeated-instantiation grind signal"; a 13-example campaign of mostly array examples IS that signal, in advance) and item 3b (`MapMem`). Chartered consumers: every G1 array-setup candidate (bubble/selection sort, two-sum, RLE, palindrome, dedup, Kadane, dot product, sieve, matrix, stack, queue) for 3a; histogram + fibonacci-memo for 3b (wordcount is the landed third). |
| **F2 — the drifted reimplementation** (`buf_walk` ×4 copies = `wp_walk` minus one branch; DELETED, not promoted — "check Layer 3 before writing a walker") | Reviewed for the same class: the slice-1/2 seals already killed the one verbatim duplicate found (`mem_of_mem_set`, slice-2 §2). The live near-miss class here is not a walker but the per-example INDUCTION boilerplate above — same lesson, resolved by the same response (delete via promotion, F1 row). Nothing else in the kit's orbit reimplements a kit lemma today (checked: the `stepFnIter_chain`/fold/mono family has single homes). | **EXISTS** (as the seal + §12 discipline); the induction copies are handled under F1 |
| **F3 — complete the family** (the dtor trio lived in one example and was duplicated into the next; promoted so the trio family has all members in WpTactics) | The entry-equation macro is our incomplete family: `derive_entry_eq` shipped with 2 of 10 consumers retrofitted (fib, gcd — slice 2 §3), 5 flat modules still hand-rolling the identical dance and 3 program-generic modules recorded as "mechanical, not zero-churn" follow-ups. Leaving it half-adopted is exactly how brick-wp got a duplicated trio. | **BUILD-NOW** — G0 item 3c: retrofit the 5 flat modules (`mmh`/`wcH`/`iharness`/`harness`/`revH` `_entry_eq`); extend the macro to the program-generic shape via the recorded show-bridge (slice-2 §3); all 10 consumers landed. |
| **P4 — the flagship exercise** (`bcopy_ok`: EVERY promoted piece exercised end-to-end on a fixture disjoint from both source examples) | The charter's flagship rule (G0 done-item 4): the FIRST new G1 example is the kit's integration exercise — kit + macro only, no hand-rolled segment where a kit form exists; deviations recorded as kit gaps. The disjoint-fixture property holds by construction (a NEW example is disjoint from every retrofit source). | **BUILD-NOW, discharged inside G1** (scheduled, not a G0 deliverable; recorded here so the mapping is complete) |
| **P5 — three-place wiring + assumptions audit** (new module wired into `all`/audit deps/cat-list + fixture-drift rules; 38 new `Print Assumptions` entries covering the promoted surface AND the test lemmas) | Our audit wiring is stronger by default (the in-build sweep covers every declaration; `scripts/ci` fails if any proofs file leaves the audited import closure) but the KIT surface has no per-lemma pins: `Audit.lean` + shards pin examples' headline/witness names only, so a kit lemma's axiom set is policed only by the coarse trio sweep, not pinned verbatim. brick-wp's move — the promoted surface gets its own audit entries in the promotion wave — transfers directly. | **BUILD-NOW** — G0 item 4: `proofs/Audit/Kit.lean`, `#print axioms` `#guard_msgs` pins for every public `StepKit`/`SliceMem`/`MapMem`/`FuelMeasure` lemma + the macro fixture theorems, wired like the example shards. |
| **P6 — the rollback wave** (after promoting, the example copies were DELETED or reduced to one-line delegations in the same series: −317/+128, net −189 while gaining capability; "a lift is not done while its duplicates survive") | Our §12 loop already requires same-commit retrofits of ≥2 consumers; what P6 sharpens is the DELETION half as a completion criterion — a lift with surviving duplicates is an open item, not a done one. Adopted for every G0 lift: the covered example-local copies are deleted or reduced to delegations in the same commit series, and the log records the net-line accounting per lift. | **EXISTS** (as §12 discipline) + **adopted as G0 completion criterion** for items 3a–3c |
| **Meta-review outcome section** (net-line accounting per wave item; deliberate NON-promotions logged with reasons — the fuzzy-resourced variant, the green-file churn, the fixture-dependent composite where "the RECIPE is what transfers") | The campaign log's measured-deltas standard (§12c / charter G0 measures) is the same practice; the explicit NON-promotion log is the part worth stealing — slice 2 did it once (W3 chaining, W4 ghost) and G0 continues it: every judgment call that declines a lift gets a logged one-liner with the reason, in `docs/gallery-campaign-log/g0.md`. | **EXISTS** (log format); non-promotion logging adopted for G0 item (d) |
| **F5 — factor the conflated tactic** (`wp_nd_args_step` = splitter + arg-eval; the splitter factored out, the old name redefined as the composition — behavior-identical for consumers) | Reviewed the kit for conflations: the conditioned one-step lemmas are each single-purpose (one machine arm, one conditioned fact); the composition lemmas (`completesIn_comp`, `stepFnIter_chain`) are already the factored primitives. No conflated member found. | **not applicable** (no consumer pain, no candidate — logged as a non-promotion) |
| **F6 — needlessly concrete internals** (`wp_int_cast_val`'s `vm_compute` replaced by the general argument that also covers the concrete cases) | The precedent already runs here: `storeTarget_arrayLocal_u64` was generalized cap-8 → `N` at promotion (slice 1); the macro's quoters stay fail-closed-narrow BY DESIGN (widen on a real harness, not preemptively — the opposite direction is correct for trust-adjacent tooling). | **EXISTS** (as practice); no current instance owed |

Transfer verdict: the wave's four load-bearing moves — catalog the
generic shapes (F1), complete half-adopted families (F3), pin the
promoted surface in the audit (P5), and treat deletion of duplicates
as the lift's completion test (P6) — all have live pull here and
become G0 items 3a/3b (F1), 3c (F3), 4 (P5), and the per-lift
rollback rule (P6). The flagship exercise (P4) is scheduled into G1's
first example. The two practices brick-wp needed and we already have:
the declaration-exhaustive axiom sweep (stronger than per-name
`Print Assumptions` as a floor — the per-name pins ADD exactness, not
coverage) and the §12 consumer rule itself, which their arc waived
and re-learned; the campaign keeps it in its scheduled-consumer form.
