# The Gallery Campaign log — INDEX (2026-08-15)

Charter: `docs/2026-08-15_gallery-campaign.md`. This directory is the
campaign's running record: ONE FILE PER GOAL (`g0.md` … `g4.md`) plus
this index (per-goal totals + checkpoint summaries), so parallel
sub-lanes never write the same file (process amendment `ea7c689a`,
user-authorized 2026-08-15).

## What the log is

Per-unit entries (example / extension / dossier / debt item): status,
judgment calls, findings, costs. The log updates IN THE SAME COMMIT as
the work it describes. Checkpoint summaries land here at least every 5
units, with honest totals per goal (complete / gap / remaining).

**The tension rule** (charter §Judgment calls): where principles
tension, **honesty beats velocity beats elegance**. A recorded honest
gap outranks a ground-out grind; a grind outranks a pretty claim that
overstates.

**Judgment-call format** (one line each, in the owning goal file):
`JC: <the call> — <the principle applied>.`

## Per-goal totals

| goal | done | remaining | notes |
|---|---|---|---|
| G0 (opening kit phase) | 5 of 5 mandatory units; (d) assessed → deferred to its pulling G1 example; **item 4 (flagship rule) DISCHARGED** by G1.1 | 0 — G0 CLOSED | see `g0.md`; the flagship's kit-gap report is in `g1.md` |
| G1 (gallery to twenty) | **1 of ≥13** new COMPLETE entries (`histogram`, the flagship); **+ the KIT-GAP CLOSURE unit (G1.1-KG): all six gaps CLOSED**; **+ the GUARDRAILS WAVE (G1.2): the CORPUS HALF of 15 further examples landed** — corpus rows, golden pins, `*Program` modules and stub proof roots, one commit each | ≥12 COMPLETE (the 15 wave entries are landed GUARDRAILS, NOT COMPLETE entries — each needs its headline) | see `g1.md`; the wave table is there, the extension pull-list in `g2.md` |
| G2 (extensions) | **1 BUILT (E1, 2026-08-15)**; the PULL-LIST is established and probe-grounded (`g2.md`) | E3 to build (consumer `stein` landed, 9 rows red); a THIRD pulled extension must be found | **HONEST FINDING: the G1 set pulls TWO of the four, not three.** E4 is a NON-PULL — `strrev` landed E4-independent, 12 rows PASS; E2 is a reasoned NON-PULL (observation is by return, not printing). Operator call recorded in `g2.md` |
| G3 (evidence dossiers) | 0 | register = denominator, fixed at dossier-lane start | register lives in `g3.md`, **enumerated by the dossier lane's first commit** (process amendment `ea7c689a`: the register is that lane's deliverable, not G0's) |
| G4 (infrastructure debt) | 0 of 4 | 4 | |

## Checkpoint summaries

(at least every 5 units; newest first)

- 2026-08-15, checkpoint 5 (unit G2.E1, 1 commit): **THE FIRST EXTENSION
  IS BUILT.** E1 — the differential driver's argument domain past
  `int64` — landed as 15 guardrail rows + a 3-line semantic change in
  `tools/coverageharness` + two id renames + the re-pin, one commit, no
  Lean source touched. Guardrails-first was MEASURED, not asserted: the
  15 rows were committed and run BEFORE the driver change and all 15
  failed at `stage=go-harness` with the recorded `strconv.ParseInt …
  value out of range`; after the change all 15 PASS. **No fidelity
  finding** — real `go run` and the machine agree everywhere in the
  `[2^63, 2^64)` wrap region the machine had always claimed, which is
  the point of the extension and the interesting negative result.
  Consumers: `dotprod` (its four probe-verified wrap shapes lifted into
  the true wrap region) plus `reverse`/`minmax`/`isort`/`wordcount`,
  whose `2^64-1` HAND PROBES from the 2026-08-14/15 audits are now
  permanent oracle rows. Baseline re-pinned from a full `scripts/ci
  --diff`: **1791 cases, 1663 PASS, 128 FAIL** (was 1776/1648/128), drift
  EXACTLY the 15 new ids, FAIL count unchanged, nothing MISSING.
  Gallery corrected in the same commit: `reverse`'s and `minmax`'s
  driver-limitation sentences (the "no oracle row reaches that region" /
  "machine only, no `go run` in the loop" admissions) are now stale and
  say so; row counts 11→14 (reverse), 13→16 (minmax), 11→13 (isort),
  11→14 (wordcount); `scripts/render-gallery` green, 52 blocks.
  **ONE CHARTERED SUB-ITEM DID NOT LAND, and needs an operator ruling:**
  the `examples/reverse/harness-wrapping` → `harness-near-max` rename
  (the seed does not wrap; the id names a behaviour it never exercised).
  It was made and ran green, then `scripts/ci`'s baseline re-pin guard
  refused it — the guard's model is PASS-id set inclusion, so a RENAMED
  id is indistinguishable from a REGRESSED one, and its only discharge is
  a `docs/BUGS.md` `- Cases:` line, i.e. calling a rename a fidelity bug.
  Backed out rather than launder the gate or ship it red; no corpus id
  has ever been renamed or retired before, so the guard has simply never
  met this event. The minimal, strictly-MORE-precise amendment is drafted
  in `g2.md` for a change that owns `scripts/ci`.
  Totals: G0 5/5; G1 **1 COMPLETE** + 16 guardrail suites landed; G2
  **1 of ≥3 BUILT** (E3 remains, third must be found); G3 22/22
  dossiers; G4 0/4.

- 2026-08-15, checkpoint 4 (unit G1.2, 18 commits): THE GUARDRAILS WAVE
  COMPLETE. The corpus half of **16 examples** landed in one pass —
  bubble, selsort, twosum, rle, stein, powmod, palin, dedup, kadane,
  dotprod, sieve, matmul, stack, queue, strrev, fibmemo — each with
  `main.go` + `cases.tsv`, a golden pin (repr baseline + `*Program`
  module, both `check-golden` links green), a STUB proof root carrying
  the named harness `rfl` pin and NOTHING else (verified: 1 def + 1
  theorem + 0 `sorry` per stub), and its two aggregator imports so the
  module is in the audited closure from birth. `scripts/ci` PASS at
  every one of the 16 commits.
  **203 new corpus rows: 194 PASS, 9 FAIL** — the nine being `stein`'s
  DELIBERATE quarantine (binary GCD in its natural Go form puts a call
  in a `&&` operand; fail-closed at stage `frontend-export`, verbatim
  message pinned, calls NOT hoisted to make it pass). Baseline re-pinned
  ONCE, dated, from a full `scripts/ci --diff` (3m43s, 1776 cases);
  drift was EXACTLY the 203 new ids with no pre-existing id moving, and
  the untriaged fidelity backlog is unchanged at 16 — `frontend-export`
  is a coverage gap, not a fidelity failure.
  **G2's pull-list established by PROBE, not by list** (`g2.md`): E1 and
  E3 are genuinely PULLED with landed consumers (`dotprod`, `stein`);
  E4 is a NON-PULL demonstrated by landing `strrev` without it, 12 rows
  PASS; E2 is a reasoned NON-PULL. Honest status: the G1 set pulls TWO
  of four, not three — surfaced for an operator ruling rather than
  re-scoped to keep the count.
  Style triad choices: 12 S3-relational, 4 S2-scalar, 0 S1-verdict —
  the S1 verdict style was not forced anywhere, because returning the
  data always said more than returning a 1. Divergence guard never
  triggered; no example dropped or substituted.
  Totals: G0 5/5; G1 **1 COMPLETE** + 16 guardrail suites landed; G2
  pull-list established, 0 built; G3 22/22 dossiers; G4 0/4.

- 2026-08-15, checkpoint 3 (unit G1.1-KG, 6 commits): KIT-GAP CLOSURE
  COMPLETE — all six flagship gaps closed, each as lift + BOTH landed
  consumers retrofitted + P6 rollback in the same commit, `scripts/ci`
  PASS per commit. Order was dependency-driven (M2, P1 first — they
  are C1's statement vocabulary — then C1, R1, P2, M1; JC logged).
  The headline deliveries: `GoLeanProofs/MapLoops.lean` (new kit
  module, ~1,100 lines) carrying the name-parameterized counting
  iteration/loop, the per-placement discharge pack
  (`mapCountIter_at` — nine conditioned discharges proven once over
  base state + live front + nine mostly-`rfl` placement facts), and
  the abstract choice-pick loop (`mapPickLoop_generic`, accumulator
  laws as conservation invariants); MapMem gains the counting fold +
  the binder-generic pick step; SliceMem gains `familyMod`/`prefixPad`;
  StepKit gains `DeadFrom` + `set_append_left`. P6 scale: GAP-C1 alone
  deleted 1,948 consumer lines across FOUR landed placements
  (CountGeneric.lean deleted outright; Histogram/CountLoop 825 → 376
  lines, 71 s → 1.2 s). Every headline statement untouched; every
  existing `#guard_msgs` pin byte-identical (pinned proof-layer names
  survive as one-line delegations); kit pins 81 → 116, all transcribed
  from fresh probes. Projected histogram-class successor: ~2,900–3,000
  lines / ~2.5–3 h (was 3,890 / 3.5 h). Totals: G0 5/5; G1 1 of ≥13 +
  kit-gaps closed; G2 0; G3 22/22 dossiers; G4 0/4.

- 2026-08-15, checkpoint 2 (unit G1.1, 2 commits): THE FLAGSHIP
  LANDED. `histogram` — a `map[uint64]uint64` count map, a queried-key
  read and a VARIABLE-FREE `for range` — is COMPLETE on all eight
  checklist items: 13 differentially green corpus rows (campaign's
  first corpus touch; full 1573-case run + negative run recorded,
  baseline re-pinned same-commit with a reason that was CORRECTED after
  checking it), golden pin green on both links, headline
  `histogram_ok` over `runFunctionWithContextM` at the classical trio
  with 13 axiom pins in a new Audit shard, shipped fuel bound
  `210·n + 344` with the exact measured count `194·n +
  16·distinctCount vals + 344` recorded separately, deletion test RUN
  (4/4 binders load-bearing), gallery entry rendered (52 verbatim
  blocks, exit 0), peak cost 2045 MiB (bar 2.5 GiB), `scripts/ci` PASS.
  **Five KIT GAPS recorded with exact shapes** (GAP-C1 the counting
  layer's name specialization ~600 lines, GAP-R1 the range induction's
  body/binder specialization ~130, GAP-P1 the counting fold ~150,
  GAP-P2 the setup family ~83, GAP-M1 the pick step ~45, GAP-M2
  `DeadFrom` ~30) — all ABSTRACTION gaps, none capability gaps; the kit
  carried every machine step (366 invocations, zero hand-rolled `stepFn`
  unfoldings). Honest verdict: the kit carried the example at the STEP
  level, not the STRUCTURE level; ~27% of the example's Lean is
  gap-witness code that closing GAP-C1/R1 would delete. Totals: G0 5/5
  + item 4 discharged; G1 1 of ≥13; G2 0; G3 22/22 dossiers; G4 0/4.

- 2026-08-15, checkpoint 1 (units G0.1–G0.4 + (d), 7 commits): G0
  CLOSED. Log init; brick-wp mapping note; P5 setup-iteration schema
  (kit +2 lemmas, ALL 9 shipped setup inductions retrofitted, zero
  `strongRecOn` setup copies survive); MapMem promotion (wordcount
  retrofitted −346/+17 in Pure, chartered histogram + fib-memo);
  entry-equation completion (all 10 entry eqs derived, macro gains
  the program-generic form, example modules net −131); Audit/Kit.lean
  (81 verbatim kit-surface axiom pins). (d): bounded-iteration
  variant assessed and deferred to its pulling G1 example. Totals:
  G0 5/5; G1–G4 untouched. Headline statements byte-unchanged
  throughout; every commit's tree built green (targeted builds per
  commit; full `scripts/ci` PASS at the G0.2 tip and at this tip —
  fast gate + `GOLEAN_ALLOW_NO_DIFF=1`, proofs-only lane, cached
  full differential record at the merge-base stands).
