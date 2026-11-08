# The defect-neighbourhood campaign — closure report (2026-11-08)

The dated report the campaign plan's §7 asks for
(`docs/2026-10-27_defect-neighbourhood-campaign.md`, approved [USER]
2026-10-27 with its four §6 decisions ruled as recommended: agreements on
distinct routes pinned as rows; retired-construct entries listed and marked,
not swept; the sweep after train 21 and before the release lane; the one-grep
speedbump added). Written by the [AGENT] lane `records/campaign-closure-1108`
at the train-34 stage `73b634f0` (`stage/train-34-1108`, 16 commits over `main`
at `4296a876`, the train-32 stage; trains 33 and 34 carry the last two sweeps
and the last fix, their merge asks pending). The campaign's running record is
row 56 of `docs/2026-10-12_release-readiness.md`; its classification record is
`docs/defect-shapes.md`, dated closed today.

Every number here is derived from the tree at `73b634f0` and says how (§9 lists
the commands); a number that exists only in a lane's ephemeral report is cited
through row 56 or the lane's commit message and marked **[lane]**. Where two
sources disagree, both are given. Dates: the records dated 2026-10-27 from the
plan onward were written late on 2026-10-26 UTC (the coordinator's calendar
error, noted in row 56 and left as written since the names are cited); the
campaign ran 2026-10-26 → 2026-11-08 by the box clock.

## 1. The headline

- **Entries.** 216 live fidelity entries in `docs/BUGS.md` — 183 fixed, 33 open,
  15 of them red-by-design (`Expect: FAIL`) — plus 9 tombstones resolving to
  `docs/APPARATUS-DEFECTS.md`, which holds 14 entries (the 9 moved on
  2026-10-27 and 5 found during the campaign). At step 2's launch the index
  held 166 live entries (175 after step 1's 39 late entries, minus the 9 moved);
  the campaign added 50: 46 sweep findings and 4 from the train-32 pre-merge
  audit.
- **Shapes.** 29 ids. 27 swept: 26 by probing both sides against gc go1.26.5
  (S1–S23, S27–S29) and one by reading the core (S26). S24 (tool-boundary
  fail-opens) retired from the sweep order on 2026-10-27 when its members left
  for the apparatus record ([USER] ruling, relayed). S25 (retired construct,
  BUG-002) listed and marked, not swept ([USER] 2026-10-27, §6.2).
- **Cells.** About 7,700 matrix cells enumerated across the 26 gc-probed shapes,
  about 6,300 of them probed on both sides **[lane figures, §4]**; S26 read 282
  grep hits plus 24 Except-absorbing arms, about 150 value-bearing `none` arms
  and 37 Option projections across the nine core and driver files **[lane]**.
- **Rows.** The differential corpus grew 4166 → 7785 (+3619, nothing removed):
  3549 rows named `sweep-s<n>-*` by the 26 sweep lanes and 70 by two fix lanes
  (62 PASS; 8 red by design on BUG-340's Cases line).
  The negative corpus grew 437 → 645 (+208, nothing removed): 154 `sweep-s<n>-*`
  rows and the S20 sweep's 54 unprefixed rows. At the tip the sweep rows stand
  3450 PASS / 99 FAIL (every FAIL on a `BUGS.md` Cases line) and the negative
  sweep rows 206 PASS / 2 FAIL (BUG-221's). The lanes reported 235 differential
  and 13 negative rows born red **[lane]**; 3 were retired by a fix lane
  (BUG-296), 133 + 11 turned PASS through the fix lanes, 99 + 2 are red at the
  tip.
- **Defects.** 46 fidelity findings entered open by the sweeps (§5): 32 fixed
  through 11 fix lanes landing on trains 24, 25, 26, 28, 31, 32 and 34; 14 open,
  nine of them awaiting a ruling posed to the owner (§6). 5 apparatus findings
  entered in `docs/APPARATUS-DEFECTS.md`, all open. 4 entries from the train-32
  audit of the fix lanes, all fixed.
- **Left open.** The cells each shape left — named refusals, envelope questions
  and the owner's rulings — are in §6 by shape; the rulings posed and not yet
  ruled are listed there by name.
- **The speedbump.** `scripts/check-bugs.sh` check 7 (report-only): every
  `Status: fixed` entry dated on or after 2026-10-27 carries a `- Neighbourhood:`
  line. At this tip it names nothing after four records corrections made at the
  closure (§8); before them it named BUG-136 (undated), BUG-227, BUG-300 and
  BUG-301.

## 2. The entries covered

The record of `docs/defect-shapes.md` §2 holds one row per live entry of the
index. Counts at the closure, reconciled against the index:

| | index (`docs/BUGS.md`) | record §2, before the closure | record §2, at the closure |
|---|---|---|---|
| live entries / rows | 216 | 215 | 216 |
| fixed | 183 | 178 | 183 |
| open | 33 | 37 | 33 |
| red-by-design (`Expect: FAIL`) | 15 | 13 | 15 |
| tombstones | 9 | — (rows removed 2026-10-27) | — |

What moved at the closure ([AGENT], this lane, each from the index's own
lines): the missing row for BUG-286 (the S9 sweep's finding, fixed by
`frontend/fix-hoist-1027` on train 26; the fix lane's records had updated
BUG-287's row and not added this one); the status cells of BUG-276, 277, 278
and 279 (`open` in the record, fixed by the same lane on train 26 in the index);
the red-by-design mark on BUG-340 and BUG-341 (fixed as guards on train 31,
`Expect: FAIL` in the index); §1's member counts (stale for S5, S7, S8, S9,
S13, S20, S21, S24 after the sweeps' findings and the audit's entries); and
three duplicated items left in §3 by the train-33/34 restacks (the S15 and S16
items' pre-sweep versions, the S27 item's repeated tail). Nothing else in the
record was changed; §3's member-list parentheticals stay as the lanes wrote them
at sweep time (several say «open» of findings fixed later — the index is
current).

By status in the index: `grep -E '^- Status: ' docs/BUGS.md | sed -E 's/^- Status: ([a-z]+).*/\1/' | sort | uniq -c`
→ 183 fixed, 33 open, 9 moved. Red-by-design: `grep -c '^- Expect: FAIL' docs/BUGS.md`
→ 15 (BUG-078, 084, 091, 093, 094, 100, 127, 128, 130, 131, 132, 153, 340, 341,
370). Live headings: 225 `## BUG-` headings minus the 9 `[MOVED …]` tombstones.
`scripts/check-bugs.sh` → `ok (216 bug(s), 9 moved tombstone(s) …)`.

By coverage of the sweep's record: 206 live entries carry a `- Neighbourhood:`
line (208 lines; BUG-171 and BUG-287 carry two, the sweep's over the earlier
placeholder or the fix lane's); before the closure 203 did, BUG-227, 300 and
301 being lined at the closure from their fix commits (§8). The 10 without:
BUG-002 (S25, not swept by the ruling), BUG-091 (S24, kept in the index pending
the owner's word on its class, row 56 train 22), and eight of the sweeps' own
open findings whose matrix is on the member entry the sweep enumerated from —
BUG-218, 221, 280, 410, 411, 413, 414, 415 (the check covers fixed entries only).

## 3. The shapes

The 29 shape ids of `docs/defect-shapes.md` §1, with each one's disposition.
Trains are the stage that carried the sweep (`git log --grep='^Stage train'`;
trains 22 and 26 have no stage commit of that name — 22 is the records commit
`12a878eb`, 26 the hoist fix lane's landing, both named in row 56); `main` is
at train 32, so the S22, S16 and S15 sweeps (trains 33, 34) are staged.

| id | shape | disposition | lane · date · train |
|---|---|---|---|
| S1 | Implicit conversion omitted at an assignable context | swept, gc | `sweep/s1-implicit-conv` · 2026-10-27 · 25 |
| S2 | Conversions: a missing kernel arm or a value not retagged | swept, gc | `sweep/s2-conversions` · 2026-10-26 · 23 |
| S3 | Type identity keys | swept, gc | `sweep/s3-type-keys` · 2026-10-26 · 23 |
| S4 | Identity, equality and nil-ness | swept, gc | `sweep/s4-identity` · 2026-10-26 · 23 |
| S5 | Method sets | swept, gc | `sweep/s5-method-sets` · 2026-10-27 · 24 |
| S6 | Assignment and return: the two-phase order | swept, gc | `sweep/s6-two-phase` · 2026-10-27 · 25 |
| S7 | Ordered events reordered by the hoist | swept, gc | `sweep/s7-hoist-order` · 2026-10-27 · 25 |
| S8 | Spec-unsequenced order realized as one member | swept, gc | `sweep/s8-unseq` · 2026-10-27 · 27 |
| S9 | Evaluation count | swept, gc | `sweep/s9-eval-count` · 2026-10-27 · 25 |
| S10 | Run-time panic missing or wrongly kinded | swept, gc | `sweep/s10-panics` · 2026-10-27 · 24 |
| S11 | Kinds, widths and float bit patterns | swept, gc | `sweep/s11-kinds` · 2026-11-05 · 29 |
| S12 | Panic and recover | swept, gc | `sweep/s12-panic-recover` · 2026-10-27 · 24 |
| S13 | Variable binding | swept, gc | `sweep/s13-binding` · 2026-10-27 · 27 |
| S14 | Map iteration over a mutating map | swept, gc | `sweep/s14-map-iter` · 2026-10-27 · 27 |
| S15 | Scheduling boundaries and the menu | swept, gc (sampled) | `sweep/s15-scheduling` · 2026-11-07 · 34 (staged) |
| S16 | Race detector footprint and keys | swept, gc (sampled) | `sweep/s16-race` · 2026-10-27, re-verified 2026-11-08 · 33 (staged) |
| S17 | Lowering coverage holes | swept, gc | `sweep/s17-forms` · 2026-11-05 · 29 |
| S18 | Implementation-specific sizes | swept, gc | `sweep/s18-sizes` · 2026-10-27 · 28 |
| S19 | Package initialization order | swept, gc | `sweep/s19-init-order` · 2026-10-27 · 28 |
| S20 | Admission boundary | swept, gc | `sweep/s20-admission` · 2026-10-27 · 24 |
| S21 | Stdlib shims and source-through | swept, gc | `sweep/s21-stdlib` · 2026-11-05 · 30 |
| S22 | The readout | swept, gc | `sweep/s22-readout` · 2026-11-07 · 33 (staged) |
| S23 | Resource budgets | swept, gc (hand cells under `capped`) | `sweep/s23-budgets` · 2026-11-05 · 30 |
| S24 | Fail-open defaults at tool boundaries | RETIRED 2026-10-27: its nine members are the apparatus record's ([USER] ruling, relayed); one member, BUG-091, kept in the index pending the owner | lane `records/apparatus-record-1027` · train 22 |
| S25 | Retired construct | NOT SWEPT by the ruling ([USER] 2026-10-27, §6.2): BUG-002's mechanism is gone; its residue is the concurrency-granularity obligation (U-5), not a differential defect | — |
| S26 | Absorbing default in the semantic core | swept BY READING, not by gc (the shape's own method, §3 of the record) | `sweep/s26-core-defaults` · 2026-10-26 · 23 |
| S27 | Byte transparency of string-carrying channels | swept, gc | `sweep/s27-bytes` · 2026-10-27 · 27 |
| S28 | Spelling admission | swept, gc | `sweep/s28-s29-spelling-symbols` · 2026-11-05 · 30 |
| S29 | Synthetic-symbol bookkeeping | swept, gc | same lane · 2026-11-05 · 30 |

Order and batches as run (row 56): batch 1 S4, S2, S3, S26 (train 23); batch 2
S20, S10, S12, S5 (train 24); batch 3 S1, S6, S9, S7 (train 25); batch 4 S27,
S8, S14, S13 (train 27); batch 5 S19, S18 (train 28), S11, S17 (train 29),
S28+S29, S23, S21 (train 30); then S22 and S16 (train 33), S15 (train 34). The
plan's §4 order (wrong answers with status ok first, then wrongly-stuck and
refusal shapes, then the readout) was kept except that S15 and S16 — begun in
batch 5 — finished last after the session stops of §7.

## 4. Cells probed and rows added, per shape

Cells, probe subjects and born-red counts are the lanes' **[lane]**, read from
`docs/defect-shapes.md` §3 (the lanes' own lines) and checked against the sweep
commit messages and row 56; «probed» is cells probed on both sides, the rest of
each matrix being covered by existing rows, out of scope by name, or hand-only.
Rows at the tip are derived from the baselines: a row belongs to shape S*n* when
its id contains `sweep-s<n>-` (S20's 54 negative rows carry no prefix and are
listed in the negative baseline's S20 re-pin header); stage is the baseline's
third column (`-` strict, `membership`, `confluent`, `racy`).

| shape | matrix → probed [lane] | rows at the tip (differential) | negative rows | born red [lane] | findings (BUG) |
|---|---|---|---|---|---|
| S1 | 208 → 168 | 209 strict, all PASS | — | 0 | none |
| S2 | 118 → 74 | 96 strict, all PASS | — | 0 | none |
| S3 | 183 probe subjects, 166 agreements | 162 strict, all PASS | — | 0 | none |
| S4 | 91 → 73 | 94 (60 strict + 1 confluent + 3 racy PASS; 30 FAIL: BUG-176 14, BUG-170 10, BUG-121 6) | — | 30 | 176 |
| S5 | 116 → 74 | 61 strict, all PASS | 15 PASS | 0 | none (301 found by S13 sits here) |
| S6 | 165 → 112 | 95 strict, all PASS | — | 0 | none |
| S7 | 182 → 145 (206 subjects) | 196 (183 PASS; 13 FAIL on BUG-280) | 3 PASS | 43 | 276, 277, 278, 279, 280 |
| S8 | 149 + 71 variants → 127 (201 subjects) | 180 (97 strict + 78 membership PASS; 5 FAIL on BUG-312) | — | 46 | 310, 311, 312, 313 |
| S9 | 217 → 177 | 247 strict, all PASS | — | 8 | 286, 287 (→ S28) |
| S10 | 151 → 147 subjects | 129 (126 strict + 3 confluent), all PASS | — | 3 (BUG-226's) | 227, 226 (→ S17) |
| S11 | 2565 → 2217 | 324 strict, all PASS | 24 PASS | 0 | none |
| S12 | 181 → 112 | 106 (105 PASS; 1 FAIL on BUG-236) | — | 1 | 236 |
| S13 | 257 → 199 (186 rowed green, 7 disagreeing, 6 by hand) | 197 strict, all PASS | 16 PASS | 9 | 300, 301 (→ S5), 302 (→ S29) |
| S14 | 102 → 87 | 83 (61 strict + 21 membership + 1 confluent), all PASS | — | 0 | none |
| S15 | 106 → 69 (54 as rows, 15 by hand; 17 350 gc draws) | 64 (6 strict + 45 membership + 13 confluent), all PASS | — | 0 | 360 (+ 361 apparatus) |
| S16 | 120 → 86 (89 subjects; 20 sampled gc schedules per cell) | 88 (33 racy + 46 confluent + 2 membership PASS; 7 strict FAIL: BUG-371 4, BUG-041 1, BUG-132 1, BUG-370 1) | — | 7 | 370, 371 |
| S17 | 300 → 125 | 390 strict, all PASS | 42 PASS | 5 | 390, 391 |
| S18 | 1055 → 1042 | 75 (47 strict + 28 membership), all PASS | — | 0 | none |
| S19 | 95 → 73 | 53 (47 PASS; 6 FAIL: BUG-340 2, BUG-341 4, red by design) | 3 PASS | 6 | 340, 341 |
| S20 | 113 → 85 (174 probe programs) | 31 strict, all PASS (34 born; 3 retired → BUG-296) | 54 unprefixed (52 PASS; 2 FAIL on BUG-221) | 4 + 11 negative | 216, 217, 218, 219, 220, 221 |
| S21 | 150 → 93 (194 hand subjects) | 256 (255 PASS; 1 FAIL: BUG-236's second route) | 7 PASS | 16 | 400, 401, 402 |
| S22 | 174 → 147 (91 as rows, 56 by hand) | 88 (84 PASS; 4 FAIL on BUG-093, by design) | 3 PASS | 5 + 2 negative | 430 (+ 431 apparatus) |
| S23 | 109 → 80 (49 as rows, 31 by hand under `capped`) | 62 (30 PASS; 32 FAIL by design: BUG-078 15, BUG-131 15, BUG-090 2) | — | 33 | 410, 411, 412, 413, 414, 415 |
| S26 | by reading: 282 grep hits, 24 Except arms, ≈150 `none` arms, 37 Option projections | no rows (both findings latent; eval pins `absorbingDefaultResidualFacts`) | — | 0 | 206, 207 |
| S27 | 122 → 97 (139 subjects) | 127 strict, all PASS | 14 PASS | 0 | none (297, 298 apparatus) |
| S28 | 537 → 410 | 79 strict, all PASS | 27 PASS | 10 | 420, 421, 422 |
| S29 | 145 → 126 | 57 strict, all PASS | — | 9 (red on main, green under train 28's fix) | none |
| **total** | ≈ 7,700 → ≈ 6,300 | **3549** (3450 PASS / 99 FAIL): 3176 strict PASS, 174 membership, 64 confluent, 36 racy, 99 FAIL (50 `differential`, 24 `frontend-export`, 25 `lean-observation`) | **208** (206 PASS / 2 FAIL) | 235 + 13 | 46 |

The 70 unprefixed differential rows are the fix lanes' own: 23 by
`frontend/fix-paren-forms-1105` (`assign-order/fix-paren-forms-blank-routes` 10,
`control-flow/fix-paren-forms-fallthrough-empties` 7,
`functions/fix-paren-forms-callee-shapes` 6) and 47 by `frontend/fix-e7-cut-1107`
(`evalorder/fix-e7-cut-*` 21, `fmt/fix-e7-cut-*` 7, `init/fix-e7-cut-*` 19): 62
PASS and 8 FAIL at the tip, the 8 red by design on BUG-340's Cases line
(`init/fix-e7-cut-{generic-method,inlined-literal,partial-static}/*`, cause
`c-pin/hidden-dep-init-order`: the E7 guard's foldable targets refuse by name
until the E7 question is ruled, §6). Sweep packages at the tip: 410 directories
`Corpus/coverage/exec/*/sweep-s*/` and 154 `Corpus/coverage/negative/compile/*/sweep-s*`
(one case each).

Where the sources differ on a row count: the S19 lane's §3 line says 56 rows
where its commit (`9e4c7c05`) and the baseline say 53 differential plus 3
negative; the S20 sweep commit (`9518f781`) says 33 exec subjects where §3 and
row 56 say 34 (the baseline holds 31 after the fix lane retired 3); the S8 lane
says 10 packages where the tree holds 9 `sweep-s8-*` directories carrying its
180 rows (the unseq-seam fix lane re-laned 7 membership rows strict and the
package set was merged at train 27 — the row count agrees, the package count
is the lane's); the S10 lane's 16 packages are 17 at the tip with BUG-226's
`range/sweep-s10-zero-len-two-vars`; the S13 lane's 18 green packages are 21
with the three red-first ones; the S19 lane's 17 packages are 19 after the
init-admission fix lane split the refused rows one package per verdict.

## 5. The defects found and fixed

### 5.1 The 46 fidelity findings of the sweeps

Entered open with a red row (plan §4 step 3, [USER]-approved 2026-10-27), then
fixed through the normal train. «Train» is the stage that carried the fix; the
BUG numbers were reserved per lane in blocks of ten ([AGENT] coordinator,
2026-10-26, so parallel findings could not collide), which is why they are
sparse.

| found by | BUG | status at the tip | fixed by (lane · train) |
|---|---|---|---|
| S4 | 176 | open — an envelope question at a latitude point (zero-size element and field addresses), the owner's | — |
| S26 | 206, 207 | fixed (latent; hand-built state only) | `core/fix-bug206-207-1027` · 24 |
| S20 | 216, 217, 219, 220 | fixed | `frontend/fix-admission-1027` · 25 |
| S20 | 218, 221 | open (low; the owner may strike) | — |
| S10 | 227 | fixed | `core/fix-bug227-236-1027` · 25 |
| S10 | 226 (S17) | fixed | `frontend/fix-admission-1027` · 25 |
| S12 | 236 | open — stopped at a named design gate (the `errors` unit's loading; option A recommended) | — |
| S9 | 286 | fixed | `frontend/fix-hoist-1027` · 26 |
| S9 | 287 (S28) | fixed | `frontend/fix-hoist-1027` · 26 |
| S7 | 276, 277, 278, 279 | fixed | `frontend/fix-hoist-1027` · 26 |
| S7 | 280 | open — gc's own deviation on `make([]T, f(), g())`; three dispositions posed, the third recommended | — |
| S13 | 300 | fixed | `frontend/fix-binding-1027` · 28 |
| S13 | 301 (S5), 302 (S29) | fixed | `frontend/fix-binding-1027` · 28 |
| S8 | 310, 311, 313 | fixed | `frontend/fix-unseq-seam-1027` · 28 |
| S8 | 312 | open — the call-free general form's envelope, the posed design decision | — |
| S19 | 340, 341 | fixed as GUARDS, red-by-design (`Expect: FAIL`): the foldable targets refuse by name until the E7 question is ruled | `frontend/fix-init-admission-1105` · 31 (scope corrected by `frontend/fix-e7-cut-1107` · 32) |
| S21 | 400, 402 | fixed | `core/fix-fmt-decoder-1105` · 31 |
| S21 | 401 | fixed | `frontend/fix-init-admission-1105` · 31 |
| S23 | 412 | fixed | `frontend/fix-init-admission-1105` · 31 |
| S23 | 410, 411, 413, 414, 415 | open (budgets and costs; BUG-410 contradicts `docs/release.md` §4's memory-kill wording) | — |
| S17 | 390 | fixed | `frontend/fix-paren-forms-1105` · 31 |
| S17 | 391 | fixed | `core/fix-fmt-decoder-1105` · 31 |
| S28 | 420, 421, 422 | fixed | `frontend/fix-paren-forms-1105` · 31 |
| S22 | 430 | fixed | `frontend/fix-print-builtin-1108` · 34 (staged) |
| S15 | 360 | open — fix, or a stated limit beside BUG-159 (posed) | — |
| S16 | 370 | open, red-by-design pending the ruling (BUG-084's go_mem-over-TSan form, or narrow the footprint) | — |
| S16 | 371 | open — fix (a zero-size access is no location) or BUG-084's form (posed) | — |

Totals: 46 found (`awk` over `docs/BUGS.md` for the live entries numbered 176
and above, less the four audit entries below): 32 fixed, 14 open. Of the open
14: 176, 236, 280, 312, 360, 370, 371 await a ruling; 218, 221 are low and
may be struck; 410, 411, 413, 414, 415 are the budget shape's open findings.
Shapes with no finding: S1, S2, S3, S5, S6, S11, S14, S18, S27, S29 (ten of
the 27 swept).

### 5.2 The fix lanes and their trains

| lane | train | fixed |
|---|---|---|
| `core/fix-bug206-207-1027` | 24 | BUG-206 (`exitOrRefusal`, one definition at seven mirror sites INCLUDING the dedup checker's main-exit mirror — a trust-surface change, stricter only, flagged for the owner), BUG-207; plus the three sole-caller-guarded arms of the same class (keep or drop: posed) |
| `frontend/fix-admission-1027` | 25 | BUG-216, 217, 219, 220, 226; three S20 rows retired because the oracle harness reprints sources through go/printer (apparatus BUG-296); the BOM policy and a hoisted-deref alternative for the zero-length range posed |
| `core/fix-bug227-236-1027` | 25 | BUG-227; BUG-236 stopped at the design gate |
| `frontend/fix-hoist-1027` | 26 | BUG-276, 277, 278, 279, 286, 287 — one predicate `containsOrderedEvent`; 38 rows FAIL→PASS; the raft twin wire re-pinned, observation byte-identical |
| `frontend/fix-binding-1027` | 28 | BUG-300, 301, 302; 9 rows FAIL→PASS; the twin re-pinned for the grouped-var split |
| `frontend/fix-unseq-seam-1027` | 28 | BUG-310, 311, 313; 41 rows FAIL→PASS, 7 membership rows re-laned strict; BUG-312 left open |
| `frontend/fix-init-admission-1105` | 31 | BUG-340, 341 (as guards), 401, 412; a method expression and a two-level promotion that were silently wrong now refuse; a 70-deep named struct chain's size scan reported, not entered |
| `frontend/fix-paren-forms-1105` | 31 | BUG-390, 420, 421, 422; 21 of `emit.go`'s 54 identifier tests read through parentheses, the 33 others listed with reasons; the frontend's top level recovers an emission panic into a named refusal |
| `core/fix-fmt-decoder-1105` | 31 | BUG-400, 402, 391; the twin re-pinned for the Sprint oracles |
| `frontend/fix-e7-cut-1107` | 32 | the train-31 audit's findings: BUG-423, 424, 426 (S8), 425 (S21) entered fixed; scope corrections on BUG-311, 340, 391; the re-pin guard's family extended in `scripts/check-cause-regressions` (a gate-script change, posed) |
| `frontend/fix-print-builtin-1108` | 34 (staged) | BUG-430: array/struct print operands refused as gc's rejection, the multi-value spread lowered; 68 cells measured both sides; 3 rows FAIL→PASS (1 differential, 2 negative) |

### 5.3 The apparatus findings (their own record)

`docs/APPARATUS-DEFECTS.md`, under the campaign's class boundary ([USER]
2026-10-27, relayed: an apparatus defect is not a fidelity bug): BUG-296 (the
oracle harness reprints sources through go/printer — from the admission fix
lane), BUG-297 (the harness reads a program's own `exit status N` line as the
go command's trailer — S27), BUG-298 (the manifest admits ASCII subject names
only — S27), BUG-361 (the dedup engine on a registry-op polling loop is killed
at the memory cap instead of refusing by name — S15), BUG-431 (the oracle
observer's fatal split hands the runtime's pre-marker diagnostic lines to
`output` — S22). All five open.

### 5.4 The audit-round entries

Not sweep findings: the pre-merge audit of trains 28–31 (two independent
auditors, train 32) found a soundness regression in the E7 guard's target cut
and two silent-wrong-value classes in the hoist lane; BUG-423, 424, 426 (S8)
and 425 (S21) were entered fixed by `frontend/fix-e7-cut-1107`, with 47 rows.
The audit also found the narrowing of the ruled E13 latitude on declined sweeps
by an [AGENT] decision — posed to the owner, not fixed (§6).

## 6. The cells left open, by shape, and the rulings posed

Each sweep's «cells left» are on its member entries' `- Neighbourhood:` lines
and in `docs/defect-shapes.md` §3; this is the summary. A «named refusal» is a
cell both sides reach where the machine refuses by name (an honest coverage
gap, recorded, not a finding); an «envelope question» is a latitude point where
the model's set is narrower than gc's and the owner chooses the remedy.

| shape | cells left |
|---|---|
| S1 | 10 named refusals (the multi-value and comma-ok forms into interface targets — FR-7's family; the plain receive into an interface target; the two-target receive into an interface-valued map element; the assign-form range over a function iterator) |
| S2 | 9 out of scope by a named refusal |
| S3 | 13 named refusals (two S5 sub-shapes; the B6 c4 stencil-closure refusal — a closure with a parameter inside a generic stencil refuses a legal program whole-wire) |
| S4 | no cell left; 30 rows red on three envelope entries — BUG-176 (14), BUG-170 R15 (10), BUG-121 R19 (6): model gc's layout, widen by a choice, or keep as recorded reds (posed, train 23) |
| S5 | 8 named refusals |
| S6 | 4 named refusals; 12 L-016 cells recorded at the ledger; the latitude inventory's §E5 still cites the dossier's reading (a records follow-up) |
| S7 | 4 named refusals; BUG-280's 13 rows red (posed) |
| S8 | 1 named refusal; BUG-312's 5 rows red (posed); the E13 narrowing (posed, train 32) |
| S9 | 9 refusal cells (a slice→array conversion of a call, `real`/`imag`/`complex`, `defer` of a builtin, range-over-func, a receive / `make` / `new` in a short-circuit operand) |
| S10 | 7 named refusals; 6 init-context cells agree by hand only (BUG-107's limit) |
| S11 | named refusals: out-of-range float → int (R6), the machine-produced NaN patterns (BUG-094), `atomic.And`/`Or`, the `math` functions, complex |
| S12 | named refusals (float and address-printing payloads at the abort line, defined over string / bool / float, Goexit, `os.Exit`, `%w`, `errors.Is`, BUG-099's runtime-error routes); 2 init-abort cells (BUG-107); BUG-236 open at the design gate |
| S13 | 5 named refusals; 6 hand-only agreeing cells (the oracle harness shares the package; the enumerator's work cap) |
| S14 | 2 named refusals (`defer` of the builtin `delete`; the dedup engine at a `mapIter` consult) |
| S15 | `fmt.Println`, `time.Sleep`, the `runtime` package (frontend refusals by name); the unbounded `continue L` / `goto` spinners (the enumerator's step-fuel refusal); the mutex poller (BUG-361); E8 (no `fatal` member for the enumerator); E10–E14 (no row by the ruling); BUG-360 (posed); the abort window re-measured for every abort kind — `docs/release.md` §4's wording (posed) |
| S16 | the dynamic-index residual (BUG-041's open half), the sort op's write set (BUG-132's open ruling), the goroutine spawned in init (`unsupported: init-go`); BUG-370 and BUG-371 (posed) |
| S17 | 2 named refusals (`L: fallthrough` under a goto — FR-20; `defer copy` — FR-16) |
| S18 | 2 out of scope (string and map sizes with no capacity to observe) |
| S19 | 17 named refusals; 3 hand-only cells; BUG-340/341's 6 rows red as guards until the E7 question (modelling gc's link-time folding) is ruled; the train-20 audit's F1/F4 pending at BUG-135's lane |
| S20 | 1 out of scope; BUG-218, 221 open (low) |
| S21 | 38 named refusals; the typed-nil pointer renders at the shim's `r.(error)` (BUG-099's class) |
| S22 | 39 named refusals among the probed cells (uintptr at both seams, the oracle's unnamed-dynamic-type and pointer / slice / map / chan refusals, complex, FR-13, FR-16, `init-go`, `os.Exit`, the observer's ambiguity and second-report refusals, the stack and fuel limits, BUG-297); 3 cells not probed by name; the uintptr readout asymmetry (posed, noted on BUG-114); the dead-print over-refusal under the gclimits precedent (posed from the BUG-430 fix lane) |
| S23 | 3 left (`bytes.Buffer` and `fmt.Sprint` doubling; a 2^23-value seed cell); BUG-410, 411, 413, 414, 415 open; 32 rows red by design |
| S26 | BUG-206's checker-side change and the three sole-caller-guarded arms (posed, train 24) |
| S27 | 4 cells and parts of 6 more as named refusals on both sides (the `IndexRune` goto frontier, the fmt shim's ASCII `%q` quoter, invalid UTF-8 in the output and in an error payload's first line, the defined-string-type `printanycustomtype` form) |
| S28 | 13 named refusals (FR-6, L2b/FR-13, FR-3, the `//go:` directives outside the allowlist — S20's class) |
| S29 | 1 named refusal (a goto beside a captured variable); 3 cells left (the unseq lane's temps at closure / generic placements) |
| S24, S25 | not swept (§3) |

**Rulings posed to the owner and not ruled at this tip** (each posed by an
[AGENT] lane or the coordinator at a train's ask; row 56 names the train):

1. The E13 narrowing on declined sweeps — keep the ruling and restore the
   probe, or ratify the narrowing (train 32).
2. BUG-370: red by design under BUG-084's form (the lane's recommendation) or
   narrow the footprint (train 33).
3. BUG-371: fix, or BUG-084's form (train 33).
4. The readout's uintptr asymmetry, noted on BUG-114 (train 33).
5. BUG-360: fix, or a stated limit beside BUG-159 (train 34).
6. `docs/release.md` §4's abort-window wording after the S15 re-measurement, and
   its memory-kill sentence after BUG-410 (trains 34 and 30).
7. The dead-print over-refusal under the gclimits precedent (train 34).
8. BUG-312's envelope — the call-free general form (trains 27, 28).
9. BUG-176, BUG-170, BUG-121 — the envelope at the zero-size and `[]byte(s)`
   identity points (train 23).
10. BUG-280 — gc's own deviation; the third disposition recommended (train 25).
11. BUG-236 — the design gate; option A recommended (train 25).
12. BUG-218, BUG-221 — low; strike or keep (train 24).
13. BUG-206's trust-surface change and the three sole-caller-guarded arms
    (train 24).
14. The BOM policy and the hoisted-deref alternative for the zero-length range
    (train 25).
15. BUG-340/341 — the E7 question behind the guards (train 31).
16. The re-pin guard's family extended in `scripts/check-cause-regressions`
    (train 32).
17. BUG-091's class, and the oracle-observer family BUG-105/106/107/114 with
    BUG-065 — kept in the index pending the owner (train 22).
18. The train-20 audit's F1/F4 at BUG-135's lane (S20).
19. The merge asks of trains 33 and 34 themselves (the last two sweeps and the
    BUG-430 fix are staged, not on `main`).

Follow-ups that are not rulings: the latitude inventory's §E5 citation of
L-016 (records); the 70-deep named struct chain's size scan (performance,
reported by the init-admission lane, not entered); the release's
supported-scope statement citing this report as plan §7 asks (the release
lane's; `docs/release.md` does not cite it yet).

## 7. The method and its limits

**The method** (plan §4, one lane per shape): the lane wrote its matrix before
probing — the same shape at the other types, routes and sites — then probed
every cell on both sides (gc go1.26.5, `baselines/go-oracle-pin`, under the
runners' pins; the native frontend and `golean native-json-run`, the
concurrency cells through `coverage-observations` over every schedule), pinned
each agreement on a distinct route as a strict row, each disagreement as an
entry with a red row, each honest refusal as a named coverage gap, and recorded
a `- Neighbourhood:` line on every member entry. Findings were fixed through
the normal train (review, gate, ask), never by a bulk re-pin; every baseline
move carries its full-run reason in the baseline header.

**What bounds the result.**

- *One oracle, one platform.* Every agreement is at the probe's program on gc
  go1.26.5, linux/amd64, under the runners' environment pins. The campaign says
  nothing about other Go versions or platforms (release-readiness row 32's
  diversity runs are the separate evidence).
- *Sampling where gc is nondeterministic.* The deterministic cells have one gc
  run per program (the differential's leg). The scheduling and detector cells
  compared the enumerator's whole set against gc SAMPLES: S16 ran gc `-race` 10
  times at each of GOMAXPROCS 1 and 8 — 20 sampled schedules per cell — against
  the enumerator over every schedule; S15 drew 100 plain, 100 `-race` and 30
  GOMAXPROCS=1 runs per row subject (17 350 draws, plus 1 600 E8 re-samplings);
  S14 and S18 ran gc against the enumerated sets and the default tape. A draw
  set bounds membership from below only: a member gc did not draw is not
  refuted — BUG-360 was seen in 8 of 400 plain draws in one session and in none
  of 1 000 in the next, a window a few microseconds wide that opens under load.
- *Hand-only and unrowable cells.* Cells that agreed but could not become rows
  are recorded on the Neighbourhood lines, not in the corpus: S10's 6 and S12's
  2 init-context cells (pre-`main` aborts are outside the observation scope,
  BUG-107), S13's 6 (the oracle harness shares the package; the enumerator's
  work cap), S19's 3, S15's 15, S22's 56, S23's 31 (under `capped`, the budget
  shape's method), S21's 194 hand-probe subjects beside its rows.
- *Read, not run.* S26 was swept by reading the core's `| _ =>` / `.getD` /
  Option-as-value arms (the shape's own method, since an absorbing default is
  found by inspection, not by the differential); its two findings were latent
  (hand-built state only) and are pinned by eval facts, not rows.
- *Not swept.* S25 by the ruling; S24 by the class boundary. The named refusals
  of §6 are the cells the machine does not reach: pinned as gaps, not probed
  past the refusal.
- *The record's own limits.* The lanes' matrices (`.tmp/matrix.md`) and reports
  are ephemeral per the charter and are not in the tree; what survives is the
  Neighbourhood line, the §3 line, the commit message and the baseline header.
  Numbers marked **[lane]** rest on those; §4 names the places where two of
  them disagree. §3's member-list statuses are as the lanes wrote them at sweep
  time; the index is the current status.
- *The sessions.* The coordinating session stopped four times (2026-10-28,
  twice, of its own process memory; later a SIGTERM; 2026-11-06, the user
  slice's memory limit — `docs/2026-10-28_coordinator-handoff.md` and its §4
  addendum). S15 and S16 were resumed from snapshots and re-verified cell by
  cell at `main` `4296a876` before their records landed; the working limits
  that followed (one merge-tier gate at a time on the box, two lanes at once,
  sampling under `CAPPED_MEM_MAX=4G`, serially) are in the handoff.
- *Sizing, planned and actual.* The plan sized ten to twenty lane-runs, two to
  four days of box time and about five hundred rows. The campaign ran 26 sweep
  lanes, 11 fix lanes and 3 records lanes (step 1, the apparatus record, this
  closure) over 2026-10-26 → 2026-11-08, and added 3 619 + 208 rows — seven
  times the plan's row budget. The merge-tier gate's measured wall at the
  campaign's corpus sizes, from the lanes' commit messages and baseline headers:
  1 117 s at 5 592 rows (`frontend/fix-admission-1027`), 913 s at 6 179 rows
  (`frontend/fix-binding-1027`), 929 s at 6 315 rows (`sweep/s28-s29-spelling-symbols`).

**The speedbump** (plan §5, [USER]-approved 2026-10-27): `scripts/check-bugs.sh`
check 7, report-only, one awk — every `Status: fixed` entry whose Status line's
first date is on or after 2026-10-27 carries a `- Neighbourhood:` line; an
entry with no parsable date is named as undated. It is not a gate: the trust
surface is unchanged. At this tip it reports nothing (§8); its four standing
names before the closure were the undated BUG-136 and the three fixed findings
whose neighbourhoods lived only in their fix commits.

## 8. What the closure changed in the records ([AGENT], this lane)

- `docs/defect-shapes.md`: dated closed in its header, pointing here; the §2
  reconciliation of §2 above (one row added, four status cells, two
  red-by-design marks); §1's row count and member cells recounted (they sum to
  216); the three duplicated §3 items folded. No matrix, axis or lane text was
  changed.
- `docs/BUGS.md`: BUG-136's Status line dated from the entry's own provenance
  line and the baseline's re-pin header (2026-10-26, lane
  `frontend/workspace-and-oracle-1026`, train 20); `- Neighbourhood:` lines on
  BUG-227, BUG-300 and BUG-301 written from their fix commits' local-space
  measurements (`c75bc5c9`: 22 subjects; `3c8a2b06`: 18 + 2 and 16 cells), each
  line saying so.
- `docs/README.md`: this report indexed; `defect-shapes.md`'s bullet says it
  is frozen.
- `docs/2026-10-12_release-readiness.md` row 56: the status cell says the
  closure is written; the row's text is untouched.
- No change under `GoLean/`, `tools/`, `scripts/`, `Corpus/` or `baselines/`;
  no build; the static speedbumps re-run after the edits (`check-bugs.sh`,
  `check-agents-alias`, `check-spec-anchors`, `check-coverage`,
  `check-stdlib-register`, `check-imported-goose`, `check-mem-callsites`,
  `check-notices`), all ok.

## 9. Derivations

Run at the tip of `stage/train-34-1108` (`73b634f0`) in a C locale
(`export LC_ALL=C`); every count in this report comes from one of these or
from the file named beside it.

```sh
# entries (§1, §2)
grep -c '^## BUG-' docs/BUGS.md                                  # 225 headings
grep -c '^## BUG-[0-9]* — \[MOVED' docs/BUGS.md                   # 9 tombstones
grep -E '^- Status: ' docs/BUGS.md | sed -E 's/^- Status: ([a-z]+).*/\1/' | sort | uniq -c   # 183 fixed / 33 open / 9 moved
grep -c '^- Expect: FAIL' docs/BUGS.md                            # 15 red-by-design
grep -c '^- Neighbourhood:' docs/BUGS.md                           # 205 lines
awk '/^## BUG-/{if(id!=""&&!mv&&!nb)print id;id=$2;mv=($0~/\[MOVED/);nb=0} /^- Neighbourhood:/{nb=1} END{if(!mv&&!nb)print id}' docs/BUGS.md   # the 13 without a line
grep -c '^## BUG-' docs/APPARATUS-DEFECTS.md                       # 14
scripts/check-bugs.sh                                              # ok (216 bug(s), 9 moved …); check 7's names
# the record (§2, §3): rows and statuses of docs/defect-shapes.md §2
sed -n '/^## 2\./,/^## 3\./p' docs/defect-shapes.md | grep -c '^| BUG-'                       # 216
sed -n '/^## 2\./,/^## 3\./p' docs/defect-shapes.md | grep '^| BUG-' | awk -F'|' '{s=$3; sub(/^ +/,"",s); sub(/[^a-z].*/,"",s); print s}' | sort | uniq -c
sed -n '/^## 2\./,/^## 3\./p' docs/defect-shapes.md | grep '^| BUG-' | awk -F'|' '$3 ~ /red-by-design/' | wc -l   # 15 in the status cell (two route cells also carry the phrase)
# the corpus (§1, §4)
sed -n 2p baselines/native-full.tsv; sed -n 3p baselines/negative-full.tsv      # 7785 (7419/366); 645 (643/2)
git show 12a878eb:baselines/native-full.tsv | sed -n 2p             # 4166 (3901/265) at step 2's launch
git show 12a878eb:baselines/negative-full.tsv | sed -n 3p           # 437 (437/0)
for b in native-full negative-full; do comm -3 <(git show 12a878eb:baselines/$b.tsv | grep -v '^#' | cut -f2 | sort) <(grep -v '^#' baselines/$b.tsv | cut -f2 | sort); done   # added ids; nothing removed
grep -v '^#' baselines/native-full.tsv | grep 'sweep-s[0-9]' | awk -F'\t' '{c[$3" "$1]++} END{for(k in c)print k,c[k]}'   # by stage and result
grep -v '^#' baselines/native-full.tsv | awk -F'\t' '{if(match($2,/sweep-s[0-9]+/)){s=substr($2,RSTART+6,RLENGTH-6);c[s" "$3" "$1]++}} END{for(k in c)print k,c[k]}' | sort -V   # per shape
grep -v '^#' baselines/native-full.tsv | grep 'sweep-s[0-9]' | awk -F'\t' '$1=="FAIL"{print $2}' | while read id; do awk -v id="$id" '/^## BUG-/{c=$2} /^- Cases:/{if(index($0,id))print c}' docs/BUGS.md | head -1; done | sort | uniq -c   # the 99 FAIL rows by Cases line
ls -d Corpus/coverage/exec/*/sweep-s*/ | wc -l; ls -d Corpus/coverage/negative/compile/*/sweep-s* | wc -l   # 410; 154
# the trains, lanes and sweeps (§3, §5)
git log --format='%h %ad %s' --date=short 73b634f0 --grep='^Stage train'
git log --format='%h %ad %s' --date=short 73b634f0 -i --grep='^Sweep S'
git log --format='%h %ad %s' --date=short 73b634f0 --grep='fixed' -i --grep='BUG-' --all-match | grep -i 'lane'
# the findings (§5): the live entries numbered 176 and above, with their Status and Discovered lines
awk '/^## BUG-/{id=$2;n=substr(id,5)+0;show=(n>=176&&$0!~/\[MOVED/)} show&&/^## BUG-|^- Status: |^- Discovered: /' docs/BUGS.md
# cells, born-red counts, cells left (§4, §6): the lanes' lines
sed -n '/^## 3\./,/^## 4\./p' docs/defect-shapes.md
sed -n '/^| 56 |/p' docs/2026-10-12_release-readiness.md
```
