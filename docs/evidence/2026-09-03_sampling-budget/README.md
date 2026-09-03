# Membership sampling rule — before/after exhibition, cost, and red-first fixtures (2026-09-03)

Consuming docs: `docs/coverage-suite-structure.md` (membership sampling
rule paragraph), `docs/2026-09-01_membership-depth.md` §4.3 / §6 P2
(status), `docs/operational-lessons.md` ("A sampling budget is a claim
about the caption…"), `docs/assessment/decisions-2026-08-31.md`
(2026-09-03 block). Branch `sampling-budget` off main `345ef090`.

## Decision provenance

[USER] ruling (Mike, 2026-09-03, relayed by the [AGENT] coordinator —
cited as relayed, not firsthand): «yeah, agree on the sampling budget,
go ahead as you propose.» — to the coordinator's proposal to adopt memo
§4.3: alternate plain and `-race` draws; stop early when the distinct
observations reach the row's `members=` pin; otherwise stop at K; report
`draws=` beside `exhibited=`; K=32 under `--diff` (the gate), K=80 under
`--slow`. [AGENT] follow-through inside that ruling: the per-row
`samples=` param (which the budget no longer reads) is RETIRED and
refused by name in `scripts/coverage-manifest` and the harness; the four
`slices/*` rows that carried `samples=1` lose it (their draws go from 2
to K — the memo's cost table already charged K to all rows). The rule's
early stop fires on `distinct >= members`; a row whose distinct count
exceeds its pin fails downstream anyway (too-narrow alarm or the
cardinality pin).

## Conclusion

37 membership rows (the memo counted 26 on 2026-09-01; the atomics,
noodler and cross-goroutine-map rows landed since). All 37 PASS before
and after — the rule cannot flip a RESULT (see below). Total exhibited
observations over the lane: **61 → 68** (of 470 enumerated over the
same 37 rows; the memo's era figure was 45 of 441 at the gate budget,
52 in 80 draws). Rows that moved: `select-default-handshake` 1→2 (pin
reached at draw 12), `google-search` 3→5 of 6, `jitter-draw` 4→5 of 5,
`range-first-key` 2→3 of 3, `choice-order` 1→2 of 2, `sb-chan` 2→3 of 3
(pin at draw 20). 17 of the 25 pinned rows reached their pin within
K=32; the 8 that did not: `len-handoff`, `select-wake-multi`,
`wake-then-abort`, `acquisition-order`, `drf`,
`insert-then-delete-during-range` (1 of 2), `google-search` (5 of 6),
`three-key-map-order` (3 of 6) — the memo's gc-immobile/slow-saturating
set plus the newer rows. The 12 unpinned rows draw the full K (the run
log names each: `after-unpinned-notes.log`); the four `slices/*`
capacity rows stay at 1–2 of 29–300 (R2 by construction). The gate
run itself (`scripts/capped scripts/ci --diff`, `ci-diff-membership-rows.tsv`)
captioned **71 exhibited, 18 pinned rows at their pin** on the same 37
rows — run-to-run variance of the scheduling rows, as the memo warned;
the honest statement is "68–71 of 470 at K=32 across two runs".

**Members=1 rows draw exactly ONE (plain) draw** under the rule as ruled
(`atomics/spin/flag-wait`, `goroutines/send-then-spin`,
`race/atomics-free/cas-failure-acquires`: distinct reaches the pin at
draw 1, so no `-race` draw is ever taken; before, they had 10). That is
the ruled rule applied literally; it is flagged in the lane report as a
finding (a 2-draw floor — one plain, one `-race` — would be a
strengthening not in the ruling and is NOT implemented here).

**Cost.** Membership-only manifests (37 rows), `GOLEAN_COVERAGE_JOBS`
default (32 on this box), run back-to-back on the same box under load
average ~15–21 (other agents' builds running): **before 41 s, after
123 s** wall (`timing.txt`). The lane's wall is bounded by its slowest
rows, which now draw 32 × ~0.7–0.9 s ≈ 25–30 s each plus enumeration.
No draw hit the 30 s `GO_TIMEOUT_SECONDS`; no row exceeded any budget
(there is no per-row wall budget in the runner — the per-draw one is
the only clock). The memo's +6.5 min estimate assumed serial draws; the
pool runs rows in parallel, so the full `--diff` grows by about the
lane's slowest row, not by the draw sum (see the ci wall in the lane
report).

## No result flip (the argument, with lines)

`scripts/diff-coverage`, `run_membership_case_rows`: the RESULT is
decided by (i) `parse_lane_params` (manifest shape), (ii) enumeration
success / non-singleton / `members=` cardinality pin, (iii) the
driver-coupling pin, and (iv) the per-draw soundness check — every
recorded draw must match some enumerated member (`if [[ "$found" -ne 1
]]` → the too-narrow alarm, :1644-1645) with an undecided comparison
failing as "membership NOT decided". `exhibited` is accumulated at
:1631 as caption metadata only and read nowhere but the
`report_pass_lane` detail (:1677/:1680); `draws`/`distinct` from the
sampling loop (:1372-1402) are read only by the early-stop test (:1400)
and the caption (:1663-1675). A draw that did not decide fails the row
at the draw (:1374-1377) exactly as before. Therefore more or fewer
draws can only add soundness checks (each an existing FAIL condition)
or change caption text; the baseline (`baselines/native-full.tsv`,
compared by `scripts/coverage-baseline-diff` on result/id/stage —
columns documented at its :35) never sees the detail column.

## Files

* `before-after-exhibited.tsv` — the joined table (id, results,
  enumerated, pin, exhibited/draws before and after, stop reason, the
  memo's 80-draw distinct count where the row existed on 2026-09-01).
* `before-latest.tsv` / `after-latest.tsv` / `after-latest.meta.tsv` —
  the two runs' results (the after meta carries `membership_draws 32`).
* `membership-before.manifest.tsv` / `membership-after.manifest.tsv` —
  the row selections (before: generated from main's `cases.tsv`, so the
  four `slices/*` rows carry `samples=1`; after: this branch's).
* `after-unpinned-notes.log` — the 12 "NO members= pin" run-log lines.
* `timing.txt` — wall clocks and load averages around each run.
* `fixtures-red-on-main.log` — `scripts/test-lane-validation --with-go`
  (this branch's fixture script) run against MAIN's runner
  (`345ef090`, main's built binary): S1 red (10 draws, no `draws=`,
  caption `samples=5`), S2 red (10 draws, no unpinned note), S3 red on
  the draw ORDER only (main did 5 plain then 5 race; its soundness FAIL
  itself was present), S4 red on the draw-index prefix only (main named
  the kill cause without `draw 2/32 (race)`); the retired-`samples=`
  fixtures (Part A, F4b) red; the confluent-arm needle red on wording.
* `fixtures-green-on-branch.log` — the same script on this branch: all
  ok (`test-lane-validation: ok`), 1:43 wall.
* `ci-diff-membership-rows.tsv` / `ci-diff-summary.log` — the gate
  run's 37 membership captions and the `scripts/ci --diff` summary
  (RESULT: PASS, 3195/3195 no regression, 477 s wall under load 27–73).
* `memo-80draw-sweep.txt` / `memo-80draw-summary.tsv` — the memo's
  measurement this rule was argued from (copied from the
  `t4-membership` lane's `artifacts/membership-depth/resume/`, which is
  untracked; kept here so the "memo distinct@80" column is checkable).

## Reproduction (from the repo root, branch `sampling-budget`)

```sh
scripts/capped lake build
# membership-only manifests (this branch = after; main's tree = before)
scripts/coverage-manifest --artifact-root /tmp/cm | awk -F'\t' '$8=="membership"' > /tmp/membership-after.tsv
git worktree add --detach /tmp/sb-main main && (cd /tmp/sb-main && scripts/coverage-manifest --artifact-root /tmp/cm0 | awk -F'\t' '$8=="membership"') > /tmp/membership-before.tsv
# before (main's runner needs main's binary: ln -s <main checkout>/.lake /tmp/sb-main/.lake)
(cd /tmp/sb-main && time GOLEAN_COVERAGE_ARTIFACTS=/tmp/before scripts/diff-coverage /tmp/membership-before.tsv)
# after
time GOLEAN_COVERAGE_ARTIFACTS=/tmp/after scripts/diff-coverage /tmp/membership-after.tsv
# fixtures, green on this branch:
scripts/test-lane-validation --with-go
# fixtures, red on main: copy scripts/test-lane-validation into /tmp/sb-main/scripts/ and run it there with --with-go
```

## Toolchain, commit, host

`go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`);
Lean toolchain per `lean-toolchain` (v4.32.2), `golean` from
`scripts/capped lake build` of this tree. Tree: main `345ef090` plus
this branch's then-uncommitted changes (the runs preceded the commit;
the branch's first commit is the one carrying this README). Host:
linux/amd64, the shared agent box (32 logical CPUs), load average
9–26 during the runs (`timing.txt`) — the wall clocks are
load-sensitive; the draw counts and exhibited numbers are not, but the
scheduling rows' exhibited counts vary run to run (memo §4.2: two of
them stayed at 1 distinct through 80 draws in one of two runs).

[AGENT] recorded 2026-09-03 by the sampling-budget lane worker.
