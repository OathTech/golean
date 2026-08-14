# grossmith differential campaign vs 458386d (channels-arc tip) — 2026-08-07

(Committed to docs/ 2026-08-07, verbatim from the working-note
.tmp/grossmith-campaign-2026-08-07.md — this provenance paragraph is
the only addition. Artifact paths under .tmp/ are scratch: every case
regenerates deterministically from (generator rev, seed) as described
below. This sentence claimed .tmp/ was "gitignored" from the day it was
written; it was not — the `/.tmp/` rule landed in .gitignore on
2026-08-14, in the verified-examples audit fix round, which is what
made the claim true.)

Campaign worker report (grossmith generator at `5b4c5b0`, main; GoLean at
`458386de87119bbdc422a930c2b9db207a36138e`, the channels-arc merged tip, built
clean in an isolated worktree; reference `go version go1.26.5 linux/amd64`,
GOTOOLCHAIN=local). Prior campaign context: grossmith's first campaigns ran
against `a38e086` and handed over two findings (BUG-042 defined-type incdec;
the diff-coverage exit-1 ambiguity) — both are regression-verified FIXED at
this tip, below.

Artifacts: batches under the main repo's `.tmp/grossmith-campaign-20260807/`
(`c0-gc386`, `c1-seed4242` … `c7-seed900000`, each with `batch.json`,
per-case `case.json` seed/tape records, and `golean-work/` holding the
translated cases, manifest, `results.tsv(.meta)`, and `diff-coverage.log`);
manual regression + harness-contract fixtures under the worktree's
`.tmp/grossmith-manual/` and `.tmp/hc/`. Every case regenerates
deterministically from (generator rev, seed): case i of a batch uses
`seed_base + i` under `golean.Profile(gen.DefaultConfig(seed))`, swarm on
unless noted.

## 1. Campaign scope and headline result: ZERO divergences in 2,900 cases

GoLean campaigns (all via grossmith's documented workflow — gc reference pass,
translation into diff-coverage strict-lane manifest rows, verdicts mapped from
the closed result vocabulary; isolated `GOLEAN_COVERAGE_ARTIFACTS/RESULTS/META`
per batch, `Jobs = nproc = 32`):

| batch | n | seeds | match | clone-infra | mismatch | notes |
|---|---|---|---|---|---|---|
| c1 | 300 | 4242.. | 287 | 13 | 0 | prior-campaign seed reused |
| c2 | 500 | 100000.. | 492 | 8 | 0 | |
| c3 | 300 | 559.. | 287 | 13 | 0 | BUG-042 discovery seed region |
| c4 | 100 | 42000..42099 | 99 | 1 | 0 | grossmith's Phase-2 anchor batch |
| c5 | 500 | 777000.. | 486 | 14 | 0 | |
| c6 | 200 | 31337.. | 192 | 8 | 0 | `-swarm=false` (all constructs, dense) |
| c7 | 1000 | 900000.. | 977 | 23 | 0 | |
| **total** | **2900** | | **2820** | **80** | **0** | |

- **observation-mismatch: 0 / 2,900.** No semantic divergence found anywhere
  in grossmith's generated grammar at this tip. 666 of the 2,900 are
  deliberate panic-path cases (`ref-ran` = n in every batch; panic equivalence
  is GoLean's own harness: expected status + exact panic message) — all
  matched.
- **All 80 clone-infra failures are ONE class**, byte-identical detail:
  `frontend-export` / `frontend-quarantined: call/allocation in short-circuit
  operand (would change evaluation order)`. This is the tip's *pinned,
  expected* native-frontend coverage gap — tracked corpus case
  `bools/short-circuit-call-operand`, baseline `FAIL frontend-export`
  (`baselines/native-full.tsv:47`). No other stage, no `harness-error`, no
  `reference-infra-failure`, no unknown-stage fallthrough occurred in any
  batch.
- Discrimination control (harness-sanity, no GoLean): `c0-gc386`, n=150 seed
  9000 against GOARCH=386 — 39 observation-mismatches, **all inside the
  declared `width_dependent` tag, 0 off-tag** (yield 39/146 = 26.7%). The
  pipeline detects real divergence when it exists; the 0/2,900 above is not a
  dead harness.

Anchor-batch delta worth recording: grossmith's Phase-2 doc measured the same
100 subjects (seeds 42000..42099, subject hashes deterministic) at
**91 match / 9 clone-infra** against the `a38e086`-era baseline. At `458386d`
they are **99 / 1** — eight frontend/machine coverage gaps closed across the
arc span; the single residual red is the short-circuit quarantine.

## 2. Regression checks on the prior campaign's findings — both fixed

Run through the exact harness path grossmith consumes (hand-written
strict-lane manifest, `scripts/diff-coverage`, isolated artifact env):

- **BUG-042 (defined-type `++`/`--`)**: the handover's 7-line minimal repro
  (`type T1 int8; v := T1(5); v++`) **PASS**; also PASS: `--` at wrap
  (`T1(-128)`), and unsigned wrap (`uint16(65535)++` on a defined type).
  Corpus-pinned at this tip (`ints/defined-incdec/*`, 11 cases per
  `docs/BUGS.md`).
- **BUG-043 (range-over-int loop-variable kind)**: `for i := range n` with
  `n int8` **PASS** (4/4 in the slice). Note grossmith cannot generate this
  shape itself — the check is hand-written; see §4.
- c3's 300 cases over the discovery seed region (559..858): zero mismatches,
  zero stuck-class verdicts.

## 3. Harness-contract verification — the M2 guarantees hold as consumed

Claim under test: no-publish paths exit 2 and leave no readable results;
published meta carries `manifest_sha256`. All verified empirically against
`scripts/diff-coverage` at this tip (fixtures in worktree `.tmp/hc/`):

| test | path exercised | result |
|---|---|---|
| A | missing manifest, stale results+meta pre-seeded at the env paths | exit **2**, stale pair **deleted** |
| B | empty (header-only) manifest | exit **2**, nothing published |
| C | lake-build timeout (stalling `lake` shim on PATH, 2s budget) after a previously-published pair existed at the same paths | exit **2**, "lake build failed or timed out (no results published)", previous pair **invalidated** |
| D | genuine FAIL row (short-circuit quarantine case) | exit **1**, results published, meta `manifest_sha256` == sha256 of the exact manifest submitted (verified byte-equal) |

Plus 8 full campaign invocations: PASS-only manual slice exited 0 with
published pair; every campaign's meta sha was accepted by grossmith's own
`checkMeta`.

**Redundancy verdict on grossmith's defenses** (the side-question): at this
tip, grossmith's pre-run delete of `results.tsv`/meta duplicates the script's
own top-of-run `rm -f` (diff-coverage line 35, hoisted above every infra
exit), and its `manifest_sha256` cross-check can no longer fire on the
stale-file scenario that motivated it — both defenses are **redundant against
458386d**. They remain correct and cheap as defense-in-depth against *older*
GoLean checkouts (grossmith supports `-clone golean:<checkout>` at arbitrary
revs, where the pre-M2 ambiguity still exists), so keeping them is right;
nothing on either side needs to change.

Residual sharp edges found (minor, environmental):

- On a warm build cache a 1-second `LAKE_BUILD_TIMEOUT_SECONDS` did NOT
  produce the timeout path — lake relinked the deleted binary in under a
  second and the run proceeded legitimately. Not a defect (the budget did its
  job); noted because a test harness that wants the timeout path must stall
  `lake` itself, not rely on small budgets.
- `gengo`'s clone identity marks the checkout `-dirty` on ANY
  `git status --porcelain` output, including untracked scratch files (c3–c7
  record `...-dirty` solely because this worker kept its scratch under the
  worktree's untracked `.tmp/`; tracked files were pristine throughout, and
  diff-coverage's own meta `git_dirty` — tracked-diff based — stayed false).
  Reader of `batch.json` beware: the two dirty bits have different
  definitions.

## 4. Capability profile at this tip: what grossmith can and cannot reach

Confirmed by reading `gen/` at grossmith `5b4c5b0` and by the campaign tag
histograms:

- **No concurrency generation.** No `chan`, `go`, or `select` construct
  exists anywhere in the generator grammar. The channels-arc surface that is
  this tip's headline (send/recv/close/select/spawn/deadlock/race detection,
  and diff-coverage's `racy`/`confluent`/`membership` lanes and their litmus
  stages) is **entirely outside grossmith's reach**: it pins `lane=strict` on
  every row, deliberately leaves the membership-lane stages unmapped, and an
  unexpected `racy`/`confluent` stage would fail closed as `harness-error`
  (none occurred). Campaigning the concurrency surface needs either grossmith
  concurrency rungs (their TODO's membership-lane item is the design hook) or
  GoLean's own litmus corpus — grossmith today adds nothing there.
- Of the four construct classes prioritized for recent GoLean changes:
  **incdec/defined types** — generated (weight-2 core `incdec` arm;
  `defined_types`/`methods` optional arms) and heavily exercised, green;
  **multi-target assignment** — not generated; **range kinds** — only
  fixed-length-array range and the order-invariant map fold; range-over-int /
  string / channel not generated; **concurrency** — not generated. So three
  of the four current GoLean hot areas are grammar-blocked on grossmith's
  side (all already on their TODO as ledger-driven rungs: multi-assign,
  range-over-int, labels/goto, type switches).
- The golean capability profile additionally masks: slices/maps out of the
  observed tier, and excludes `observe_point`, `defer`, `recover` (all
  grossmith defer/recover forms are obs*-event-shaped and GoLean has no obs*
  model). Consequence visible in every conformance statement: `recovered: 0`
  — **defer/recover semantics are untested by these campaigns** despite full
  tip support and 666 panic paths. Their own Phase-2 doc reaches the same
  conclusion ("defer/recover is UNMEASURABLE against GoLean under the current
  profile"); the g06/c54 named-results-defer rung would unblock it.
- What the 2,900 green cases DO cover, per tag histograms: all integer kinds
  + widths, bool/string ops, arrays/index, structs/fields, defined types,
  value-receiver methods, interfaces (derived + `interface{}`) with
  assertions and comma-ok, helpers incl. bare calls, if/for/range/switch,
  break/continue, block scoping, early returns, division/modulo/shift panic
  paths (tagged `panic_risk`), conversions, min/max/len/append/delete,
  boundary corners (`corner_boundary`), dead code, unreachable switch cases.

## 5. Corpus-promotion candidates: none new

Zero divergences means no new red to pin. The two candidates from the prior
handover are both already adopted at this tip: the defined-type incdec family
(`ints/defined-incdec/*`) and the short-circuit-operand quarantine
(`bools/short-circuit-call-operand`, pinned as an expected `frontend-export`
red in the baseline). The 80 quarantine hits in these campaigns are density on
an already-pinned gap, not new information. When the frontend closes that gap
the baseline move is already visible-by-design; grossmith will then re-exercise
it for free (its short-circuit arm generates the shape at ~2.5–4.5% of cases).

## 6. Side observations (grossmith-side, informational)

- grossmith's own witness suite is red in a stock module-mode Go environment:
  `harness` package tests (`TestVerdictTaxonomy`, `TestGcCrossArchStillJudges`,
  `TestSensitivityMatrix`) build cases in bare `t.TempDir()` dirs with no
  `go.mod`, failing with "go.mod file not found" under default
  `GO111MODULE=on` semantics (their dev environment presumably carries a
  GOPATH-mode `go env` override; `HOME` pass-through in `buildEnv` would pick
  it up). The production `gengo` path is unaffected — it writes a throwaway
  `go.mod` at the batch root, and all campaigns here ran green on
  infrastructure. Worth a line in the next handover to them.
- `gengo -n 10 -judge` smoke and all reference passes: 100% `ref-ran`, no
  observation-parse failures, no timeouts at the 10s default.
