# Grossmith integration: the standing instrument + campaign 3

Lane: `t4-grossmith` (fidelity work program Tier 4, [USER]-approved —
`docs/assessment/synthesis.md` "Tier 4 … grossmith integration
(cadence, adapter contract test, generator widening …)";
`docs/assessment/decisions-2026-08-31.md`; assessment findings
`lane-b-lower-bound.md` §B10 and `lane-d-apparatus.md` D-8). Tracked
output: this report plus one lane tool, `scripts/grossmith-run`. **NO
baseline, gate, corpus, or reference-checkout changes** — promotions
and BUGS/ledger entries are RECOMMENDED here, never made. Everything
below is [AGENT]-executed and [AGENT]-judged inside that mandate. Base
commit `7cf19198` (+ `864d1bdc`, the bus-free `scripts/capped`
cherry-picked from main so the cap could be proven from the agent's
process); oracle pin go1.26.5 (`baselines/go-oracle-pin`); generator
`deps/grossmith` @ `e68867d6` (campaign 2's revision, now a deliberate
pin in the tool).

**One-paragraph status.** The instrument is built and its contract
test is GREEN against today's harness (C1–C9, §1): the adapter the
assessment presumed interface-dead is not — the 7-vs-10-field manifest
and stage-vocabulary drift belong to the RETIRED `side/gofuzz`
prototype, and `deps/grossmith`'s adapter already speaks today's
10-column manifest and 5-column results file; what was missing was
anything that would TELL us when that stops being true, which now
exists. The soundness kit (dedup, four-class triage under the
pinned-oracle rule, §2) is built and exercised on real divergences.
**Campaign 3 ran** (§4): the first `m3a` attempt was a RUNNER
infrastructure failure (19,999 of 20,000 rows "worker produced no
result" — root cause `ls "$ROWDIR"/*.in` exceeding ARG_MAX at 20,000
rows under this tree's long TMPDIR, §4.1; it is now a static contract
clause C9 plus a leg guard that fails LOUD instead of triaging
artifacts), and the re-run plus the pairwise leg judged
39,800 programs: 39,796 match, 3
observation-mismatches, 1 reference-infra failures,
zero clone-infra, zero harness-error. Every divergence is triaged in
§5: one reference refusal = L-015's assembler bug (third witness); two mismatches = E5 (gc stores a multi-target assignment's earlier right-hand value before a later operand's division panic — both legs); one mismatch = E13 on a new axis (string slicing vs sibling calls). **No new machine bug**; the machine's two
disagreements with gc land on two latitude points already in the
inventory (E5, E13), with gc on the exotic member both times, and the
reference refusals are L-015's assembler bug again. The widening-cost
assessment (§7) and the cadence recommendation (§8) close the mandate.

---

## 0. Decisions logged in this lane

| # | decision | provenance |
|---|---|---|
| 0.1 | Generator revision pinned at `e68867d6…` in `scripts/grossmith-run` (`GROSSMITH_PIN`); a mismatch is contract DRIFT (C1), moved only by editing the constant with a written reason in a campaign report. | [AGENT] — applies the oracle-pin discipline to the second external witness |
| 0.2 | Machine statuses `fatal`, `fuel-out` are ACKNOWLEDGED-unknown to the adapter (its fallthrough is `harness-error` with the status preserved: fail-closed, visible, only infra-vs-semantic-undecided); any OTHER unknown status is DRIFT (C5). | [AGENT] — see §1 C5 |
| 0.3 | Lane-only stages `membership`/`confluent`/`racy` are accepted as unmapped ONLY while the adapter provably pins `lane=strict` (asserted, C2/C4). | [AGENT] |
| 0.4 | No shrink/reducer step: grossmith has none (`-replay` reproduces, nothing minimizes) and building one is outside an integration lane. Stated, not hidden. | [AGENT] |
| 0.5 | Campaign 3 parameters pre-registered BEFORE any result existed (§3, committed at `3e3cca00`); the runs in §4 use exactly those seeds and sizes. | [AGENT] |
| 0.6 | `deps/` populated in the lane worktree by `scripts/setup-deps --from <main checkout> --only go,goose,raft,grossmith` (local clones, gitignored); `.lake/` seeded from the main checkout's build tree (identical sources at `7cf19198`), then rebuilt by the capped `lake build` inside every `diff-coverage` run. | [AGENT] |
| 0.7 | A leg runs as K contiguous-seed CHUNKS of at most 4,000 cases, each a separately published, `gengo -verify`-able batch (`<label>/part-NN`), because `diff-coverage` fans rows out through one argv (§4.1). The chunk bound is computed from the actual TMPDIR path length and ARG_MAX (C9) and refused when exceeded. | [AGENT] — response to the first m3a run |
| 0.8 | LEG GUARD: a published chunk with any worker-death rows, more than 50 % clone-infra/harness-error/unjudged, or runner-failure text in the harness log ("Argument list too long", "worker pool exited nonzero", "lake build failed", "no results published") FAILS the leg with exit 2 and is NOT triaged. The smoke gets the same guard. **Revised 2026-09-02 (audit fix G-2; campaign 3 RAN under the 50 % form above):** the infra rate now also counts `reference-infra-failure` and `both-infra-failure`; the abort threshold is a PRE-REGISTERED **1 %** of the chunk (`INFRA_ABORT_PCT=1`, written into every `.params.txt` before the chunk runs); the rate is reported UNCONDITIONALLY — in the guard's output, each chunk's `.params.txt`, and the leg's `verdicts.txt` (`infraRate` line); and an unreadable or malformed `batch.json` FAILS the guard by name (the first cut's `local n="$(python3 …)"` masked python's exit status with `local`'s, so a broken `batch.json` gave `n=""`, empty `infra`, and a guard that passed on nothing). Campaign 3's ten valid chunks re-checked under the revised guard: all pass, max infra rate 1/4,000 = 0.025 % (`m3a-rerun/part-03`, the L-015 reference refusal); the failed first `m3a` still fails on every criterion. | [AGENT] — a runner that returns 20,000 empty results is an infrastructure failure, not a campaign result |
| 0.9 | Campaign 3's legs all live under `artifacts/grossmith/2026-09-01/` (the campaign date) — the `m3pairs` leg started after midnight and was pointed there explicitly with `GOLEAN_GROSSMITH_ARTIFACTS`; the tool's default tree is date-keyed per invocation. | [AGENT] |
| 0.10 | The runner refuses to start a leg while the documented box-wide build lock (`artifacts/build-lock.d`, `docs/operational-lessons.md`) exists in this worktree or the primary checkout. Note: no script implements that lock today — the check is a courtesy against the convention, not a mechanism. | [AGENT] — coordinator's request; the first m3a failure was NOT load (§4.1) |
| 0.11 | Triage auto-class `machine-bug-candidate` is overridden by hand to LATITUDE (recorded E5) for BOTH campaign-3 witnesses: `m3a-rerun/part-04/case_03110` (§5.2) AND `m3pairs/part-01/case_03079` (§5.0 — `artifacts/grossmith-m3pairs.log` ends with the pairs leg's `machine-bug-candidate 1`, and that row is case_03079). The first cut of this row logged only case_03110 (audit fix G-3). The rule stays as written: a wrong-answer candidate with a self-stable oracle defaults to OURS until a human clears it against the record; both overrides stand only as far as the E5 classification itself does — see the caveat at the head of §5. | [AGENT] |

---

## 1. The contract test — `scripts/grossmith-run contract`

**What it is.** A static test (seconds, no build) run in front of every
campaign, reading BOTH sides' sources — `scripts/diff-coverage`,
`scripts/coverage-manifest`, `GoLean/GoCore/Value.lean`,
`GoLean/CLI.lean` on ours; `golean/golean.go`, `gen/constructs.go` on
grossmith's — and asserting the interface they meet at. Every clause
runs; every violation prints; the verdict is the conjunction; exit 1 =
DRIFT and no campaign may proceed (the `campaign` mode calls it
first). The assessment's named gap was that nothing would surface an
interface drift until a campaign silently mis-judged; this is that
something.

| clause | asserts | today |
|---|---|---|
| C1 | `deps/grossmith` is a git checkout at `GROSSMITH_PIN` and CLEAN (reference checkouts stay pristine — trust-tools rule) | ok — `e68867d`, clean |
| C2 | manifest columns: the adapter's header line ≡ the columns `diff-coverage` reads (positional, names mapped `function→function_name`, `args→arg_ints`); the adapter's row builder emits that many cells; the LIVE `coverage-manifest` output has that width on every row; the adapter pins `lane=strict` | ok — 10 fields `id go_dir function_name arg_ints expected_status features expected_reason lane why params`; 2506 live rows all 10-wide; strict pinned |
| C3 | results file: header string identical on both sides; all four row emitters (`report_pass`, `report_pass_lane`, `report_fail`, the worker-death row) write 5 cells | ok — `result\tid\tfeatures\tstage\tdetail`; 4/4 emitters 5-wide |
| C4 | stage vocabulary: every stage literal `diff-coverage` can put in a row ∈ adapter `judge()` cases ∪ lane-only set | ok — harness {confluent differential frontend-export go-harness go-observation go-run go-source lean-observation lean-run litmus-contract manifest membership nondet racy harness}; adapter maps 11; lane-only unmapped {membership confluent racy} |
| C5 | observation statuses the CLI can emit ⊆ adapter's two closed sets ∪ acknowledged; schema constant equal | ok — CLI {ok panic unsupported stuck error fuel-out deadlock race fatal}; adapter knows 7; acknowledged {fatal fuel-out}; schema `golean-observation-v1` |
| C6 | `golean.Profile`'s excluded tags all exist in `gen.Optional()` | ok — {observe_point defer recover} ⊂ 48 optional tags |
| C7 | `go` on PATH == `baselines/go-oracle-pin` (gengo `-go` pins this exact binary for the reference pass AND the nested oracle) | ok — go1.26.5 at /usr/local/go/bin/go |
| C8 | `gengo` compiles (into `artifacts/grossmith/…/bin`, repo-local GOCACHE) and compiling left the reference checkout clean | ok |
| C9 | (campaign mode) the ROW-GLOB BOUND: `(len(TMPDIR) + len("/golean-coverage-rows.XXXXXX/000000.in") + 1) × rows-per-chunk ≤ ARG_MAX/2`; chunks are sized to satisfy it and a chunk that cannot is refused before anything runs | ok — path 130 B, ARG_MAX 2,097,152 → ≤ 8,065 rows per invocation; legs chunked at ≤ 4,000 |

**Findings from building it (record corrections, no code change):**

- **C9 exists because the first `m3a` run found a contract gap the
  smoke cannot see** (§4.1): a 12-case smoke passes and a 20,000-row
  manifest fails at the harness's row fan-out, with gengo exiting 0
  and every verdict `clone-infra-failure`. The static bound is the
  honest check; the leg guard (decision 0.8) is the backstop.

- **The "adapter interface-dead (7-field vs 10-field manifest,
  stage-vocab drift)" claim in `lane-d-apparatus.md` D-8 describes
  `side/gofuzz`**, the retired prototype — not `deps/grossmith`, whose
  adapter writes the 10-column header verbatim (`golean/golean.go:273`)
  and parsed today's results on 2026-08-20 through 79,800 cases. B10
  says this correctly ("side/gofuzz is retired; grossmith is the live,
  proven, unintegrated instrument"); D-8's wording conflates the two.
  The mandate's premise ("repair the adapter on OUR side") therefore
  resolves to: nothing was broken to repair; the CONTRACT TEST is the
  repair — it is the thing whose absence let side/gofuzz die unnoticed.
- **Two real, non-blocking deltas surfaced (C5):** the machine can
  emit `fatal` (runtime fatal errors — Go's `fatal error:` class,
  concurrency-only today) and `fuel-out` (the interpreter's budget),
  neither known to the adapter's closed status sets
  (`cloneStatusCarriesObservation` / `…ProducedNoObservation`). Its
  fallthrough is `harness-error` with the status text preserved —
  fail-closed and visible, so a campaign cannot mis-count either as a
  pass or as a semantic mismatch; it just cannot attribute them to the
  infra or the semantic side. Both are unreachable for grossmith's
  import-free, goroutine-free, budget-bounded programs. Decision 0.2:
  acknowledged by name (a campaign that shows one triages as
  `harness-artifact` with the status in the evidence column); anything
  else unknown is DRIFT. Handing grossmith a two-entry addition to its
  status sets is the clean fix (external project; not patched here).
- **The `stage=`/`detail=` prefixes** in `diff-coverage`'s progress
  lines are stdout-only; the results FILE rows are un-prefixed
  (verified: the two `printf`s in each emitter). A reader of the log
  who assumed the file matched would think the vocabulary had drifted;
  it has not.
- The lane-only stages (`membership`/`confluent`/`racy`, plus
  `report_pass_lane`'s PASS-with-stage rows) are reachable only for
  non-strict rows. The adapter pins strict, so they are unmapped by
  design; C4 accepts them ONLY under C2's strict-pin assertion, so a
  future adapter that stops pinning strict trips C2 and C4 together.

**Refusal behaviour (self-tested):** the output root is canonicalised
twice (lexical pre-mkdir, symlink-resolving post-mkdir) and refused if
it resolves into `artifacts/coverage` (the judged records), `baselines/`,
`Corpus/`, `deps/`, or the grossmith checkout — tested with the direct,
nested, `../`-relative, and symlinked spellings (all exit 2). `TMPDIR`
and `GOCACHE` are forced inside the artifacts tree: `/tmp` is
write-only under the agent sandbox, and a harness that cannot glob its
own row files reports every case as a worker death.

---

## 2. The soundness kit — dedup and triage

`scripts/grossmith-run triage <batch>` post-processes a published
gengo batch (`batch.json` + `manifest.tsv`) into `<batch>.triage.tsv`
(one row per non-`match` case) and `<batch>.triage-groups.tsv` — BESIDE
the batch, because a gengo batch is a digest-bound immutable tree and
`gengo -verify` refuses undeclared files inside it (the first cut wrote
into the batch and broke `-verify`; fixed, verified on two chunks).

**Dedup.** Key = (verdict, stage, normalized detail), where
normalization collapses case ids, absolute paths, quoted strings, hex
and decimal literals. For `differential` mismatches the two JSON
documents in the detail would normalize to the same skeleton, so those
are keyed by the SHAPE of the disagreement instead — both statuses plus
the differing value slots (`q6:uint64`) — a merge the first cut got
wrong (the two campaign-3 mismatches landed in one group until the key
was fixed). Two hits of one mechanism share a group; the group file
carries count + representative; a chunked leg is merged into
`<leg>/triage-all.tsv` + `triage-groups-all.tsv`, re-deduplicated
across chunks. (Self-test on a real 300-case batch: 300 clone-infra
rows → 2 groups, split only by "(core dumped)" presence.)

**Classes** (closed set; every row is a CANDIDATE with `needs_human=yes`
and an `evidence` column — nothing here promotes, pins, or files):

| class | rule |
|---|---|
| `gc-bug-candidate` | `observation-mismatch` whose reference re-run at `-gcflags=all=-N -l` produces a DIFFERENT observation document than the recorded default-flags one (gc disagrees with itself; campaign 2 §2's shape); or `reference-infra-failure` that compiles AND runs at `-N -l` (campaign 2 §3's shape) |
| `latitude-candidate` | `observation-mismatch`, gc self-stable, and the case carries the `order_witness` instrument (the only construct that reaches unsequenced points; campaign 2 §4) — the human decides forced vs unsequenced against spec#Order_of_evaluation |
| `machine-bug-candidate` | `observation-mismatch`, gc self-stable, no order instrument (the machine disagrees with a stable oracle); or `clone-infra-failure` at stage `frontend-export`/`lean-run` — a REFUSAL inside grossmith's supported fragment is a load-bearing signal, never a pass |
| `harness-artifact` | timeouts/kills on either side; `harness-error` (adapter contract); `both-infra-failure`; unjudged cases; gc failing at `-N -l` too |

**The pinned-oracle rule, operationalized.** gc is a bounded-trust
witness: in campaign 2 the oracle was the wrong side 3 times to the
machine's 1 (`docs/2026-08-20_grossmith-findings-2.md` §0.2; ledger
L-014/L-015). So the metamorphic compile+run at `-N -l` is applied to
EVERY mismatch and reference refusal BEFORE the machine is suspected,
and the machine is to be compared against the `-N -l` document when gc
is self-unstable. This is campaign 2's "cheaper, higher-yield shape for
next time" (§5) — metamorphic attribution over the whole divergence
population rather than metamorphic sampling.

**Self-tests run.** (0) The failed first `m3a` run: 19,999 worker-death
rows → 1 group, 1 reference refusal → 1 group (`gc-bug-candidate`,
compiles at `-N -l`), and — after decision 0.8 — the leg guard refuses
that batch on all three of its criteria. (i) A synthetic batch with two `observation-mismatch`
cases: one with its genuine recorded document → `machine-bug-candidate`
("gc self-stable"); one with the recorded document doctored →
`gc-bug-candidate` ("gc default != -N -l"). The first cut of the
comparison mis-fired on Go's `omitempty` (recorded documents omit `0`
and `false`, the live driver spells them) — fixed by canonicalising
both sides; noted because it is exactly the kind of wire-format
subtlety that would have produced a wall of false gc-bug rows. (ii)
The real 300-case gc-386 batch (§4.1) — 300 rows, 2 groups, all
`harness-artifact` as they should be.

**No shrink step** (decision 0.4). What exists instead: every case
regenerates from `(generator rev, seed)`; `gengo -replay <case>`
reproduces it byte-for-byte; the triage row carries the seed. Hand
minimization stays the human's job, as in both prior campaigns.

---

## 3. Campaign 3 — pre-registered parameters (as committed at `3e3cca00`, before any result)

Stated before any result exists. Budget target: **~40 min wall for
~40,000 programs** (campaign 2 measured ~1,100 programs/min at 32
workers; two 20k legs took ~18 min each), inside the mandate's 30–60
min window, plus the 12-case smoke and the 386 control.

| leg | command (from the repo root, the ONLY way to run it) | cases | seeds |
|---|---|---|---|
| `m3a` swarm | `GOLEAN_MEM_MAX=32G scripts/capped scripts/grossmith-run campaign --seed 5000000 --n 20000 --control386 2000 --label m3a` | 20,000 | 5,000,000–5,019,999 |
| `m3pairs` pairwise | `GOLEAN_MEM_MAX=32G scripts/capped scripts/grossmith-run campaign --seed 6000000 --pairs 20 --control386 0 --label m3pairs` | 19,800 (45 profile-kept tags → 990 pairs × 20) | 6,000,000–6,019,799 |

Generator settings, verbatim (recorded per leg in
`artifacts/grossmith/<date>/<label>.params.txt` and per case in
`case.json` `config`): `gen.DefaultConfig(seed)` = `{Vars:4 Stmts:14
Depth:2 ExprFuel:3 LoopCap:6 Swarm:true}` + `golean.Profile` (NoObserve
{slice, map}; Exclude {observe_point, defer, recover}); `-timeout 10s`;
`-workers` = nproc (32); `-go /usr/local/go/bin/go` (go1.26.5); panic
equivalence = GoLean's harness (expected status + exact panic
message). Seed ranges are fresh (campaign 1 used 4242…/100000…/559…/
42000…/777000…/31337…/900000…; campaign 2 used 1M–4M).

The `campaign` mode's sequence: contract (§1) → C9 → smoke (12 cases,
seed 424242, end-to-end through gengo → diff-coverage → verdicts;
refuses on any `harness-error`/`clone-infra`, unjudged case, or
reference that did not run) → the leg in contiguous-seed chunks
(decision 0.7: `m3a` = 5 × `-n 4000`, seeds 5,000,000 + 4,000·i;
`m3pairs` = 5 × `-pairs 4`, seeds 6,000,000 + 3,960·i — every pair still
forced 20 times, the leg's seed range exactly the pre-registered one)
→ the gc-386 control → `triage`. The control was run with
`--control386 0` on both legs: this box aborts 386 binaries (§4.2), so
it is not a measurement here.

**Exclusion census of the pre-registered population** (3,000 programs
of the `m3a` range generated locally, 264,388 subject lines, scanned
with fixed strings — the same method as campaign 2 §8): unary `&`: 0;
`chan`/`go `/`select`: 0; `float`/`complex`: 0; `rune`: 0; `goto`: 0;
`import`: 0; type parameters (`[T `): 0. Present: `min(` 4,178, `max(`
4,288, `len(` 1,345, `append(` 1,683, type assertions `.(T` 354, `wit(`
1,520, `switch` 2,305, `map[` 3,154. Caveat: this census was generated
WITHOUT the golean profile (gengo applies it only when `-clone golean`
is given), so `defer`/`obs*` appear here (5,259 / 2,649 files) and will
NOT in the campaign; the absent-surface zeros hold regardless.

---

## 4. Results

| leg | cases | ref-ran | match | observation-mismatch | reference-infra | clone-infra | harness-error | wall |
|---|---|---|---|---|---|---|---|---|
| `m3a` (first run) | 20,000 | 19,999 | 0 | 0 | 1 | **19,999** (worker deaths) | 0 | 509 s | 
| `m3a-rerun` | 20,000 | 19,999 | **19,997** | **2** | **1** | 0 | 0 | 1,767 s (5 chunks) |
| `m3pairs` | 19,800 | 19,800 | **19,799** | **1** | **0** | 0 | 0 | 1,512 s (5 chunks) |
| **campaign 3 (valid legs)** | **39,800** | 39,799 | **39,796** | **3** | **1** | 0 | 0 | — |

The first `m3a` row is NOT a campaign result (§4.1) and is excluded
from the campaign total; it is kept (`artifacts/grossmith/2026-09-01/m3a/`)
as the diagnosis record. Its one reference refusal is the same
program, at the same seed, as `m3a-rerun`'s (`case_11428` ≡
`part-03/case_03428`, seed 5,011,428) — deterministic, counted once.
Wall clocks were measured under a box load of 70–100 (other lanes'
gates running concurrently); campaign 2's 18 min per 20k was on an
idle box.

**Base of the measurement (audit fix G-5).** The 39,800-judged /
39,796-match measurement was taken against the machine at base
`7cf19198` (the `golean:` line of every `part-NN.params.txt`); it has
NOT been re-run at the rebased tip `e7d07b26`. Whether the intervening
main commits reach grossmith's fragment is not assessed here — the
number is a statement about `7cf19198`.

**The 3,999-vs-4,000 row asymmetry in `m3a-rerun/part-03` (audit fix
G-6).** `part-03/golean-work/results.tsv` has 3,999 rows for a
4,000-case chunk. The missing row is `case_03428` (§5.1): its
reference build failed, so gengo recorded `reference-infra-failure`
as the verdict and never submitted the case to the clone harness —
no results row exists for it BY DESIGN (there is no reference
observation to compare against). `batch.json` is the complete
record: 4,000 cases, `refRan` 3,999, 3,999 `match` + 1
`reference-infra-failure`; the leg guard and the §4 table read
`batch.json`, not `results.tsv`, for exactly this reason.

Every case regenerates from `(e68867d6, seed)`; every chunk is a
published gengo batch with `complete.json`, re-checkable offline with
`gengo -verify <chunk>`. Records: `artifacts/grossmith/2026-09-01/
{m3a-rerun,m3pairs}/{part-01..05/batch.json, part-NN.triage.tsv,
verdicts.txt, triage-all.tsv, triage-groups-all.tsv}`, `<label>.chunks.txt`,
`part-NN.params.txt` (verbatim argv, identities, load at start), the
runner logs `artifacts/grossmith-m3a-rerun.log`,
`artifacts/grossmith-m3pairs.log`.

### 4.1 The first `m3a` run: a runner infrastructure failure, root-caused

**Symptom.** 20,000 cases, gengo exit 0, smoke 12/12 match, leg
verdicts `clone-infra-failure` 19,999 (every one `stage harness: worker
produced no result`) + 1 `reference-infra-failure`. The first cut of
the runner then TRIAGED the 19,999 as harness-artifacts and exited 1 —
exactly the shape the coordinator named as unacceptable.

**Root cause (from the harness log, not inferred).**
`m3a/golean-work/diff-coverage.log`:

```
scripts/diff-coverage: line 1370: /usr/bin/ls: Argument list too long
environment: line 2: : No such file or directory
diff-coverage: WARNING — worker pool exited nonzero; unclassified cases fail closed below
differential coverage summary: cases=19999 pass=0 fail=19999 export_status=0
```

`diff-coverage` fans its rows out as
`ls "$ROWDIR"/*.in | xargs -P $JOBS -n 1 bash -c 'run_case "$1"' _`
(line 1370): one absolute path per row, all in ONE argv. Under this
tree the row path is 129 bytes
(`…/t4-grossmith/artifacts/grossmith/2026-09-01/tmp/golean-coverage-rows.XXXXXX/000001.in`);
19,999 of them are 2.58 MB; `ARG_MAX` is 2,097,152. `ls` refused,
`xargs` received EMPTY input and — GNU xargs without `-r` — ran the
command ONCE with no argument: `run_case ""` wrote a manifest-error row
to `.out` in the repo root (the stray untracked file
`FAIL\t\tunknown\tmanifest\texpected 10 tab-separated fields`, removed),
which is the `environment: line 2` message. No row was ever run; the
assembler's fail-closed fallback wrote "worker produced no result" for
every row, as designed. Campaign 2 never saw this because it used
`/tmp` (45-byte paths → ~900 KB for 20,000 rows); this lane forces
TMPDIR inside the artifacts tree because `/tmp` is write-only under
the agent sandbox.

**Not the cause: load.** The coordinator's hypothesis (a concurrent
`ci --diff` starving 10 s per-case timeouts) does not fit the
evidence: timeouts land as stage `go-run`/`lean-run` rows with the
timeout text, never as `harness` worker deaths; the log names the real
failure; and the per-case clone step is the prebuilt `golean` binary
(`diff-coverage` runs `lake build` once up front — the smoke did that,
under the cap — and never per case). Load DID show in the rerun's wall
clock (29.5 min vs 18 min), not in its verdicts (0 timeouts).

**Fix (runner side; `diff-coverage` is trusted surface and was not
touched).** Decision 0.7 (chunking under the C9 bound), 0.8 (leg
guard), 0.10 (build-lock courtesy check). Verified: the guard refuses
the failed batch on all three criteria; the rerun's five chunks all
passed it.

**Owed to the apparatus (recommendation, not done — a trusted-surface
change needs its own gate + audit):** the fan-out at
`diff-coverage:1370` is a latent bound on corpus size × TMPDIR length —
`find "$ROWDIR" -name '*.in' -print0 | xargs -0 -r …` removes both the
ARG_MAX ceiling and the empty-input worker (`-r`). Today's full corpus
(2,506 rows under `/tmp`) is ~110 KB, far from the limit; the limit
becomes real at ~23,000 rows under `/tmp` or ~8,000 under a 130-byte
TMPDIR.

### 4.2 The 386 discrimination control

Not run in campaign 3: `gengo -clone gc-386` (300 cases, seed
5,000,000, run while diagnosing) had the reference pass 300/300 and
EVERY 386 clone binary die with SIGTRAP (exit 133) — reproduced with a
3-line `GOARCH=386` hello world, sandboxed and unsandboxed. grossmith's
own guard printed "INCOMPLETE CAMPAIGN — 0 of 300 cases reached a
semantic verdict". This is the box limitation
`docs/2026-09-01_oracle-legs.md` Leg 2 already recorded; campaign 2
ran the same control fine on 2026-08-20, so it is environmental. The
runner prints the control's outcome and never counts it toward the
leg; the last valid discrimination measurement remains campaign 2 §6
(870/3,493 in-tag, 0 off-tag).

---

## 5. Every divergence, triaged

From `triage-all.tsv` of both legs (mechanical class in brackets; the
human re-class and disposition follow). Controls: every metamorphic
statement below is the runner's `-N -l` re-run of the case's own
`driver.go` compared to the recorded default-flags document; hand
derivations were checked against the recorded observation values.

**Classification caveat (audit fix G-3; [AGENT] note — the doctrine
question is escalated to the [USER] by the coordinator, and NOTHING is
re-labelled here).** The LATITUDE dispositions below inherit their
classification from `docs/2026-08-11_latitude-inventory.md` as it
stands, and that inheritance is UNDER REVIEW on two points. (i) **E5.**
The inventory reads gc's early store (an earlier target written before
a later right-hand operand panics) as a spec-legal member of a two-point
latitude. The verifier observed that this sits against BUG-075's
treatment of the SAME two-phase sentence (spec#Assignment_statements,
applied to `return` through spec#Return_statements "like an
assignment"): there the machine's own early store of result 1 before
operand 2's panic was filed and fixed as a wrong-answer BUG — a forced
point — while here gc's identical shape on an assignment is recorded as
permitted. Both readings cannot hold of one sentence unless the
assignment/return distinction is doing the work; until the [USER] rules,
§5.0 and §5.2 are "latitude per the inventory as it stands", not
settled, and the two decision-0.11 overrides carry the same caveat.
(ii) **E13.** The inventory entry scopes itself to type assertions and
index expressions ("a type assertion is none of these, and neither is
an index expression") and does not name slice expressions, so §5.3's
E13 classification of `case_01848` is a RECOMMENDED annotation (a new
axis for the entry), not an application of it. One fact wants a probe
row BEFORE annotating: on E13's own `bare-index` probe (`s[i], wit()`)
gc ran the sibling call FIRST — the machine's order — whereas on
`case_01848`'s string SLICE gc panicked BEFORE the sibling calls. Index
and slice thus fall on opposite sides in gc; that is either more of
E13's "the axes fall on opposite sides" evidence or a hint that slicing
is a distinct point. A `"ab"[i:], wit(…)` probe beside `bare-index`
decides which, and belongs in the annotation's evidence table.

### 5.0 `m3pairs/part-01/case_03079` (seed 6,003,079; forced pair `early_return+defined_types`) — observation-mismatch, `q5` (`v9 uint64`): machine 53, gc 34 → [machine-bug-candidate] → **re-classified LATITUDE: E5 again (second witness of the same point, the other leg)**

Both sides recovered at `psite = 13`; gc self-stable. Inside the loop:

```go
v9, v5, _ = max((v19-v19), (v19%uint64(60))), ((v5 << 1) << 1), ((v0 % v0) + (v0 | v0))   // v0 == 0
```

`v0` is 0 by psite 10 (`((v0 % v0) & max(v0, -10)) % -2147483648` with
`v0 = -8` gives 0), so the third right-hand operand divides by zero on
the first iteration. The machine holds every store (`v9` stays 53);
gc has already stored `max(0, 34) = 34` into `v9`. Same mechanism as
§5.2 with a COMPUTED first operand (a `max` call over a variable) —
E5's early store is not about constants at all. **Disposition:** the
same E5 annotation as §5.2 (two campaign-3 witnesses, one per leg; rate
2 in 39,800 — the shape needs a multi-target assignment whose later
operand panics by division, which the generator's `panic_risk` arm
supplies at ~5 % of statements); NO corpus row; no BUGS entry.

### 5.1 `m3a-rerun/part-03/case_03428` (seed 5,011,428) — reference-infra → [gc-bug-candidate] → **L-015, third witness**

```
<autogenerated>:1: offset too large in 00166 (…/case_03428/subject.go:55)	MOVB	AL, main.v13+2147483664(SP)(CX*1)
```

gc at default flags refuses to assemble the program; at
`-gcflags=all=-N -l` it compiles AND runs. Same class, same message
shape, same 2^31+ stack displacement as the two campaign-2 cases
(`docs/spec-divergence-ledger.md` L-015, kind `gc-bug`,
reference-infra class): a legal program whose defined behavior is a
runtime index panic (`spec#Run_time_panics`) fails at assembly time.
Rate is now 3 in ~100k generated programs. The machine never saw the
case (the harness refused it before the clone) — nothing to attribute.
**Disposition:** annotate L-015 with the third case; no corpus row.

### 5.2 `m3a-rerun/part-04/case_03110` (seed 5,015,110) — observation-mismatch, `q6` (`v9 uint64`): machine 318047311615681922, gc 29 → [machine-bug-candidate] → **re-classified LATITUDE: E5, the machine on the spec-literal point**

Both sides recovered a panic at the same site (`q13 = psite = 12`);
gc is self-stable (`-N -l` byte-identical). The site is

```go
v7, v9, v2 = ((-v7) + v7), uint64(29), (min(w3, w3) / w3)   // w3 == 0
```

The third right-hand operand divides by zero. `spec#Assignment_statements`: "the
assignment proceeds in two phases. First, the operands of index
expressions and pointer indirections on the left and the expressions
on the right are all evaluated in the usual order. Second, the
assignments are carried out in left-to-right order." Read literally, a
phase-1 panic precedes every phase-2 store, so `v9` keeps its earlier
value `((-v9) - v9) / v9` with `v9 = 58` = `(2^64 - 116) / 58` =
318047311615681922 — the machine's answer. gc stored `29` into `v9`
before evaluating the panicking operand.

This is exactly `docs/2026-08-11_latitude-inventory.md` **E5 "Early
store across the phase boundary — PINNED to the spec-literal point; gc
elsewhere"** (`x, a[i].f = 1, 7/z`), including its note that "here the
machine's point is the SPEC-shaped one and gc's is the exotic one".
Reduced probes (`artifacts/grossmith/2026-09-01/probe-e5/case/main.go`),
both sides:

| probe | shape | gc (default = `-N -l`) | machine | spec-literal | harness |
|---|---|---|---|---|---|
| p1 | `a, v, b = -a+a, 29, z/z` | 29 (early store) | 58 | 58 | FAIL differential |
| p2 | `a, v, b = -a+a, w, z/z` (non-constant middle RHS) | 29 (early store) | 58 | 58 | FAIL differential |
| p3 | `b, v = z/z, 29` (panic FIRST) | 58 | 58 | 58 | PASS |
| p4 | `v, b = 29, s[i]` (INDEX panic instead of division) | **58** (store held back) | 58 | 58 | PASS |
| p5 | `v, b = 29, z/z` (two targets, as generated) | 29 (early store) | 58 | 58 | FAIL differential |
| p6 | control: `v = 29; b = z/z` | 29 | 29 | 29 | PASS |

(gc column: `go run` at default flags and at `-gcflags=all=-N -l`,
identical; machine column: the same file run through
`scripts/diff-coverage` under the cap with a six-row hand manifest,
`artifacts/grossmith/2026-09-01/probe-e5/`. The machine realizes the
spec-literal point on every row.)

New facts for E5's record: gc's early store is not a constant-folding
artifact (p2: a variable read is stored early too) and it is
OPERATION-SPECIFIC — an index bounds panic holds the store back (p4),
a division panic does not (p1/p5). That is a compiler-internal
realization, unpinnable, which confirms E5's disposition ("a future pin
must use the membership treatment"). The generated case adds the
uint64/multi-target/third-operand shape as a second witnessed point.
**Disposition:** annotate E5 with this case and the p1–p6 matrix; NO
corpus row (a strict pin of either member is forbidden by E5); no BUGS
entry. The triage rule's default to "ours" was right to fire and right
to be overridden by the record.

### 5.3 `m3a-rerun/part-05/case_01848` (seed 5,017,848) — observation-mismatch, `q15` (`wOrd`): machine 1026, gc 1 → [latitude-candidate] → **LATITUDE: E13, string-SLICE axis (new witnessed shape)**

Both sides recovered at `psite = 9`; gc self-stable. The site is

```go
v11, _ = "ab"[v0:], wit(min(wit(int(v5), 2), (v0/57)), 3)   // v0 == -52
```

after `v1 = h0(wit(v0, 1))` at psite 8. The slice bound is negative, so
`"ab"[v0:]` panics (slice bounds out of range). The machine ran both
remaining `wit` calls first — `wOrd = ((0·31+1)·31+2)·31+3 = 1026` —
and then panicked; gc panicked at the slice expression with only
`wit(…, 1)` recorded (`wOrd = 1`). `spec#Order_of_evaluation` orders
"function calls, method calls, receive operations, and binary logical
operations"; a slice expression is none of these, and it is a SIBLING
operand of the calls, not their argument, so nothing lexically forces
it before them. This is
`docs/2026-08-11_latitude-inventory.md` **E13 "Non-call panicking
operations (type assertion, indexing) vs SIBLING calls — PINNED,
structural: calls first"**, reading I-2/L-013 (UNSEQ), now witnessed on
a third axis: string SLICING (E13 lists type assertion and index). gc
realizes the other member, as it did in campaign 2 §4.
**Disposition:** annotate E13 with the string-slice axis and this
case; NO corpus row (E13's pin is structural and "no strict row should
pin it"); no BUGS entry.

### 5.4 Not divergences: environment artifacts

The 386 SIGTRAP (§4.2) and the first-run worker deaths (§4.1) are
runner/box artifacts, classified `harness-artifact` by the tool and
excluded from the campaign total. No `harness-error` occurred in any
valid chunk: the adapter fit today's harness on every judged case
(including the acknowledged `fatal`/`fuel-out` statuses — neither
appeared).

---

## 6. Promotion recommendations (none made; all RECOMMENDED)

- **Corpus rows: none.** Both machine/gc disagreements are recorded
  latitude points whose inventory entries forbid a strict pin (E5,
  E13); the reference refusal never reached the machine.
- **BUGS.md entries: none.** No forced-point wrong answer was found in
  39,800 judged programs — this is the campaign's headline,
  stated as a lower bound: observed ∈ modeled on every judged program
  in grossmith's fragment at `7cf19198`.
- **Three annotations owed** (record-side, not fixes): L-015 (+1
  witness, seed 5,011,428, rate 3/~100k); E5 (+ the campaign-3 shape
  and the p1–p6 matrix: early store is variable-too and
  operation-specific); E13 (+ string-slice axis).
- **Regression evidence delivered by construction:** BUG-062 (fixed
  2026-08-31; `min`/`max` vs call order) — `min`/`max` appear in ~4,200
  lines per 3,000 programs (§3 census) and produced zero mismatches;
  BUG-042/043 (defined-type incdec / range-over-int) — `defined_types`
  is a swarm arm, zero mismatches. Campaign 2's F-1…F-4 are all
  disposed at tip (BUG-062 Cases line; L-014/L-015; E13).
- **To the apparatus (ours, future slice, trusted surface):** the
  `diff-coverage:1370` row fan-out hardening (§4.1). **To grossmith
  (external, not patched here):** add `fatal`/`fuel-out` to the
  adapter's status sets (§1 C5); campaign 2's F-5 stands; a
  `-profile golean` generate-only flag would make the §3 census exact.

---

## 7. What widening each exclusion costs (assessed, NOT done)

Read from the generator and its design docs ([AGENT] sub-assessment,
read-only on `deps/grossmith`). The six exclusions are exactly the
model's riskiest surface; this lane widens none of them (a change to
the reference checkout — propose only). "Size" is relative to
grossmith's own delivered rungs (`type_switch` +128 lines, `strings`
+204, `slice_triple` +212, `order_witness` +491, `tuple_forward` +680).

| exclusion | where it lives | invariant hazard (compile / HALTS / strict determinism / observation injectivity) | size vs a delivered rung | GoLean-side prerequisite | GoLean bug classes it reaches (title census: all / open) |
|---|---|---|---|---|---|
| **defer/recover beyond `recover_wrapper`** | NOT a grammar gap: `defer`/`recover` arms exist and emit (`gen/stmt.go:66,68,970,986,1005`); blocked by ONE consumer line, `golean/golean.go:97` (Exclude), enforced by `obsCallRe` (`:215`) | none new — both forms are budget-priced and deterministic; the only hazard is the obs\* EVENT stream, which GoLean has no model for | **< `type_switch`**: a non-obs defer form (write a named result instead of `obsX(...)`) reuses the arm, ~80–150 lines; then drop `defer`/`recover` from Profile | none (option a: grossmith emits a non-obs defer); or GoLean models obs\* (option b, larger) | defer/recover/panic: 18 / 1 open (BUG-004) |
| **pointers / closures / package vars** | grammar absence: no pointer `Shape` (`gen/types.go:29-72`); helpers pure by construction, with the revisit trigger named in-source (`gen/gen.go:266-271`); ledger `deferred(effect discipline)` | determinism (aliasing + unordered effects) — ANSWERED: effect-discipline design E1/E2/E4, mechanism 2 = `wit(p *int, x, tag int)` is the staged first pointer rung; nil-deref is an existing panic kind (`observe/observe.go:47`) | mechanism 2 ≈ `order_witness` or less (corner + instrument already built); GENERAL pointers (new Shape, `&`/`*`, pointer receivers, pointee observation) ≈ 2–3× `tuple_forward` | none hard-blocking (10 pointer bug titles show the machine already carries the surface) | pointer/deref/address: 10 / 0 open — but BUG-056/063/038/039/033's habitat |
| **floats / complex** | grammar AND wire absence: no `ShapeFloat`; `observe.Value` has Bool/Int/Uint/Str only (`observe/observe.go:90-107`); ledger `deferred(equivalence policy)` | observation injectivity (−0, NaN payloads, JSON lossiness) and cross-arch determinism (excess precision/FMA — load-bearing for the 386 lane); recorded answer: adopt GoLean's bit-pattern + NaN-canonicalized equivalence | ≈ 2× `strings` PLUS a protocol bump (observe v2→v3, driver reflect arm, `Equal` float policy, literal ranges): ~400–600 lines / 4 packages | GoLean's float equivalence policy adopted verbatim in `observe.Equal` (cheap: GoLean already has it) | float/complex: 0 / 0 — pure prospecting |
| **stdlib imports** | charter-level: subjects import-free (`gen/gen.go:189-191`; only the driver imports); ledger Out of scope ("harness is single-file") | HALTS: unpriced foreign call bodies break `budget.go`'s "every callee body generated before its first call site"; determinism: most useful packages are map-ordered/allocation-visible | narrow slice (one pure total package, e.g. `math/bits`) ≈ `slice_triple`; the single-file harness assumption is the real cost; full stdlib/fmt co-dearest with concurrency | GoLean multi-package frontend maturity + shim coverage | import/stdlib/package: 11 / **3 open** (BUG-061, BUG-059, BUG-008) — largest open class |
| **generics / type params / embedding** | grammar absence; ledger `deferred(rung order)`: "blocked on embedding + pointer receivers"; BRIEF ladder item 8 wants a validity-by-construction design first | compile legality: instantiation validity, constraint satisfaction, promotion depth rules; breaks the "exactly ONE defined type satisfies each interface" invariant (`gen/types.go:52-58`) | ≥ `tuple_forward` after a design note; strictly downstream of the pointer rung; realistically two arcs | none blocking; low yield until pointers land | generic/embed/promotion: 5 / 0 open |
| **channels / goroutines / select** | grammar absence AND out of scope in both roadmaps ("GoLean's enumerator covers it ahead of generation"); effect-discipline §4 puts it behind relational oracles | kills STRICT-lane determinism by construction; HALTS (deadlock = non-termination; the execution budget is single-threaded); recorded answer = the lanes model, whose membership lane is itself BLOCKED-ON a stable machine-readable GoLean reason-code contract | multi-arc: membership lane (R6) is a full rung; concurrency needs a further permutation/confluence lane + deadlock-freedom-by-construction + a re-priced budget; ≥ 5× `tuple_forward` | GoLean publishes stable stage strings for the membership failure kinds; adapter maps the confluent/racy vocabulary | chan/goroutine/select/race/sync: 16 / 2 open (BUG-041, BUG-002) |

**Cheapest → dearest:** defer (one consumer line + a ~100-line non-obs
form) → pointers via mechanism 2 (the discipline is signed off and its
instrument shipped) → floats (self-contained but crosses the wire
schema) → stdlib narrow slice (grammar-cheap, breaks the import-free
charter and the budget premise; highest OPEN-bug reach) → generics
(design note first; gated behind pointers) → concurrency (the only one
that contradicts the strict-lane invariant; its cheapest prerequisite
is blocked on a contract GoLean has not published).

**Two facts worth the coordinator's attention:** exclusion 4 is not an
exclusion of defer at all — GoLean already receives real defer/recover
semantics through `recover_wrapper` (13,592 of campaign 2's 79,800
cases), and what the profile excludes is the obs\*-event SHAPE; and the
`Shape` enum is an append-only persisted wire format
(`gen/types.go:24-33`), so adding a float or pointer shape is cheap in
`gen` — the cost lives in `observe`. **Recommended first widening (for
grossmith's owners; a consumer request, per its PLAN):** the non-obs
defer form, then mechanism 2 — together they put grossmith on the two
classes with the densest bug history (defer/panic 18, pointers 10) for
under one `order_witness` of work.

---

## 8. Cadence recommendation

Evidence: two campaigns, 82,700 judged programs, 6 findings (1 machine
bug in each campaign, 3 gc bugs, 1 latitude point, 1 harness sharp
edge); ~1,100 programs/min; zero frontend refusals in-fragment at
79,798 cases. Yield per program is low and falling inside the FIXED
fragment (campaign 2 found nothing new in the shapes campaign 1 had
covered; its find was a shape the corpus never had). Recommendation,
[AGENT], for the [USER] to set:

1. **Weekly, not nightly** — one `m3a`-shaped leg (20k swarm, seeds
   advancing by 10^6 per run, recorded in the report series): measured
   29.5 min on a loaded box (§4), ~18 min idle. Nightly would spend ~10 h/week of box time re-sampling a
   fragment whose divergence rate is ~1 in 40k; weekly keeps the
   regression signal (min/max, defined-type incdec, BUG-042/062 at
   scale) at a tenth of the cost.
2. **Per-frontier-widening** — a full two-leg campaign (swarm +
   pairwise, §3 shape) whenever EITHER side widens the reachable
   fragment: the frontend/machine closing a refusal class grossmith
   emits (today: none — the short-circuit quarantine from campaign 1 is
   closed), or a generator rung landing (defer form, mechanism 2 —
   §7). This is where the yield is: both machine bugs came from newly
   reached shapes.
3. **Per-oracle-pin-move** — one leg, because the oracle is a
   bounded-trust witness and a new gc can change which side is wrong
   (L-014 survives into go1.26.6/go1.27rc3; the version sweep tool
   covers the CORPUS, grossmith covers the generated population).
4. **Not a gate step.** The smoke (12 cases, ~1 min after the build)
   could be added to `ci --slow` as a contract-and-liveness check;
   this lane recommends it and does not add it (no gate changes).
   Anything larger belongs on the schedule, judged by artifacts
   (`no-background-differential-runs` is retired; judge async by
   `triage.tsv`).
5. **Every run is a findings record**: seeds, generator rev, SUT rev,
   verdict counts, `triage.tsv` groups, promotions RECOMMENDED — this
   report's §3–§6 shape. The tool writes the machine half; the human
   writes §5's prose.

---

## 9. Verification performed in this lane

- `scripts/grossmith-run contract`: exit 0, C1–C8 ok (§1); C9 evaluated
  and printed at both legs' start (≤ 8,065 rows/invocation; chunks of
  4,000 / 3,960).
- Refusal self-tests: 7 protected-root spellings (incl. symlink) exit 2;
  unknown mode exit 2; `campaign` without a proven cap: exit 4 from
  `scripts/capped`; `campaign` with an implausible pairs universe
  (a mis-extracted tag count during development) exit 2 before any
  case was generated.
- Leg guard: refuses the failed first `m3a` batch on all three
  criteria (log text, 19,999 worker deaths, >50 % infra); passes all
  ten valid chunks.
- `gengo -verify` on `m3a-rerun/part-04` and `m3pairs/part-01`: every
  case-input digest intact and bound to the manifest; report bound;
  report self-consistent; clone tree bound (4 of 4 claims, both chunks).
  The in-campaign run behind this sentence left NO artifact (audit fix
  G-4); it was re-run post-campaign on 2026-09-02 with the same
  `2026-09-01/bin/gengo`, output saved at
  `artifacts/grossmith/2026-09-01/verify-m3a-rerun-part-04.txt` and
  `…/verify-m3pairs-part-01.txt` — 4,000 and 3,960 cases, exit 0, all
  four claims printed.
- `triage`: real batches (the failed `m3a`; the ten campaign-3 chunks;
  the 300-case 386 control); synthetic 2-case batch exercising both
  outcomes of the metamorphic attribution.
- Campaign 3: `m3a-rerun` and `m3pairs` under
  `GOLEAN_MEM_MAX=32G scripts/capped` (cap proven: `GOLEAN_CAPPED=verified`
  readback), §4; every mismatch hand-derived and matched to the record
  (§5).
- Static gate steps at tip: `check-spec-anchors` ok (this report's
  `spec#Assignment_statements`, `spec#Order_of_evaluation`, `spec#Run_time_panics`
  resolve), `check-bugs.sh` ok, `check-coverage` ok, `bash -n` on the
  tool. `scripts/ci` (plain; no runtime code touched): a fresh worktree carries no
  recorded differential run (the plain gate FAILS closed on that,
  correctly), so `scripts/ci --diff` was run once under the cap — PASS,
  full native corpus + negative corpus re-run and judged against the
  tracked baselines, no regression — and the plain `scripts/ci` then
  replayed it at the committed tree: PASS.

**Failures during the lane, reported with output (audit fix G-4).**

- **`scripts/grossmith-run` CRASHED during the live `m3a-rerun`**, after
  all five chunks had been judged by gengo and each chunk's own
  `triage.tsv`/`triage-groups.tsv` had been written, at the CROSS-CHUNK
  triage merge. `artifacts/grossmith-m3a-rerun.log` ends:

  ```
  Traceback (most recent call last):
    File "<stdin>", line 10, in <module>
  ValueError: not enough values to unpack (expected 7, got 3)
  EXIT=1
  ```

  Cause: `part-03.triage-groups.tsv`'s normalized-detail cell carried
  gc's assembler message verbatim, including a literal newline and tab
  (`… # grossmith-cases/case_ID⏎<autogenerated>:N: offset too large in
  …`), so the merge's line-based 7-field split met a 3-field line. Fix
  (in `7061c5c7`): `norm()` collapses `[\t\r\n]+` to one space, so dedup
  keys and TSV cells are single-line (newline-safe keys); the triage was
  then regenerated in ONE pass (`scripts/grossmith-run triage part-01 …
  part-05`), producing the `triage-all.tsv`/`triage-groups-all.tsv` §5
  cites. The §4 verdict counts come from `batch.json` (written by gengo
  before any triage) and are unaffected; the crash cost the first-pass
  leg merge, not a judgement. `m3pairs` ran after the fix to completion
  (its log's `EXIT=1` is the documented "divergences found" code).
- **`check-spec-anchors` FAILED on this report's own citation** in the
  first plain `scripts/ci` at the tip — `artifacts/ci-plain.log` lines
  26–28 (the offending anchor is spelled out in words here rather than
  quoted verbatim, because the checker scans this report too and a
  verbatim quote re-trips it — which it did, on the first draft of this
  very bullet):

  ```
  UNRESOLVED docs/2026-09-01_grossmith-campaign-3.md:401: spec# + "Assignments" — no id="Assignments" in the pinned go_spec.html
  UNRESOLVED docs/2026-09-01_grossmith-campaign-3.md:611: (the same anchor)
  check-spec-anchors: FAIL — unresolved citations above (pin c19862e5f)
  ```

  The anchor had been written from memory as the bare section title;
  the pinned spec's id is `Assignment_statements`. Corrected in the
  committed report; the `--diff`
  run and the second plain run (`artifacts/ci-diff.log`,
  `artifacts/ci-plain2.log`) resolve every citation. That first log's
  two baseline-diff FAILs are the fresh-worktree "no recorded run"
  refusals the previous bullet describes, not regressions.

Artifacts (gitignored): `artifacts/grossmith/2026-09-01/{bin/gengo,
m3a/ (failed run, kept), m3a-rerun/, m3pairs/, *-smoke/,
selftest-control386/, selftest-synthetic/, census-m3a-3000/,
verify-*.txt}` and the
runner logs `artifacts/grossmith-m3a*.log`, `artifacts/grossmith-m3pairs.log`.
Operational notes for the next operator: the tool's default artifacts
tree is date-keyed per invocation (pin it with
`GOLEAN_GROSSMITH_ARTIFACTS` for a campaign that crosses midnight); a
`pkill -f` whose pattern matches the caller's own command line kills
the caller (it did, once, here — kill by PID).
