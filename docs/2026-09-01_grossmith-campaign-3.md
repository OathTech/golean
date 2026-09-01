# Grossmith integration: the standing instrument + campaign 3 (pre-registered)

Lane: `t4-grossmith` (fidelity work program Tier 4, [USER]-approved —
`docs/assessment/synthesis.md` "Tier 4 … grossmith integration
(cadence, adapter contract test, generator widening …)";
`docs/assessment/decisions-2026-08-31.md`; assessment findings
`lane-b-lower-bound.md` §B10 and `lane-d-apparatus.md` D-8). Tracked
output: this report plus one lane tool, `scripts/grossmith-run`. **NO
baseline, gate, corpus, or reference-checkout changes** — promotions
and BUGS entries are RECOMMENDED here, never made. Everything below is
[AGENT]-executed and [AGENT]-judged inside that mandate; the two
places the lane could not proceed are marked and handed back rather
than worked around. Base commit `7cf19198`; oracle pin go1.26.5
(`baselines/go-oracle-pin`); generator `deps/grossmith` @ `e68867d6`
(campaign 2's revision, now a deliberate pin in the tool).

**One-paragraph status.** The instrument is built and its contract
test is GREEN against today's harness (C1–C8, §1): the adapter that
the assessment presumed interface-dead is not — the 7-vs-10-field
manifest and stage-vocabulary drift belong to the RETIRED `side/gofuzz`
prototype, and `deps/grossmith`'s adapter already speaks today's
10-column manifest and 5-column results file; what was missing was
anything that would TELL us when that stops being true, which now
exists. The soundness kit (dedup, four-class triage under the
pinned-oracle rule, §2) is built and self-tested on real and synthetic
batches. **Campaign 3 is PRE-REGISTERED (§3) but NOT EXECUTED in this
lane**: every `lake build` and every campaign must run inside a proven
memory cap (`scripts/capped`), and the agent's process cannot reach
the systemd user bus (`Failed to connect to bus: Permission denied` /
`Operation not permitted`, sandboxed and unsandboxed alike — the
zellij snap confinement, `NoNewPrivs=1`). The cap wrapper refuses
fail-closed, the sandbox rule is ask-don't-hack, so §4 is a placeholder
with the exact two commands the operator (or a process with bus
access) runs; the tool then fills §4/§5 mechanically (`triage.tsv`).
The widening-cost assessment (§7) and the cadence recommendation (§8)
do not depend on the run and are complete.

---

## 0. Decisions logged in this lane

| # | decision | provenance |
|---|---|---|
| 0.1 | Generator revision pinned at `e68867d6…` in `scripts/grossmith-run` (`GROSSMITH_PIN`); a mismatch is contract DRIFT (C1), moved only by editing the constant with a written reason in a campaign report. | [AGENT] — applies the oracle-pin discipline to the second external witness |
| 0.2 | Machine statuses `fatal`, `fuel-out` are ACKNOWLEDGED-unknown to the adapter (its fallthrough is `harness-error` with the status preserved: fail-closed, visible, only infra-vs-semantic-undecided); any OTHER unknown status is DRIFT (C5). | [AGENT] — see §1 C5 for why acknowledging beats failing |
| 0.3 | Lane-only stages `membership`/`confluent`/`racy` are accepted as unmapped ONLY while the adapter provably pins `lane=strict` (asserted, C2/C4). | [AGENT] |
| 0.4 | No shrink/reducer step: grossmith has none (`-replay` reproduces, nothing minimizes; campaign 2 minimized by hand) and building one is outside an integration lane. Stated, not hidden. | [AGENT] |
| 0.5 | Campaign 3 parameters pre-registered BEFORE any result exists (§3) — seeds, sizes, budget. Not run by this lane (§4). | [AGENT]; the run itself is handed to the operator |
| 0.6 | `deps/` populated in the lane worktree by `scripts/setup-deps --from <main checkout> --only go,goose,raft,grossmith` (local clones, gitignored). The worktree `.lake/` was seeded by copying the main checkout's build tree (identical sources at `7cf19198`; the binary post-dates the last `GoLean/` source commit `dd93725f`) — a repo-local convenience, NOT a substitute for the capped `lake build` the operator's run performs. | [AGENT] |

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

**Findings from building it (record corrections, no code change):**

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
gengo batch (`batch.json` + `manifest.tsv`) into `<batch>/triage.tsv`
(one row per non-`match` case) and `<batch>/triage-groups.tsv`.

**Dedup.** Key = (verdict, stage, normalized detail), where
normalization collapses case ids, absolute paths, quoted strings, hex
and decimal literals. Two hits of one mechanism share a group; the
group file carries count + representative. (Self-test on a real
300-case batch: 300 clone-infra rows → 2 groups, split only by
"(core dumped)" presence — honest, not over-merged.)

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

**Self-tests run.** (i) A synthetic batch with two `observation-mismatch`
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

## 3. Campaign 3 — pre-registered parameters

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

The `campaign` mode's sequence: contract (§1) → smoke (12 cases, seed
424242, end-to-end through gengo → diff-coverage → verdicts; refuses on
any `harness-error`, unjudged case, or reference that did not run) →
the leg → the gc-386 discrimination control (`m3a` only) → `triage`.

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

## 4. Results — NOT RUN IN THIS LANE (operator hand-off)

**Why.** `scripts/capped` (mandatory for `lake build`, which
`diff-coverage` performs, and for a 32-worker reference pass) creates a
transient `systemd-run --user --scope`; from this agent's process the
user bus is unreachable — sandboxed: `Failed to connect to bus:
Permission denied`; with the tool sandbox disabled: `Operation not
permitted` (`/run/user/1000` itself is unreadable; AppArmor profile
`snap.zellij.zellij`, `NoNewPrivs=1`). The wrapper refuses (exit 4)
exactly as designed; the lane did not run `lake` or the campaign
uncapped (`GOLEAN_MEM_MAX=none` exists as a loud opt-out — declining
it is the point: a shared 125 G box with other agents' builds is the
scenario the cap exists for), and did not bypass the bus (sandbox
rule: ask, don't hack). `scripts/grossmith-run campaign` self-wraps and
inherits this refusal; `contract` and `triage` need no cap and ran.

**What the operator runs** (two commands, §3's table, ~40 min total,
from `/home/dev/projects/golean/.claude/worktrees/t4-grossmith`; the
worktree already has `deps/` and a seeded `.lake/`, and the first
`diff-coverage` inside the smoke performs the real capped `lake
build`):

```sh
GOLEAN_MEM_MAX=32G scripts/capped scripts/grossmith-run campaign --seed 5000000 --n 20000 --control386 2000 --label m3a
GOLEAN_MEM_MAX=32G scripts/capped scripts/grossmith-run campaign --seed 6000000 --pairs 20 --control386 0 --label m3pairs
```

Each leg ends by printing verdict counts and the triage summary; the
record is `artifacts/grossmith/<date>/{m3a,m3pairs}/{batch.json,
triage.tsv,triage-groups.tsv}` plus `<label>.params.txt` /
`<label>.log`. `gengo -verify <leg>` re-checks the batch offline. This
lane, on resume, fills the table below from those files and writes §5.

| leg | cases | ref-ran | match | observation-mismatch | reference-infra | clone-infra | harness-error | wall |
|---|---|---|---|---|---|---|---|---|
| m3a | — | — | — | — | — | — | — | — |
| m3pairs | — | — | — | — | — | — | — | — |
| m3a-control386 | — | — | — | (in-tag / off-tag: — / —) | | | | |

### 4.1 What DID run here, and what it showed

- **Contract**: C1–C8 green (§1).
- **`gengo -clone gc-386`, 300 cases, seed 5,000,000** (no lake
  needed): the reference pass ran 300/300 (53 panic paths, 23
  wrapper-caught), but **every 386 clone binary died with SIGTRAP (exit
  133)** — 300 `clone-infra-failure`, "INCOMPLETE CAMPAIGN — 0 of 300
  cases reached a semantic verdict" printed by grossmith itself (its
  generated-vs-judged guard doing its job). Reproduced with a 3-line
  `GOARCH=386` hello world, sandboxed and unsandboxed alike. This is
  the box limitation `docs/2026-09-01_oracle-legs.md` Leg 2 already
  recorded ("386 binaries abort in this sandbox — exit 133 / SIGTRAP …
  carried to the operator, not worked around"); campaign 2 ran the
  same control fine on 2026-08-20, so it is environmental. Consequence
  for campaign 3: the `--control386` leg will show the same until the
  host capability call is made; the operator may pass `--control386 0`
  and the report must then say the discrimination control was NOT run
  (the width-tag yield from campaign 2 §6, 870/3,493 with 0 off-tag,
  stays the last measurement). The tool prints the control's outcome
  and never counts it toward the leg.
- **Triage self-tests** (§2): behave as specified.

---

## 5. Every divergence, triaged

Pending §4. The mechanical output is `triage.tsv` per leg; this
section's format, fixed now: one row per dedup GROUP —
`Gn × count | verdict/stage | class | representative id, seed |
evidence | proposed disposition` — then per-group prose with the
minimal repro where the class is `machine-bug-candidate` or
`gc-bug-candidate`, following campaign 2's conventions (controls on the
same path, hypothesis stated, disposition proposed).

Two environment artifacts are already known and pre-classified
`harness-artifact`, not divergences: the 386 SIGTRAP (§4.1) and any
`fatal`/`fuel-out` status landing as `harness-error` (§1 C5).

---

## 6. Promotion recommendations (none made; all RECOMMENDED)

- **From campaign 3:** pending §4/§5. Rule to apply: every
  `machine-bug-candidate` confirmed by hand becomes a corpus row +
  BUGS entry (red pin); every confirmed `gc-bug-candidate` becomes a
  `spec-divergence-ledger` `gc-bug` entry with the `-N -l` matrix (as
  L-014/L-015); every confirmed `latitude-candidate` becomes a
  latitude-inventory row (never a strict corpus row, as E13).
- **Campaign 2's offers are all disposed** — verified at this tip, so
  campaign 3 is regression evidence rather than a re-offer: BUG-062
  fixed 2026-08-31 with the five `builtins/min-max-vs-call-order/*` and
  `len-vs-call-order/*` rows on its Cases line (F-1/F-2); L-014 and
  L-015 in the divergence ledger (F-4); E13 in the latitude inventory
  (F-3). `min`/`max` are generated in ~4,200 lines per 3,000 programs
  (§3 census), so campaign 3 exercises the fix at scale by
  construction.
- **Grossmith-side notes to hand back (external project, not patched
  here):** (a) add `fatal` and `fuel-out` to the adapter's status sets
  (§1 C5); (b) campaign 2's F-5 (the STRICT lane can land on
  unsequenced points via `order_witness`) still stands; (c) a
  `-profile golean` flag that applies `golean.Profile` WITHOUT judging
  would make the §3 census exact.

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
   advancing by 10^6 per run, recorded in the report series) at ~20
   min. Nightly would spend ~10 h/week of box time re-sampling a
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

- `scripts/grossmith-run contract`: exit 0, C1–C8 ok (output in §1).
- Refusal self-tests: 7 protected-root spellings (incl. symlink) exit 2;
  unknown mode exit 2; `campaign` without a proven cap: exit 4 from
  `scripts/capped` with its diagnostic (the fail-closed path, §4).
- `triage`: real 300-case batch (300 rows → 2 groups, all
  `harness-artifact`); synthetic 2-case batch (one `machine-bug-candidate`
  with "gc self-stable", one `gc-bug-candidate` with "gc default != -N -l").
- `gengo`: builds from the pinned checkout into the artifacts tree
  (repo-local GOCACHE); the reference checkout stayed clean
  (`git status --porcelain` empty before and after).
- Static gate steps that need no build, run by hand at tip:
  `check-spec-anchors` ok (this report's `spec#Order_of_evaluation`
  resolves), `check-bugs.sh` ok, `check-coverage` ok, `bash -n` on the
  tool. **`scripts/ci` itself (self-wrapped in `scripts/capped`) could
  not run from this process for the §4 reason** — it is owed at tip by
  the operator's run: `scripts/ci` (plain; this lane touched no runtime
  code, so no `--diff`).

Artifacts (gitignored): `artifacts/grossmith/2026-09-01/{bin/gengo,
selftest-control386/, selftest-synthetic/, census-m3a-3000/, tmp/,
go-build-cache/}`.
