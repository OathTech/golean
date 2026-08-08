# The membership testing lane — design note (2026-08-04)

Status: design of record for arc slice 3 (landed 2026-08-05, after the
control-flow sub-branch merged).

Charter: general-coverage arc slice 3; nondeterminism doctrine's testing
half (`docs/2026-08-04_nondeterminism-doctrine.md`). For observables that
genuinely depend on the `Choices` stream, equality against one `go run`
is the wrong question; the right one is MEMBERSHIP: every Go-observed
behavior lies inside the machine's admitted set.

## Lane classification (fail-closed)

`cases.tsv` gains an optional `lane` column: `strict` (default) or
`membership` with a mandatory free-text `why` (which observable depends
on which consumption site). Guards, both directions:
- a STRICT case that varies across the adversarial streams keeps failing
  (`nondet` stage — unchanged);
- a MEMBERSHIP case whose enumerated observation set is a SINGLETON
  fails classification ("belongs in the strict lane") — no lazy
  demotions of deterministic cases to the weaker oracle.

Gate self-test (delta-review T2, 2026-08-05): the lane's shell gates are
covered by `scripts/test-lane-validation`, wired into `scripts/ci` — the
bad-shape fixtures hand-run at landing (nine manifest rejections incl.
the explicit-width requirement, three acceptances) run on every gate,
and the go-dependent harness half (samples=0 re-validation, the
non-native-frontend guard) runs under `--diff`. This deliberately stops
short of a tamper-test framework: shell-gate integrity remains the
pre-merge audit's dimension, per repo practice; the script only keeps
the landing-time fixtures runnable instead of leaving them in commit
messages.

## The machine-side enumerator

New CLI subcommand (`lean coverage-observations --input <wire> --max-width B
--max-sites D --cap N`): enumerate the DISTINCT observations over the
choice tree by exploring stream prefixes over alphabet `[0, B)` to
consumption depth `D`, deduplicating observations.

Key design point — NO semantics changes: `Choices.consume` takes picks
modulo the site's bound, so exploring values `0..B-1` at each position
covers every behavior IF AND ONLY IF `B ≥` every site's bound in the
case. `B` (`width`) is per-case metadata and EXPLICIT — no silent
default (audit F2a, 2026-08-05): the coverage claim rests on the
author-asserted width, so every membership row declares it and argues
the site bound in its `why`. The enumerator FAILS CLOSED wherever it
cannot certify: the alias guard probes each explored pick position with
a small ladder of values ≥ B (`+B`, `+2B`, `+4B`) — an observation
outside the enumerated set REFUTES the width assertion ("raise width").
The guard is a HEURISTIC cross-check, not a proof: a bound > B whose
extra residues alias existing observations escapes the ladder.

Correction of record (delta-review T1, 2026-08-05): commit e2141ca's
message (and the guard's docstring as first shipped) claimed "bounds
beyond 5B are unprobed" — BACKWARDS. For a true bound M ≥ 5B every
rung's probe value is its own residue, a live unenumerated one (the
most informative case); what a rung cannot reach is residues its offset
never lands on. The real inert condition: a rung of offset d is
provably inert at a site of true bound M when d ≡ 0 (mod M) — with the
original +B/+2B/+4B ladder that alignment happened whenever M divides
m·B (concretely the shipped cap-zero configuration, width 16 over bound
8: all 48 probes inert — harmless there because width ≥ bound means
enumeration itself covers every residue and rung silence is exactly a
correct assertion's expected behavior, but the prose claimed the wrong
condition). The ladder offsets are now +B, +2B+1, +4B+3 (upper rungs
de-aligned from divisor coincidences; probe counts unchanged at 48 /
36864, both lane cases re-verified green, refutation at width 2 over
the bound-3 map site re-verified firing). When width ≥ the true bound,
ALL rungs are necessarily silent — expected, not a blind spot.

`N` caps
the observation set (fail loud if exceeded — such a case is too wide for
enumeration and needs a per-case predicate instead; none expected in the
current corpus). Every enumerated member must carry a status in the
case's DECLARED STATUS SET (audit F1; SET-VALUED since the arc-final
audit F8, 2026-08-08): a member whose status is outside the set fails
the enumeration loudly. The original claim here — "a member whose
status differs is by construction a machine bug, not an envelope
point" — was FALSE and is corrected in place: gc itself realizes
status-diverse envelopes (a leaked goroutine with an observable effect
legitimately spans `ok` and `panic` — the D6 main-exit latitude,
realized through BUG-044's main-exit window and verifier-probed:
ok=176/panic=24 over 200 plain runs on the dossier's p60 shape). Such
cases declare `statuses=ok+panic` in their lane params (the manifest
requires the set to include the row's `expected_status`, the
default-stream status); the enumerator receives the whole set via
`--expect-status ok,panic`, and only membership OUTSIDE the declared
set is a machine bug. `race` remains a singleton (the racy lane's
every-path-refuses claim admits no value members), and deadlock
members still have no membership handling (they fail the enumeration
as the member-class failures they are — audit F15 fixed the
diagnostic that used to misattribute them to the site-bound
accountant).

What the enumerator REUSES vs COPIES (audit F7 correction — this note
originally claimed "reuses `execStmt` verbatim", which was wrong):
reused is `stepFn`, the semantic core's step function, so every machine
step is the machine's own; COPIED (hand-mirrored, not shared — a shared
helper would touch GoCore, which stays bit-identical) are the driver
layers: `enumSetup` mirrors `runFunctionWithContextM`'s entry wiring and
`enumRun` mirrors `runConfig`'s terminal handling. (Dated addendum,
arc-final audit F16 2026-08-06: "GoCore stays bit-identical" was TRUE
of this slice — `git diff eeb0b74..f8c3687 -- GoLean/GoCore/` is empty
— but it is a slice-scoped fact, not a standing constraint; later
slices changed GoCore freely, and the init slice shared `seedGlobals`
with the CLI. The standing rationale is the POLICY stated in
`GoLean/CLI.lean`: the lane adds no driver helper to GoCore, and the
copies stay pinned by the two mechanisms below.) The copies are pinned
by the driver-agreement eval tests in `Tests/GoCoreEval.lean` (per
consumption-site class, incl. the panic-observation path) and by the
harness's per-case coupling check (`native-json-run --choices <s>`'s
observation ∈ enumerated set, four streams, every membership case, every
differential run).

Deferred decision (recorded, audit F2): MECHANICAL bound certification —
the enumerator reading each consumption site's actual bound instead of
trusting the author's width — would need a core-adjacent instrumentation
hook (e.g. `Choices` recording site bounds as it consumes). That touches
the semantic core's surface and is explicitly NOT taken unilaterally in
this slice; it goes to the arc-final audit as a candidate.

## The Go side

- Features where Go itself randomizes (map order): sample `go run` R
  times (per-case `samples`, default 5). Every sample must be a member.
- Features where Go is deterministic per version (append cap): one
  sample per run; membership is then effectively VERSION-TRACKING — a
  toolchain bump that leaves the envelope turns the case red, which is
  exactly the alarm we want (widen deliberately, per the doctrine).

## Pass criterion and the width signal

PASS = every Go sample ∈ the enumerated set (possibilistic — the
doctrine's scope). Additionally the harness RECORDS (metadata, never a
pass criterion): |enumerated set|, |Go-exhibited subset|, and the
unexhibited members. That record operationalizes half of the
envelope-width review — a set Go never touches any corner of is a
review flag, not a failure (Go may be deterministic where the spec is
loose; that is the append case by design).

## Baseline integration

Membership cases enter `baselines/native-full.tsv` with stage
`membership` on PASS rows' metadata untouched (result+stage remain the
regression signal). `slices/full-slice-cap-zero` reclassifies to the
membership lane in the same commit the lane lands, with the re-pin
reason; BUG-005's three order-observing differential reds stay OUT until
their live-iteration fix (recorded coupling) — the lane must not be used
to launder a known divergence.

## Envelope-width review — recorded at landing (2026-08-05)

The lane run on its two cases (full run 918: 712/206; both PASS with
stage `membership`; go1.26.5 samples). The width signal, per the pass
criterion above (metadata, never a pass criterion):

- `slices/full-slice-cap-zero` (version-tracking mode, `samples=1`):
  |enumerated| = 8 — observations 14912..21912, i.e. caps 4..11 =
  `appendGrowthCap` + extra ∈ [0,8). Go exhibits exactly 1 member
  (14912, cap 4 = extra 0); 7 members unexhibited. Enumerator: 17 runs
  + 16 alias probes, 16 leaves at depth 1 (48 probes after the audit's
  F2c ladder). REVIEW VERDICT: not a flag —
  deterministic-inside-a-window BY DESIGN. The append envelope is the
  doctrine's declared pragmatic subset of the spec's "any sufficient
  capacity" latitude; a single Go version necessarily sits at one point
  of it, and the `samples=1` mode turns a toolchain whose policy leaves
  the window into a red (the deliberate-widening alarm).
- `maps/range-first-key` (sampling mode, `samples=5` default):
  |enumerated| = 3 — exactly {1,2,3}, every key of the 3-key map, so the
  envelope is the full permutation set's first-key projection (the map
  envelope statement: all permutations of the snapshot ⊇ any Go).
  Go exhibited 2 of 3 in the recorded run's samples (1 and 3;
  unexhibited {2}). Enumerator: 4369 runs + 12288 alias probes, 4096
  leaves at depth 3 (the size-1 tail site consumes a pick too), 0.3 s
  (36864 probes after the audit's F2c ladder, still ~0.4 s).
  REVIEW VERDICT: not a flag — per-run randomization re-explores, the
  unexhibited member is sampling noise, not an unreachable corner (other
  runs during development exhibited it).

No gratuitous width found: the only never-touched corners are the append
window's 7 upper slots, which the nondeterminism doctrine's envelope
statement already argues against the spec text and the version-tracking
mode polices.

Machine-side regression pin for version-tracking cases (audit F3,
decision recorded): before the lane, a machine-side `appendGrowthCap`
change moved cap-zero nondet→differential in the baseline; under the
lane, Go staying inside the (moved) window would keep the case PASS. The
restored pin is the `appendGrowthCap` value tests in
`Tests/GoCoreEval.lean` (one per formula regime, incl. the (0,1)=4
window base) — the Lean side, which is the direction the baseline used
to catch. The optional per-case exhibited-member pin (`pin=<member>`
params, compared at run time) was considered and DECLINED: within-window
toolchain drift is by design a PASS (the envelope is the claim, not the
point Go currently occupies), the exhibited member is already recorded
per run in the membership artifacts and the PASS detail, and a run-time
member pin would re-introduce exactly the single-point equality
brittleness the lane exists to remove. Revisit only if a real toolchain
bump inside the window needs to be surfaced as more than metadata.

Enumerator cross-evidence from landing, kept for the record: on
`maps/delete-during-range` (a BUG-005 strict differential red, NOT in
the lane) the enumerator collapses 4096 leaves to the SINGLETON {30} —
the machine's wrong answer — while Go observes 10: had that case been
laundered into the lane it would FAIL membership, and as a singleton it
would fail lane classification anyway. Both fail-closed directions were
also exercised live: width below a site bound trips the alias guard
(probe observation outside the set), depth/cap/work overruns fail loud,
and a deliberately misclassified order-independent case fails as a
singleton ("belongs in the strict lane").

## Out of scope (recorded)

Distributional claims (never); scheduling membership (the concurrency
arc — this lane is its oracle pattern, but interleaving enumeration
needs the partial-order machinery that arc will design); a general
per-case membership PREDICATE language (only if enumeration's `N` cap is
ever genuinely exceeded).

## Deferred: the enumerator OPTIMIZATION layer (2026-08-07)

Backlog record, NOT implementation (provenance: user discussion
2026-08-07; TODO.md carries the pointer entry). Standing admission
rule for every layer below — the BOTH-EXPLORERS cross-check: an
optimized explorer is adopted only while a reference (unoptimized)
explorer cross-checks it on every instance where full enumeration is
tractable, with identical observation sets required; a divergence
ejects the optimization. Each layer names its soundness obligation up
front so the proof direction stays reachable:

- **Verified POR (partial-order reduction).** Independence oracle: the
  race-detector footprints (`GoLean/GoCore/Race.lean`'s access
  records) — two steps commute when their footprints are disjoint.
  Eventual proof: the NPDRF mover lemmas (the S3 statement layer) as
  the soundness argument for the reduction; until proven, POR runs
  only behind the both-explorers adoption gate.
- **Symmetry reduction** via decidable `Config` equality: quotient
  explored states by goroutine/location id relabeling. Named soundness
  obligation: the ID-RELABELING LEMMA — a relabeled Config bisimulates
  the original, so observation sets are invariant under the
  relabeling. Cross-check: both-explorers.
- **Preemption-bound-as-metadata.** Bounded exploration is admissible
  only when the certificate NAMES its bound — a preemption-bounded
  certificate claims the bounded tree, never silently the full one
  (the claim-strength/vacuity audit dimension applied to
  certificates). Cross-check: unbounded reference runs on tractable
  shrinks of the same case.
- **State memoization on canonicalized MultiConfig.** Requires the
  decidable-equality/canonicalization layer above (memoization without
  a proven canonical form is a silent-pruning hazard). Cross-check:
  memoized vs unmemoized explorer set equality.
- **PCT / portfolio sampling beyond enumeration scale.** Sampling is a
  SAMPLE SOURCE (the lane's Go-side oracle half), never a
  certification — certificates stay enumeration-only. Cross-check:
  every sampled observation must be a member of any certified set it
  accompanies (the existing membership alarm, unchanged).

These stay deferred until the membership/confluent/racy lanes hit a
tractability wall the work caps cannot absorb (pipeline/{two-stage,
buffered-stage} and worker-pool/shared-feed — today's
beyond-tractable-caps strict-lane residents — are the natural first
customers).

## Slice-4 addendum (2026-08-07, channels arc): the stepwise pool engine

The enumerator was REBUILT for schedule enumeration (channels arc slice
4; `GoLean/CLI.lean`'s "stepwise pool explorer" section is the design
of record for the engine, this addendum the design-note record):

- **The whole-run frontier is replaced by a stepwise DFS** over the
  pool (init phase sequential, subject on the ThreadPool), sharing
  prefixes: work is counted in machine STEPS (+ probe runs) over the
  distinct-behavior tree, and the `work` param's unit changed
  accordingly (per-case params recalibrated in the same change).
- **Per-site bounds are MECHANICALLY COMPUTED** — this note's deferred
  "mechanical bound certification" candidate, now taken, WITHOUT the
  core-adjacent hook the deferral worried about: the CLI-layer
  consumption ACCOUNTANT (`stepNeeds`/`stepNeedsSeq`) mirrors only the
  consumption decision points and REUSES the machine's own analysis
  functions (`runnableIdxs`, `arrivalCases`, `applySelectCore`,
  `appendSpillWidth`) for every bound. GoCore is untouched. The
  uniform-width alternative is intractable at scheduler scale (a
  3-goroutine litmus case has ~15 sites of bound 2-3; width-3
  exploration at every bound-2 site is a ~300× blowup).
- **The author `width` is now a mechanically-checked CAP** (F2a made
  exact): a site whose computed bound exceeds it fails loud.
- **The alias ladder is retargeted at the accountant**: per site of
  computed bound `b`, three full ROOT-replays through the real
  semantics (`enumRunProgram` — empty-tail defaults included) at raw
  picks `b`, `2b+1`, `4b+3`; a probe observation outside the final set
  refutes the computed bound. HONEST SCOPE (S4 audit correction —
  this addendum first called the dropped per-leaf multiplicity "pure
  redundancy", which is FALSE): the probe stream is prefix-only, so
  every later site takes the empty-stream default and each rung
  exhibits only the ALL-DEFAULTS leaf of the bumped branch — an
  under-counted bound whose escaping residue's distinguishing
  behavior needs a later non-default pick aliases back into the set
  (demonstrated by the audit on schedLenHandoff, node [1,1]: branch
  subtree {110}, divergent 100 one non-default pick deeper). The old
  position × leaf-suffix multiplicity carried exactly that refutation
  power. The ladder is therefore the heuristic MAGNITUDE cross-check;
  the systematic checks on the accountant are the two-sided sentinel
  drift alarm (below) and the external driver-agreement/coupling
  pins. Probe streams still run end-to-end through the real machine,
  never through the accountant.
- **Pinning the copies** (the standing policy): the accountant and the
  loop mirrors are pinned by the driver-agreement eval tests (now
  including POOL classes: L1+pairing, L1+L4 waiter-extended select,
  lane-d refusal, the exit-no-sync mixed-leaf class) and by the
  harness's per-case coupling check, plus the in-engine TWO-SIDED
  sentinel drift alarm (S4 audit upgrade — the first form checked
  only unconsumed over-supply, leaving a MISSED consumption site
  silent since `Choices.consume` defaults to 0 on an exhausted
  stream): every step runs sentinel-suffixed and must return the
  sentinel exactly, so over-counted AND missed sites both fail loud.
  The accountant-exhaustiveness inventory (the six semantic-core
  consume sites → accountant arms) is recorded in `GoLean/CLI.lean`'s
  engine docstring as a standing lockstep obligation, Race.lean-
  inventory style.
- **New member statuses**: `race` (lane d's full-strength claim via
  `--expect-status race`: every enumerated path refuses); deadlock
  members still fail loud.
- **New lanes wired** (`scripts/coverage-manifest`,
  `scripts/diff-coverage`, fixtures in `scripts/test-lane-validation`):
  `confluent` (certify |set|=1 over all schedules, then the strict
  pipeline; stage `confluent`) and `racy` (mandatory for every
  race-expectation row; stage `racy`), plus the `members=` cardinality
  pin and plain+`-race` dual sampling for membership rows.
