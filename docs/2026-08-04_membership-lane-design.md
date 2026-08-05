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
current corpus). Every enumerated member must carry the case's expected
status (audit F1): a member whose status differs — e.g. a panic under a
stream Go can never realize — is by construction a machine bug, not an
envelope point, and fails the enumeration loudly.

What the enumerator REUSES vs COPIES (audit F7 correction — this note
originally claimed "reuses `execStmt` verbatim", which was wrong):
reused is `stepFn`, the semantic core's step function, so every machine
step is the machine's own; COPIED (hand-mirrored, not shared — a shared
helper would touch GoCore, which stays bit-identical) are the driver
layers: `enumSetup` mirrors `runFunctionWithContextM`'s entry wiring and
`enumRun` mirrors `runConfig`'s terminal handling. The copies are pinned
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
