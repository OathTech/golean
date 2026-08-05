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

## The machine-side enumerator

New CLI subcommand (`lean coverage-observations --input <wire> --max-width B
--max-sites D --cap N`): enumerate the DISTINCT observations over the
choice tree by exploring stream prefixes over alphabet `[0, B)` to
consumption depth `D`, deduplicating observations.

Key design point — NO semantics changes: `Choices.consume` takes picks
modulo the site's bound, so exploring values `0..B-1` at each position
covers every behavior PROVIDED `B ≥` every site's bound in the case.
`B` is per-case metadata (default 16 — covers append's 8 and small
maps); the enumerator FAILS CLOSED if it cannot certify coverage
(a case whose map could exceed `B` keys must raise `B` explicitly, and
the enumerator cross-checks by probing one value ≥ B for changed
observation — a cheap alias-detection guard). `N` caps the observation
set (fail loud if exceeded — such a case is too wide for enumeration and
needs a per-case predicate instead; none expected in the current
corpus). Exploration reuses `execStmt` verbatim — the enumerator is CLI
layer, the semantic core is untouched.

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
  + 16 alias probes, 16 leaves at depth 1. REVIEW VERDICT: not a flag —
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
  leaves at depth 3 (the size-1 tail site consumes a pick too), 0.3 s.
  REVIEW VERDICT: not a flag — per-run randomization re-explores, the
  unexhibited member is sampling noise, not an unreachable corner (other
  runs during development exhibited it).

No gratuitous width found: the only never-touched corners are the append
window's 7 upper slots, which the nondeterminism doctrine's envelope
statement already argues against the spec text and the version-tracking
mode polices.

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
