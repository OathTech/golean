# Nondeterminism doctrine — modeling, testing, and its limits (2026-08-04)

Recorded from the 2026-08-04 design discussion (user + agent), folding the
strategy and its honest epistemic limits into the record. This is
doctrine: binding on every future choice-consumption site and on the
concurrency arc's design.

## The model

All Go implementation latitude we model routes through ONE mechanism: the
`Choices` stream in `sem()`'s signature. The interpreter is total and
deterministic GIVEN a stream (executability — the differential trust root
— is the project's foundational requirement and the reason a set-valued
semantics was never an option). Consumption sites are named and few (map
iteration pick; append spill capacity), enforced structurally
(`applyStmtOpCore` is choices-free; step SUCCESS is provably
choice-independent — the sem-adequacy arc's stream-obliviousness kit).
Headline theorems ∀-quantify the stream: true under EVERY resolution of
the latitude — deliberately stronger than any single Go implementation.

## Testing today: the strict lane + invariance guard

Corpus cases run under the default stream and must EQUAL `go run`'s
observation; then re-run under fixed adversarial streams — variance fails
the case (stage `nondet`). The strict lane therefore admits only
choice-INVARIANT observables, and the corpus is written to observe
order-independent quantities; that convention also neutralizes Go's own
per-run randomization. Genuinely choice-dependent observables
(`slices/full-slice-cap-zero`'s `cap()`) sit honestly red until the
membership lane exists (general-coverage arc, slice 3).

## The epistemic limits, stated plainly

Differential testing is VERIFICATION for deterministic behavior and
degrades to SANITY-CHECKING at the nondeterministic frontier. The failure
directions are asymmetric:

- **Too NARROW** (real Go exhibits a behavior outside our envelope) is
  the SOUNDNESS-relevant direction: ∀-stream theorems transfer to real Go
  only if Go's behaviors ⊆ modeled behaviors. It is DETECTABLE — the
  membership lane's job (Go's observation ∈ our admitted set), plus
  equality-lane mismatches. Sampling density varies by feature: map order
  re-randomizes per run (every go-run explores — dense, and fuzz-generated
  order-SENSITIVE contexts make it a real exploration); append growth is
  deterministic per Go version (one point per toolchain — membership is
  version-tracked); SCHEDULING sampling is nearly useless (the runtime
  explores a tiny biased corner — see the concurrency inputs below).
- **Too WIDE** (we admit behaviors no conforming Go could exhibit) is
  UNDETECTABLE by any oracle — go run cannot demonstrate a behavior it
  never has — but it is the benign direction: ∀-stream theorems become
  harder to prove, never wrong. The check is REVIEW, not testing (below).

## Binding requirements

1. **Envelope statements.** Every choice-consumption site ships with a
   spec-anchored envelope statement in its design note or docstring: what
   the Go spec text says, exactly which set our stream resolves, and the
   argument that the set contains every behavior conforming Go can
   exhibit (the soundness direction). Current sites' statements: map
   iteration — spec says unspecified order, envelope = all permutations
   of the snapshot, which is ⊇ any Go ONLY for programs that do not
   mutate the map during iteration: the spec MANDATES that an entry
   removed before being reached "will not be produced", and the snapshot
   model still produces it (and stale values) — the known, triple-pinned
   divergence BUG-005, deliberately deferred to its live-iteration fix;
   until then the map envelope statement is scoped to mutation-free
   iteration (arc-final audit F14, 2026-08-06); append spill — spec
   allows any sufficient capacity, envelope = growth formula + [0,8)
   extra (a PRAGMATIC SUBSET of the spec's latitude: sound for transfer
   as long as real Go's policy lands inside, which the membership lane
   version-tracks; widen deliberately if a toolchain leaves the window).
   CAUTION (arc-final audit F2, 2026-08-06): the append statement is
   FALSE on go1.26.5 — the oracle toolchain realizes capacities outside
   the window in both directions (BUG-021, three membership pins red) —
   and a samples=1 membership case version-tracks its one (elem,
   oldCap, newLen) triple, not the site's envelope. The deliberate
   widening is in flight in the same audit response; this caution is
   replaced by the widened statement in that commit.
2. **Envelope fidelity is a standing audit dimension** (like
   over-specialization): reviewers argue each envelope against the spec
   TEXT, because the too-wide direction has no oracle.
3. **Possibilistic scope, declared.** Our claims quantify all
   resolutions; we never make probabilistic claims. Spec language like
   `select`'s "uniform pseudo-random" enters the model only as "any";
   statements must never imply distributional facts.

## Inputs to the concurrency arc's design note (binding starting points)

- **DRF-SC discipline**: data races FAIL CLOSED (an error, not an
  interleaving) — Go's memory model gives racy programs essentially
  undefined behavior, and modeling races as well-defined nondeterministic
  interleavings would be wrong in KIND. Sequentially-consistent
  interleaving is claimed only for race-free programs (the DRF-SC
  theorem's territory; Goose/Perennial take the same line).
- **`go run -race` as a second oracle**: programs the race detector flags
  must fail closed in our model — a testable boundary exactly where
  interleaving sampling cannot help.
- **Litmus corpus**: memory-model litmus shapes (message passing, store
  buffering, …) as corpus cases probing the envelope's edges.
- **Fairness quantifier decision**: ∀-stream termination is FALSE for
  correct programs that spin-wait on another goroutine (unfair schedules
  starve the writer). Concurrency termination claims need an explicit
  fairness-constrained quantifier, decided in the design note — not
  discovered as an unprovable theorem.
