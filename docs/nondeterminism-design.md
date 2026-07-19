# Nondeterminism as an Explicit Choice Oracle

Design direction (2026-07-18, user steer). Status: **agreed direction, not yet
implemented.** Supersedes the earlier "deterministic executable policy + the
relation allows any behavior" note for map iteration order.

## Non-negotiable principle: never commit to determinism Go doesn't have

The reference (relational) semantics must faithfully permit **every**
nondeterministic behavior Go permits. It never bakes in a determinism Go does
not have. The executable interpreter is allowed to pick a *particular* behavior
— but only by *instantiating the choice oracle*, and that instantiation is a
testing convenience, never a semantic claim. The invariance check (run several
oracles) is precisely how we avoid mistaking "the interpreter's canonical run"
for "the program is deterministic."

This principle indicts things GoCore already does. Both are current
determinism-commitments Go does not make, and both should migrate to
oracle-driven choices:

- **append capacity growth** — currently a fixed deterministic executable
  policy (`appendGrowthCap`). Go does not specify post-reallocation capacity;
  the relation must allow any valid capacity `>= newLen`, with the interpreter
  choosing one via the oracle.
- **fresh allocation addresses / pointer identity** — currently the next
  sequential address. Go does not specify addresses; only distinctness and
  aliasing are observable. Address choice should be oracle-driven (and
  observations must not leak concrete addresses).

Map iteration order is simply the next instance of the same problem, and the
first one we are forced to model.

## Core idea

Nondeterminism in GoCore is modeled as an explicit **choice sequence** that the
semantics consumes — "generation is a parser of randomness." Both the
executable interpreter and the relational semantics are parameterized by a
stream of choices; every nondeterministic point consumes the next choice.

This is the QuickCheck/Hypothesis model (Hypothesis calls its input the "choice
sequence"; a generator is a function from a bit-stream to a value) and the
Interaction-Trees model (nondeterminism is an explicit event resolved by an
oracle).

Nondeterministic points that consume choices, now and later:

- map iteration order (`for k := range m`);
- append capacity growth after reallocation;
- fresh allocation addresses;
- eventually: goroutine scheduling (the scheduler is the oracle, consuming a
  choice per step) — the concurrency endgame for raft.

## Why this resolves both problems

1. **Differential testing.** The interpreter becomes *deterministic given the
   oracle*. The harness can:
   - run under a canonical oracle; for programs whose observation is invariant
     across oracles (all of quorum — it only counts/sorts), this matches Go;
   - run under several sampled oracles and check invariance: if Lean's
     observation varies with the oracle, the program is genuinely
     nondeterministic → flag/quarantine instead of a silent Go mismatch;
   - optionally, oracle-search for order-sensitive programs: does Go's output
     match Lean under *some* oracle?
   Nondeterminism becomes detectable and controllable, not a surprise.

2. **Reference semantics.** The relation is indexed by the choice stream
   (equivalently, the union over all streams). Properties are proved for all
   streams; the executable behavior is "instantiate the stream," not a baked-in
   determinism lie. Same mechanism generalizes append-growth, allocation, and
   scheduling.

## Sketch of the mechanism

- A `Choices` input: a consumable sequence of bounded nondeterministic
  decisions (a "parser of randomness" input). Concretely, e.g. a `List Nat`
  consumed left-to-right, each choice bounded by the number of alternatives at
  that point; exhaustion yields a canonical default (e.g. 0 → insertion order).
- Thread it through the interpreter (an added `ExecState` field with a cursor,
  or a Reader/State layer over the exec monad) with a `consume : Nat → m Nat`
  that reads the next choice bounded by the alternative count.
- Map range: pick the iteration order by consuming choices (e.g. select the
  next entry among the remaining); the default oracle gives a canonical
  deterministic order.
- Relational semantics: the step relation is indexed by (or quantifies over)
  the choice stream. Reasoning quantifies over streams.

## Differential-lane policy (refines the coverage ledger)

- A case is **deterministic-lane-eligible** iff its observation is invariant
  across choice streams. The harness can *check* this by running several
  oracles. This replaces the current informal "order-insensitive by
  construction" judgement with a testable criterion.
- `deferred-nondet` cases become "observation varies across oracles" — the
  harness can classify them automatically rather than by hand.

## Open questions

- Representation of `Choices` (list vs lazy stream vs splittable seed) and how
  bounds are supplied at each consume point.
- Whether to thread through `ExecState` or a monad layer (affects the
  interpreter's shape and the relation's index).
- How the relational skeleton (`Rel.lean`) takes the stream as an index and
  what the interpreter/relation correspondence statement becomes.
- Scope of first implementation: map-range only, or also retrofit
  append-growth/allocation immediately (they are currently deterministic
  policies that this generalizes).

## Range / iteration representation (decided 2026-07-18)

Validated against new Goose/Perennial (`deps/perennial/new/golang/defn/`),
which is our proof-layer reference — "build for the future" means matching it:

- `slice.for_range` is an **index-based for-loop** over `0..len` using
  `IndexRef` — desugared onto the generic loop combinator, *not* a primitive.
- `map.for_range` is a **dedicated semantic primitive** `InternalMapForRange`
  with its own step rule (wrapped in StartRead/FinishRead for iteration
  invalidation), because maps have no index and iteration order is
  nondeterministic.

So GoCore mirrors this:

- **Slice / array / string / int range → desugar** (in `NativeToIR`) to a
  GoCore index for-loop using existing `while` + `length` + `indexGet`. No new
  GoCore construct.
- **Map range → a dedicated GoCore `mapRange` primitive.** This is the one
  genuine iteration primitive and the first per-step oracle consumer: at each
  step it consumes a choice bounded by the number of remaining keys to pick the
  next entry. The abstract map value stays an unordered finite map; order lives
  entirely in the per-step choices.
- Range-over-func (Go 1.23) and channel range are later primitives that slot in
  beside `mapRange`; they are not needed for raft's core.

This is less machinery than a universal cursor and more faithful (it is what
the reference framework does). It also keeps the reasoning story clean: index
ranges get the standard loop-invariant rule; `mapRange` gets one step rule that
threads the oracle.

## Recommended path

Build the choice-oracle abstraction now, before adding `range`/maps, so map
iteration is its first principled consumer rather than a retrofit. Keep the
first implementation minimal (map-range consumes; append/alloc can be migrated
next), and document the executable default oracle as a policy the relation
generalizes.
