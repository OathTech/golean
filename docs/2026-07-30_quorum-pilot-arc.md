# Arc: the quorum pilot (2026-07-30) — the sprint arc

Decided with the user 2026-07-30, immediately after the proof-corpus
catch-up arc merged (`main` @ e844c9c; corpus 787/471, untriaged 31,
Audit sweep 5006). This arc FUSES arcs 3 and 4 of the recorded sequence
(`docs/2026-07-25_arc-sequence.md`) — the interfaces campaign and the
quorum pilot — into one long arc with an external milestone, on the
user's direction: the machinery (two-program golden pins, proof-corpus
discipline, parallel runner, audited gates) is in place to sprint.

## THE GOAL

**A kernel-checked theorem about etcd-io/raft's real `CommittedIndex`**,
proven over the pinned actual lowering of the real `quorum` package
source, with the differential green on that package against etcd's own
test values — the first "Verdi results, but on real code" artifact
(F5 tier 1, `TODO.md`).

## Why this goal (recorded so the alternative is visible)

- It forces BOTH project-priority tracks at once: coverage (interfaces —
  the 48-case unlock and the raft blocker, since `AckedIndexer` is an
  interface; multi-package lowering; the stdlib-extern policy) and proof
  depth (`AckedIndex` returns `(Index, bool)`, so the sprint FORCES the
  `GoFuncSpec` arity widening — W1/prediction-3 debt stops being
  deferrable).
- The rejected alternatives: a pure interfaces campaign (no external
  success criterion), R4 concurrency (sequenced after the sequential
  story is proven on real code; BUG-002's fix wants that foundation),
  a pure proof-depth sprint (machinery with nothing real to aim at).

## Phases

0. **Statement first (the widening-loop discipline — this phase gates
   the rest).** Write the target theorem STATEMENTS as `def ... : Prop`
   targets, not results: (a) the `CommittedIndex` property (the returned
   index is committed by a majority quorum of the config against the
   acked indexes — exact form pinned against the real code, not from
   memory); (b) the interface-dispatch `GoFuncSpec` statement; (c) the
   `(T, bool)` / multi-result `GoFuncSpec` arity form. Plus the negative
   twins. This pre-declares the proof-corpus entries so the campaign
   cannot accumulate silent calculus debt. DEPENDS on `deps/raft` being
   cloned (the user is doing this in a separate thread) — statements are
   pinned against the real source, never reconstructed.
1. **Interfaces, guardrails first.** Fix defined-vs-alias identity
   (BUG-004's root — `type T int` currently lowers as an alias, erasing
   identity); retire raw-mangled-name dispatch for `TypeId`/method-set
   identity (the recorded green-on-junk risk — expect intentional
   transient reds, recorded per practice); type asserts + type switches
   frontend-side; differentially validate the dormant Gobra-era machine
   half (`toInterface`/`typeAssert`/dynamic dispatch). Seed corpus: the
   48+ interface-blocked cases + edge enumeration per the three-layer
   strategy. Design comparison against `deps/perennial`
   `new/golang/defn/interface.v` recorded in this doc's build log.
   **Interim mini-audit at phase-1 exit** (semantics dimension at
   minimum): interfaces touch the trust surface hardest, and a
   dispatch-identity defect discovered at phase 4 would be expensive.
2. **The real-code frontend.** Multi-package lowering; the stdlib-extern
   decision note (what `quorum` actually imports — check early whether
   `majority.go` still hand-rolls its insertion sort, which would spare
   a `sort` extern; decide how far externs reach before generics
   monomorphization is ever needed); order-insensitive map-fold
   observations for map-range nondeterminism (the D2 decision bites
   here — record it).
3. **Quorum through the differential** against etcd's own test values
   (`quorum` package tests as the oracle corpus). Every gap found
   becomes a corpus case FIRST (guardrails before tool buildout, as
   always).
4. **The proof.** Pin the actual lowering of the relevant `quorum`
   source (golden-pin mechanism, program #3+); walk `CommittedIndex`;
   discharge the phase-0 statements. Spec-surface widenings land here
   with witnesses in the same commit.

## Out of scope

- Goroutines / channels / R4-R5 (BUG-002 remains the recorded blocker).
- Floats/complex (IEEE doctrine — own arc).
- Generics beyond what the phase-2 extern-policy note explicitly
  decides.
- Multi-node / network modeling (F5 tier-1 scoping only).

## Exit criteria

- Phase-0 statements proven over the pinned actual lowering; negative
  twins hold; all referenced from `proofs/Audit.lean`.
- `quorum`-package differential green against etcd test values; every
  interface machine rule exercised by at least one corpus case (no
  read-only-validated rules — the panicFrameDeferNil lesson).
- Every new law witnessed same-commit; sweep clean; untriaged ratchet
  not up; gate green.
- Full pre-merge audit (the unconditional ask) + merge sign-off.

## Process notes for this arc

- Long arc, one branch (`quorum-pilot`); interim slice gates stay green
  throughout; the phase-1 interim mini-audit is IN ADDITION to the
  final pre-merge audit, not a substitute.
- `deps/` restructure landed with this doc: reference checkouts move
  from sibling `../deps/` to gitignored in-repo `deps/` (CLAUDE.md
  updated) so the sandbox workdir grant covers them.

## Build log

- 2026-07-30: arc opened; branch `quorum-pilot`; this plan of record +
  the `deps/` restructure. Phase 0 blocked on the `deps/raft` clone
  (user, separate thread).
