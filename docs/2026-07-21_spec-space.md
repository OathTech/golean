# The specification space: decisions, candidates, and what binds when

**Date: 2026-07-21 (arc `spec-surface`).** A map of the decision space around
specifications, recorded from design discussion (user + assistant) so future
arcs inherit the reasoning, not just the conclusions. Companion to
`docs/2026-07-21_native-spec-surface.md` (which governs the *current* claim
surface); this note governs how the spec architecture may grow.

**Status: DIRECTION, NOT DECISION.** Nothing in §4 binds today. The recorded
plan is to build the pieces that are needed under *every* candidate (§6),
learn from use, and possibly run multiple spec idioms side by side. The
library-spec decision binds at the moment we write the first real library
spec, not before.

## 1. The razor

A specification must earn its keep as at least one of:

- **a composition interface** — real client *proofs* can consume it
  modularly; or
- **a semantically simple explanation** — a human can review it and know
  what was promised.

Ideally both. Specs that are neither — powerful-looking internal artifacts
that no client proof consumes and no human can read — are banned. (Iris
triples raw are arguably the former and never the latter; that is why they
are internal, below.)

Three distinct jobs hide under the word "spec", with different consumers:
**(a) review** (what a human trusts by reading), **(b) composition** (what a
client proof builds on), **(c) claim** (what a milestone asserts). The
recurring architectural error is forcing one language to do all three.

## 2. The ladder of spec forms

Each rung is the ∀-closure of the rung below; validation is uniform
(execute/sample first, prove second):

1. **Concrete testcase** — specific input, specific heap, run, check.
   (The differential corpus. Exists.)
2. **Quantified testcase** — "give X any value, in any heap where y is
   allocated; then you return z and y contains f(X)". This is precisely a
   **frame-closed sequential-SL triple with a return value**, and it is the
   prototypical *human-comprehensible* spec — because it is the ∀-closure
   of an object (a test) whose meaning engineers already trust. Note the
   phrase "any heap where y is allocated" IS the frame quantifier: without
   frame closure a triple describes hermetic laboratory heaps, not call
   sites.
3. **Reference implementation** — when the contract is too rich to
   enumerate as quantified testcases (raft), the spec is *simpler Go code*,
   connected to the real implementation by refinement (§4). The reference's
   own guarantees are stated as rung-2 objects about it.
4. **Protocol properties** — plain theorems over the reference/world
   system (election safety, log matching …), transferred to the real
   implementation along the refinement.

**A quantified testcase is exactly a property-based test.** Sampling its
quantifiers yields corpus cases; so any spec can be differentially
*executed* against the implementation before its proof is attempted. Specs
enter the repo as running property tests first, theorems second —
guardrails-first, lifted to the spec layer with zero new concepts. A
failing sample is a found bug (a distinguishing context), which is a spec's
third job.

## 3. Candidates considered for the library-spec language

- **Iris triples as the contract of record — REJECTED as first-class.**
  Semantically powerful, compositionally right, humanly unreadable ("more
  like internal lemmas"). Verdict: Iris stays strictly internal. Where
  library-facing Iris lemmas exist, they are *derived conveniences*, never
  the contract of record, and any exported abstract predicate must carry a
  surface-level readout theorem cashing it out (the non-vacuity gate
  generalized to abstractions: an abstract predicate without a readout
  theorem is a scaffold and may not claim a meaning).

- **"Go with knobs on" (extern-primitive-extended semantics as the
  abstract machine) — REJECTED as a spec concept.** A hybrid
  language-with-magic-ops is a concept only this project would understand:
  not portable to a Go programmer, not runnable Go, meaningful only via our
  private extension mechanism. Fails the explanation criterion. **Retained
  in exactly one place:** primitive semantics is unavoidable where Go
  itself ends — `time`, the network, the scheduler have no reference Go
  implementation. Principled line: *primitive ops only at the true
  language boundary; reference code wherever Go can express the contract.*

- **Reference implementation + contextual refinement — CANDIDATE OF
  RECORD.** Spec = naive Go code (Figure-2-shaped for raft); judgment =
  `real ⊑ ref`: every observable behavior of any Go client using the real
  library is possible with the reference. REFINEMENT, not equivalence —
  the reference is deliberately looser/more nondeterministic. Merits: the
  statement quantifies only over Go programs and observable behavior;
  matches Go documentation culture ("equivalent to" reference snippets);
  "equivalence under testing" is its finite approximation, so the existing
  differential machinery is its testing semantics. Known costs, recorded
  honestly: (i) protocol-imposing libraries ("don't call Close twice")
  break unconditional context quantification — conditional refinement
  (CCR-style: SL conditions + refinement) is the known-hard extension;
  (ii) *proving* contextual refinement needs binary logical-relations
  machinery (ReLoC genre) that does not exist in this repo — a major
  internal build to be priced when the first library spec is written.

## 4. The layered architecture (as currently imagined)

- **Review objects**: plain Lean transition systems (the `Rel.lean` genre —
  the trust chain already bottoms out in a human reviewing exactly this
  kind of object), reference Go implementations, and native-surface
  theorems. The vocabulary criterion (native-spec-surface D1) governs ALL
  review objects: no `IProp`, no step-indexing, no masks — in models just
  as in claims.
- **Composition objects**: internal Iris (triples, ghost state, logical
  relations). Derived, never trusted-by-reading.
- **Claim objects**: the native surface (triples over interpreter runs;
  plain predicates over designated observables).
- **Refinement statements** are first-order over traces of two systems in
  the same judgment vocabulary; Iris appears only in their proofs (ghost
  state tracks the abstract side *during* the proof — Perennial-style).
- **Trust guards at the model level**: models/references are executable
  and differentially validated before refinement proofs are attempted;
  observation functions get refutation twins (exhibit that the projection
  distinguishes known-divergent behaviors) so "observes too little" is
  caught the way vacuous laws are caught by witnesses.

## 5. The compass caveat (recorded verbatim in spirit)

Closed sequential-separation-logic triples — quantified testcases — are the
current orienting target: an understandable spec surface for testcase-scale
programs, right for calibrating the machinery. **They are a compass, not a
north star.** They are known-insufficient for: concurrency (logically
atomic specs / interleaved clients), protocol-scale contracts (reference
implementations), liveness (outside step-indexed Iris entirely), and
protocol-imposing usage conditions. Do not over-index: no doctrine may
assume "all specs are triples", and surface/exit machinery should be built
generic over what it reads out where that is cheap.

## 6. What must be built under EVERY candidate (therefore build now)

- **Frame closure** for the surface triple (`P ∗ F`, F unchanged) — the
  composition currency whether specs are triples or refinement conditions,
  and the difference between a quantified testcase and a laboratory.
- **Progress packaging** — triple + never-stuck as one surface judgment
  (partial-correctness triples alone are vacuously satisfiable by broken
  programs).
- **Function-level spec form with return values** (`∀ args, {P} f(args)
  {ret z, Q}`) — the presentation form of rung 2; currently returns are
  threaded through observable cells by driver convention, which is honest
  but backwards as a reading surface. Go-idiom notes that shape this form:
  (i) Go's return semantics IS named-result-variables (the frontend's
  `$res0` lowering reflects it; GoCore `Func.results` models it) — so the
  spec's `ret` binder is semantically a read of the result locals at
  `return`, already faithfully lowered; (ii) returns are VALUE-copies —
  plain values get pure equations (`ret v. v = z`), pointer returns get an
  address whose content is heap-side (`ret p. p ↦ …`), which SL handles
  natively; (iii) multi-value returns are first-class (arrays of results,
  already modeled by multi-assignee calls); (iv) the dominant Go contract
  idiom is `(T, error)` — which requires interfaces (nil-interface
  comparison), i.e. a semantic-fragment widening; v1 function specs cover
  plain-value returns and the error idiom is the recorded target the form
  must grow into; (v) the spec form should observe returns exactly where
  the differential oracle observes them (`runNamedFunction`'s result
  values), never through a bespoke observation.
- **Invariant readout** — extraction at every reachable state, not just
  terminal ones (`adequate_alt` already quantifies over reachable
  configurations; the current proof discards the non-value branch). Raft
  safety properties are invariants of non-terminating systems; this is the
  safety-property exit door.
- **User-level ghost state / abstract-predicate machinery** — needed the
  moment any library (or refinement proof) is specced, under every
  candidate.
- **F4 concurrency model** — goroutines/channels are the identity of the
  language; gates everything raft-shaped and most of "lots of other Go".
- **Extern primitives at the true language boundary** — needed regardless
  (stdlib externs are already on the roadmap); axiomatized layer-2
  objects validated differentially where possible.

## 7. Deferred decisions, and when they bind

| Decision | Binds when |
| --- | --- |
| Library-spec language (contextual refinement vs alternatives) | first real library spec |
| Conditional refinement machinery | first protocol-imposing library |
| `HProp` opaque-atom constructor vs per-library readout relations | first abstract-predicate export |
| World/network semantics shape | first multi-node target (F4+) |
| Liveness machinery (tier 2) | explicitly deferred (F5 stretch) |
| Surface-level composition rule for exported statements | first multi-library client |

**On the last row (added 2026-07-22):** our surface statements are adequacy
*readouts* of Layer-I reasoning, not composition interfaces — two exported
`GoInvariant`/`GoSpec` theorems do not link; their quantifiers are already
discharged. Until the library-spec decision binds, composition happens at
Layer I (namespaced invariants, abstract predicates), and the composable
artifact is the WP lemma, not the exported theorem (the golden walk's
one-walk-four-shapes reuse is the existing instance of this). See
`docs/2026-07-22_invariant-readout-design.md` §5.
