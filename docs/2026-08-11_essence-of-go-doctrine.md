# The essence-of-Go doctrine — the two bounds (2026-08-11)

Status: DRAFT for user review — the project-charter articulation (Mike,
2026-08-11), written as binding doctrine. On acceptance: CLAUDE.md carries
the compact form; the nondeterminism doctrine is rewritten beneath this;
every future charter names the portable semantics as the goal.

## What we are building

**A trustworthy, portable Go semantics** — not a model of any particular
implementation, test suite, or scheduler. The machine we want is the
WEAKEST machine that Go can plausibly ever do: the semantics that
exercises *all* degrees of freedom latent in the language. Verifying
programs against the exact behavior we have already observed verifies
nothing worth having; any real implementation dramatically subsets the
permitted behavior — most dramatically in concurrency (cf. Cerberus:
years reconstructing what the C standards committee thought might be
allowed).

## The two bounds

- **Differential testing establishes the LOWER bound.** "We saw this
  datapoint." Its entire meaning is membership: real Go behavior ∈
  modeled Go behavior. The oracle can never validate the model's width —
  it can only witness members and expose too-narrowness.
- **Reasoning, the spec, the memory model, and documentation establish
  the UPPER bound.** "Go will never do this." Go is not chaos — it makes
  real guarantees (happens-before edges, DRF-SC, typed memory, the
  ordered subset of evaluation) — and the upper bound is *argued from
  evidence*, never asserted from silence alone.

**The bug definition:** if a conforming Go implementation does something
our machine cannot, that is definitionally a bug somewhere — far more
likely in GoLean than in Go. `observed ∉ modeled` is always
red, never latitude.

## Evidence classes for the upper bound

In rough order of authority: the language spec's text; the memory model
document; runtime/library documentation; cross-implementation observation
(gc across versions, gccgo, tinygo); proposal and issue-tracker
archaeology (committee-intent reconstruction, Cerberus-style); measured
gc behavior (a lower-bound instrument that can also *motivate* narrowing
arguments, never conclude them). All of these lanes eventually feed the
model. Simplifying assumptions are permitted — recorded in the register
below, never silently.

## Pins are scaffolding

Deterministic pins of spec latitude (matching gc's realization where the
spec permits many behaviors) were legitimate velocity scaffolding while
the machinery was being built. Under this doctrine each pin carries a
**re-envelope obligation**: it is a recorded debt, not a fidelity
achievement, and no record may present gc-conformance at a latitude
point as correctness. The latitude inventory (companion document)
enumerates every pin with its obligation and estimated cost.

## The simplifying-assumptions register

The honest list of every place the machine models less than the
plausible envelope. Seeded at drafting; the latitude inventory will
extend it; every entry names what is assumed, why, and what removing it
costs. We do not BS ourselves about the distance to the goal.

1. **Scheduling is gc-shaped.** The coarse scheduler's
   forced-continuation (run-to-boundary) and the fused effect boundary
   narrow scheduling latitude below what Go permits — including one
   oracle-visible divergence (the spinner program: gc exit-0 100/100,
   machine fuelOut — a definitional bug, first in the re-envelope
   queue).
2. **Sequential evaluation-order latitude is pinned** at several points
   (call-vs-operand order BUG-052, inter-target order, hidden-dep
   order) to gc's realization.
3. **One-implementation evidence base**: the differential oracle is gc
   at a pinned version; no cross-implementation lane exists yet.
4. **SC-only interleaving within DRF**: correct per the memory model's
   DRF-SC promise for the programs we accept (racy programs refused
   fail-closed — racy semantics is undefined by Go and unmodelable as a
   testable artifact today).
5. **Registry-granularity scheduling points**: sound only where
   scheduling is unobservable between them for race-free programs; the
   fused-boundary discovery shows the current point set is incomplete
   (termination-ordering races are schedule-observable without data
   races).

## Why (the mission)

Traditional verifiers were built over PhD-years: high trust, low reach.
This project exists to learn whether semantics and verification tools
can be built in months — with AI labor, adversarial review, differential
grounding, and kernel-checked reasoning — at a trust level fit for
deployment anywhere, because the threat environment (much of it
AI-created) will not wait a decade. Cerberus took ten years. The
scientific question here is whether the essence of a language can be
captured trustworthily at speed. Every doctrine choice above serves that
question: the lower bound keeps us honest cheaply; the upper bound is
the product.
