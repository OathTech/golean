# The essence-of-Go doctrine — the two bounds (2026-08-11)

Status: ACCEPTED (user, 2026-08-12) with the de-facto-spec evidence class added at acceptance — the project-charter articulation (Mike,
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
document; runtime/library documentation; **the deployed-program corpus as
de-facto spec** — "does this program behave as people expect" is a
powerful argument, because an implementation cannot plausibly break
behaviors that a large body of running code depends on (this is much of
why C is such a mess: decades of old code pinning committee-unintended
behavior; Go is the best-behaved case — the Go 1 compatibility promise
institutionalizes the constraint, and the team's deliberate map-iteration
randomization shows them actively *preventing* de-facto pins they don't
want honored); cross-implementation observation (gc across versions,
gccgo, tinygo); proposal and issue-tracker archaeology (committee-intent
reconstruction, Cerberus-style); measured gc behavior (a lower-bound
instrument that can also *motivate* narrowing arguments, never conclude
them). All of these lanes eventually feed the model. Simplifying
assumptions are permitted — recorded in the register below, never
silently.

## The language-version pin (2026-08-17, spec-truth campaign)

"Go" is versioned semantics: the go.mod `go` directive selects language
behavior (the 1.22 loop-variable change is the canonical example).
**GoCore models the Go 1.26 language.** The concrete pins — spec text at
`go1.26.5`, oracle toolchain, and their agreement rule — live in
`docs/spec-sources.md`; re-pins are deliberate, both sides together,
with the reason recorded. Upper-bound arguments cite the pinned spec,
never the live web page.

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
   oracle-visible divergence, the SEND-THEN-SPIN wedge: a worker
   performs one registry op (a cap-1 send that wakes main) and then
   spins with no further registry op, and the machine pins the
   scheduler on the worker forever — exit-0 unreachable on EVERY
   stream (511/511 fuel-out in an exhaustive mod-2 depth-8 sweep)
   where gc exits 0, 60/60. `observed ∉ modeled` — a definitional
   bug, first in the re-envelope queue; recorded probe:
   `docs/evidence/2026-08-12_scheduler-wedge-probes/`. (Exhibit
   corrected at the 2026-08-12 audit: a REGISTRY-FREE spinner — no
   registry op anywhere — is NOT this bug: gc's exit-0 there is in
   the modeled set via the default stream; its extra never-yielding
   streams are the too-wide, transfer-safe direction, and ∀-stream
   termination on that shape is the fairness quantifier's territory,
   not this re-envelope's.)
2. **Sequential evaluation-order latitude is pinned**, each axis to a
   recorded conforming point — gc's where pinnable (call-vs-operand
   order, BUG-052), OURS where gc's realization is compiler-internal
   (inter-target order, early-store-across-phase), and hidden-dep init
   order to go/types' point — with the known ≠ gc cases (E3, E5, E7)
   carried as standing deviation records queued for re-envelope
   (inventory §7 items 3 and 5). This wording adopts and supersedes
   §8's prescribed sentence: its "permanent deviation records" phrase
   is dropped, because under the bug definition a probed gc-elsewhere
   observation is an observed-∉-modeled candidate — a debt with a
   queue position, never a divergence we are at peace with (that
   stronger reading is this register's own gloss, not §8's).
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
6. **Sequential allocation addressing — DISCHARGED BY QUOTIENT
   (2026-08-13), the register's first theorem-closed entry.** The
   deterministic `nextAddr` allocator models less than Go promises
   (which is: nothing — addresses vary run to run, stacks move
   intra-run), but the executable frame theorem's generalized renaming
   proves every conforming address choice observationally equal
   (`Frame.allocatorIndependence`; inventory C11's (q)
   ENVELOPE-BY-QUOTIENT upgrade; frame-theorem note §5b). The
   assumption stays listed because its discharge is CONDITIONAL on the
   modeled observation surface (pointer equality only): an
   address-exposing channel (`%p`, pointer order, `unsafe`) re-opens
   it. Cost of removal already paid — by proof, not by widening the
   machine.
7. **Unbounded memory / allocation never fails** (added 2026-08-14 from
   the verified-examples pre-merge audit, finding R1-F1). The machine's
   heap is unbounded and every allocation succeeds: `make`, composite
   literals and frame allocation have no failure mode, and runs start
   from an empty heap. Real Go is memory-bounded — an allocation can
   fail (OOM, or the runtime's own limits) at any size, and long before
   a length reaches `2^63`. Consequence, and the reason this is
   recorded rather than shrugged off: a theorem's domain condition
   states the MODEL's domain, which is wider than the practical Go
   domain, so `n < 2^63` in the gallery means "where Go's `int` domain
   ends in the model", never "where the program stops working"
   (`docs/verified-examples.md` says this at each entry). Disposition:
   STANDING IDEALIZATION, not a gc-pin — it carries no re-envelope
   obligation, because the too-wide direction here does not threaten
   theorem transfer to real runs that DO allocate successfully. Cost of
   removal (only if resource-bounded claims are ever wanted): an
   allocation-failure outcome in the machine plus a memory budget in
   every statement — deliberately not paid.

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
