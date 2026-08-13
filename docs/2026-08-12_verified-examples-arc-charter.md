# The verified-examples arc — charter (2026-08-12)

Status: DRAFT for user blessing. Lane `foundation` (renamed in spirit:
this lane now carries the examples arc; the width arc gets its own).
Governing doctrine: the two bounds (docs/2026-08-11_essence-of-go-doctrine.md).

## End state (the user's words, 2026-08-12)

(1) a set of Go programs, and (2) a set of GoLean theorems such that a
user can SEE that the top-level specification establishes the property
they want — e.g. NO ERRORS, and RETURNS THE CORRECT VALUE.

The corpus is the OBJECT OF AGREEMENT: it explains, to a reader who is
not a Lean expert, what GoLean reasoning actually establishes.

## What this arc is and is not (the two-questions separation)

This arc answers USABILITY: can the reasoning layer carry natural,
human-readable specs through real programs? On the current (over-tight)
machine, every example is EXPECTED to prove — all-green here is claimed
as usability evidence only, never as machine-hardening evidence. The
WIDTH question (is the machine permissive enough for what Go might do
that gc doesn't) belongs to the sequential-width arc, whose exit
includes RE-PROVING this corpus over the widened machine.

## The headline statement form (PROPOSAL — slice-1 checkpoint decides)

One top-level theorem per example, readable as total correctness:

    for all inputs (in the stated domain): execution completes
    normally — no panic, no error, no fuel-out at sufficient fuel —
    and the result equals the specified function of the input.

Mechanically: the single-carrier completes-AND-verdict shape (the
TotalReadout composition precedent from spec-parity S6), ∀-input
quantified, deletion-test clean, machine-integer honest (fib's claim is
fib mod 2^64 or a bounded domain — the overflow boundary is part of
what the example teaches). The house D1 twins and completion pins
remain as supporting theorems beneath; the HEADLINE is the one
statement a user reads. THIS FORM IS A PROPOSAL: slice 1 builds one
exemplar end-to-end and brings the concrete statement to the user for
agreement before anything scales — the arc explicitly expects
discussion here.

## Slices

1. **The exemplar + the form** (fib, iterative): spec-form design note
   (options where latitude exists: domain conditions, overflow
   phrasing, how "no errors" is stated, input quantification limits) +
   fib proved end-to-end in the proposed form + a draft gallery entry.
   → USER CHECKPOINT: agree the statement form on the concrete object.
2. **Scale to the set** (agreed form): gcd, min/max of a slice, slice
   reverse, binary search, insertion sort, map word-count. Mechanical
   replication may go to Opus workers once the exemplar shape exists
   (model policy 2026-08-11); anything that fights the form is a
   finding brought back, not forced through.
3. **The gallery + close**: docs/verified-examples.md rendered from the
   example modules (scripts/render-gallery; staleness check at
   speedbump standard); programs in Corpus/coverage/exec/examples/
   (differentially tested like all corpus Go); reasoning-friction list
   recorded as input to future arcs; claims sweep; arc-end audit ask.

## Front-loaded (blessed with this charter) vs checkpointed

- FD-E1 — the example set: as slice 2 lists; additions in-lane if a
  friction class needs an exhibit (recorded); removals are a park.
- FD-E2 — homes: corpus programs under Corpus/coverage/exec/examples/,
  proofs under proofs/GoLeanProofs/Examples/, gallery at
  docs/verified-examples.md.
- FD-E3 — machine-integer honesty is a REQUIREMENT of every arithmetic
  spec; ∀-input where the layer supports it, concrete-domain fallbacks
  RECORDED as foundation debt (input to the width arc's queue).
- FD-E4 — models: Fable for the exemplar/spec design; Opus acceptable
  for replication.
- CHECKPOINTED (not front-loaded): the headline statement form —
  slice-1 exit, decided by the user on the concrete fib theorem.

## Checkpoint rulings (user, 2026-08-12 — slice 1)

1. **L1/L2 as recommended**: the inline ∃N-∀fuel≥N completion idiom
   stands (wrappable later, uniformly, if surface readability wins);
   BOTH theorems (bounded exact-value + full-domain wrapped) per
   arithmetic example.
2. **ENUMERATION IS BANNED AS A PROOF METHOD, corpus-wide**: this is a
   symbolic reasoning project — every theorem in the examples corpus
   is symbolic in its inputs. Kernel enumeration is legitimate ONLY as
   per-instance evidence (corpus oracle rows, e.g. fib's n=94 wrap
   row), never the discharge of a quantified claim. (The slice-1
   exemplar's 94-seed completion enumeration was replaced accordingly
   in slice 1.5 by the fuel-measure rule family,
   `proofs/GoLeanProofs/FuelMeasure.lean`.)
3. **The fuel-measure rule family is arc scope** (promoted from parked
   debt at the checkpoint): loop invariant + per-iteration fuel bound
   + decreasing measure ⇒ completion, by induction over the executable
   semantics; designed as `wp_while_inv_break`'s completion-side twin;
   no Iris in the termination half (rationale recorded in the design
   note and the module).

## Form ruling (user, 2026-08-13, SUPERSEDED same day — see below)

Headlines UNIFY to the MEMORY-QUANTIFIED form: input data + arbitrary
disjoint frame, with frame preservation VISIBLE in the statement. The
exact frame structure is under iteration, so slice 2 splits: **2a**
designs the form on one memory-input exemplar (slice reverse) plus the
fib retrofit and STOPS AT A CHECKPOINT (packet: design note §9);
**2b** scales to gcd/min-max/binsearch/insertion-sort/word-count after
the frame-structure ruling. The enumeration ban binds everything.

## THE HARNESS RULING (user, 2026-08-13 — final headline form)

Headlines are HARNESS-shaped: one fixed three-phase Go function per
example (`setup_*_state` from scalar parameters → the call under test
→ `test_*_state` folding memory analysis into return values), with the
Lean statement over the machine's native entry
(`runFunctionWithContextM`, `runProgramM` for whole-program): ∀
well-typed argument values, ∃N-∀fuel≥N-∀ch, the run returns `.ok` with
the specified values. NO Lean-side heap readback, NO frame clauses, NO
AST splicing in user-facing statements — memory analysis happens in Go
inside the verified footprint; implicit framing is inherent in the
empty-heap entry. The §9 memory-quantified form demotes to proof-side/
reserve (segments, inductions, and the frame theorem carry the harness
headlines; nothing is re-proven). Full record incl. the user's quoted
rulings, the CBMC parallel, the designed-not-built choice-consuming
input pick (+ its differential obligation), the concurrency extension,
and the ghost-variable horizon addendum:
`docs/2026-08-12_example-spec-form.md` §11.

## Must-park

Machine changes of ANY kind (this arc is proofs/records only — width
belongs to the other arc); designation (candidates recorded; curation
at merge windows); doctrine amendments; new Choices sites; compat/**;
merges/pushes (operator-gated).

## Discipline (inherited, binding)

The standing set: sub-branch audits (claims/spec-honesty as the primary
dimension here), TCB-grounding walk per export, honest records,
deletion test, D1-BOTH beneath the headline, zero corpus drift beyond
the new examples' explained additions, 48 designated byte-identical,
worktree discipline, commit-on-agreement.

## Exit criterion

The gallery renders with every listed example proved in the agreed
headline form (or its gap recorded as named foundation debt with a
consumer); every claim scoped per the two-questions separation; gates
green. Deferral with an honest log entry is success.
