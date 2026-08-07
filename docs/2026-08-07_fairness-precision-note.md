# D5 fairness precision: the ∀-stream Terminates claim, made exact (slice 5)

Status: the note D5 owed ("to be made precise … when a concurrent
`Terminates` is first stated"). The concurrent notion now exists —
`Surface.TerminatesNormallyC` (slice 5): one fuel bound, EVERY choice
stream (schedules + latitude, D8's single stream), main's `.normal`
terminal — so the claim can be stated against it exactly.

## 1. What the assumption-free quantifier actually is

`TerminatesNormallyC env₀ σ₀ prog` says: ∃ N, every stream's `execProg`
run completes at main's `.normal` terminal within fuel N. Because the
pool's branching at every consumption site is FINITE (the L1 bound is
the runnable count, L2/L4 the ready/candidate counts, the data sites
their own finite widths), König's lemma gives the exact semantic
characterization:

> **The ∀-stream-termination class is the FINITE-SCHEDULE-TREE class:**
> `TerminatesNormallyC` holds iff (a) no stream has an infinite run and
> (b) every completion is main-`.normal`. The uniform bound N is not an
> extra assumption — for finitely-branching trees, "no infinite run"
> and "uniformly bounded depth" coincide.

This is the strongest termination claim available WITHOUT any fairness
vocabulary: it quantifies over every schedule including maximally
unfair ones. Its discharge route is mechanical — the pool ∀-streams
kernel checker (`allStreamsOkPool` + soundness + `execProgLoop_mono`,
`MultiStreams.lean`) certifies exactly the finite tree.

## 2. The membership instance (proved) and the class lemma (not)

* **Proved, slice 5**: `forkJoinTerminatesNormallyC` — the fork/join
  rendezvous program is IN the class (kernel-certified tree, bound
  400). This is the class-membership lemma at instance strength; it is
  a designated statement.
* **Not proved, recorded honestly**: a general syntactic-discipline ⇒
  finite-tree theorem. No Lean definition of the discipline ships —
  deliberately: with no consumer it would be inert scaffolding. The
  discipline below is the PROSE criterion a future lemma would
  formalize.

## 3. The blocking-discipline argument, made exact — and a CORRECTION

The slice-2/D5 prose argued: "true because the scheduler picks among
RUNNABLE goroutines and starvation requires a runnable spinner (not
expressible race-free without atomics)". Made precise, the sound core
is:

An infinite run must step some goroutine infinitely often — a
**spinner**: a goroutine that is runnable infinitely often and never
terminally parked. Spinners come in exactly two shapes:

* **(a) an infinite registry-op-free segment** — a pure compute loop.
  Excluded by the discipline "every loop body crosses a registry op or
  is bounded" (a sequential-fragment property).
* **(b) an infinite registry-op sequence that never parks** — a
  busy-wait THROUGH the registry: every op finds the cell ready (or
  declines to block).

**The correction (recorded per the too-wide/too-narrow review duty):**
the parenthetical "not expressible race-free without atomics" is FALSE
for shape (b) in the current fragment. A `select`-with-`default` poll
loop — `for { select { case <-ch: …; default: } }` — is race-free,
atomics-free, channel-only, LIVE in the machine since slice 4 made
select-with-default and the L2 site real, and spins forever when `ch`
never fires: on adversarial streams it starves every other goroutine.
Such programs are correctly OUTSIDE `TerminatesNormallyC` (their
schedule tree is infinite), so no shipped claim is wrong — but the
DOCTRINE consequence is real and now recorded: the additive
`FairStream` quantifier planned for the atomics arc (D5's "later"
lane) is needed for the select-default polling idiom too, not only for
atomics. Unbounded productive communication loops (e.g. a
producer/consumer pair that forever finds buffer room) are a second
atomics-free shape (b) instance.

So the exact sufficient discipline for the assumption-free lane is:

> bounded compute between registry ops (no shape-(a) loops), no
> select-`default` polling loops, no unbounded productive
> communication cycles, finitely many spawns — jointly: the schedule
> tree is finite.

Membership is argued per program (mechanically, by the kernel
checker); the general implication from the syntactic discipline is the
recorded scaffold.

## 4. Statement hygiene

`TerminatesNormallyC` and the fork/join instance are first-order over
`execProg` alone — no Iris, no relation, no fairness vocabulary; any
future `Fair`-conditioned statement remains ABOVE-SPEC per D5 and must
carry its caveat. Nothing in this note restates an existing designated
statement.
