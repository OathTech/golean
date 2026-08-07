# D5 fairness precision: the ∀-stream Terminates claim, made exact (slice 5)

Status: the note D5 owed ("to be made precise … when a concurrent
`Terminates` is first stated"). The concurrent notion now exists —
`Surface.TerminatesNormallyC` (slice 5): one fuel bound, EVERY choice
stream (schedules + latitude, D8's single stream), main's `.normal`
terminal — so the claim can be stated against it exactly.

CORRECTED at the S5 pre-merge audit (MAJOR, claim-precision): this
note's first form stated the §1 characterization as "holds iff (a) no
stream has an infinite run and (b) every completion is main-`.normal`;
the uniform bound N is not an extra assumption". That "iff" is FALSE
in the ⟸ direction, and was internally inconsistent with this note's
own tree reading in §3 — the corrected-of-record form is below, with
the refuting program family recorded and eval-pinned. No Lean
statement was affected (`TerminatesNormallyC`'s ∃N∀ form is
tree-equivalent — §1; `allStreamsOkPool` certifies the tree).

## 1. What the assumption-free quantifier actually is

`TerminatesNormallyC env₀ σ₀ prog` says: ∃ N, every stream's `execProg`
run completes at main's `.normal` terminal within fuel N. Because the
pool's branching at every consumption site is FINITE (the L1 bound is
the runnable count, L2/L4 the ready/candidate counts, the data sites
their own finite widths), König's lemma over the PICK TREE gives the
exact semantic characterization:

> **The ∀-stream-termination class is the FINITE-PICK-TREE class:**
> `TerminatesNormallyC` holds iff the pick tree (every finite or
> infinite sequence of in-bound picks) is finite and every leaf is
> main-`.normal`. Finiteness of a finitely-branching tree, uniform
> depth bound, and "no infinite BRANCH" coincide (König); the ∃N∀ form
> is equivalent to the tree form because any fuel-N run consumes at
> most N picks, so truncating a branch to its first N picks and
> padding realizes it as a stream.

**The stream-vs-branch distinction, spelled out — the ⟸ correction.**
"Stream" means `ch : Choices = List Nat`, a FINITE list;
`Choices.consume [] b = (0, [])`, so an exhausted stream picks 0
forever. Streams therefore realize only the *eventually-canonical*
branches of the pick tree (a finite prefix, then pick-0 forever) — a
PROPER subset of the branches. Consequently:

> "no stream has an infinite run" does NOT imply the tree is finite,
> and does NOT imply `TerminatesNormallyC`. A program can terminate on
> every finite stream while its minimum fuel grows without bound in
> the stream.

The refuting family (the S5 audit's counterexample, reproduced at
machine level and EVAL-PINNED — `Tests/GoCoreEval.lean`, "poller
family" pins): main spawns a sender on `done` and a select-`default`
poller on a never-fired channel (`for { select { case <-poll:;
default: } }`), then receives from `done`. Every finite stream
terminates main-`.normal` 42 (once the stream exhausts, canonical
picks run the lowest-index runnable and main eventually completes) —
but streams `[2]*n` keep picking the poller, and the machine-probed
minimum fuel is 43, 43, 57, 93, 165, 309, 597 for n = 0, 2, 4, 8, 16,
32, 64 (≈ 9n + 21, unbounded). So "(a) ∧ (b) over streams" holds while
`TerminatesNormallyC` is false: the uniform N is genuinely more than
∀-stream termination. The two eval pins fix fuel 165 and exhibit the
growth (`[2]*16` completes; `[2]*32` exhausts).

**Why this matters beyond wording**: "discipline ⇒ no stream diverges
⇒ TerminatesNormallyC" is exactly the inference a future
class-membership lemma would be tempted to rest on, and it is unsound
at the second step. Any such lemma must conclude finiteness of the
TREE (all branches), not absence of diverging streams.

The tree characterization's discharge route is mechanical — the pool
∀-streams kernel checker (`allStreamsOkPool` + soundness +
`execProgLoop_mono`, `MultiStreams.lean`) certifies exactly the finite
tree: it explores every in-bound pick at every consumption site, not
merely the stream-realizable branches.

## 2. The membership instance (proved) and the class lemma (not)

* **Proved, slice 5**: `forkJoinTerminatesNormallyC` — the fork/join
  rendezvous program is IN the class (kernel-certified tree, bound
  400). This is the class-membership lemma at instance strength; it is
  a designated statement.
* **Not proved, recorded honestly**: a general syntactic-discipline ⇒
  finite-tree theorem. No Lean definition of the discipline ships —
  deliberately: with no consumer it would be inert scaffolding. §3
  records what such a lemma must and must not assume.

## 3. The blocking-discipline argument — corrected twice over

The slice-2/D5 prose argued: "true because the scheduler picks among
RUNNABLE goroutines and starvation requires a runnable spinner (not
expressible race-free without atomics)". Two corrections, both S5
findings:

**Correction 1 (the parenthetical is false, and was false when
written).** Call a goroutine that steps infinitely often in some
infinite branch a *spinner*. Race-free, atomics-free spinners exist in
the modeled fragment, in several shapes:

* a select-`default` poll loop on a never-ready channel (the §1
  family) — select-with-`default` has been a live machine step since
  SLICE 1, and `go` since slice 2, so the idiom has been expressible
  since slice 2: D5's parenthetical was already false at the moment
  the slice-2 note was written, not newly falsified (this note's first
  form misdated it to slice 4 and mis-credited the L2 site — a
  one-clause select has 0 or 1 ready clauses and never touches L2);
* a drain loop on a CLOSED channel (`close(ch); for { <-ch }` — the
  closed-empty receive completes with the zero value, never parks),
  and its select twin `for { select { case <-closedCh: } }` with no
  `default` at all;
* a single-goroutine buffered self-cycle
  (`ch := make(chan int, 1); for { ch <- 1; <-ch }` — every op finds
  room/data, no partner involved);
* park-and-wake-forever cycles: an unbuffered ping-pong pair
  (`A: for { ch1 <- 1; <-ch2 }` / `B: for { <-ch1; ch2 <- 1 }`) whose
  goroutines each park and pair once per iteration — spinners that DO
  park, refuting this note's first form's "spinners come in exactly
  two shapes (never-parking or registry-free)" taxonomy: parking
  spinners are a third shape, and an infinite branch need not contain
  any spinner of the first two shapes.

**Correction 2 (no syntactic discipline is claimed sufficient).** This
note's first form offered a four-condition discipline ("bounded
compute between registry ops, no select-`default` polling loops, no
unbounded productive communication cycles, finitely many spawns") as
"the exact sufficient discipline". It is NOT sufficient — the
closed-channel drain loop and the buffered self-cycle above satisfy
all four conditions and have infinite trees. The honest position of
record: **the only exact criterion is the finite pick tree itself**
(§1); the idioms above are KNOWN infinite-tree sources a syntactic
discipline must exclude, with no claim the list is exhaustive;
membership is certified mechanically per program (the kernel checker),
and a general syntactic lemma remains future work that must prove
tree-finiteness directly.

**Doctrine consequence (stands from the first form)**: the additive
`FairStream` quantifier planned for the atomics arc (D5's "later"
lane) is needed for all the atomics-free spinner idioms above — the
select-`default` poller, closed-channel drains, buffered self-cycles,
unbounded ping-pong — not only for atomics. Programs containing them
are correctly OUTSIDE `TerminatesNormallyC` (their trees are
infinite), so no shipped claim is wrong; they simply await the weaker
quantifier.

## 4. Statement hygiene

`TerminatesNormallyC` and the fork/join instance are first-order over
`execProg` alone — no Iris, no relation, no fairness vocabulary; any
future `Fair`-conditioned statement remains ABOVE-SPEC per D5 and must
carry its caveat. Nothing in this note restates an existing designated
statement.
