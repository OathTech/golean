import GoLeanProofs.Surface
import GoLeanProofs.Specs.ForkJoinTargets
import GoLean.GoCore.MultiStreams

/-!
# The fork/join kernel witnesses (channels arc slices 2 + 5)

The witnesses for the concurrent carrier (see the witness-status
note in `Surface.lean`'s D8 section): a hand-built fork/join program —
main spawns a worker, the worker sends 42 over an unbuffered channel,
main receives it into the pinned output cell — KERNEL-EVALUATED through
the ThreadPool driver (`execProg`) under three pinned choice streams
realizing three DISTINCT schedules (the scheduler's L1 site genuinely
consumes: two goroutines are runnable at the registry boundaries —
including, since slice 4's BUG-040 fix, the POST-SPAWN `.spawned`
boundary; the schedules were re-derived by probe after that fix and
the distinctness argument re-recorded at `forkJoinStreamAlternating`;
stream literals and readouts unchanged). The multi-goroutine DEADLOCK
program that once sat beside them was RETIRED at the 2026-08-28
hygiene slice — see the retirement note below.

THE DEFS the designated statements reference (`fjRunGives42`,
`fjReadout42`, the programs/seeds/env) live in
`Specs/ForkJoinTargets.lean` — the def-only statement module in
Challenge's trusted closure (split at the channels-arc final audit,
F4, 2026-08-07: this file holds `decide +kernel` PROOFS of designated
theorems and therefore must NOT be imported by the trusted root).
This module holds the proofs and reaches the judge only through
`Solution`.

The slice-2 witnesses are rung-1, pinned-stream readouts; SLICE 5
added the ∀-SCHEDULE family below (the `∀ ch` quantifier discharged by
the pool ∀-streams kernel checker) which subsumes them. DESIGNATION
STATUS (triage landing 2026-08-27, [USER] decision, plan L-13): the
five pinned-stream rows were RECLASSIFIED to NON-DESIGNATED witnesses
— removed from Challenge/Solution/Audit's designated list and
judge-config; the ∀-schedule family stays designated. The three
SURVIVING pinned-stream rows are kept byte-identical here with their
Audit axiom pins (the two deadlock rows were retired at the 2026-08-28
hygiene slice — note below). What the surviving pinned-stream
witnesses pin, non-vacuously: the spawn step forks, the arrival
intercept pairs the rendezvous, the handoff delivers the value, and
main's exit joins — end to end, through the kernel.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

set_option maxRecDepth 1000000

/-- Canonical schedule (the empty stream: every pick 0): main runs
through the post-spawn boundary, parks at its receive, and the
worker's ARRIVING SEND pairs with the parked receiver. -/
theorem forkJoinStreamCanonical : fjRunGives42 400 [] = true := by
  decide +kernel

/-- Adversarial schedule: descending picks at every consumption.
RE-DERIVED at slice 4 (BUG-040: the post-spawn `.spawned` boundary is
a new consumption site, so the same literal now realizes a DIFFERENT
schedule — probed): picks 1,0,1 mod the bound 2 give worker-first at
the fork's completion, main's marker strip, then the worker PARKS at
its send (main is mid-statement, not parked) and main's arriving
receive pairs with the parked sender — the handoff direction the
pre-fix literal could not reach. -/
theorem forkJoinStreamAdversarial :
    fjRunGives42 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true := by
  decide +kernel

/-- The third DISTINCT execution (S2 audit response introduced the
all-ones literal; slice 4's BUG-040 re-derivation, by probe): picks
1,1 run the WORKER TWICE consecutively from the post-spawn boundary —
it parks at its send while main still holds the `.spawned` marker —
then main (the only runnable) strips and its arriving receive pairs.
Distinctness of the three: the realized pick sequences are [], [1,0,1]
and [1,1] (every site here has bound exactly 2), and the interleavings
differ pairwise — canonical is the parked-RECEIVER direction; the
other two are the parked-SENDER direction but place main's marker
strip on opposite sides of the worker's park. -/
theorem forkJoinStreamAlternating :
    fjRunGives42 400 [1, 1, 1, 1, 1, 1, 1, 1] = true := by
  decide +kernel

/-! RETIRED at the hygiene slice (2026-08-28, gate-audit L-7, plan
§6.3): `forkJoinDeadlockCanonical` and `forkJoinDeadlockAdversarial`,
the two pinned-stream `fjRunDeadlocks 400 <literal> = true` replays,
are DELETED together with the `fjRunDeadlocks` def and its deadlock
program (`Specs/ForkJoinTargets.lean`) and their two Audit axiom pins.
They were de-designated at the triage landing (2026-08-27) as
single-pinned-stream kernel replays, which left them with no consumer
at all. `forkJoinNoDeadlock` below carries the deadlock content in the
form the doctrine wants: ∀ ch, NO schedule of the fork/join program
reaches the `.deadlock` terminal. Recoverable at 05e81b70
(docs/ARCHIVE.md). -/

/-! ## The slice-5 ∀-SCHEDULE witnesses — the `∀ ch` quantifier
DISCHARGED (the pool ∀-streams kernel checker route the slice-2 note
recorded; `allStreamsOkPool`, `MultiStreams.lean`).

One kernel evaluation (`forkJoinAllStreamsCert`) explores EVERY choice
stream's run of the fork/join program — the L1 scheduler branched at
every multi-runnable boundary, every other step certified
stream-oblivious — and the soundness theorem
(`execProgLoop_ok_of_allStreamsOkPool`) turns it into: every schedule
and every latitude stream completes the rendezvous at main's `.normal`
terminal with the 42 readout. The pinned-stream witnesses above are
subsumed but deliberately KEPT (byte-identical — the designated set
grows by extension, never restatement). -/

/-- The kernel certificate: the checker explores every schedule of the
fork/join pool within fuel 400 and certifies the `.normal`/42 outcome
on all of them.

NON-VACUITY, STATED HONESTLY (audit finding F-5, 2026-08-28): the
discriminating leg of this claim was `forkJoinDeadlockCanonical`, and
it was RETIRED at the hygiene slice (see the retirement note above).
That theorem's deadlock program was probed against this same checker
and REFUSED — as it must be, since a certificate for it plus the
soundness theorem would contradict its `.deadlock` classification —
but that probe now survives only as an ARCHIVED record
(docs/ARCHIVE.md, recoverable at 05e81b70), not as a live theorem.
So: `allStreamsOkPool` has NO surviving in-tree demonstration that it
can return `false`. Its discrimination is UNWITNESSED in the tree
today. This is a real evidentiary gap, not a formality — a checker
that returned `true` unconditionally would satisfy every live use.
The named re-supplier is the corpus's fork/join member when
concurrency resumes (iris-corpus plan §5): its negative twin restores
a live false-witness. -/
theorem forkJoinAllStreamsCert :
    allStreamsOkPool fjReadout42 400
      ⟨#[.exec forkJoinDriver fjEnv .stop], fjSeed, 0⟩ {} = true := by
  decide +kernel

/-- **THE ∀-SCHEDULE WITNESS**: EVERY choice stream — schedules and
latitude together — runs the fork/join program to `.normal` with the
output cell holding 42. The slice-2 pinned-stream witnesses are the
`[]`/`[9,…,0]`/`[1,…,1]` instances of this statement. -/
theorem forkJoinAllSchedules42 : ∀ ch : Choices, fjRunGives42 400 ch = true := by
  intro ch
  obtain ⟨σf, ch', hrun, hpost⟩ :=
    execProgLoop_ok_of_allStreamsOkPool forkJoinAllStreamsCert ch
  unfold fjRunGives42
  rw [show execProg 400 fjEnv fjSeed ch forkJoinDriver
      = execProgLoop 400 ⟨#[.exec forkJoinDriver fjEnv .stop], fjSeed, 0⟩ {} ch
    from rfl, hrun]
  simpa [fjReadout42] using hpost

/-- First-order readout corollary: NO schedule of the fork/join program
deadlocks (the run completes, so the `.deadlock` classification is
unreachable on every stream). -/
theorem forkJoinNoDeadlock : ∀ ch : Choices,
    execProg 400 fjEnv fjSeed ch forkJoinDriver ≠ .error .deadlock := by
  intro ch hcontra
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool forkJoinAllStreamsCert ch
  rw [show execProg 400 fjEnv fjSeed ch forkJoinDriver
      = execProgLoop 400 ⟨#[.exec forkJoinDriver fjEnv .stop], fjSeed, 0⟩ {} ch
    from rfl, hrun] at hcontra
  cases hcontra

/-- First-order readout corollary: NO schedule of the fork/join program
trips the race detector (`execProg` runs the detecting loop, and every
stream's run completes `.ok`). -/
theorem forkJoinNoRace : ∀ ch : Choices,
    execProg 400 fjEnv fjSeed ch forkJoinDriver ≠ .error .raceDetected := by
  intro ch hcontra
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool forkJoinAllStreamsCert ch
  rw [show execProg 400 fjEnv fjSeed ch forkJoinDriver
      = execProgLoop 400 ⟨#[.exec forkJoinDriver fjEnv .stop], fjSeed, 0⟩ {} ch
    from rfl, hrun] at hcontra
  cases hcontra

/-- **Concurrent termination of the fork/join program** — the first
`TerminatesNormallyC` instance (D5's ∀-stream `Terminates` claim, made
concrete on a program IN the blocking-discipline class): one fuel bound
works for every stream, lifted to all larger fuels by
`execProgLoop_mono`. -/
theorem forkJoinTerminatesNormallyC :
    TerminatesNormallyC fjEnv fjSeed forkJoinDriver := by
  refine ⟨400, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool forkJoinAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Surface
