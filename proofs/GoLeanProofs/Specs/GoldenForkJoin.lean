import GoLeanProofs.Surface
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
stream literals and readouts unchanged), plus a
multi-goroutine DEADLOCK program classified `.deadlock` the same way.

The slice-2 witnesses are rung-1, pinned-stream readouts; SLICE 5
added the ∀-SCHEDULE family below (the `∀ ch` quantifier discharged by
the pool ∀-streams kernel checker) which subsumes them — they are
deliberately KEPT byte-identical (designated-set growth by extension,
never restatement). What the pinned-stream witnesses pin, non-vacuously:
the spawn step forks, the arrival intercept pairs the rendezvous, the
handoff delivers the value, main's exit joins, and the all-asleep state
classifies as the deadlock terminal — end to end, through the kernel.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

set_option maxRecDepth 1000000

/-- The fork/join worker: send 42 on the channel argument. -/
def forkJoinWorker : Func := {
  id := ⟨"fjWorker"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanSend (.var "ch") (.intLit 42) .int]
}

/-- Main's body: make an unbuffered channel, spawn the worker on it,
receive the worker's value into the pinned output cell `r`. -/
abbrev forkJoinDriver : Stmt := .block
  #[{ id := "chv", typ := .chan .both .int }]
  #[
    .makeChan (.var "chv") .int none,
    .goStmt (.funcVal ⟨"fjWorker"⟩ #[]) #[.var "chv"],
    .chanRecv #[.var "r"] (.var "chv") .int
  ]

abbrev fjEnv : LocalEnv := [[("r", .base ⟨0⟩)]]

/-- The seeded state: the output cell at base 0 holding 0. -/
def fjSeed : ExecState :=
  { functions := #[forkJoinWorker],
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- The pinned-run readout: did the pool run complete `.normal` with
the output cell holding 42? Bool-valued so the kernel decides it. -/
def fjRunGives42 (fuel : Nat) (ch : Choices) : Bool :=
  match execProg fuel fjEnv fjSeed ch forkJoinDriver with
  | .ok (.normal σf, _) =>
      match loadLoc σf (.base ⟨0⟩) with
      | .ok (.int 42 .int) => true
      | _ => false
  | _ => false

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

/-- The blocked worker for the deadlock witness: receive on a channel
nobody sends on. -/
def fjBlockedWorker : Func := {
  id := ⟨"fjBlocked"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanRecv #[] (.var "ch") .int]
}

/-- Main parks on one channel while the spawned worker parks on
another: ALL goroutines asleep after real multi-goroutine progress. -/
abbrev fjDeadlockDriver : Stmt := .block
  #[{ id := "av", typ := .chan .both .int },
    { id := "bv", typ := .chan .both .int }]
  #[
    .makeChan (.var "av") .int none,
    .makeChan (.var "bv") .int none,
    .goStmt (.funcVal ⟨"fjBlocked"⟩ #[]) #[.var "av"],
    .chanRecv #[.var "r"] (.var "bv") .int
  ]

def fjDeadlockSeed : ExecState :=
  { functions := #[fjBlockedWorker],
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- Does the pool classify the run as the all-asleep DEADLOCK terminal? -/
def fjRunDeadlocks (fuel : Nat) (ch : Choices) : Bool :=
  match execProg fuel fjEnv fjDeadlockSeed ch fjDeadlockDriver with
  | .error .deadlock => true
  | _ => false

theorem forkJoinDeadlockCanonical : fjRunDeadlocks 400 [] = true := by
  decide +kernel

theorem forkJoinDeadlockAdversarial :
    fjRunDeadlocks 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true := by
  decide +kernel


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

/-- The joined-final-state readout: the output cell holds 42. -/
def fjReadout42 : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.int 42 .int) => true
  | _ => false

/-- The kernel certificate: the checker explores every schedule of the
fork/join pool within fuel 400 and certifies the `.normal`/42 outcome
on all of them. (The deadlock program of `fjRunDeadlocks` is REFUSED
by the same checker — probed; a certificate for it cannot exist, since
the soundness theorem would then contradict
`forkJoinDeadlockCanonical`.) -/
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
