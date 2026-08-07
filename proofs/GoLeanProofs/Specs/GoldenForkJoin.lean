import GoLeanProofs.Surface

/-!
# The fork/join kernel witnesses (channels arc slice 2)

The slice-2 witnesses for the concurrent carrier (see the witness-status
note in `Surface.lean`'s D8 section): a hand-built fork/join program —
main spawns a worker, the worker sends 42 over an unbuffered channel,
main receives it into the pinned output cell — KERNEL-EVALUATED through
the ThreadPool driver (`execProg`) under three pinned choice streams
realizing three DISTINCT schedules (main-first, worker-then-main,
worker-twice — the scheduler's L1 site genuinely consumes: two
goroutines are runnable at the registry boundaries; distinctness
argued at `forkJoinStreamAlternating`), plus a
multi-goroutine DEADLOCK program classified `.deadlock` the same way.

These are rung-1, pinned-stream readouts — deliberately NOT `GoSpecC`
instances (the `∀ ch` schedule quantifier's discharge is the slice-5
deliverable, per the design's slice plan). What they pin, non-vacuously:
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

/-- Canonical schedule (the empty stream: every pick 0). -/
theorem forkJoinStreamCanonical : fjRunGives42 400 [] = true := by
  decide +kernel

/-- Adversarial schedule: descending picks at every consumption. -/
theorem forkJoinStreamAdversarial :
    fjRunGives42 400 [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] = true := by
  decide +kernel

/-- The worker-first-twice schedule — the third DISTINCT execution
(S2 audit response: the original stream [1,0,1,0,…] reduced mod the
scheduler's bound 2 to the same pick sequence as the adversarial
stream, certifying the same execution twice; every consumption in this
program has bound exactly 2, so distinctness is decided by the pick
sequence mod 2: canonical [] = main-first (main parks, worker's
arriving send pairs), adversarial [9,8,…] = worker-then-main (main
still parks — the worker sits unparked at its boundary — then the
send pairs), all-ones = worker-twice (the WORKER parks first and
main's arriving receive pairs — the handoff's other direction). -/
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

end GoLean.Surface
