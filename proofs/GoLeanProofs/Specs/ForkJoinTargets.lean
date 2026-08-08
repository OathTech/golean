import GoLean.GoCore.Multi

/-!
# The fork/join statement targets — DEFS ONLY (statement module)

The definitions the designated fork/join theorem STATEMENTS reference
(`fjRunGives42`, `fjRunDeadlocks`, and their program/seed/env
constituents), split out of `Specs/GoldenForkJoin.lean` at the
channels-arc final audit (F4, 2026-08-07): the Comparator Challenge —
the judge's trusted root — must import ONLY clean statement modules
(defs a skeptic reads, zero theorems), and `GoldenForkJoin.lean` had
grown the `decide +kernel` PROOFS of nine designated theorems, putting
proved designated declarations inside the trusted closure. This module
restores the discipline mechanically (it mirrors the existing
`Statements.lean`/`GoldenTargets.lean` def-only pattern); the proofs
stay in `GoldenForkJoin.lean`, which imports this and reaches the
judge only through `Solution`. The ci surface-purity scan pins this
file's imports, and the statement-TCB closure gate (ci step 1c3)
asserts no designated theorem is declared anywhere in Challenge's
import closure.

Content notes (verbatim from the slice-2 originals — the split moves
text, never restates it): the fork/join program is a hand-built
two-goroutine rendezvous — main spawns a worker, the worker sends 42
over an unbuffered channel, main receives it into the pinned output
cell — and the deadlock program parks main and its worker on two
different channels, all goroutines asleep after real multi-goroutine
progress.
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

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

/-- The joined-final-state readout: the output cell holds 42 (the
slice-5 ∀-schedule certificate's post; lives here beside
`fjRunGives42` so the two readouts share one matcher — the
`forkJoinAllSchedules42` proof bridges them definitionally). -/
def fjReadout42 : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.int 42 .int) => true
  | _ => false

/-- Does the pool classify the run as the all-asleep DEADLOCK terminal? -/
def fjRunDeadlocks (fuel : Nat) (ch : Choices) : Bool :=
  match execProg fuel fjEnv fjDeadlockSeed ch fjDeadlockDriver with
  | .error .deadlock => true
  | _ => false

end GoLean.Surface
