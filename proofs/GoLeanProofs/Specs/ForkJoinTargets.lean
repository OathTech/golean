import GoLean.GoCore.Multi

/-!
# The fork/join statement targets — DEFS ONLY (statement module)

The definitions the designated fork/join theorem STATEMENTS reference
(`fjRunGives42`, `fjReadout42`, and their program/seed/env
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
cell.

RETIRED at the hygiene slice (2026-08-28, gate-audit L-7, plan §6.3):
the DEADLOCK program and its readout — `fjRunDeadlocks`,
`fjBlockedWorker`, `fjDeadlockDriver`, `fjDeadlockSeed` — are deleted.
Their only consumers were the two pinned-stream theorems
`forkJoinDeadlockCanonical`/`Adversarial`, de-designated at the triage
landing (2026-08-27) and retired in the same commit; the def then had
zero consumers anywhere in the tree. The `.deadlock` content that
matters is carried by `forkJoinNoDeadlock` (`GoldenForkJoin.lean`),
which says NO schedule of the fork/join program deadlocks — a
∀-quantified statement, strictly stronger than a pinned-stream replay
of one deadlocking program. Recoverable at 05e81b70 (docs/ARCHIVE.md).
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

/-- The joined-final-state readout: the output cell holds 42 (the
slice-5 ∀-schedule certificate's post; lives here beside
`fjRunGives42` so the two readouts share one matcher — the
`forkJoinAllSchedules42` proof bridges them definitionally). -/
def fjReadout42 : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.int 42 .int) => true
  | _ => false

end GoLean.Surface
