import GoLean.GoCore.MultiStreams

/-!
# The non-consuming-select checker witnesses (spec-parity slice 4)

Same-commit discharge witnesses for the `allStreamsOkPool` refinement
(`selectApplyDone`, `MultiStreams.lean` — design note
`docs/2026-08-10_gospecc-decomposition.md` §6(b)): a hand-built
two-goroutine program whose runs exercise every `.done` select-apply
shape the refinement certifies —

- ZERO-READY + DEFAULT, both directions (main's non-blocking send
  probe and the worker's non-blocking receive probe never rendezvous —
  the `select_nb_not_ready` idiom in miniature);
- the SINGLETON-READY COMMIT (main's final one-clause select receives
  from the closed channel — ready via close, committed without an L2
  pick);

on every schedule, including the main-exit window over the possibly
leaked worker. The negative control pins the fail-closed line: a
genuinely L2-CONSUMING (two-ready) select program is REFUSED by the
same checker (`decide` on its negation), so the refinement widened the
checker to exactly the non-consuming class, not to selects at large.

These are NOT designated statements (they are the extension's
witnesses, the slice-3 witness-discipline precedent); they are
referenced from `proofs/Audit.lean`'s witness registry
(name-existence/deletion tripwire scope, as recorded there).
-/

open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Surface

set_option maxRecDepth 1000000

/-- The worker: a non-blocking receive probe — `select { case <-ch:
default: }` — that must take DEFAULT on every schedule (main never
sends; its own probe is non-blocking too). -/
def selDoneWorker : Func := {
  id := ⟨"selDoneWorker"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.selectStmt
    #[(.recv #[] (.var "ch") .int, .seqn #[])]
    (some (.seqn #[]))]
}

/-- Main: spawn the worker's receive probe, run the send probe
(zero-ready + default — the buffer has no room and no partner is
parked on any schedule where the worker hasn't parked, and the worker
NEVER parks), close the channel, then a SINGLETON-READY one-clause
select (recv on the closed channel commits without any pick) writing
the readout. -/
abbrev selDoneDriver : Stmt := .block
  #[{ id := "chv", typ := .chan .both .int }]
  #[
    .makeChan (.var "chv") .int none,
    .goStmt (.funcVal ⟨"selDoneWorker"⟩ #[]) #[.var "chv"],
    .selectStmt
      #[(.send (.var "chv") (.intLit 1) .int, .seqn #[])]
      (some (.seqn #[])),
    .closeChan (.var "chv"),
    .selectStmt
      #[(.recv #[] (.var "chv") .int,
         .assign (.var "r") (.intLit 42))]
      none
  ]

abbrev selDoneEnv : LocalEnv := [[("r", .base ⟨0⟩)]]

def selDoneSeed : ExecState :=
  { functions := #[selDoneWorker],
    heap := [(.base ⟨0⟩, ⟨some (.int .int), .int 0 .int⟩)],
    nextAddr := 1 }

/-- The joined-final-state readout: the cell holds 42. -/
def selDoneReadout : ExecState → Bool := fun σf =>
  match loadLoc σf (.base ⟨0⟩) with
  | .ok (.int 42 .int) => true
  | _ => false

/-- **The extension's kernel certificate**: every schedule of the
select-probe program completes at main's `.normal` with the 42 readout
— through select applies the pre-refinement checker refused
unconditionally. -/
theorem selDoneAllStreamsCert :
    allStreamsOkPool selDoneReadout 200
      ⟨#[.exec selDoneDriver selDoneEnv .stop], selDoneSeed, 0⟩ {} = true := by
  decide +kernel

/-- The ∀-schedule readout (the `forkJoinAllSchedules42` shape). -/
theorem selDoneAllSchedules42 : ∀ ch : Choices,
    ∃ (σf : ExecState) (ch' : Choices),
      execProg 200 selDoneEnv selDoneSeed ch selDoneDriver
        = .ok (.normal σf, ch') ∧ selDoneReadout σf = true := by
  intro ch
  obtain ⟨σf, ch', hrun, hpost⟩ :=
    execProgLoop_ok_of_allStreamsOkPool selDoneAllStreamsCert ch
  exact ⟨σf, ch', hrun, hpost⟩

/-! ## The negative control (the fail-closed line)

A select whose apply IS L2-consuming — TWO ready clauses (two buffered
channels, both holding a value) — must still be REFUSED by the checker:
the refinement covers exactly the `.done` class. -/

/-- Two one-slot channels are made and filled, then a two-ready-clause
select — `applySelectCore` returns `.picks`, the L2 site consumes. -/
abbrev selConsumingDriver : Stmt := .block
  #[{ id := "av", typ := .chan .both .int },
    { id := "bv", typ := .chan .both .int }]
  #[
    .makeChan (.var "av") .int (some (.intLit 1)),
    .makeChan (.var "bv") .int (some (.intLit 1)),
    .chanSend (.var "av") (.intLit 7) .int,
    .chanSend (.var "bv") (.intLit 8) .int,
    .selectStmt
      #[(.recv #[.var "r"] (.var "av") .int, .seqn #[]),
        (.recv #[.var "r"] (.var "bv") .int, .seqn #[])]
      none
  ]

/-- The consuming select is REFUSED (fail closed), at the same fuel,
even with the readout weakened to `true` — the refusal is the select
apply itself, not the readout. -/
theorem selConsumingRefused :
    allStreamsOkPool (fun _ => true) 200
      ⟨#[.exec selConsumingDriver selDoneEnv .stop], selDoneSeed, 0⟩ {}
      = false := by
  decide +kernel

end GoLean.Surface
