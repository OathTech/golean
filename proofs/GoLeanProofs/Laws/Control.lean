import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.Rel
import GoLeanProofs.Ghost

/-!
# Pure control-step laws
Deterministic, state-preserving control transitions: sequencing, return
unwinding, frame fall-through.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- `seqn` is a pure, deterministic control step: `.exec (.seqn ss) env k`
reduces only to `.next (.seq ss.toList env k)` with the state unchanged. A
genuine weakest-precondition law over GoCore's actual `Step` relation (holds
under the real gen_heap state interpretation, since the step is pure). The
control environment `env` rides through unchanged — sequencing reads no
variables. -/
theorem wp_seqn {ss env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next (.seq ss.toList env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.seqn ss) env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (.seq ss.toList env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next (.seq ss.toList env k), σ, [], GoPrimStep.step Step.seqn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic frame pop: normal completion of a function body
resumes the caller (`Step.frameFall`; stores no results — void frames). -/
theorem wp_frame_fall {targets results k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.frame targets results k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step Step.frameFall⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic step: advance a sequence to its next statement
(`Step.seqNext`). -/
theorem wp_seq_next {t : Stmt} {rest : List Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.exec t env (.seq rest env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.seq (t :: rest) env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.exec t env (.seq rest env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.seqNext⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic step: `return` starts unwinding, carrying the current
env into `.returning` (so the frame can read named results). -/
theorem wp_return {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec .returnStmt env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning env k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.returnStmt⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic step: `return` unwinds past a sequence continuation,
discarding that scope (`Step.seqReturn`); the callee env rides in
`.returning`. -/
theorem wp_seq_return {retEnv : LocalEnv} {rest : List Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning retEnv k) @ s ; E {{ Φ }}) ⊢
      WP (Config.returning retEnv (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning retEnv k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.seqReturn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic control step: an exhausted sequence pops to its
continuation (discarding that scope's env — CEK scope exit). Mirror of
`wp_seqn` for `Step.seqDone`. -/
theorem wp_seq_done {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.seq [] env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step Step.seqDone⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

end

end GoLean.Iris
