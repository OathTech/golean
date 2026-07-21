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
reduces only to `.next (seqCont ss.toList env k)` with the state unchanged
(D1: under a same-env governing seq this splices; at a concrete non-seq
continuation `seqCont` reduces definitionally to the old wrap, so existing
applications are unchanged). A genuine weakest-precondition law over
GoCore's actual `Step` relation. -/
theorem wp_seqn {ss env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next (seqCont ss.toList env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.seqn ss) env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (seqCont ss.toList env k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next (seqCont ss.toList env k), σ, [], GoPrimStep.step Step.seqn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- Pure, deterministic frame pop for VOID frames: normal completion of a
body with no results and no targets resumes the caller (`Step.frameFall`
with empty read/store legs — D2-proper: value-returning frame exits are
state-reading and get their own law in `Laws/Call`). -/
theorem wp_frame_fall {k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.frame [] [] k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next k, σ, [], GoPrimStep.step (Step.frameFall .nil .nil)⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        cases st with
        | frameFall hld hst =>
          cases hld
          cases hst
          exact ⟨rfl, rfl, rfl, rfl⟩))
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

/-- Pure, deterministic step: `return` starts unwinding (env-free after
D2-proper: the frame reads results from call-time-pinned locations). -/
theorem wp_return {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning k) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec .returnStmt env k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning k)
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
discarding that scope (`Step.seqReturn`). -/
theorem wp_seq_return {rest : List Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.returning k) @ s ; E {{ Φ }}) ⊢
      WP (Config.returning (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.returning k)
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
