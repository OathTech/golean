import GoLeanIris.Rules

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

inductive FrameExitSite :
    Config → List (TargetShape × List Expr) → LocalEnv → List Loc → Cont → Bool → Prop where
  | fall {plans env roots k w} : FrameExitSite (.next (.frame plans env roots [] k w)) plans env roots k w
  | returning {plans env roots k w} :
      FrameExitSite (.signal .ret (.frame plans env roots [] k w)) plans env roots k w

theorem FrameExitSite.not_value {c plans env roots k w}
    (site : FrameExitSite c plans env roots k w) : ToVal.toVal c = (none : Option Unit) := by
  cases site <;> rfl

theorem FrameExitSite.step {c plans env roots k w s next t ch}
    (site : FrameExitSite c plans env roots k w)
    (run : stepFrameExit s plans env roots [] k w ch = .ok (next, t, ch)) :
    stepFn s c ch = .ok (next, t, ch) := by
  cases site <;> simp [stepFn, signalStep, run]

section
variable {GF : BundledGFunctors} [GoGS GF]
variable {E : CoPset} {Φ : Unit → IProp GF}

theorem wp_frame_empty {c env k w} (site : FrameExitSite c [] env [] k w) :
    (▷ WP (Config.next k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP c @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_context_step site.not_value (fun _ _ _ => site.step rfl)

/-- Read the callee's pinned result only after its defer chain is drained.
Target operands and the later writeback still execute in the caller's saved
environment. The result cell remains owned by the caller of this rule. -/
theorem wp_frame_result {c shape e ops plans env k w a ty v dq}
    (site : FrameExitSite c ((shape, e :: ops) :: plans) env [.base ⟨a⟩] k w) :
    (a ↦{dq} (.value ty v) ∗ ▷ (a ↦{dq} (.value ty v) -∗
      WP (Config.evalE e env (.tgtOpK shape [] ops [] plans .vals [] [v] (.seqn #[]) env k))
        @ Stuckness.NotStuck; E {{ Φ }})) ⊢
    WP c @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_read_step site.not_value
  intro state _ hlook choices
  apply site.step
  simp [stepFrameExit, loadMany, loadLoc_cell hlook, Bind.bind, Except.bind]

theorem wp_deref_cell {a ty v dq env k} :
    (a ↦{dq} (.value ty v) ∗ ▷ (a ↦{dq} (.value ty v) -∗
      WP (Config.retV v k) @ Stuckness.NotStuck; E {{ Φ }})) ⊢
    WP (Config.retV (.addr (.base ⟨a⟩)) (.strictK (.deref ty) [] [] env k))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_read_step rfl
  intro state _ hlook choices
  simp [stepFn, applyStrictOp, valueAsLoc, loadLoc_cell hlook, toResult,
    deliverS, Bind.bind, Except.bind, Pure.pure, Except.pure]

end
end GoLean.IrisCustomer
