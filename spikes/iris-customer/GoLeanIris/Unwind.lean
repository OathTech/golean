import GoLeanIris.Rules
import GoLean.Interface

/-! Context-sensitive recovery and unwind rules. Every rule names the actual
continuation or local machine walk. None is an evaluation-context bind law. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

/-- A local recovery-walk fact about the tail immediately below an actual
non-wrapper frame. This is neither a whole-run premise nor an admission rule. -/
def FrameRecovery (tail : Cont) (v : GoValue) (next : Cont) : Prop :=
  recoverThroughWrappers tail = some (v, next) ∨
    (recoverThroughWrappers tail = none ∧ v = .nil ∧ next = tail)

section
variable {GF : BundledGFunctors} [GoGS GF]
variable {E : CoPset} {Φ : Unit → IProp GF}

theorem wp_recover {env k v next} (h : recoverResult k = (v, next)) :
    (▷ WP (Config.retV v next) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Config.evalE .recoverCall env k) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  simp only [GateA1.recover_stepFn, h]

theorem wp_recover_direct {chain next v targets env results ds k eenv}
    (hm : markNewestRecovered chain = some (v, next)) :
    (▷ WP (Config.retV v (.frame targets env results ds (.panicResumeK next k) false))
      @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.evalE .recoverCall eenv
      (.frame targets env results ds (.panicResumeK chain k) false))
      @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_recover (recover_direct hm targets env results ds k)

theorem wp_recover_indirect {world fs k targets env results ds eenv}
    (hk : ReturnCont world fs k) :
    (▷ WP (Config.retV .nil (.frame targets env results ds k false))
      @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.evalE .recoverCall eenv (.frame targets env results ds k false))
      @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_recover (recover_indirect hk targets env results ds)

/-- The arbitrary chain may contain earlier recovered entries or equal
payloads. Only the actual newest-entry operation determines this result. -/
theorem wp_recover_rhs {rop refs done pending body env eenv rest kenv targets targetEnv results ds v k chain next}
    (hm : markNewestRecovered chain = some (v, next)) :
    (▷ WP (Config.retV v (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results ds (.panicResumeK next k) false))))
      @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.evalE .recoverCall eenv (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results ds (.panicResumeK chain k) false))))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_recover
  unfold recoverResult
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [Cont.tail]
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [Cont.tail]
  rw [Cont.rebuild_act (by rfl)]
  dsimp only
  unfold recoverThroughWrappers
  rw [Cont.rebuild_act (by rfl)]
  simp [hm, Cont.withTail]

theorem wp_defer_register {callee env k next}
    (hc : deferrableCallee callee = true) (hk : pushDefer (callee, []) k = some next) :
    (▷ WP (Config.next next) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.retV callee (.deferCalleeK [] env k))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  simp [stepFn, hc, hk]

theorem wp_recover_rhs_nil {rop refs done pending body env eenv rest kenv targets targetEnv results ds k}
    (hk : recoverThroughWrappers k = none) :
    (▷ WP (Config.retV .nil (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results ds k false))))
      @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.evalE .recoverCall eenv (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results ds k false))))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_recover
  unfold recoverResult
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [Cont.tail]
  rw [Cont.rebuild_descend (by rfl)]
  dsimp only [Cont.tail]
  rw [Cont.rebuild_act (by rfl)]
  simp [hk, Cont.withTail]

theorem wp_recover_rhs_frame {rop refs done pending body env eenv rest kenv targets targetEnv results ds k v next}
    (hk : FrameRecovery k v next) :
    (▷ WP (Config.retV v (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results ds next false))))
      @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.evalE .recoverCall eenv (.rhsK rop refs done pending body env (.seq rest kenv
      (.frame targets targetEnv results ds k false))))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  rcases hk with hk | ⟨hk, rfl, rfl⟩
  · apply wp_recover
    unfold recoverResult
    rw [Cont.rebuild_descend (by rfl)]
    dsimp only [Cont.tail]
    rw [Cont.rebuild_descend (by rfl)]
    dsimp only [Cont.tail]
    rw [Cont.rebuild_act (by rfl)]
    simp [hk, Cont.withTail]
  · exact wp_recover_rhs_nil hk

theorem wp_defer_register_args {callee done v env k next}
    (hk : pushDefer (callee, done ++ [v]) k = some next) :
    (▷ WP (Config.next next) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.retV v (.deferArgsK callee done [] env k))
      @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  simp [stepFn, hk]

theorem wp_panic_payload {v k} :
    (▷ WP (Config.panicking [⟨panicPayload v, false⟩] k)
      @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.retV v (.panicArgK k)) @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_context_step rfl (fun _ _ _ => rfl)

theorem wp_panic_strip {chain k next} (h : panicPassthrough k = some next) :
    (▷ WP (Config.panicking chain next) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.panicking chain k) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step (by cases k <;> rfl)
  intro state _ choices
  cases k <;> simp_all [panicPassthrough, Cont.isGlue, Cont.class, Cont.tail, stepFn]

theorem wp_panic_frame {chain targets env results k w} :
    (▷ WP (Config.panicking chain k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.panicking chain (.frame targets env results [] k w))
      @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_context_step rfl (fun _ _ _ => rfl)

theorem wp_panic_merge {chain suspended k} :
    (▷ WP (Config.panicking (suspended ++ chain) k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.panicking chain (.panicResumeK suspended k))
      @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_context_step rfl (fun _ _ _ => rfl)

theorem wp_resume_recovered {chain k} (h : chainNewestRecovered chain = true) :
    (▷ WP (Config.next k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.next (.panicResumeK chain k)) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  simp [stepFn, h]

theorem wp_resume_panic {chain k} (h : chainNewestRecovered chain = false) :
    (▷ WP (Config.panicking chain k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
    WP (Config.next (.panicResumeK chain k)) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_context_step rfl
  intro state _ choices
  simp [stepFn, h]

end
end GoLean.IrisCustomer
