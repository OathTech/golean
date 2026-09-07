import GoLeanIris.SharedHelpers

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

def recoveredValue (active : Bool) (bytes : GoString) : GoValue :=
  if active then .interface .string (.string bytes) else .nil

theorem wp_shared_recover_handler {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap)
    {capture root : Nat} (b active : Bool) (bytes : GoString) {k next : Cont}
    (hrecover : FrameRecovery k (recoveredValue active bytes) next)
    {Φ : Unit → IProp GF} :
    (capture ↦ (.value (.pointer .bool) (.addr (.base ⟨root⟩))) ∗
      root ↦ (.value .bool (.bool b)) ∗
      (capture ↦ (.value (.pointer .bool) (.addr (.base ⟨root⟩))) ∗
        root ↦ (.value .bool (.bool (if active then true else b))) -∗
        WP (Config.next next) @ Stuckness.NotStuck; ⊤ {{ Φ }})) ⊢
    WP (Config.exec sharedProgram.funcs[3].body [[("result$cap", .base ⟨capture⟩)]]
      (.frame [] [] [] [] k false)) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro ⟨Hcapture, Hroot, Hcont⟩
  repeat customer_pure hctx
  iapply wp_initialize (v := .bool false) (hv := by intros; rfl)
  inext
  iintro %outside Houtside
  customer_pure hctx
  iapply wp_call (world := #[]) (fid := ⟨"indirectRecover"⟩) (f := sharedProgram.funcs[1])
    (zeros := [.bool false]) shared_typed (by rw [hctx]; rfl) (by rfl)
    .nil (.boolean rfl .nil) (.direct (by rfl))
  inext
  iintro %base
  rw [show callCells sharedProgram.funcs[1] [] [.bool false] =
    [.value .bool (.bool false)] from rfl]
  simp only [ownsCells]
  iintro ⟨Hresult, _⟩
  rw [show callEnv sharedProgram.funcs[1] base = [[("result", .base ⟨base⟩)]] from rfl]
  rw [show callResults sharedProgram.funcs[1] base = [.base ⟨base⟩] from rfl]
  simp only [show sharedProgram.funcs[1].wrapper = false from rfl]
  iapply wp_indirect_body hctx (.bool false) (by
    unfold recoverThroughWrappers
    rw [Cont.rebuild_descend (by rfl)]
    dsimp only [Cont.tail]
    rw [Cont.rebuild_act (by rfl)]
    rfl)
  isplitl [Hresult]
  · iexact Hresult
  iintro Hresult
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  iapply wp_frame_result (a := base) (ty := .bool) (v := .bool true) (dq := .own 1) .returning
  isplitl [Hresult]
  · iexact Hresult
  inext
  iintro _
  repeat customer_pure hctx
  simp only [List.nil_append]
  iapply wp_store_cell (ty := .bool) (old := .bool false) (v' := .bool true)
    (hv := by intros; rfl)
  isplitl [Houtside]
  · iexact Houtside
  inext
  iintro Houtside
  repeat customer_pure hctx
  iapply wp_initialize (v := .nil) (hv := by intros; rfl)
  inext
  iintro %payload Hpayload
  customer_pure hctx
  customer_pure hctx
  customer_pure hctx
  customer_pure hctx
  iapply wp_recover_rhs_frame hrecover
  inext
  repeat customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .interface ⟨"any"⟩) (old := .nil)
    (v' := recoveredValue active bytes) (hv := by intros; cases active <;> rfl)
  isplitl [Hpayload]
  · iexact Hpayload
  inext
  iintro Hpayload
  repeat customer_pure hctx
  iapply wp_load_var (a := payload) (dq := .own 1) (ty := .interface ⟨"any"⟩)
    (v := recoveredValue active bytes) (hvar := by rfl)
  isplitl [Hpayload]
  · iexact Hpayload
  inext
  iintro _
  cases active with
  | false =>
    simp only [recoveredValue, Bool.false_eq_true, ↓reduceIte]
    repeat customer_pure hctx
    iapply Hcont
    iframe
  | true =>
    simp only [recoveredValue, ↓reduceIte]
    customer_pure hctx
    customer_pure hctx
    iapply wp_neq_interface_nil
    inext
    repeat customer_pure hctx
    iapply wp_load_var (a := capture) (dq := .own 1) (ty := .pointer .bool)
      (v := .addr (.base ⟨root⟩)) (hvar := by rfl)
    isplitl [Hcapture]
    · iexact Hcapture
    inext
    iintro Hcapture
    repeat customer_pure hctx
    iapply wp_load_var (a := outside) (dq := .own 1) (ty := .bool)
      (v := .bool true) (hvar := by rfl)
    isplitl [Houtside]
    · iexact Houtside
    inext
    iintro _
    repeat customer_pure hctx
    simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
    iapply wp_store_cell (ty := .bool) (old := .bool b) (v' := .bool true)
      (hv := by intros; rfl)
    isplitl [Hroot]
    · iexact Hroot
    inext
    iintro Hroot
    repeat customer_pure hctx
    iapply Hcont
    iframe

end GoLean.IrisCustomer
