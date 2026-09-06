import GoLeanIris.Examples
import GoLeanIris.SharedProgram
import GoLeanIris.Return

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

def flipEnv (arg result : Nat) : LocalEnv :=
  [[("result", .base ⟨result⟩), ("b", .base ⟨arg⟩)]]

/-- Functional proof of the ordinary helper, parameterized by its caller's
actual continuation and result-target plan. The result resource is handed
back for the shared writeback rule. -/
theorem wp_flip_body {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap)
    {arg result : Nat} (b : Bool) (old : GoValue) {plans env k}
    {Φ : Unit → IProp GF} :
    (arg ↦ (.value .bool (.bool b)) ∗ result ↦ (.value .bool old) ∗
      (arg ↦ (.value .bool (.bool b)) ∗ result ↦ (.value .bool (.bool (!b))) -∗
        WP (Config.signal .ret (.frame plans env [.base ⟨result⟩] [] k false))
          @ Stuckness.NotStuck; ⊤ {{ Φ }})) ⊢
    WP (Config.exec sharedProgram.funcs[0].body (flipEnv arg result)
      (.frame plans env [.base ⟨result⟩] [] k false))
      @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro ⟨Harg, Hresult, Hcont⟩
  repeat customer_pure hctx
  iapply wp_load_var (a := arg) (dq := .own 1) (ty := .bool) (v := .bool b)
    (hvar := by rfl)
  isplitl [Harg]
  · iexact Harg
  inext
  iintro Harg
  repeat customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .bool) (old := old) (v' := .bool (!b))
    (hv := by intros; rfl)
  isplitl [Hresult]
  · iexact Hresult
  inext
  iintro Hresult
  repeat customer_pure hctx
  iapply Hcont
  iframe

theorem wp_shared_flip_handler {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap)
    {capture root : Nat} (b : Bool) {k : Cont} {Φ : Unit → IProp GF} :
    (capture ↦ (.value (.pointer .bool) (.addr (.base ⟨root⟩))) ∗
      root ↦ (.value .bool (.bool b)) ∗
      (capture ↦ (.value (.pointer .bool) (.addr (.base ⟨root⟩))) ∗
        root ↦ (.value .bool (.bool (!b))) -∗
        WP (Config.next k) @ Stuckness.NotStuck; ⊤ {{ Φ }})) ⊢
    WP (Config.exec sharedProgram.funcs[2].body [[("result$cap", .base ⟨capture⟩)]]
      (.frame [] [] [] [] k false)) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro ⟨Hcapture, Hroot, Hcont⟩
  repeat customer_pure hctx
  iapply wp_load_var (a := capture) (dq := .own 1) (ty := .pointer .bool)
    (v := .addr (.base ⟨root⟩)) (hvar := by rfl)
  isplitl [Hcapture]
  · iexact Hcapture
  inext
  iintro Hcapture
  iapply wp_deref_cell (a := root) (ty := .bool) (v := .bool b) (dq := .own 1)
  isplitl [Hroot]
  · iexact Hroot
  inext
  iintro Hroot
  iapply wp_call (world := #[]) (fid := ⟨"flip"⟩) (f := sharedProgram.funcs[0])
    (zeros := [.bool false]) shared_typed (by rw [hctx]; rfl) (by rfl)
    (.cons ⟨.boolean, .boolean, .boolean b⟩ .nil) (.boolean rfl .nil)
    (.arguments (done := []) (v := .bool b))
  inext
  iintro %base
  rw [show callCells sharedProgram.funcs[0] [.bool b] [.bool false] =
    [.value .bool (.bool b), .value .bool (.bool false)] from rfl]
  simp only [ownsCells]
  iintro ⟨Harg, Hresult, _⟩
  rw [show callEnv sharedProgram.funcs[0] base = flipEnv base (base + 1) from rfl]
  rw [show callResults sharedProgram.funcs[0] base = [.base ⟨base + 1⟩] from rfl]
  simp only [show sharedProgram.funcs[0].wrapper = false from rfl]
  iapply wp_flip_body hctx b (.bool false)
  isplitl [Harg]
  · iexact Harg
  isplitl [Hresult]
  · iexact Hresult
  iintro ⟨_, Hresult⟩
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  iapply wp_frame_result (a := base + 1) (ty := .bool) (v := .bool (!b))
    (dq := .own 1) .returning
  isplitl [Hresult]
  · iexact Hresult
  inext
  iintro _
  iapply wp_load_var (a := capture) (dq := .own 1) (ty := .pointer .bool)
    (v := .addr (.base ⟨root⟩)) (hvar := by rfl)
  isplitl [Hcapture]
  · iexact Hcapture
  inext
  iintro Hcapture
  repeat customer_pure hctx
  simp only [List.nil_append]
  iapply wp_store_cell (ty := .bool) (old := .bool b) (v' := .bool (!b))
    (hv := by intros; rfl)
  isplitl [Hroot]
  · iexact Hroot
  inext
  iintro Hroot
  repeat customer_pure hctx
  iapply Hcont
  iframe

theorem wp_indirect_body {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap)
    {result : Nat} (old : GoValue) {plans env k} (hk : recoverThroughWrappers k = none)
    {Φ : Unit → IProp GF} :
    (result ↦ (.value .bool old) ∗
      (result ↦ (.value .bool (.bool true)) -∗
        WP (Config.signal .ret (.frame plans env [.base ⟨result⟩] [] k false))
          @ Stuckness.NotStuck; ⊤ {{ Φ }})) ⊢
    WP (Config.exec sharedProgram.funcs[1].body [[("result", .base ⟨result⟩)]]
      (.frame plans env [.base ⟨result⟩] [] k false))
      @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro ⟨Hresult, Hcont⟩
  repeat customer_pure hctx
  iapply wp_initialize (v := .nil) (hv := by intros; rfl)
  inext
  iintro %localCell Hlocal
  customer_pure hctx
  customer_pure hctx
  customer_pure hctx
  customer_pure hctx
  iapply wp_recover_rhs_nil hk
  inext
  repeat customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .interface ⟨"any"⟩) (old := .nil) (v' := .nil)
    (hv := by intros; rfl)
  isplitl [Hlocal]
  · iexact Hlocal
  inext
  iintro Hlocal
  repeat customer_pure hctx
  iapply wp_load_var (a := localCell) (dq := .own 1) (ty := .interface ⟨"any"⟩)
    (v := .nil) (hvar := by rfl)
  isplitl [Hlocal]
  · iexact Hlocal
  inext
  iintro _
  repeat customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .bool) (old := old) (v' := .bool true)
    (hv := by intros; rfl)
  isplitl [Hresult]
  · iexact Hresult
  inext
  iintro Hresult
  repeat customer_pure hctx
  iapply Hcont $$ Hresult

end GoLean.IrisCustomer
