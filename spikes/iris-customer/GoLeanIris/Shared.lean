import GoLeanIris.SharedDrain

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine GoCore.RecoveryRuntime
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

def sharedConfig (arg root : Nat) : Config :=
  .exec sharedProgram.funcs[4].body (flipEnv arg root) (.frame [] [] [] [] .stop false)

def sharedPanicBytes : GoString :=
  ⟨#[115, 104, 97, 114, 101, 100, 32, 114, 101, 99, 111, 118, 101, 114, 121]⟩

/-- Complete functional customer. It uses the same call/allocation/unwind
rules as A2 and keeps one exclusively owned result cell through two closures.
The argument selects normal return or direct recovery, producing its negation. -/
theorem wp_shared {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = sharedState heap) (arg root : Nat) (b : Bool) (old : GoValue) :
    (arg ↦ (.value .bool (.bool b)) ∗ root ↦ (.value .bool old)) ⊢
    WP (sharedConfig arg root) @ Stuckness.NotStuck; ⊤
      {{ _v, root ↦ (.value .bool (.bool (!b))) }} := by
  iintro ⟨Harg, Hroot⟩
  repeat customer_pure hctx
  iapply wp_call (world := #[]) (fid := ⟨"flip"⟩) (f := sharedProgram.funcs[0])
    (zeros := [.bool false]) shared_typed (by rw [hctx]; rfl) (by rfl)
    (.cons ⟨.boolean, .boolean, .boolean true⟩ .nil) (.boolean rfl .nil)
    (.arguments (done := []) (v := .bool true))
  inext
  iintro %base
  rw [show callCells sharedProgram.funcs[0] [.bool true] [.bool false] =
    [.value .bool (.bool true), .value .bool (.bool false)] from rfl]
  simp only [ownsCells]
  iintro ⟨HcallArg, Hresult, _⟩
  rw [show callEnv sharedProgram.funcs[0] base = flipEnv base (base + 1) from rfl]
  rw [show callResults sharedProgram.funcs[0] base = [.base ⟨base + 1⟩] from rfl]
  simp only [show sharedProgram.funcs[0].wrapper = false from rfl]
  iapply wp_flip_body hctx true (.bool false)
  isplitl [HcallArg]
  · iexact HcallArg
  isplitl [Hresult]
  · iexact Hresult
  iintro ⟨_, Hresult⟩
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, Bool.not_true]
  iapply wp_frame_result (a := base + 1) (ty := .bool) (v := .bool false)
    (dq := .own 1) .returning
  isplitl [Hresult]
  · iexact Hresult
  inext
  iintro _
  repeat customer_pure hctx
  simp only [List.nil_append]
  iapply wp_store_cell (ty := .bool) (old := old) (v' := .bool false)
    (hv := by intros; rfl)
  isplitl [Hroot]
  · iexact Hroot
  inext
  iintro Hroot
  repeat customer_pure hctx
  iapply wp_load_var (a := arg) (dq := .own 1) (ty := .bool) (v := .bool b)
    (hvar := by rfl)
  isplitl [Harg]
  · iexact Harg
  inext
  iintro _
  cases b with
  | false =>
    repeat customer_pure hctx
    have drain := wp_shared_drain hctx root false false sharedPanicBytes
    simp only [drainConfig, sharedFrame, recoverDefer, flipDefer,
      Bool.false_eq_true, ↓reduceIte] at drain
    iapply drain $$ Hroot
  | true =>
    repeat customer_pure hctx
    have drain := wp_shared_drain hctx root false true sharedPanicBytes
    simp only [drainConfig, sharedFrame, recoverDefer, flipDefer, ↓reduceIte,
      sharedPanicBytes] at drain
    simp only [panicPayload]
    iapply drain $$ Hroot

end GoLean.IrisCustomer
