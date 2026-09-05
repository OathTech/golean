import GoLeanIris.Rules
import GoLeanIris.Adequacy
import GoLeanIris.Program

namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

def programState (heap : Heap := #[]) : ExecState :=
  { types := recoveryProgram.typeDefs, functions := recoveryProgram.funcs,
    methods := recoveryProgram.methods, methodSets := recoveryProgram.methodSets,
    typeDisplays := recoveryProgram.typeDisplays, heap }

def normalConfig (a : Nat) : Config :=
  .exec recoveryProgram.funcs[3].body [[("result", .base ⟨a⟩)]]
    (.frame [] [] [] [] .stop false)

/-- Each use proves ONE actual context-preserving machine step. This small
macro only composes the public lifting rule with kernel-checked reduction;
it does not evaluate a whole run or trust a generated trace certificate. -/
macro "customer_pure " hctx:term : tactic => `(tactic|
  (try simp only [seqCont, if_pos rfl]
   iapply wp_context_step (hnv := by rfl) (hred := by
    intro state h choices
    unfold ContextEq at h
    rw [($hctx)] at h
    rw [h]
    first
    | rfl
    | simp only [stepFn, pushDefer, Cont.rebuild, Cont.class, Cont.tail, Cont.withTail]
      rfl
    )
   inext))

theorem wp_normal {GF : BundledGFunctors} [GoGS GF]
    {heap : Heap} (hctx : GoGS.context GF = programState heap)
    (a : Nat) (old : GoValue) :
    (a ↦ (.value .bool old)) ⊢
      WP (normalConfig a) @ Stuckness.NotStuck; ⊤ {{ _v, a ↦ (.value .bool (.bool true)) }} := by
  iintro Hr
  customer_pure hctx
  repeat customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .bool) (old := old) (v' := .bool true) (hv := by intros; rfl)
  isplitl [Hr]
  · iexact Hr
  inext
  iintro Hr
  repeat customer_pure hctx
  iapply wp_value' (v := ())
  iexact Hr

def recoveredConfig (a : Nat) : Config :=
  .exec recoveryProgram.funcs[2].body [[("result", .base ⟨a⟩)]]
    (.frame [] [] [] [] .stop false)

theorem enter_fail (heap : Heap) :
    enterFrame (programState heap) ⟨"fail"⟩ [] =
      .ok (recoveryProgram.funcs[0], [], [], programState heap) := by
  with_unfolding_all rfl

theorem wp_call_fail {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = programState heap) {env : LocalEnv} {k : Cont}
    {Φ : Unit → IProp GF} :
    (▷ WP (Config.exec recoveryProgram.funcs[0].body [] (.frame [] env [] [] k false))
      @ Stuckness.NotStuck; ⊤ {{ Φ }}) ⊢
    WP (Config.exec (.call #[] ⟨"fail"⟩ #[]) env k) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  apply wp_context_step rfl
  intro state h choices
  unfold ContextEq at h
  rw [hctx] at h
  rw [h]
  with_unfolding_all rfl

def handlerConfig (p : Nat) (chain : List PanicEntry) : Config :=
  .exec recoveryProgram.funcs[1].body [[("result$cap", .base ⟨p⟩)]]
    (.frame [] [] [] [] (.panicResumeK chain (.frame [] [] [] [] .stop false)) false)

abbrev customerPanic : GoValue :=
  .interface .string (.string ⟨#[99, 117, 115, 116, 111, 109, 101, 114, 32, 112, 97, 110, 105, 99]⟩)

theorem wp_enter_deferred {GF : BundledGFunctors} [GoGS GF] {heap : Heap}
    (hctx : GoGS.context GF = programState heap) (a : Nat) (chain : List PanicEntry)
    {Φ : Unit → IProp GF} :
    (▷ ∀ p : Nat, p ↦ (.value (.pointer .bool) (.addr (.base ⟨a⟩))) -∗
      WP (handlerConfig p chain) @ Stuckness.NotStuck; ⊤ {{ Φ }}) ⊢
    WP (Config.panicking chain (.frame [] [] []
      [(.funcVal ⟨"Recovered$lit0"⟩ [.addr (.base ⟨a⟩)], [])] .stop false))
      @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  apply wp_alloc_step (handlerConfig · chain) rfl
  intro state h choices
  unfold ContextEq at h
  rw [hctx] at h
  rw [h]
  with_unfolding_all rfl

theorem wp_recovered {GF : BundledGFunctors} [GoGS GF]
    {heap : Heap} (hctx : GoGS.context GF = programState heap)
    (a : Nat) (old : GoValue) :
    (a ↦ (.value .bool old)) ⊢
      WP (recoveredConfig a) @ Stuckness.NotStuck; ⊤ {{ _v, a ↦ (.value .bool (.bool true)) }} := by
  iintro Hr
  repeat customer_pure hctx
  iapply wp_call_fail hctx
  inext
  repeat customer_pure hctx
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
  iapply wp_enter_deferred hctx a
  inext
  iintro %p Hp
  repeat customer_pure hctx
  iapply wp_initialize (v := .nil) (hv := by intros; rfl)
  inext
  iintro %t Ht
  customer_pure hctx
  customer_pure hctx
  customer_pure hctx
  customer_pure hctx
  iapply wp_recover_assignment
  inext
  customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .interface ⟨"any"⟩) (old := .nil)
    (hv := by intros; rfl)
  isplitl [Ht]
  · iexact Ht
  inext
  iintro Ht
  repeat customer_pure hctx
  simp only [panicPayload]
  iapply wp_load_var (a := t) (dq := .own 1) (ty := .interface ⟨"any"⟩) (v := customerPanic)
    (hvar := by rfl)
  isplitl [Ht]
  · iexact Ht
  inext
  iintro Ht
  customer_pure hctx
  customer_pure hctx
  iapply wp_neq_interface_nil
  inext
  repeat customer_pure hctx
  iapply wp_load_var (a := p) (dq := .own 1) (ty := .pointer .bool)
    (v := .addr (.base ⟨a⟩)) (hvar := by rfl)
  isplitl [Hp]
  · iexact Hp
  inext
  iintro Hp
  repeat customer_pure hctx
  simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
  iapply wp_store_cell (ty := .bool) (old := old) (v' := .bool true)
    (hv := by intros; rfl)
  isplitl [Hr]
  · iexact Hr
  inext
  iintro Hr
  repeat customer_pure hctx
  iapply wp_value' (v := ())
  iexact Hr


end GoLean.IrisCustomer
