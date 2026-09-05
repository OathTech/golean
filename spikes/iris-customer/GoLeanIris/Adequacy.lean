import GoLeanIris.Ghost
import GateA1.Trace

/-! Adequacy hands the concrete initial heap to the client and extracts a
final-state fact. Proof pattern: archived GoLean GoLeanProofs/Adequacy.lean,
reworked for the current dense heap and complete context equality. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap Iris.BI
open Iris.ProgramLogic.Language.Notation

theorem steps_erased {c c' : Config} {state state' : ExecState}
    (h : Steps c state c' state') : ([c], state) -·->ₜₚ* ([c'], state') := by
  induction h with
  | refl => exact .refl
  | tail hab hstep ih =>
    exact FromMathlib.Relation.ReflTransGen.tail ih ⟨[], Language.Step.of_primStep
      (GateA1.Customer.Prim.step hstep) (t₁ := []) (t₂ := [])⟩

theorem heap_adequacy {GF : BundledGFunctors} [GoGpreS GF]
    (c : Config) (state : ExecState)
    (Ψ : ∀ [GoGS GF], Unit → IProp GF) (φ : Unit → ExecState → Prop)
    (Hwp : ∀ [GoGS GF], GoGS.context GF = state →
      iprop([∗map] l ↦ cell ∈ heapToMap state.heap, l ↦ cell) ⊢
        WP c @ Stuckness.NotStuck; ⊤ {{ v, Ψ v }})
    (Hext : ∀ [GoGS GF], GoGS.context GF = state →
      ∀ (state' : ExecState) (v : Unit),
        iprop(genHeapInterp (GF := GF) (H := HeapMap) (heapToMap state'.heap) ∗ Ψ v)
          ⊢ |==> ⌜φ v state'⌝) :
    adequate .NotStuck c state φ := by
  refine (adequate_alt _ c state φ).mpr ?_
  intro t2 state2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) .NotStuck
    (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
  imod (genHeap_init_names (GF := GF) (heapToMap state.heap))
    with ⟨%γh, %γm, Hstate, Hpts, Htok⟩
  letI : GoGS GF := ⟨⟨γh, γm⟩, state⟩
  imodintro
  iexists (fun state' _ _ _ =>
    iprop(genHeapInterp (GF := GF) (H := HeapMap) (heapToMap state'.heap) ∗
      ⌜ContextEq state' state⌝))
  iexists [(fun v => Ψ v)], (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [Hstate]
  · isplitl [Hstate]
    · iexact Hstate
    · ipureintro; rfl
  isplitl [Hpts]
  · iapply BigSepL2.bigSepL2_singleton
    iapply (Hwp rfl) $$ Hpts
  iintro %es' %t2' %Heq %Hlen %HNS Hst Hwptp _
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hwptp with ⟨%e', %_, %Heq', Hpost, H⟩
  subst Heq' Heq
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq
  subst Heq
  icases Hst with ⟨Hgh, %Hpure⟩
  cases h : toVal e'
  · iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind
  · dsimp only [Option.elim_some]
    imod (Hext rfl state2 _) $$ [$Hgh $Hpost] with %Hφv
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind

/-- A caller can use the Iris adequacy result directly on the interpreter's
successful execution. Fuel and the choice stream are not erased in the
premise; the A1 counted trace supplies the relational execution. -/
theorem adequate_execStmtLoop {c : Config} {state final : ExecState}
    {fuel : Nat} {choices residual : Choices} {φ : ExecState → Prop}
    (ha : adequate .NotStuck c state (fun _ s => φ s))
    (hr : execStmtLoop fuel state c choices = .ok (final, residual)) : φ final := by
  obtain ⟨n, _, ht⟩ := GateA1.run_ok_iff.mp hr
  exact ha.adequate_result [] final () (steps_erased ht.erase)

end GoLean.IrisCustomer
