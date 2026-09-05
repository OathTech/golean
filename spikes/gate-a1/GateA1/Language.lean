import GateA1.Counterexamples
import Iris.ProgramLogic.Lifting

/-! A thin customer over the current sequential relation. This has no
`EctxLanguage` instance, no scheduler, and no I/O adequacy claim. Refused
operations and an uncaught abort have no successful `Step` and are stuck
for this adapter. `NotStuck` proofs must exclude them; they are not values.
Lineage: parked GoLeanProofs/Lang.lean; CerberusHeapLang/Lang.lean.
-/
namespace GoLean.GateA1.Customer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.ProgramLogic.Language

instance : ToVal Config Unit where
  toVal c := match c with | .next .stop => some () | _ => none
  ofVal _ := .next .stop
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

inductive Prim : Config × ExecState → List Empty → Config × ExecState × List Config → Prop where
  | step : Step c s c' s' → Prim (c, s) [] (c', s', [])

instance : PrimStep Config ExecState (List Empty) where primStep := Prim
instance : Language Config ExecState Empty Unit where
  val_stuck h := by cases h with | step st => cases st <;> rfl
instance : Inhabited ExecState := ⟨{}⟩

/-- A stream-oblivious, state-preserving executable step gives an Iris
pure step. The inverse direction uses the current `step_complete`. -/
theorem pure_of_stepFn {c c' : Config}
    (h : ∀ s ch, stepFn s c ch = .ok (c', s, ch)) :
    Language.PurePrimStep c c' := by
  constructor
  · intro s
    exact ⟨c', s, [], Prim.step (stepFn_sound (h s []))⟩
  · intro s₁ s₂ obs c₂ forks hp
    cases hp with
    | step hs =>
      obtain ⟨ch, ch', he⟩ := step_complete hs
      rw [h] at he
      obtain ⟨hc, hp⟩ := Prod.mk.inj (Except.ok.inj he)
      obtain ⟨hσ, _⟩ := Prod.mk.inj hp
      subst hc; subst hσ
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- The sound interface keeps the continuation in the rule's parameters
AND its postcondition. No context-commutation assumption is required. -/
theorem pure_recover (env : LocalEnv) (k : Cont) :
    Language.PurePrimStep (Config.evalE .recoverCall env k)
      (.retV (recoverResult k).1 (recoverResult k).2) :=
  pure_of_stepFn (fun _ _ => rfl)

instance recover_exec (env : LocalEnv) (k : Cont) :
    PureExec True 1 (Config.evalE .recoverCall env k)
      (.retV (recoverResult k).1 (recoverResult k).2) where
  pureExec _ := Relation.Iterate.once (pure_recover env k)

/-- A real Iris WP rule over the current machine, polymorphic in the
customer's resources, state interpretation, mask and postcondition. -/
theorem wp_recover {GF : BundledGFunctors} {hlc : HasLC}
    [IrisGS_gen hlc Config GF] (env : LocalEnv) (k : Cont)
    {E : CoPset} {Φ : Unit → IProp GF} :
    (▷ (£ 1 -∗ WP (Config.retV (recoverResult k).1 (recoverResult k).2)
      @ Stuckness.NotStuck; E {{ Φ }})) ⊢
    WP (Config.evalE .recoverCall env k) @ Stuckness.NotStuck; E {{ Φ }} :=
  wp_pure_step_later (n := 1) trivial

end GoLean.GateA1.Customer
