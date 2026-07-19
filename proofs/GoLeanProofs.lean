import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProofMode
import GoLean.GoCore.Rel

/-!
# GoCore ⊳ Iris — the proof layer

Instantiates iris-lean's bare `Language` (no evaluation contexts) on GoCore's
**real** reshaped relation: `Config` (state-free control, the Iris `Expr` after
Reshape A) with `ExecState` as the Iris `State`, and `Step` as the primitive
reduction. This is the port of the validated toy spike
(`docs/2026-07-18_iris-spike-result.md`) onto the real semantics.

`IrisGS_gen` + gen_heap over the real heap and the `wp_store`/`wp_load` laws
follow in the next step (they need gen_heap wired over `ExecState.heap`).
-/

open Iris Iris.ProgramLogic
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

/-- Iris `Val` is unit; the terminal control configuration is `.next .stop`
(a GoCore statement run produces no value — results are written to caller heap
locations, so the content lives in the `State`). -/
instance : ToVal Config Unit where
  toVal c := match c with | .next .stop => some () | _ => none
  ofVal _ := .next .stop
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

/-- The Iris primitive step: GoCore's small-step `Step`, with no observations
and no forked threads (the sequential relation forks nothing). -/
inductive GoPrimStep :
    Config × ExecState → List Unit → Config × ExecState × List Config → Prop where
  | step {c s c' s'} : Step c s c' s' → GoPrimStep (c, s) [] (c', s', [])

instance : PrimStep Config ExecState (List Unit) where
  primStep := GoPrimStep

/-- The bare `Language` instance: a CK machine seats on iris-lean directly, with
no `EctxLanguage`. `val_stuck` holds because no `Step` rule has `.next .stop` as
its source — the terminal control is irreducible. -/
instance : Language Config ExecState Unit Unit where
  val_stuck h := by
    cases h with
    | step st => cases st <;> rfl

instance : Inhabited ExecState := ⟨{}⟩

/-! ## Step 3a — a real WP law over GoCore's `Step` (pure control, no gen_heap)

Assumes the invariant+credit cameras `[InvGS_gen hlc GF]` (as HeapLang's WP laws
assume `[HeapLangGS]`), a trivial state interpretation (step 3b replaces it with
gen_heap over `ExecState.heap`), and derives `IrisGS_gen`. Then proves a WP rule
for `seqn` — a pure deterministic control step — validating iris-lean's WP
machinery on the real relation. -/

section PureWP
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]

/-- Trivial state interpretation (no heap reasoning yet). `Obs = Unit`. -/
instance : StateInterp ExecState Unit GF where
  stateInterp _ _ _ _ := iprop(True)

instance : IrisGS_gen hlc Config GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- `seqn` is a pure, deterministic control step: `.exec (.seqn ss) k` reduces
only to `.next (.seq ss.toList k)` with the state unchanged. This is a genuine
weakest-precondition law over GoCore's actual `Step` relation. -/
theorem wp_seqn {ss k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next (.seq ss.toList k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.seqn ss) k) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.next (.seq ss.toList k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], Config.next (.seq ss.toList k), σ, [], GoPrimStep.step Step.seqn⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

end PureWP

end GoLean.Iris
