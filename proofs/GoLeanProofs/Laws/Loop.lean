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
import GoLeanProofs.Lifting
import GoLeanProofs.Inversions
import GoLeanProofs.Laws.Assign

/-!
# Loop laws (arc E rung B1, `docs/2026-07-22_arc-e-while-invariant.md`)

The while-invariant WP law: a partial-correctness Hoare while-rule over
the CK machine, proven by Löb induction, **mirroring Goose/Perennial's
`wp_forBreak_cond` shape** (user direction 2026-07-22: follow the
established Iris-project structure, generalize early): the loop invariant
is `I : Bool → IProp` — arbitrary resources indexed by the condition's
value — so multi-cell footprints, pure facts, and (later) ghost state all
fit; `I false` is what the exit continuation receives. The single-cell
counter witness below is an *instance*, not the primitive.

Recorded divergence from HeapLang/Goose (not a reinvention): they route
the loop condition through `wp_bind` as a sub-expression WP; our CK
machine has no bind and `ExprR` is premise-level (same fact that makes
`wp_atomic` inapplicable — see `wp_store_step₂_inv`). So the condition
arrives as a resource-conditioned operational premise (`Hcond`). If
expression evaluation ever moves into the configuration language (the
tracked note in `Rel.lean`), revisit these laws toward the bind form.

Body scope (v1): the body premise speaks only of normal completion —
`break`/`continue`/`return` inside the body are outside this law. Their
loop-side step rules exist (`loopBreak/Continue/Return`), and the
`Bool`-indexed `I` is exactly the shape Goose uses to add them (break ⇒
`I false` early); laws arrive with a witness that needs them, fail-closed
until then.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- Pure, deterministic step: the loop back edge — normal body completion
re-enters the `while` (`Step.loopNext`). The `▷` slot in the premise is
where the Löb hypothesis strips. -/
theorem wp_loop_next {c : Expr} {b : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.loop c b env k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E)
    (e₂ := Config.exec (.while c b) env k)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], _, σ, [], GoPrimStep.step Step.loopNext⟩
      · rfl)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st => cases st; exact ⟨rfl, rfl, rfl, rfl⟩))
  iexact H

/-- **The while-invariant law** (Hoare while-rule, partial correctness;
the Goose `wp_forBreak_cond` shape adapted to the CK machine).
`I : Bool → IProp` is the loop invariant indexed by the condition's
value. Premises:
- `Hcond` — from the state interpretation and `I d`, the condition
  evaluates (deterministically) to `d`. This is the premise-level stand-in
  for Goose's `wp_bind` over the condition (module docstring); determinism
  also excludes the `whilePanic` rule by inversion.
- `Hbody` — one body iteration, continuation-passing: from `I true`, run
  the body and re-establish `I` at some condition value. A Lean-level
  premise, hence freely reusable across iterations (the □ of Goose's
  persistent body spec, for free).

Conclusion: from `I` at any condition value, the loop runs safely and the
exit continuation receives `I false`.

Partial correctness, honestly: an infinite loop satisfies this vacuously
at the postcondition layer (progress/safety still real). Termination is
out of scope until liveness (F5 tier 2). Proven by Löb induction
(`iloeb`): the back-edge step (`wp_loop_next`) strips the `▷` on the
induction hypothesis. -/
theorem wp_while_inv {c : Expr} {b : Stmt} {env k} {I : Bool → IProp GF}
    (Hcond : ∀ (σ₁ : ExecState) (d : Bool),
      iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ₁.heap) ∗ I d)
        ⊢ |==> ⌜ExprR env σ₁ c (.value (.bool d) σ₁)
            ∧ ∀ out, ExprR env σ₁ c out → out = .value (.bool d) σ₁⌝)
    (Hbody : iprop(I true
        ∗ ((∃ d, I d) -∗ WP (Config.next (.loop c b env k)) @ s ; E {{ Φ }}))
        ⊢ WP (Config.exec b env (.loop c b env k)) @ s ; E {{ Φ }}) :
    iprop((∃ d, I d)
      ∗ (I false -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.exec (.while c b) env k) @ s ; E {{ Φ }} := by
  apply BI.wand_entails
  iloeb as IH
  iintro ⟨⟨%d, HId⟩, Hexit⟩
  cases d with
  | false =>
    iapply (wp_det_step_keep (P := I false) (c₁ := Config.next k)
      (hnv := rfl)
      (hred := fun σ₁ =>
        (Hcond σ₁ false).trans (bupd_mono (BI.pure_mono
          fun ⟨hev, hdet⟩ =>
            ⟨Step.whileFalse hev, by
              intro c' s' hst
              cases hst with
              | whileTrue h =>
                have := hdet _ h
                injection this with hv _
                cases hv
              | whileFalse h =>
                have := hdet _ h
                injection this with _ hs
                exact ⟨rfl, hs⟩
              | whilePanic h =>
                exact ExprOut.noConfusion (hdet _ h)⟩))))
    isplitl [HId]
    · iexact HId
    iintro HId
    iapply Hexit $$ HId
  | true =>
    iapply (wp_det_step_keep (P := I true)
      (c₁ := Config.exec b env (.loop c b env k))
      (hnv := rfl)
      (hred := fun σ₁ =>
        (Hcond σ₁ true).trans (bupd_mono (BI.pure_mono
          fun ⟨hev, hdet⟩ =>
            ⟨Step.whileTrue hev, by
              intro c' s' hst
              cases hst with
              | whileTrue h =>
                have := hdet _ h
                injection this with _ hs
                exact ⟨rfl, hs⟩
              | whileFalse h =>
                have := hdet _ h
                injection this with hv _
                cases hv
              | whilePanic h =>
                exact ExprOut.noConfusion (hdet _ h)⟩))))
    isplitl [HId]
    · iexact HId
    iintro HId
    iapply Hbody
    isplitl [HId]
    · iexact HId
    iintro HId'
    iapply wp_loop_next
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred
    iapply IH
    isplitl [HId']
    · iexact HId'
    · iexact Hexit

/-- **The discharge witness: `while (x == 0) { x = x + 1 }`** — the
eq-conditioned single-iteration loop pinned by the corpus guardrail
`control-flow/while-eq-single-iteration` (differential PASS). Instantiates
`wp_while_inv` with the `Bool`-indexed invariant
`I d := ∃ n ∈ {0,1}, ⌜(n == 0) = d⌝ ∗ x ↦ n`: from `{x ↦ 0}` the loop
delivers `{x ↦ 1}`. Every premise discharged (condition via
`exprR_var_eq_lit`(`_det`), body via `wp_var_inc`). HONEST SCOPE (design
note §1): with only `eqCmp` in `ExprR`, a terminating loop's condition
flips after one iteration — this witness exercises the full Löb cycle
(true branch, body, back edge, IH, false branch, exit) but only one
iteration; the multi-iteration witness arrives with the `ltCmp` semantics
widening (rung B2). -/
theorem wp_while_eq_once {xa : Addr} {x : String} {env k}
    (hres : LocalEnv.lookup env x = some (.base xa)) :
    xa.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (xa.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.while (.eqCmp (.int .int) (.var x) (.intLit 0 .int))
              (.assign (.var x) (.add (.var x) (.intLit 1 .int)))) env k)
          @ s ; E {{ Φ }} := by
  have hnorm : IntKind.normalize .int 0 = 0 := by decide
  iintro ⟨Hpt, Hcont⟩
  iapply (wp_while_inv
    (I := fun d => iprop(∃ n : Int,
      ⌜(n = 0 ∨ n = 1) ∧ (n == 0) = d⌝
        ∗ xa.id ↦ (⟨some (.int .int), .int n .int⟩ : HeapCell)))
    (Hcond := by
      intro σ₁ d
      iintro ⟨Hσ, ⟨%n, %hn, Hpt⟩⟩
      obtain ⟨h01, hnd⟩ := hn
      imod genHeap_valid $$ [$Hσ $Hpt] with %Hmap
      have hlook : Heap.lookup σ₁.heap (.base xa)
          = some ⟨some (.int .int), .int n .int⟩ := by
        rw [get?_heapToMap] at Hmap; simpa using Hmap
      imodintro
      ipureintro
      constructor
      · have h := exprR_var_eq_lit (z := 0) hres hlook
        rw [hnorm, hnd] at h
        exact h
      · intro out hout
        have h := exprR_var_eq_lit_det (z := 0) hres hlook hout
        rw [hnorm, hnd] at h
        exact h)
    (Hbody := by
      iintro ⟨⟨%n, %hn, Hpt⟩, Hk⟩
      obtain ⟨h01, hnd⟩ := hn
      have hn0 : n = 0 := by
        rcases h01 with rfl | rfl
        · rfl
        · simp at hnd
      subst hn0
      iapply (wp_var_inc (a := xa) (kind := .int) (m := 0) (lit := 1) hres)
      isplitl [Hpt]
      · iexact Hpt
      iintro Hpt
      rw [show varIncCell .int 0 1
          = (⟨some (.int .int), .int 1 .int⟩ : HeapCell) from by
        show (⟨some (.int .int),
          .int (IntKind.normalize .int (0 + IntKind.normalize .int 1))
            .int⟩ : HeapCell) = _
        rw [show IntKind.normalize .int (0 + IntKind.normalize .int 1) = 1
          from by decide]]
      iapply Hk
      iexists false
      iexists (1 : Int)
      isplitl []
      · ipureintro
        exact ⟨Or.inr rfl, by decide⟩
      · iexact Hpt))
  isplitl [Hpt]
  · iexists true
    iexists (0 : Int)
    isplitl []
    · ipureintro
      exact ⟨Or.inl rfl, by decide⟩
    · iexact Hpt
  · iintro ⟨%n, %hn, Hpt2⟩
    obtain ⟨h01, hnd⟩ := hn
    have hn1 : n = 1 := by
      rcases h01 with rfl | rfl
      · simp at hnd
      · rfl
    subst hn1
    iapply Hcont $$ Hpt2

end

end GoLean.Iris
