import Iris.ProgramLogic.TotalWeakestPre
import Iris.ProgramLogic.TotalLifting
import Iris.ProgramLogic.TotalAdequacy
import Iris.ProofMode
import GoLeanProofs.Adequacy

/-!
# U0/A1 — the total-WP theory inhabited for GoCore's language instance

The plan of record's COMMITTED ADOPTION (docs/2026-08-28_iris-corpus-plan.md
§3, amendment A1; [USER]-approved at N-2): upstream iris-lean's
`TotalWeakestPre`/`TotalLifting`/`TotalAdequacy` (pin `e7a0a438…`, the
class's first-ever inhabitant) seated on OUR `Config`/`ExecState` language
instance. This module is the ∃-fuel row's RULE SUPPLIER (§2d's quantifier
table): every new `Terminates`-class sentence discharges through total-WP —
never through `allStreamsOk` enumeration — and G-TOTAL's variant-carrying
loop rule builds on exactly these pieces.

LINEAGE: total-correctness weakest preconditions (Floyd-style variants at
the loop rule to come; here the least-fixed-point total WP of Iris),
upstream `Iris.ProgramLogic.twp`; the adequacy readout is
`Relation.StronglyNormalizing` of the thread-pool erased step, bridged to
the sequential `Step` chain below (`sn_no_infinite_step_chain` — the joint
the ∃-fuel/`Terminates` route consumes at G-TOTAL).

Contents:
1. the instance pin (`TotalWp` for our language — by inheritance, checked);
2. total lifting for our prim steps: the pure-det core used exactly like
   `wp_lift_pure_det_step_no_fork` is on the partial side, instantiated as
   the two seqn laws `twp_seqn`/`twp_seq_done` (total twins of
   `Laws/Control.wp_seqn`/`wp_seq_done` — no later, no credit: total WP
   has no Löb to pay);
3. `go_total_adequacy` — `twp_total` seated on the GoCore ghost state
   (genHeap + pins), concluding strong normalization of the erased pool
   step from `([c], σ)`;
4. the sequential bridge `sn_no_infinite_step_chain`;
5. the charter's discharge witness: `sn_seqn_nil` — a CLOSED strong-
   normalization theorem for the empty-sequence program, assembled from
   the laws above through `go_total_adequacy` (the total twin of
   `Adequacy.adequate_seqn_nil`).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.ProgramLogic.Language.Notation Iris.BI

namespace GoLean.Iris

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The instance pin** (adoption piece 1): our `Config` language inherits
the upstream total-WP instance — `WP c @ s ; E [{ Φ }]` is inhabited
notation for GoCore. Kept as a named example so a regression (e.g. an
upstream class reshape at a future pin move) fails HERE, at the adoption
site, not at a distant use. -/
example : TotalWp (IProp GF) Config Unit Stuckness := inferInstance

/-- Total twin of `wp_seqn` (`Laws/Control.lean`): entering a statement
sequence is a pure deterministic step, so the total WP of the continuation
carries over — with no later and no credit (total WP is a least fixpoint;
there is no Löb debt to pay, which is exactly why it certifies
termination). -/
theorem twp_seqn {ss : Array Stmt} {env k} :
    WP (Config.next (seqCont ss.toList env k)) @ s ; E [{ Φ }] ⊢
      WP (Config.exec (.seqn ss) env k) @ s ; E [{ Φ }] := by
  iintro H
  iapply (twp.lift_pure_det_step_no_fork
    (e₂ := Config.next (seqCont ss.toList env k))
    (Hsafe := fun σ =>
      ⟨Config.next (seqCont ss.toList env k), σ, [], GoPrimStep.step Step.seqn⟩)
    (Hpure := by
      intro σ κ e₂' σ₂ eₜ h
      cases h with
      | step st =>
          cases st <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro $$ H

/-- Total twin of `wp_seq_done`: popping an exhausted sequence frame. -/
theorem twp_seq_done {env k} :
    WP (Config.next k) @ s ; E [{ Φ }] ⊢
      WP (Config.next (.seq [] env k)) @ s ; E [{ Φ }] := by
  iintro H
  iapply (twp.lift_pure_det_step_no_fork
    (e₂ := Config.next k)
    (Hsafe := fun σ => ⟨Config.next k, σ, [], GoPrimStep.step Step.seqDone⟩)
    (Hpure := by
      intro σ κ e₂' σ₂ eₜ h
      cases h with
      | step st =>
          cases st <;> simp_all))
  iapply fupd_intro $$ H

end

/-- **Total adequacy for GoCore** (adoption piece 3): a total-WP proof at
the trivial postcondition, under the GoCore ghost state over any
well-formed initial state, yields STRONG NORMALIZATION of the erased
thread-pool step from the singleton pool — no infinite reduction exists,
under EVERY demonic choice resolution. The postcondition is fixed to
`True` deliberately: termination needs no observation, and the
result-carrying forms arrive with G-TOTAL's rules (weakening a richer WP
to this shape is `twp.strong_mono`). Mirrors `go_adequacy`'s ghost
allocation exactly, so `Hwp`'s WP (stated under the canonical
`GoCoreGS`-derived instance) is definitionally the one `twp_total`
constructs. -/
theorem go_total_adequacy [GoCoreGpreS .hasLC GF] (c : Config) (σ : ExecState)
    (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ⊢@{IProp GF} (WP c @ Stuckness.NotStuck ; ⊤ [{ fun _ => iprop(True) }])) :
    Relation.StronglyNormalizing Language.ErasedStep ([c], σ) := by
  refine twp_total (hlc := .hasLC) (GF := GF) Stuckness.NotStuck c σ
    (fun _ => iprop(True)) 0 0 ?_
  intro _inst
  imod iOwn_alloc (E := GhostMapG.elem (K := Nat) (V := HeapCell) (H := GoHeapF))
    (HeapView.Auth (H := GoHeapF) (.own 1)
      (Std.PartialMap.map (fun v : HeapCell => toAgree (DiscreteO.mk v))
        (heapToMap σ.heap)))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem (K := Nat) (V := GName) (H := GoHeapF))
    (HeapView.Auth (H := GoHeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (DiscreteO.mk g))
        (∅ : GoHeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions, σ.methods, σ.types⟩
  imodintro
  iexists (fun σ' _ _ _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ σ'.methods = σ.methods
          ∧ σ'.types = σ.types ∧ HeapWf σ'⌝))
  iexists (fun _ => 0), (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  isplitl [Hh Hm]
  · isplitl [Hh Hm]
    · simp only [genHeapInterp]
      iexists (∅ : GoHeapF GName)
      isplitr
      · ipureintro
        intro k hk
        simp [Std.PartialMap.dom, LawfulPartialMap.get?_empty] at hk
      unfold ghost_map_auth
      iframe Hh Hm
    · ipureintro
      exact ⟨rfl, rfl, rfl, hσwf⟩
  · iintro Hcred
    iapply (Hwp rfl rfl rfl)

/-- A single sequential `Step` embeds as one erased step of the singleton
thread pool (the one-step sibling of `Adequacy.steps_erased`). -/
theorem step_erased {c c' : Config} {σ σ' : ExecState}
    (h : Step c σ c' σ') : ([c], σ) -·->ₜₚ ([c'], σ') :=
  ⟨[], Language.Step.of_primStep (GoPrimStep.step h) (t₁ := []) (t₂ := [])⟩

/-- **The sequential bridge** (adoption piece 4): strong normalization at
the singleton pool forbids any infinite sequential `Step` chain. This is
the pure-fact joint the `Terminates`/∃-fuel route consumes: at G-TOTAL,
`step_complete` turns a non-terminal `stepFn` run into a `Step`, so a
fuel-independent non-terminating execution would build exactly the chain
this refutes. -/
theorem sn_no_infinite_step_chain {c₀ : Config} {σ₀ : ExecState}
    (hsn : Relation.StronglyNormalizing Language.ErasedStep ([c₀], σ₀))
    (f : Nat → Config × ExecState) (h0 : f 0 = (c₀, σ₀))
    (hstep : ∀ n, Step (f n).1 (f n).2 (f (n + 1)).1 (f (n + 1)).2) :
    False := by
  have main : ∀ (x : List Config × ExecState),
      Acc (flip Language.ErasedStep) x →
      ∀ n, x = ([(f n).1], (f n).2) → False := by
    intro x hacc
    induction hacc with
    | intro y _hy ih =>
        intro n hyn
        refine ih ([(f (n + 1)).1], (f (n + 1)).2) ?_ (n + 1) rfl
        show Language.ErasedStep y ([(f (n + 1)).1], (f (n + 1)).2)
        rw [hyn]
        exact step_erased (hstep n)
  exact main _ hsn 0 (by rw [h0])

/-- **The discharge witness** (adoption piece 5, the charter's witness
rule): a CLOSED strong-normalization theorem — for every well-formed
initial state and environment, the empty-sequence program admits NO
infinite reduction, proved end-to-end through the total-WP laws above and
`go_total_adequacy` with the concrete functor bundle `GoCoreS`. The total
twin of `adequate_seqn_nil`: same program, same bundle, but the
conclusion is termination — the statement mentions no Iris. -/
theorem sn_seqn_nil (σ : ExecState) (env : LocalEnv) (hwf : HeapWf σ) :
    Relation.StronglyNormalizing Language.ErasedStep
      ([Config.exec (.seqn #[]) env .stop], σ) :=
  go_total_adequacy (GF := GoCoreS) _ _ hwf (by
    intro _ _ _ _
    iapply twp_seqn
    simp only [seqCont]
    iapply twp_seq_done
    iapply (twp.value (v := ()) rfl)
    itrivial)

end GoLean.Iris
