import GoLeanProofs.SurfaceBridge
import GoLeanProofs.Adequacy

/-!
# The generic exit theorem (arc `spec-surface` stages 4 + frame closure)

`goSpec_of_wp`: an Iris WP proof of `⟦P⟧ ⊢ WP prog {{ ⟦Q⟧ }}` discharges
the full NATIVE judgment `GoSpec` — the **frame-closed** triple (any heap
where the footprint is allocated; the frame survives untouched) plus
**progress** (every relation-reachable configuration is terminal or can
step). The once-proven pipe: correspondence witness → trace erasure →
initial-heap-handover adequacy, with `reflect` feeding the precondition
in, Iris's frame rule (`wp_frame_l`) carrying the frame — the user's WP
obligation never mentions it — and `extract` reading the postcondition
out. Per-program obligations are exactly: fragment shape checks and the
WP proof. Nothing else, ever (`docs/2026-07-21_native-spec-surface.md`,
the anti-hack invariant).
-/

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.GoCore.Correspondence
open GoLean.Surface

namespace GoLean.Iris

section

variable {funcs : Array Func} {env₀ : LocalEnv} {P Q : HProp} {prog : Stmt}

/-- The shared adequacy core: from the WP obligation, an `adequate` fact
whose φ carries the framed native postcondition. Both halves of `GoSpec`
read off it. -/
private theorem goSpec_adequate
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      embed (GF := GoCoreS) P
        ⊢ WP (Config.exec prog env₀ .stop) {{ _v, embed Q }})
    {hp : Heap} {na : Nat} {hP F : Heaplet}
    (hinit : InitialSplit P hp na hP F) :
    adequate .NotStuck (Config.exec prog env₀ .stop)
      (ExecState.mk (types := []) (functions := funcs) (methods := #[])
        (locals := env₀) (heap := hp) (nextAddr := na))
      (fun _ σ2 => ∃ hQ : Heaplet,
        (∀ k, hQ.get? k = none ∨ F.get? k = none)
        ∧ Heaplet.sub hQ (heapToMap σ2.heap)
        ∧ Heaplet.sub F (heapToMap σ2.heap) ∧ sat hQ Q) := by
  refine go_heap_adequacy_own (GF := GoCoreS) _ _
    (Ψ := fun _ => iprop(ownHeaplet F ∗ embed Q))
    (φ := fun _ σ2 => ∃ hQ : Heaplet,
      (∀ k, hQ.get? k = none ∨ F.get? k = none)
      ∧ Heaplet.sub hQ (heapToMap σ2.heap)
      ∧ Heaplet.sub F (heapToMap σ2.heap) ∧ sat hQ Q)
    hinit.bounded ?_ ?_
  · intro _inst hprog
    have hsplit : ownHeaplet (GF := GoCoreS) (heapToMap hp)
        ⊢ embed P ∗ ownHeaplet F := by
      rw [← heapletOf_eq_heapToMap]
      refine ((BigSepM.bigSepM_eqv_of_perm
        (cover_equiv hinit.disj hinit.cover)).1).trans ?_
      exact ((ownHeaplet_union hinit.disj).1).trans
        (sep_mono (reflect P hP hinit.sat_pre) .rfl)
    exact hsplit.trans ((BI.sep_comm.1).trans
      ((sep_mono .rfl (Hwp hprog)).trans wp_frame_l))
  · intro _inst _hprog σ2 _v
    iintro ⟨Hσ, HF, HQ⟩
    icases (embed_toHeaplet Q) $$ HQ with ⟨%hQ, %hsQ, HownQ⟩
    ihave %hdisjQF := ownHeaplet_disjoint $$ [$HownQ $HF]
    ihave HU := (ownHeaplet_union hdisjQF).2 $$ [$HownQ $HF]
    ihave %hsub := ownHeaplet_sub $$ [$Hσ $HU]
    imodintro
    ipureintro
    obtain ⟨h1, h2⟩ := sub_union_split hdisjQF hsub
    exact ⟨hQ, hdisjQF, h1, h2, hsQ⟩

/-- **The generic exit theorem.** Premises:
- `hfrag`/`hfuncs` — the v1 fragment shape checks (mechanical);
- `Hwp` — the real proof: the embedded precondition WPs the program to the
  embedded postcondition, over the concrete bundle `GoCoreS` with the
  function table pinned. The frame never appears — Iris's frame rule
  carries it inside the pipe.
Conclusion: the full native judgment — frame-closed triple + progress. -/
theorem goSpec_of_wp
    (hfrag : StmtFragNS prog)
    (hfuncs : FuncsFrag funcs)
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      embed (GF := GoCoreS) P
        ⊢ WP (Config.exec prog env₀ .stop) {{ _v, embed Q }}) :
    GoSpec funcs env₀ P prog Q := by
  constructor
  · -- the frame-closed triple
    intro hp na hP F hinit fuel ch σf ch' hrun
    have hinv : StInv (ExecState.mk (types := []) (functions := funcs)
        (methods := #[]) (locals := env₀) (heap := hp) (nextAddr := na)) :=
      ⟨hinit.frag, rfl, hfuncs⟩
    have hsteps := interpreterSound_frag fuel _ σf prog ch ch' hfrag hinv hrun
    have htp := steps_erased hsteps
    have hres := (goSpec_adequate Hwp hinit).adequate_result [] σf () htp
    obtain ⟨hQ, hd, h1, h2, hs⟩ := hres
    exact ⟨hQ, hd, by rw [heapletOf_eq_heapToMap]; exact h1,
      by rw [heapletOf_eq_heapToMap]; exact h2, hs⟩
  · -- progress
    intro hp na hP F hinit c' σ' hsteps
    have htp := steps_erased hsteps
    have hns := (goSpec_adequate Hwp hinit).adequate_not_stuck
      [c'] σ' c' rfl htp (by simp)
    rcases hns with hval | hred
    · left
      cases c' with
      | next k => cases k <;> simp_all [ToVal.toVal]
      | _ => simp_all [ToVal.toVal]
    · right
      obtain ⟨_obs, c'', σ'', _eₜ, hstep⟩ := hred
      cases hstep with
      | step h => exact ⟨_, _, h⟩

/-- The triple half alone, for consumers that only need it. -/
theorem goTriple_of_wp
    (hfrag : StmtFragNS prog)
    (hfuncs : FuncsFrag funcs)
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      embed (GF := GoCoreS) P
        ⊢ WP (Config.exec prog env₀ .stop) {{ _v, embed Q }}) :
    GoTriple funcs env₀ P prog Q :=
  (goSpec_of_wp hfrag hfuncs Hwp).1

end

end GoLean.Iris
