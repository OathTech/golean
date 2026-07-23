import GoLeanProofs.SurfaceBridge
import GoLeanProofs.Adequacy
import Iris.Instances.Lib.Invariants

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

/-- **The invariance exit theorem** (arc `invariant-readout`, design of
record `docs/2026-07-22_invariant-readout-design.md` §6): from a WP proof
with **trivial postcondition** that works with `I` held in an Iris
invariant (∀-quantified namespace) beside the residual precondition `P'`,
the NATIVE invariance judgment `GoInvariant`: every relation-reachable
configuration has a sub-heaplet satisfying `I`.

The once-proven pipe: reflect the initial split; allocate
`inv nroot (embed I)` from `I`'s footprint — **persistence is the
transport** (design note §2): the extraction wand receives only the state
interpretation at the reachable state, and the persistent invariant token
is the one resource that crosses to it; at the reachable state, open the
invariant against the state interpretation, strip the later
(`embed_timeless`), and read the sub-heaplet out (`embed_toHeaplet` +
`ownHeaplet_sub`). Per-program obligations: the WP proof (which must
respect the per-atomic-step preservation discipline for `I`'s footprint —
e.g. `wp_frame_return_inv`). Nothing else, ever. -/
theorem goInvariant_of_wp {I P' : HProp}
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      ∀ N : Namespace,
        iprop(Iris.inv N (embed (GF := GoCoreS) I) ∗ embed (GF := GoCoreS) P')
          ⊢ WP (Config.exec prog env₀ .stop) {{ _v, iprop(True) }}) :
    GoInvariant funcs env₀ (.sep I P') prog I := by
  intro hp na hP F hinit c' σ' hsteps
  have htp := steps_erased hsteps
  suffices h : ∃ hI : Heaplet, Heaplet.sub hI (heapToMap σ'.heap) ∧ sat hI I by
    obtain ⟨hI, hsub, hsat⟩ := h
    exact ⟨hI, by rw [heapletOf_eq_heapToMap]; exact hsub, hsat⟩
  refine go_heap_invariance (GF := GoCoreS)
    (Config.exec prog env₀ .stop)
    (ExecState.mk (types := []) (functions := funcs) (methods := #[])
      (locals := env₀) (heap := hp) (nextAddr := na))
    [c'] σ' _ hinit.bounded ?_ htp
  intro _inst hprog
  have hsplit : ownHeaplet (GF := GoCoreS) (heapToMap hp)
      ⊢ iprop((embed I ∗ embed P') ∗ ownHeaplet F) := by
    rw [← heapletOf_eq_heapToMap]
    refine ((BigSepM.bigSepM_eqv_of_perm
      (cover_equiv hinit.disj hinit.cover)).1).trans ?_
    exact ((ownHeaplet_union hinit.disj).1).trans
      (sep_mono (reflect (.sep I P') hP hinit.sat_pre) .rfl)
  show ownHeaplet (GF := GoCoreS) (heapToMap hp) ⊢ _
  iintro Hpts
  icases hsplit $$ Hpts with ⟨⟨HI0, HP'⟩, -⟩
  ihave HIlater : iprop(▷ embed (GF := GoCoreS) I) $$ [HI0]
  · inext
    iexact HI0
  imod (inv_alloc nroot ⊤ (embed I)) $$ HIlater with #HinvT
  imodintro
  isplitl [HP']
  · iapply (Hwp hprog nroot)
    isplitl []
    · iexact HinvT
    · iexact HP'
  iintro Hgh
  iexists (⊤ \ ↑(nroot : Namespace))
  imod (inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full)) $$ HinvT with ⟨HI, -⟩
  imod HI with HI
  icases (embed_toHeaplet I) $$ HI with ⟨%hI, %hsI, HownI⟩
  ihave %hsub := ownHeaplet_sub $$ [$Hgh $HownI]
  imodintro
  ipureintro
  exact ⟨hI, hsub, hsI⟩

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
