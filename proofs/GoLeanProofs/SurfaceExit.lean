import GoLeanProofs.SurfaceBridge
import GoLeanProofs.Adequacy

/-!
# The generic exit theorem (arc `spec-surface` stage 4)

`goTriple_of_wp`: an Iris WP proof of `⟦P⟧ ⊢ WP prog {{ ⟦Q⟧ }}` discharges
the NATIVE triple `GoTriple funcs env₀ P prog Q` — the once-proven pipe
`correspondence witness → trace erasure → initial-heap-handover adequacy
(with `reflect` feeding the precondition in and `extract` reading the
postcondition out)`. Per-program obligations are exactly: the fragment
shape checks and the WP proof. Nothing else, ever
(`docs/2026-07-21_native-spec-surface.md`, the anti-hack invariant).
-/

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.GoCore.Correspondence
open GoLean.Surface

namespace GoLean.Iris

/-- **The generic exit theorem.** Premises:
- `hfrag`/`hfuncs` — the v1 fragment shape checks (mechanical);
- `Hwp` — the real proof: the embedded precondition WPs the program to the
  embedded postcondition, over the concrete bundle `GoCoreS` with the
  function table pinned.
Conclusion: the native surface triple, over interpreter runs. -/
theorem goTriple_of_wp {funcs : Array Func} {env₀ : LocalEnv} {P Q : HProp}
    {prog : Stmt}
    (hfrag : StmtFragNS prog)
    (hfuncs : FuncsFrag funcs)
    (Hwp : ∀ [GoCoreGS .hasLC GoCoreS], GoCoreGS.prog GoCoreS = funcs →
      embed (GF := GoCoreS) P
        ⊢ WP (Config.exec prog env₀ .stop) {{ _v, embed Q }}) :
    GoTriple funcs env₀ P prog Q := by
  intro hp na hbound hheapfrag hsatP fuel ch σf ch' hrun
  have hinv : StInv (ExecState.mk (types := []) (functions := funcs)
      (methods := #[]) (locals := env₀) (heap := hp) (nextAddr := na)) :=
    ⟨hheapfrag, rfl, hfuncs⟩
  have hsteps := interpreterSound_frag fuel _ σf prog ch ch' hfrag hinv hrun
  have htp := steps_erased hsteps
  have hadeq := go_heap_adequacy_own (GF := GoCoreS)
    (Config.exec prog env₀ .stop)
    (ExecState.mk (types := []) (functions := funcs) (methods := #[])
      (locals := env₀) (heap := hp) (nextAddr := na))
    (Ψ := fun _ => embed Q)
    (φ := fun _ σ2 => ∃ h : Heaplet,
      Heaplet.sub h (heapToMap σ2.heap) ∧ sat h Q)
    hbound
    (fun hprog =>
      ((heapletOf_eq_heapToMap hp ▸ reflect P (heapletOf hp) hsatP)).trans
        (Hwp hprog))
    (fun _hprog σ2 _v => by
      iintro H
      imodintro
      iapply extract $$ H)
  have hres := hadeq.adequate_result [] σf () htp
  obtain ⟨h, hsub, hsat⟩ := hres
  exact ⟨h, by rw [heapletOf_eq_heapToMap]; exact hsub, hsat⟩

end GoLean.Iris
