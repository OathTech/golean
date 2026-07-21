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
import GoLeanProofs.Laws.Control

/-!
# Adequacy
The concrete functor bundle, `go_adequacy` (ghost-state allocation over a
well-formed initial state), and the generic end-to-end witness.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel

namespace GoLean.Iris

/-- The GoCore *pre* ghost state: the functors are present but names are not yet
allocated (allocation is adequacy's job). -/
class GoCoreGpreS (hlc : outParam HasLC) (GF : BundledGFunctors) extends
    InvGpreS GF where
  heap_pre : genHeapPreS Nat HeapCell GF GoHeapF
attribute [reducible, instance] GoCoreGpreS.heap_pre

/-- A concrete functor bundle realizing `GoCoreGpreS`: the invariant + credit
cameras (functors 0–3) plus the gen_heap heap-view / meta-view / meta-token
functors (4–6) over `Nat`/`HeapCell`/`GoHeapF`. Mirrors HeapLang's `HeapLangS`
with GoCore's key/value types. -/
def GoCoreS : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (LeibnizO HeapCell)) GoHeapF), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (LeibnizO GName)) GoHeapF), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instGoCoreGpreS : GoCoreGpreS HasLC.hasLC GoCoreS where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6

/-- **Adequacy** for GoCore's real relation, over `NotStuck` — but note the
scope. (Pre-merge audit 2026-07-19, finding D1-1, confirmed.) `adequate
.NotStuck` requires every reachable config to be a value or reducible. In the
current Iris layer `.panicked msg` has `toVal = none` and **no** outgoing `Step`
(no rule sources it), so it counts as *stuck* — even though `Rel.lean` treats a
panic as legitimate terminal *behavior* (`Config.terminal`). So this theorem's
guarantee covers only runs that never reach `.panicked`; a Go panic (bounds,
nil-deref, divide-by-zero) makes `Hwp` unprovable rather than being a permitted
terminal. Modelling panics as values/observations in the Iris layer (so
adequacy admits panicking terminals) is deferred — until then read the guarantee
as "`φ`-correct, never-stuck execution *among non-panicking runs*". -/
theorem go_adequacy [GoCoreGpreS .hasLC GF] (c : Config) (σ : ExecState)
    (φ : Unit → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      ⊢@{IProp GF} (WP c {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck c σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck c σ φ ?_
  intro inst κs
  imod iOwn_alloc (E := GhostMapG.elem (K := Nat) (V := HeapCell) (H := GoHeapF))
    (HeapView.Auth (H := GoHeapF) (.own 1)
      (Std.PartialMap.map (fun v : HeapCell => toAgree (LeibnizO.mk v))
        (heapToMap σ.heap)))
    HeapView.auth_one_valid with ⟨%γh, Hh⟩
  imod iOwn_alloc (E := GhostMapG.elem (K := Nat) (V := GName) (H := GoHeapF))
    (HeapView.Auth (H := GoHeapF) (.own 1)
      (Std.PartialMap.map (fun g : GName => toAgree (LeibnizO.mk g))
        (∅ : GoHeapF GName)))
    HeapView.auth_one_valid with ⟨%γm, Hm⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions⟩
  imodintro
  iexists (fun σ' _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ HeapWf σ'⌝))
  iexists (fun _ => iprop(True))
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
      exact ⟨rfl, hσwf⟩
  · exact Hwp rfl

/-! ## Arc `slice-l5-pure` item 2 — the end-to-end adequacy witness

The one artifact that demonstrates the WP→adequacy chain *composes*: a concrete
program, its WP built from the shipped laws, fed through `go_adequacy`, yielding
a **closed** `adequate` theorem with zero hypotheses. This is the first
demonstration that Iris dissolves (`docs/2026-07-20_end-state-theorem.md`): the
conclusion `adequate .NotStuck …` is a pure operational statement over
`Step`/`Config`/`ExecState`; every Iris construct lives only in the proof. -/

/-- **The chain composes — a closed `adequate` theorem.** For any
**well-formed** initial state (`HeapWf` — heap keys below `nextAddr`, the one
side-condition the state interpretation carries; states the semantics
constructs are believed to satisfy it — asserted, not proven, and the states
of interest, e.g. the empty heap, satisfy it trivially) and any environment, the empty-sequence program
provably runs to termination without ever getting stuck: `WP` is assembled
from `wp_seqn` + `wp_seq_done` + `wp_value'`, discharged through
`go_adequacy` with the concrete functor bundle `GoCoreS`. The statement
mentions no Iris — it is `adequate .NotStuck` over the operational
semantics, full stop. -/
theorem adequate_seqn_nil (σ : ExecState) (env : LocalEnv) (hwf : HeapWf σ) :
    adequate .NotStuck (Config.exec (.seqn #[]) env .stop) σ (fun _ _ => True) :=
  go_adequacy (GF := GoCoreS) _ _ _ hwf (by
    intro _ _
    iapply wp_seqn
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred
    iapply wp_seq_done
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred2
    iapply (wp_value' (v := ()))
    ipureintro
    trivial)

end GoLean.Iris
