import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.Laws.Control

/-!
# Adequacy
The concrete functor bundle, `go_adequacy` (ghost-state allocation over a
well-formed initial state), and the generic end-to-end witness.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.ProgramLogic.Language.Notation Iris.BI

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
  | 4 => ⟨constOF (HeapView Nat (Agree (DiscreteO HeapCell)) GoHeapF), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (DiscreteO GName)) GoHeapF), by infer_instance⟩
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
current Iris layer `.panicked msg` has `toVal = none` and **no** outgoing `Step`,
so it counts as *stuck* — even though the machine treats it as legitimate
terminal *behavior* (`Config.terminal`). Since the unwinding arc
(`docs/2026-07-25_unwinding-arc.md`), `.panicked` is reached only by an
UNRECOVERED panic chain: a panic mid-unwind (`.panicking`) steps — defers run
and `recover` can cancel it — so a recovered panic is an ordinary control path
this guarantee covers. What remains outside it is the unrecovered abort: that
makes `Hwp` unprovable rather than being a permitted terminal. Modelling the
abort as a value/observation in the Iris layer is deferred — until then read
the guarantee as "`φ`-correct, never-stuck execution *among runs that do not
abort on an unrecovered panic*". Since the channels arc (slice 1) the blocked
configurations (`.blockedSend`/`.blockedRecv`/`.blockedSelect` — the
deadlocked terminal class) are a SECOND `toVal = none`, no-outgoing-`Step`
class in exactly the same position: a provable `Hwp` additionally rules them
out, so the honest reading is "…among runs that do not abort on an
unrecovered panic *and do not deadlock*" — the guarantee got STRONGER, never
looser (audit S12). -/
theorem go_adequacy [GoCoreGpreS .hasLC GF] (c : Config) (σ : ExecState)
    (φ : Unit → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ⊢@{IProp GF} (WP c {{ v, ⌜φ v⌝ }})) :
    adequate .NotStuck c σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) .NotStuck c σ φ ?_
  intro inst κs
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
  iexists (fun σ' _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ σ'.methods = σ.methods
          ∧ σ'.types = σ.types ∧ HeapWf σ'⌝))
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
      exact ⟨rfl, rfl, rfl, hσwf⟩
  · exact Hwp rfl rfl rfl

/-! ## Arc `exit-infra` (2b): the strong-adequacy operational readout

`go_heap_adequacy` is the exit door for STATE-property specs: the WP carries
a resource postcondition `Ψ` (e.g. `a.id ↦ cell`), and an extraction
entailment turns `genHeapInterp σf ∗ Ψ v` into a pure fact about the final
`ExecState` — surfacing what the Iris proof knows into `adequate`'s φ.
Built on `wp_strong_adequacy_gen`, whose φ-continuation hands us the FINAL
state interpretation (the plain `wp_adequacy` route discards it). -/

/-- Sequential `Steps` embed into the (singleton) thread-pool erased-step
closure — the trace form `adequate` quantifies over. -/
theorem steps_erased {c c' : Config} {σ σ' : ExecState}
    (h : Steps c σ c' σ') : ([c], σ) -·->ₜₚ* ([c'], σ') := by
  induction h with
  | refl => exact .refl
  | tail hab hstep ih =>
    exact FromMathlib.Relation.ReflTransGen.tail ih ⟨[], Language.Step.of_primStep
      (GoPrimStep.step hstep) (t₁ := []) (t₂ := [])⟩

theorem go_heap_adequacy [GoCoreGpreS .hasLC GF] (c : Config) (σ : ExecState)
    (Ψ : ∀ [GoCoreGS .hasLC GF], Unit → IProp GF)
    (φ : Unit → ExecState → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ⊢@{IProp GF} (WP c {{ v, Ψ v }}))
    (Hext : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ∀ (σ2 : ExecState) (v : Unit),
        iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ2.heap) ∗ Ψ v)
          ⊢ |==> ⌜φ v σ2⌝) :
    adequate .NotStuck c σ φ := by
  refine (adequate_alt _ c σ φ).mpr ?_
  intro t2 σ2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) .NotStuck
    (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
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
  iexists [(fun v => Ψ v)], (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
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
  isplitl
  · iapply BigSepL2.bigSepL2_singleton
    exact Hwp rfl rfl rfl
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
    imod (Hext rfl rfl rfl σ2 _) $$ [$Hgh $Hpost] with %Hφv
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind

/-- **Strong adequacy with initial-heap handover** (arc `spec-surface`
stage 2; the full HeapLang `heap_adequacy` shape, via iris-lean's
`genHeap_init_names`): the WP proof now RECEIVES the `↦` fragments for the
entire initial heap, so specs can name seeded observable cells at concrete
addresses (`docs/2026-07-21_native-spec-surface.md` D5) instead of
allocating their cells inside the run behind the `∀ fresh` quantifier.
`go_heap_adequacy` (empty handover) remains for self-allocating drivers. -/
theorem go_heap_adequacy_own [GoCoreGpreS .hasLC GF] (c : Config)
    (σ : ExecState)
    (Ψ : ∀ [GoCoreGS .hasLC GF], Unit → IProp GF)
    (φ : Unit → ExecState → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      iprop([∗map] l ↦ cell ∈ heapToMap σ.heap, l ↦ cell)
        ⊢@{IProp GF} (WP c {{ v, Ψ v }}))
    (Hext : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      ∀ (σ2 : ExecState) (v : Unit),
        iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ2.heap) ∗ Ψ v)
          ⊢ |==> ⌜φ v σ2⌝) :
    adequate .NotStuck c σ φ := by
  refine (adequate_alt _ c σ φ).mpr ?_
  intro t2 σ2 hreach
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF) (hlc := .hasLC) .NotStuck
    (Hsteps := hsteps) (numLaters := fun _ => 0)
  iintro %Hinv
  imod (genHeap_init_names (GF := GF) (heapToMap σ.heap))
    with ⟨%γh, %γm, Hσ, Hpts, Htok⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions, σ.methods, σ.types⟩
  imodintro
  iexists (fun σ' _ _ _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ σ'.methods = σ.methods
          ∧ σ'.types = σ.types ∧ HeapWf σ'⌝))
  iexists [(fun v => Ψ v)], (fun _ => iprop(True)), (fun _ _ _ _ => fupd_intro)
  dsimp only
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨rfl, rfl, rfl, hσwf⟩
  isplitl [Hpts]
  · iapply BigSepL2.bigSepL2_singleton
    iapply (Hwp rfl rfl rfl) $$ Hpts
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
    imod (Hext rfl rfl rfl σ2 _) $$ [$Hgh $Hpost] with %Hφv
    iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
    ipureintro
    grind

/-- **The invariance readout** (arc `invariant-readout`, design of record
`docs/2026-07-22_invariant-readout-design.md`): iris-lean's `wp_invariance`
instantiated with GoCore's genHeap state interpretation and initial-heap
handover. Unlike `go_heap_adequacy*`, the conclusion `φ` is extracted at an
**arbitrary reachable** configuration `(t2, σ2)` — not a terminal one — and
the WP obligation carries the **trivial postcondition** (the triple's `Q`
plays no role in invariance). The extraction wand receives ONLY the state
interpretation at `σ2`: owned resources inside the WP never reach it, so
the fact must arrive via something persistent the user's `|={⊤}=>` staged —
in practice an Iris invariant token (`inv_alloc` from the handed-over
fragments; persistence is the transport, design note §2). -/
theorem go_heap_invariance [GoCoreGpreS .hasLC GF] (c : Config)
    (σ : ExecState) (t2 : List Config) (σ2 : ExecState) (φ : Prop)
    (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
      iprop([∗map] l ↦ cell ∈ heapToMap σ.heap, l ↦ cell)
        ⊢ |={⊤}=> iprop(
            (WP c {{ _v, iprop(True) }}) ∗
            (genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ2.heap)
              -∗ ∃ E : CoPset, |={⊤,E}=> ⌜φ⌝)))
    (Hsteps : ([c], σ) -·->ₜₚ* (t2, σ2)) :
    φ := by
  refine wp_invariance_gen (GF := GF) (hlc := .hasLC) .NotStuck c σ σ2 t2 φ
    ?_ Hsteps
  iintro %Hinv %κs
  imod (genHeap_init_names (GF := GF) (heapToMap σ.heap))
    with ⟨%γh, %γm, Hσ, Hpts, Htok⟩
  letI _ : GoCoreGS .hasLC GF := ⟨⟨γh, γm⟩, σ.functions, σ.methods, σ.types⟩
  imod (Hwp rfl rfl rfl) $$ Hpts with ⟨Hwp', Hcont⟩
  imodintro
  iexists (fun σ' _ _ =>
    iprop(genHeapInterp (GF := GF) (H := GoHeapF) (heapToMap σ'.heap)
      ∗ ⌜σ'.functions = σ.functions ∧ σ'.methods = σ.methods
          ∧ σ'.types = σ.types ∧ HeapWf σ'⌝))
  iexists (fun _ => iprop(True))
  dsimp only
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨rfl, rfl, rfl, hσwf⟩
  isplitl [Hwp']
  · iexact Hwp'
  iintro ⟨Hgh, %Hpure⟩
  iapply Hcont $$ Hgh

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
    intro _ _ _ _
    iapply wp_seqn
    simp only [seqCont]
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
