import GoLeanProofs

/-! # Throwaway spike — de-risk the location-resolved core before reshaping Rel.lean

**SUPERSEDED (2026-07-19).** This spike de-risked the CEK reshape; the reshape has
since landed in `GoLeanProofs.lean` (`wp_assign` is now a usable law with a pure
resolution premise — `wp_assign_lit` discharges it — all axiom-clean). Kept as a
historical record; not part of any build target. The two claims below are now
realized in the real relation, so the `env_bridge*` lemmas restate the real
`Step.assign` (whose target is now resolved against the control `env`) rather
than a separate name-based relation.

Validates the two load-bearing claims of the Goose-aligned recommendation
(`docs/2026-07-19_goose-perennial-mapping.md`) before we commit to the reshape:

1. **A store law over a RESOLVED location needs no `hred`** — Perennial-shape
   `wp_store`. The whole `hred` hypothesis in `GoLean.Iris.wp_assign` existed only
   to resolve the target from the locals; with the target `Loc` resolved from the
   control `env` (fixed in the goal), the step is unconditional and the law is a
   clean `wp_store`.
2. **The env is a clean one-line correspondence bridge** — the name-carrying
   relation step is the resolved store, and the resolution witness
   (`LocalEnv.lookup env`) never enters the separation logic.

Not imported by the lib. Built standalone (`lake env lean`). -/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Rel GoLean.Iris

namespace SliceSpike

/-- Location-resolved control: the store target `a` and the new cell are IN the
config — no name, no `AssigneeR`, no locals. -/
inductive LConfig where
  | store (a : Addr) (cell : HeapCell) (k : Cont)
  | next (k : Cont)

/-- The resolved store mutates the heap at `.base a`. Unconditional. -/
inductive LStep : LConfig → ExecState → LConfig → ExecState → Prop where
  | store {a cell k s} :
      LStep (.store a cell k) s (.next k) { s with heap := Heap.set s.heap (.base a) cell }

instance : ToVal LConfig Unit where
  toVal c := match c with | .next .stop => some () | _ => none
  ofVal _ := .next .stop
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

inductive LPrimStep :
    LConfig × ExecState → List Unit → LConfig × ExecState × List LConfig → Prop where
  | step {c s c' s'} : LStep c s c' s' → LPrimStep (c, s) [] (c', s', [])

instance : PrimStep LConfig ExecState (List Unit) where
  primStep := LPrimStep

instance : Language LConfig ExecState Unit Unit where
  val_stuck h := by cases h with | step st => cases st <;> rfl

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

instance : IrisGS_gen hlc LConfig GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **(1) Store law over a resolved location — NO `hred`.** The step is
unconditional (`LStep.store`); determinism is one `cases`. Everything else is the
same gen_heap update + `heapToMap` bridge as `wp_assign`, minus the locals
resolution that forced `hred`. -/
theorem wp_store {a : Addr} {oldcell newcell : HeapCell} {k} :
    a.id ↦ oldcell ∗ (a.id ↦ newcell -∗ WP (LConfig.next k) @ s ; E {{ Φ }})
      ⊢ WP (LConfig.store a newcell k) @ s ; E {{ Φ }} := by
  iintro ⟨Hpt, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], LConfig.next k, _, [], LPrimStep.step LStep.store⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    cases st
    imod (genHeap_update (v₂ := newcell)) $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap a newcell kk).symm)) $$ Hσ
    · isplitl [Hpt Hcont]
      · iapply Hcont $$ Hpt
      · itrivial

end

/-- **(2) The env bridge.** Given the control environment resolves `x` to
`.base a` (`LocalEnv.lookup env`), the relation's assign step is exactly the
resolved store: one proof term. The resolution witness never enters the
separation logic; it lives purely in the (now realized) control `env`. -/
theorem env_bridge {s s₂ s₃ : ExecState} {env : LocalEnv} {x : String} {a : Addr}
    {rhs v k}
    (hres : LocalEnv.lookup env x = some (.base a))
    (hrhs : ExprR env s rhs (.value v s₂))
    (hstore : storeLoc s₂ (.base a) v = .ok s₃) :
    Step (Config.exec (.assign (.var x) rhs) env k) s (.next k) s₃ :=
  Step.assign (AssigneeR.var hres) hrhs hstore

/-- And the reverse: an assign step *recovers* the env resolution — the bridge is
bidirectional, so the location-resolved relation loses nothing. -/
theorem env_bridge_inv {s s₃ : ExecState} {env : LocalEnv} {x : String} {rhs k}
    (h : Step (Config.exec (.assign (.var x) rhs) env k) s (.next k) s₃) :
    ∃ loc, LocalEnv.lookup env x = some loc := by
  cases h with
  | assign hass _ _ => cases hass with | var hres => exact ⟨_, hres⟩

end SliceSpike

#print axioms SliceSpike.wp_store
#print axioms SliceSpike.env_bridge
#print axioms SliceSpike.env_bridge_inv
