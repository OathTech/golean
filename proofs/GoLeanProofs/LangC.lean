import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MultiSound
import GoLeanProofs.Ghost
import GoLeanProofs.Adequacy

/-!
# The CONCURRENT Iris `Language` instance (channels arc slice 5, item 1)

iris-lean's thread-pool `Language` instantiated over the POOL's
per-goroutine relation — `StepE` with its spawn component (`Multi.lean`;
the interface was built for exactly this shape: one thread steps, forked
threads are appended) — plus the per-goroutine marker strip: BUG-040's
`.spawned` boundary is pool-level in `StepM` (`StepM.spawned`), so the
Iris-side per-thread relation `StepEC` adds it as a thread-local rule
(otherwise a parent could never proceed past its own fork in the
Language's world). Everything here is INTERNAL machinery: no designated
statement mentions any of it (the statement-TCB gate walks would flag
it), and the statement layer's concurrent notions live in `Surface.lean`
over `execProg` alone.

**Scope, recorded honestly** (the slice-5 build log's obstruction
record): this Language covers interleavings of sequential steps, spawns,
and marker strips. It does NOT cover `StepM`'s pairing/wake rules — a
pairing touches TWO threads' configurations in one step, which the
thread-pool `Language` (one thread per step) cannot express. The
recorded route to the full concurrent WP pipe (a frame-quantified
`GoSpecC` on a genuinely spawning program) is a proof-layer
DECOMPOSITION: park/deposit/wake per-thread rules simulating each
pairing with structural state equality, plus a pool-reachability kit for
the deadlock/race exclusions — successor-arc work. Consequently the
laws below are the fork-fragment kit: gen_heap over the shared
`ExecState` (the sequential `GoCoreGS`/`StateInterp` reused verbatim —
the state type is the same), the pure-det lift, the marker strip, the
FORK RULE, and a closed end-to-end adequacy witness over a program that
spawns. Channel invariants/ghost protocol machinery is deliberately NOT
built this slice: with the witness discharged by the pool ∀-streams
checker (`MultiStreams.lean`), an Actris-lite layer would have no
consumer — building it now would be exactly the inert-scaffolding the
fail-closed doctrine forbids; it lands with the decomposition arc that
consumes it.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

/-- Per-goroutine configuration on the CONCURRENT carrier: a one-field
wrapper around `Config`, so the pool `Language` instance can coexist
with the sequential one (typeclass instances are keyed by the
expression type). -/
structure PoolCfg where
  c : Config

/-- The per-goroutine relation the concurrent `Language` runs on:
`StepE` (sequential steps + the spawn, forking one child) plus the
thread-local `.spawned` marker strip (pool-level `StepM.spawned`,
needed thread-locally here — see the module docstring). Proof
infrastructure, exactly like `Step`/`StepE`/`StepM`. -/
inductive StepEC : Config → ExecState → Config → ExecState → List Config → Prop where
  | lift {c σ c' σ' efs} : StepE c σ c' σ' efs → StepEC c σ c' σ' efs
  | strip {k σ} : StepEC (.spawned k) σ (.next k) σ []

/-- A spawn position is not the terminal (feeds `val_stuck`). -/
private theorem spawnPlan_toVal_aux {c : Config}
    {p : GoValue × List GoValue × Cont} (h : spawnPlan c = some p) :
    (match c with
      | Config.next Cont.stop => some ()
      | _ => (none : Option Unit)) = none := by
  match c, h with
  | .retV _ (.goCalleeK [] _ _), _ => rfl
  | .retV _ (.goArgsK _ _ [] _ _), _ => rfl

instance : ToVal PoolCfg Unit where
  toVal e := match e.c with | .next .stop => some () | _ => none
  ofVal _ := ⟨.next .stop⟩
  coe_of_toVal_eq_some {e v} h := by
    obtain ⟨c⟩ := e
    cases c with
    | next k => cases k <;> simp_all
    | _ => simp_all
  toVal_coe _ := rfl

/-- The concurrent primitive step: one goroutine's `StepEC` against the
shared state, forked children appended (iris-lean's thread-pool `Step`
places them at the pool's end — exactly `stepThread`'s push). -/
inductive GoPrimStepC :
    PoolCfg × ExecState → List Unit → PoolCfg × ExecState × List PoolCfg → Prop where
  | step {c σ c' σ' efs} : StepEC c σ c' σ' efs →
      GoPrimStepC (⟨c⟩, σ) [] (⟨c'⟩, σ', efs.map PoolCfg.mk)

instance : PrimStep PoolCfg ExecState (List Unit) where
  primStep := GoPrimStepC

instance : Language PoolCfg ExecState Unit Unit where
  val_stuck h := by
    cases h with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq <;> rfl
        | spawn hsp hstep => exact spawnPlan_toVal_aux hsp
      | strip => rfl

instance : Inhabited PoolCfg := ⟨⟨.next .stop⟩⟩

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- The pool carrier's `IrisGS`: the SAME state interpretation as the
sequential instance (gen_heap over the shared `ExecState` plus the
program/methods/types pins — `Ghost.lean`'s `StateInterp` is keyed by
the state type, which is unchanged), `forkPost = True` (Go goroutines
return nothing — heap_lang's choice, and the right one per the
research note). -/
instance : IrisGS_gen hlc PoolCfg GF where
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by iintro $

variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The pure deterministic lift on the pool carrier**: a sequential
`Step` that is pure (state unchanged) and deterministic, at a
configuration that is neither a spawn position nor the marker, is a
`WP` step of the concurrent Language — the strip and spawn rules are
refuted by the side conditions, so the sequential behavior is the
whole behavior. -/
theorem wpC_pure_det {c c' : Config}
    (hsp : spawnPlan c = none) (hsc : spawnedCont c = none)
    (hstep : ∀ σ : ExecState, Step c σ c' σ)
    (hdet : ∀ (σ : ExecState) (c₂ : Config) (σ₂ : ExecState),
      Step c σ c₂ σ₂ → c₂ = c' ∧ σ₂ = σ) :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfg.mk c') @ s ; E {{ Φ }}) ⊢
      WP (PoolCfg.mk c) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := PoolCfg.mk c')
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], ⟨c'⟩, σ, [], GoPrimStepC.step (.lift (.lift (hstep σ)))⟩
      · exact Language.val_stuck (GoPrimStepC.step (.lift (.lift (hstep σ))))
    )
    (Hpuredet := by
      intro σ₁ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        cases st with
        | strip => simp [spawnedCont] at hsc
        | lift ste =>
          cases ste with
          | lift sq =>
            obtain ⟨rfl, rfl⟩ := hdet _ _ _ sq
            exact ⟨rfl, rfl, rfl, rfl⟩
          | spawn hsp' _ =>
            rw [hsp] at hsp'
            cases hsp'))
  iexact H

/-- **The marker strip on the pool carrier**: the parent's `.spawned`
boundary marker steps to its continuation — thread-locally here, the
Iris-side twin of `StepM.spawned`. Pure and deterministic: the strip
is the ONLY `StepEC` rule from the marker (sequential steps and spawns
are relation-silent there — `step_spawnedMarker_elim`,
`spawnPlan (.spawned k) = none`). -/
theorem wpC_spawned_strip {k : Cont} :
    (|={E}[E]▷=> £ 1 -∗ WP (PoolCfg.mk (.next k)) @ s ; E {{ Φ }}) ⊢
      WP (PoolCfg.mk (.spawned k)) @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := PoolCfg.mk (.next k))
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], ⟨.next k⟩, σ, [], GoPrimStepC.step .strip⟩
      · rfl)
    (Hpuredet := by
      intro σ₁ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        cases st with
        | strip => exact ⟨rfl, rfl, rfl, rfl⟩
        | lift ste =>
          cases ste with
          | lift sq => exact absurd sq (step_spawnedMarker_elim rfl)
          | spawn hsp' _ => cases hsp'))
  iexact H

/-- **THE FORK RULE** (the `go` statement's WP law — heap_lang's
`wp_fork`, over GoCore's spawn step). At a completed spawn position
whose `spawnStep` is STATE-PRESERVING under the pins (the no-fresh-cell
class: a callee with no parameters, results, or declarations — the
witness's shape; the allocating class needs the gen_heap-update
variant, which lands with its first consumer — SHIPPED 2026-08-11 on
the D-CARRIER as `wpD_fork_alloc₁` (ChanD.lean, channel-logic S1)
with the rendezvous exemplar as consumer; the C-carrier sibling
remains unbuilt, this record back-annotated at the S1 audit fix
round), the parent proceeds to
its `.spawned` marker and the child runs under the trivial `forkPost`:

    ▷ WP child {{ True }} ∗ ▷ WP (.spawned k) {{ Φ }} ⊢ WP c {{ Φ }}

The `hspawn` premise pins the child configuration and the
state-preservation; determinism of the spawn position (the sequential
relation and the strip are silent there) makes it the whole
behavior. -/
theorem wpC_fork {c child : Config} {cv : GoValue} {args : List GoValue}
    {k : Cont}
    (hsp : spawnPlan c = some (cv, args, k))
    (hspawn : ∀ σ : ExecState, σ.functions = GoCoreGS.prog GF →
      σ.methods = GoCoreGS.methods GF → σ.types = GoCoreGS.types GF →
      spawnStep σ cv args k = .ok (.spawned k, child, σ)) :
    ▷ WP (PoolCfg.mk child) @ s ; ⊤ {{ fun _ => iprop(True) }}
      ∗ ▷ WP (PoolCfg.mk (.spawned k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfg.mk c) @ s ; E {{ Φ }} := by
  iintro ⟨Hchild, Hparent⟩
  have hnv : ToVal.toVal (PoolCfg.mk c) = (none : Option Unit) := by
    match c, hsp with
    | .retV cv' (.goCalleeK [] env k'), _ => rfl
    | .retV v (.goArgsK cv' vals [] env k'), _ => rfl
  iapply wp_lift_step hnv
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.spawned k⟩, σ₁, [⟨child⟩],
        GoPrimStepC.step (.lift (.spawn hsp (hspawn σ₁ hfns hmeths htypes)))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  have hshape : e₂ = PoolCfg.mk (.spawned k) ∧ σ₂ = σ₁
      ∧ eₜ = [PoolCfg.mk child] := by
    cases Hstep with
    | step st =>
      cases st with
      | strip => simp [spawnPlan] at hsp
      | lift ste =>
        cases ste with
        | lift sq => exact absurd sq (step_spawnPos_elim hsp)
        | spawn hsp' hstep' =>
          rw [hsp] at hsp'
          injection hsp' with heq
          injection heq with h1 hrest
          injection hrest with h2 h3
          subst h1
          subst h2
          subst h3
          rw [hspawn σ₁ hfns hmeths htypes] at hstep'
          injection hstep' with hp
          injection hp with hpar hrest'
          injection hrest' with hchild hσ
          subst hpar
          subst hchild
          subst hσ
          exact ⟨rfl, rfl, rfl⟩
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  imod Hclose
  imodintro
  isplitl [Hσ]
  · isplitl [Hσ]
    · iexact Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf⟩
  isplitl [Hparent]
  · iexact Hparent
  · simp only [Algebra.BigOpL.bigOpL_cons, Algebra.BigOpL.bigOpL_nil]
    isplitl [Hchild]
    · iexact Hchild
    · itrivial

end


/-! ## The fork-rule witness (non-vacuity gate) + pool adequacy

A concrete spawning program — main forks a no-op worker and stops —
walked end to end through the concurrent laws, then discharged into a
CLOSED `adequate` statement over the pool Language: the first
demonstration that the concurrent Iris layer dissolves into an
operational claim, and the same-commit discharge witness for
`wpC_fork`/`wpC_pure_det`/`wpC_spawned_strip`. -/

/-- The no-op worker: no parameters, no results, empty body (the
state-preserving spawn class `wpC_fork` covers). -/
def noopWorker : Func :=
  { id := ⟨"noopWorker"⟩, args := #[], results := #[], body := .seqn #[] }

/-- `go noopWorker()` — the witness program. -/
abbrev spawnNoopProg : Stmt := .goStmt (.funcVal ⟨"noopWorker"⟩ #[]) #[]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

set_option maxHeartbeats 1600000 in
/-- The fork-rule WITNESS: the full WP of the spawn-noop program, every
premise of the concurrent laws discharged by computation against the
concrete program; external premises = the standard program/method
pins. The child's obligation (`forkPost = True`) is discharged by
walking the forked goroutine's frame to its terminal. -/
theorem wpC_spawn_noop_witness
    (hprog : GoCoreGS.prog GF = #[noopWorker])
    (hmeths : GoCoreGS.methods GF = #[]) :
    ⊢@{IProp GF} WP (PoolCfg.mk (.exec spawnNoopProg [] .stop))
      {{ _v, iprop(True) }} := by
  -- main: goStmt entry (pure det)
  iapply (wpC_pure_det (hsp := rfl) (hsc := rfl)
    (hstep := fun σ => Step.goStmtEntry)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred1
  -- main: the callee literal evaluates (nullary strict op, pure det)
  iapply (wpC_pure_det (hsp := rfl) (hsc := rfl)
    (hstep := fun σ => Step.evalStrictNullary rfl rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq
      case evalStrictNullary op v hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"noopWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"noopWorker"⟩ [], σ) from rfl] at happly
        injection happly with hp
        injection hp with hv hσ
        subst hv
        subst hσ
        exact ⟨rfl, rfl⟩
      case evalStrictNullaryPanic op msg hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"noopWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"noopWorker"⟩ [], σ) from rfl] at happly
        cases happly
      all_goals simp_all [strictPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred2
  -- main: THE FORK
  iapply (wpC_fork (hsp := rfl)
    (child := .exec (.seqn #[]) [] (.frame [] [] [] [] .stop false))
    (hspawn := by
      intro σ hf hm ht
      simp +decide [spawnStep, enterFrame, findFunctionIn?, noopWorker,
        dynamicDispatch?, bindParams, allocDecls, pinResultLocs,
        methodInfoByFuncId?, hf, hm, hprog, hmeths,
        Bind.bind, Except.bind, pure, Except.pure]))
  isplitl []
  · -- the CHILD: empty body under its barrier frame, to the terminal
    inext
    iapply (wpC_pure_det (hsp := rfl) (hsc := rfl)
      (hstep := fun σ => Step.seqn)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred3
    simp only [seqCont]
    iapply (wpC_pure_det (hsp := rfl) (hsc := rfl)
      (hstep := fun σ => Step.seqDone)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred3b
    iapply (wpC_pure_det (hsp := rfl) (hsc := rfl)
      (hstep := fun σ => Step.frameFall)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [loadMany, storeMany, pure, Except.pure]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred4
    iapply (wp_value' (v := ()))
    itrivial
  · -- the PARENT: strip the marker, stop
    inext
    iapply wpC_spawned_strip
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred5
    iapply (wp_value' (v := ()))
    itrivial

end

/-- **Pool adequacy** — `go_adequacy`'s twin over the CONCURRENT
Language (same ghost allocation, same functor bundle `GoCoreS`): a WP
against the pool carrier discharges into `adequate` over thread-pool
executions — every reachable pool's threads are values or reducible,
and terminal main results satisfy `φ`. -/
theorem goC_adequacy {GF : BundledGFunctors} [GoCoreGpreS .hasLC GF]
    (c : PoolCfg) (σ : ExecState)
    (φ : Unit → Prop) (hσwf : HeapWf σ)
    (Hwp : ∀ [GoCoreGS .hasLC GF], GoCoreGS.prog GF = σ.functions →
      GoCoreGS.methods GF = σ.methods → GoCoreGS.types GF = σ.types →
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

/-- **The closed end-to-end pool witness**: the spawn-noop program,
from the seeded state, provably runs NotStuck on the CONCURRENT
Language — parent and forked child both — assembled from the fork
rule, the pure lifts, and pool adequacy, with zero hypotheses. The
concurrent counterpart of `adequate_seqn_nil`. -/
theorem adequateC_spawn_noop :
    adequate .NotStuck (PoolCfg.mk (.exec spawnNoopProg [] .stop))
      { functions := #[noopWorker] } (fun _ _ => True) :=
  goC_adequacy (GF := GoCoreS) _ _ _
    (fun _ _ => rfl)
    (by
      intro _ hprog hmeths _htypes
      exact wpC_spawn_noop_witness hprog hmeths)

end GoLean.Iris
