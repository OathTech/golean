import GoLeanProofs.ChanDMRes
import GoLeanProofs.Specs.ChanRendezvous

/-!
# The RESOURCE-TRANSFER exemplar (channel-logic slice 3, mini-dsp)

**The claim the pure tier provably cannot make** (slice-2 note §6
obstacle 1; design note `docs/2026-08-11_channel-resource-tier.md`
§4): a frame-quantified triple whose post RE-OWNS a cell the receiving
thread never touched — the points-to travels through the channel with
the message. The program is the dsp session's outbound leg in
miniature: main spawns `xferWorker(chv, &x)` handing it `x`'s cell
(`x = 40`); the worker writes `*p = 42` and sends the POINTER on the
channel; main receives — and the message's protocol resource
(`Ψ v := ⌜v = &x⌝ ∗ x ↦ 42`) is the ONLY route by which main's post
can own `x ↦ 42`. The route is the slice-3 resource tier end to end:
`chanInv` over the mediated carrier, the four `wpDM_*_inv` laws, the
two-parameter allocating fork, and the `goTripleC_of_wpDM` exit.

D1-BOTH per the convention: `chanTransferReadoutC` (run-conditioned
first-order readout at the seed, the 42 pin included) +
`chanTransferTerminatesNormallyC` (seeded completion pin via the
kernel certificate, `#eval`-confirmed first).

This module is the same-commit DISCHARGE WITNESS for the ChanDMRes
laws: `wpDM_send_inv`, `wpDM_blocked_send_inv`, `wpDM_recv_inv`,
`wpDM_blocked_recv_inv`, plus `wpDM_fork_alloc₂`.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface
open Iris.BI

namespace GoLean.Iris

/-- The transfer worker: write 42 through the pointer parameter, then
send the pointer on the channel parameter. -/
def xferWorker : Func := {
  id := ⟨"xferWorker"⟩,
  args := #[{ id := "ch", typ := .chan .both (.pointer .int) },
            { id := "p", typ := .pointer .int }],
  results := #[],
  body := .seqn #[.assign (.addr (.var "p")) (.intLit 42),
                  .chanSend (.var "ch") (.var "p") (.pointer .int)]
}

/-- Main: spawn the worker on the pre-seeded channel with `&x`, then
receive-and-discard — the RESOURCE, not the value, is the payload. -/
abbrev xferProg : Stmt := .seqn
  #[.goStmt (.funcVal ⟨"xferWorker"⟩ #[]) #[.var "chv", .ref "x"],
    .chanRecv #[] (.var "chv") (.pointer .int)]

/-- Main's environment: the channel handle and the transferred cell. -/
abbrev xferEnv : LocalEnv := [[("chv", .base ⟨1⟩), ("x", .base ⟨3⟩)]]

abbrev xferHarnessCell : HeapCell := ⟨some (.int .int), .int 0 .int⟩
abbrev xferHandleCell : HeapCell :=
  ⟨some (.chan .both (.pointer .int)), .chan ⟨some (.base ⟨2⟩)⟩⟩
abbrev xferChanCell : HeapCell := ⟨none, .chanData #[] 0 false⟩
abbrev xferXCell40 : HeapCell := ⟨some (.int .int), .int 40 .int⟩
abbrev xferXCell42 : HeapCell := ⟨some (.int .int), .int 42 .int⟩

/-- The precondition: harness ∗ handle ∗ channel-data ∗ x ↦ 40. -/
abbrev xferPre : HProp :=
  .sep (.pointsTo 0 xferHarnessCell)
    (.sep (.pointsTo 1 xferHandleCell)
      (.sep (.pointsTo 2 xferChanCell) (.pointsTo 3 xferXCell40)))

/-- The postcondition: harness ∗ handle ∗ **`x ↦ 42` — RE-OWNED
through the message** (the chanData cell is surrendered to the
invariant; `x`'s cell went to the worker at the fork and came back
with the receive). -/
abbrev xferPost : HProp :=
  .sep (.pointsTo 0 xferHarnessCell)
    (.sep (.pointsTo 1 xferHandleCell) (.pointsTo 3 xferXCell42))

/-- The invariant namespace. -/
def xferN : Namespace := ndot nroot "chanTransfer"

/-- The worker's parameter cells (the spawn's `bindParams` order). -/
abbrev xferParamChCell : HeapCell :=
  ⟨some (.chan .both (.pointer .int)), .chan ⟨some (.base ⟨2⟩)⟩⟩
abbrev xferParamPCell : HeapCell :=
  ⟨some (.pointer .int), .addr (.base ⟨3⟩)⟩

/-- The child configuration over the machine-chosen first parameter
address (`wpDM_fork_alloc₂`'s discipline; `declare` prepends, so `p`
sits in front of `ch`). -/
def xferChildOf (pa : Addr) : Config :=
  .exec xferWorker.body
    [[("p", .base ⟨pa.id + 1⟩), ("ch", .base pa)]]
    (.frame [] [] [] [] .stop false)

/-- Main's continuation at the receive. -/
abbrev xferMainK : Cont := .seq [] xferEnv .stop

/-- The message protocol: the value IS `&x`, and it CARRIES `x ↦ 42`. -/
abbrev xferP {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF] :
    GoValue → IProp GF := fun v =>
  iprop(⌜v = .addr (.base ⟨3⟩)⌝ ∗ (3 : Nat) ↦ xferXCell42)

/-- The zero-target delivery is `.next k` (σ- and value-independent). -/
theorem xferDel (σ : ExecState) (v : GoValue) :
    resumeRecvDelivery σ v true [] xferEnv xferMainK
      = .ok (.next xferMainK, σ) := rfl

/-- The channel handle rides through parameter normalization. -/
theorem xferNormChan (σ : ExecState) :
    normalizeValueForTy σ (.chan .both (.pointer .int))
      (.chan ⟨some (.base ⟨2⟩)⟩) = .ok (.chan ⟨some (.base ⟨2⟩)⟩) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

/-- The pointer rides through normalization at its declared type
(parameter binding AND the send's element type). -/
theorem xferNormPtr (σ : ExecState) :
    normalizeValueForTy σ (.pointer .int)
      (.addr (.base ⟨3⟩)) = .ok (.addr (.base ⟨3⟩)) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 3200000 in
/-- **The DM-carrier walk of the transfer program** — the discharge
witness for the whole ChanDMRes family (module docstring). -/
theorem wpDM_chan_transfer_witness
    (hprog : GoCoreGS.prog GF = #[xferWorker])
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) xferPre
      ⊢ WP (PoolCfgDM.mk (.exec xferProg xferEnv .stop))
        @ Stuckness.MaybeStuck ; ⊤ {{ _v, embed (GF := GF) xferPost }} := by
  iintro HP
  simp only [xferPre, xferPost, embed]
  icases HP with ⟨H0, H1, H2, Hx⟩
  -- surrender the chanData cell to the resource-protocol invariant
  iapply fupd_wp
  imod inv_alloc xferN ⊤ (chanInv (GF := GF) ⟨2⟩ 0 xferP) $$ [H2] with Hinv
  · inext
    iexists (#[] : Array GoValue)
    isplitr [H2]
    · simp only [Array.toList_empty]
      iapply (BigSepL.bigSepL_nil (Φ := fun _ v => xferP (GF := GF) v)).2
      itrivial
    · iexact H2
  icases Hinv with #Hinv
  imodintro
  -- main: seqn entry, head → the go statement
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqn)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr1
  simp only [seqCont]
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqNext)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr2
  -- main: goStmt entry + callee literal
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goStmtEntry)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr3
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.evalStrictNullary rfl rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq
      case evalStrictNullary op v hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"xferWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"xferWorker"⟩ [], σ) from rfl] at happly
        injection happly with hp
        injection hp with hv hσ
        subst hv
        subst hσ
        exact ⟨rfl, rfl⟩
      case evalStrictNullaryPanic op msg hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"xferWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"xferWorker"⟩ [], σ) from rfl] at happly
        cases happly
      all_goals simp_all [strictPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr4
  -- main: first spawn argument (the handle)
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goCalleeArg rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr5
  iapply (wpDM_eval_var (a := ⟨1⟩) (cell := xferHandleCell) (hres := rfl))
  isplitl [H1]
  · iexact H1
  iintro H1
  -- main: second spawn argument (&x — a pure ref)
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goArgNext)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr6
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.evalRef rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [strictPlan,
        show xferEnv.lookup "x" = some (.base ⟨3⟩) from rfl]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr7
  -- main: THE TWO-PARAMETER ALLOCATING FORK — x's cell goes to the child
  iapply (wpDM_fork_alloc₂ xferChildOf
    (pcell₁ := xferParamChCell) (pcell₂ := xferParamPCell) (hsp := rfl)
    (hspawn := by
      intro σ hf hm ht
      simp +decide [spawnStep, enterFrame, findFunctionIn?, xferWorker,
        dynamicDispatch?, bindParams, allocDecls, pinResultLocs,
        methodInfoByFuncId?, hf, hm, hprog, hmeths, xferChildOf,
        LocalEnv.declare, xferNormChan, xferNormPtr, allocMany,
        ExecState.alloc, ExecState.freshLoc,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl [Hx]
  · -- THE CHILD: write 42 through p, send &x paying the resource
    inext
    iintro %pa ⟨Hpch, Hpp⟩
    simp only [xferChildOf, xferWorker]
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqn)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc1
    simp only [seqCont]
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqNext)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc1b
    -- child: the assign spine — target phase 1 (read p)
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.assignFirst (lhs := .addr (.var "p"))
        (rhs := .intLit 42) (sh := .chain []) (e := .var "p") (ops := []) rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan, targetPlan,
          targetSpine]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc2
    iapply (wpDM_eval_var (a := ⟨pa.id + 1⟩) (cell := xferParamPCell)
      (hres := by simp [LocalEnv.lookup, Scope.lookup]))
    isplitl [Hpp]
    · iexact Hpp
    iintro Hpp
    -- child: target completes, RHS evaluates
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.tgtOpRhs rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [completeTargetRef, indexStepCount]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc3
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.evalIntLit)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [strictPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc4
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.rhsStores rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq with
        | rhsStores h =>
            simp only [applyRhsOp, Pure.pure, Except.pure,
              Except.ok.injEq] at h
            subst h
            simp
        | rhsStoresPanic h =>
            simp [applyRhsOp, Pure.pure, Except.pure] at h))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc5
    -- child: THE STORE THROUGH THE POINTER: *p := 42 (x's cell, child-owned)
    iapply (wpDM_store_step (a := ⟨3⟩) (oldcell := xferXCell40)
      (newcell := xferXCell42)
      (c₁ := .next (.storeK [] []
        (.seqn #[]) [[("p", .base ⟨pa.id + 1⟩), ("ch", .base pa)]]
        (.seq [.chanSend (.var "ch") (.var "p") (.pointer .int)]
          [[("p", .base ⟨pa.id + 1⟩), ("ch", .base pa)]]
          (.frame [] [] [] [] .stop false))))
      (hnv := rfl) (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := by
        intro σ₁ _hf _hm _ht hlook
        have hstore : storeTarget σ₁
            (.chain (.addr (.base ⟨3⟩)) [] [])
            (.int ((IntKind.unbounded "integer").normalize 42)
              (.unbounded "integer"))
            = .ok { σ₁ with
                heap := Heap.set σ₁.heap (.base ⟨3⟩) xferXCell42 } := by
          simp [storeTarget, resolveChain, valueAsLoc, storeLoc, hlook,
            rdvNorm42 σ₁, Bind.bind, Except.bind, Pure.pure, Except.pure]
        refine ⟨Step.storeStep hstore, ?_⟩
        intro c' s' hst
        cases hst with
        | storeStep h' =>
          rw [hstore] at h'
          injection h' with h'
          exact ⟨rfl, h'.symm⟩
        | storeStepPanic h' =>
          rw [hstore] at h'
          cases h'))
    isplitl [Hx]
    · iexact Hx
    iintro Hx
    -- child: drain the store frame, on to the send
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.storeDone)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc6
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqn)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc7
    simp only [seqCont, Array.toList_empty, List.nil_append, if_true]
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqNext)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc9
    -- child: the send spine
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStFirst rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc10
    iapply (wpDM_eval_var (a := pa) (cell := xferParamChCell)
      (hres := by simp [LocalEnv.lookup, Scope.lookup]))
    isplitl [Hpch]
    · iexact Hpch
    iintro Hpch
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStShift)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc11
    iapply (wpDM_eval_var (a := ⟨pa.id + 1⟩) (cell := xferParamPCell)
      (hres := by simp [LocalEnv.lookup, Scope.lookup]))
    isplitl [Hpp]
    · iexact Hpp
    iintro Hpp
    -- child: THE SEND APPLY under the resource protocol — PAY x ↦ 42
    iapply (wpDM_send_inv (a := ⟨2⟩) (cap := 0) (Ψ := xferP)
      (v' := .addr (.base ⟨3⟩))
      (hN := CoPset.subseteq_top)
      (hnorm := fun σ _ => xferNormPtr σ))
    isplitl []
    · iexact Hinv
    isplitl [Hx]
    · isplitr [Hx]
      · ipureintro
        rfl
      · iexact Hx
    iintro %c₂ Hc₂
    icases Hc₂ with (⟨%hc₂, HΨ⟩ | %hc₂)
    · -- parked sender: the deposit completes it (the resource re-paid)
      subst hc₂
      iapply (wpDM_blocked_send_inv (a := ⟨2⟩) (cap := 0) (Ψ := xferP)
        (hN := CoPset.subseteq_top))
      isplitl []
      · iexact Hinv
      isplitl [HΨ]
      · iexact HΨ
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc12
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.frameFall)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc13
      iapply (wp_value' (v := ()))
      itrivial
    · -- immediate push: same tail
      subst hc₂
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc14
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.frameFall)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc15
      iapply (wp_value' (v := ()))
      itrivial
  · -- THE PARENT: strip, receive (the resource comes back), stop
    inext
    iapply wpDM_spawned_strip
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcr8
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqNext)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcr9
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStFirst rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;>
          simp_all [stmtPlan, chanPlan, syncPlan, targetsPlan, targetPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcr10
    iapply (wpDM_eval_var (a := ⟨1⟩) (cell := xferHandleCell) (hres := rfl))
    isplitl [H1]
    · iexact H1
    iintro H1
    -- main: THE RECEIVE APPLY under the resource protocol
    iapply (wpDM_recv_inv (a := ⟨2⟩) (cap := 0) (Ψ := xferP)
      (targets := []) (elem := .pointer .int)
      (hN := CoPset.subseteq_top)
      (deliverCfg := fun _ => .next xferMainK)
      (hdel := xferDel))
    isplitl []
    · iexact Hinv
    iintro %c₂ Hc₂
    icases Hc₂ with (%hc₂ | ⟨%v, %hc₂, HΨ⟩)
    · -- parked receiver: the drain delivers the resource
      subst hc₂
      iapply (wpDM_blocked_recv_inv (a := ⟨2⟩) (cap := 0) (Ψ := xferP)
        (targets := []) (elem := .pointer .int)
        (hN := CoPset.subseteq_top)
        (deliverCfg := fun _ => .next xferMainK)
        (hdel := xferDel))
      isplitl []
      · iexact Hinv
      iintro %c₃ Hc₃
      icases Hc₃ with ⟨%v, %hc₃, HΨ⟩
      subst hc₃
      icases HΨ with ⟨%hv, Hx⟩
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcr11
      iapply (wp_value' (v := ()))
      isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      · iexact Hx
    · -- immediate drain
      subst hc₂
      icases HΨ with ⟨%hv, Hx⟩
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcr12
      iapply (wp_value' (v := ()))
      isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      · iexact Hx

end

/-- **The frame-quantified resource-transfer `GoTripleC`** — every
`.normal` completion from ANY admissible seeded heap leaves `x = 42`
(with the harness and handle intact): the post's `x ↦ 42` is re-owned
THROUGH the message, compositionally. Run-conditioned as always; the
completion pin below carries the existence evidence. -/
theorem chanTransferTripleC :
    GoTripleC [] #[xferWorker] #[] xferEnv xferPre xferProg xferPost :=
  goTripleC_of_wpDM (fun hprog hmeths _htypes =>
    wpDM_chan_transfer_witness hprog hmeths)

/-- The seeded state for the D1 pair. -/
def xferSeed : ExecState :=
  { types := [], functions := #[xferWorker], methods := #[],
    heap := [(.base ⟨0⟩, xferHarnessCell), (.base ⟨1⟩, xferHandleCell),
             (.base ⟨2⟩, xferChanCell), (.base ⟨3⟩, xferXCell40)],
    nextAddr := 4 }

/-- ONE HALF of the witness pair: the run-conditioned first-order
readout at the seed — **including the 42 pin**. -/
theorem chanTransferReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel xferEnv xferSeed ch xferProg = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 0 .int)
        ∧ loadLoc σf (.base ⟨1⟩) = .ok (.chan ⟨some (.base ⟨2⟩)⟩)
        ∧ loadLoc σf (.base ⟨3⟩) = .ok (.int 42 .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf xferSeed.heap) xferPre := by
    show sat (((((∅ : Heaplet).insert 3 xferXCell40).insert 2
      xferChanCell).insert 1 xferHandleCell).insert 0 xferHarnessCell) xferPre
    refine sat_sep_insert ?_ (sat_sep_insert ?_ (sat_sep_insert ?_ rfl))
    · rw [heaplet_get?_insert_ne (by omega),
        heaplet_get?_insert_ne (by omega),
        heaplet_get?_insert_ne (by omega),
        heaplet_get?_empty]
    · rw [heaplet_get?_insert_ne (by omega),
        heaplet_get?_insert_ne (by omega),
        heaplet_get?_empty]
    · rw [heaplet_get?_insert_ne (by omega),
        heaplet_get?_empty]
  have hsplit := InitialSplit.noFrame (P := xferPre)
    (hp := xferSeed.heap) (na := 4)
    (funcs := #[xferWorker]) (env₀ := xferEnv) (prog := xferProg)
    hsat (by decide +kernel)
  have hres := chanTransferTripleC _ 4 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hsub, _hF, hsatQ⟩ := hres
  obtain ⟨h₁, h₂, hs₁, hs₂, -, hcover⟩ := hsatQ
  obtain ⟨h₂₁, h₂₂, hs₂₁, hs₂₂, -, hcover₂⟩ := hs₂
  have hget0 : hQ.get? 0 = some xferHarnessCell := by
    rw [hs₁] at hcover
    exact (hcover 0 xferHarnessCell).mpr
      (Or.inl (by rw [heaplet_get?_insert_self]))
  have hget1 : hQ.get? 1 = some xferHandleCell := by
    rw [hs₂₁] at hcover₂
    exact (hcover 1 xferHandleCell).mpr
      (Or.inr ((hcover₂ 1 xferHandleCell).mpr
        (Or.inl (by rw [heaplet_get?_insert_self]))))
  have hget3 : hQ.get? 3 = some xferXCell42 := by
    rw [hs₂₂] at hcover₂
    exact (hcover 3 xferXCell42).mpr
      (Or.inr ((hcover₂ 3 xferXCell42).mpr
        (Or.inr (by rw [heaplet_get?_insert_self]))))
  refine ⟨?_, ?_, ?_⟩
  · have hg := hsub 0 xferHarnessCell hget0
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg
  · have hg := hsub 1 xferHandleCell hget1
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg
  · have hg := hsub 3 xferXCell42 hget3
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg

/-- The completion half's kernel certificate: every schedule completes
at main's `.normal` with the three cells at their pinned values —
`x = 42` included ("every schedule" = every REGISTRY-POINT schedule — the settled S4 NPDRF caption, docs/2026-08-11_npdrf-reduction.md §6; sub-registry transfer is unproved). (`#eval`-confirmed before `decide`, per doctrine.) -/
theorem chanTransferAllStreamsCert :
    allStreamsOkPool
      (fun σf =>
        match loadLoc σf (.base ⟨0⟩), loadLoc σf (.base ⟨1⟩),
            loadLoc σf (.base ⟨3⟩) with
        | .ok (.int 0 .int), .ok (.chan ⟨some (.base ⟨2⟩)⟩),
            .ok (.int 42 .int) => true
        | _, _, _ => false)
      500 ⟨#[.exec xferProg xferEnv .stop], xferSeed, 0⟩ {} = true := by
  decide +kernel

/-- THE OTHER HALF of the witness pair: the seeded completion pin. -/
theorem chanTransferTerminatesNormallyC :
    TerminatesNormallyC xferEnv xferSeed xferProg := by
  refine ⟨500, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool chanTransferAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Iris
