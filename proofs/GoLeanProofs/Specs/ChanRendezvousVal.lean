import GoLeanProofs.ChanDM
import GoLeanProofs.Specs.ChanRendezvous

/-!
# The VALUE-PINNING rendezvous exemplar (channel-logic slice 2, item 3)

**The claim slice 1 explicitly could not make** (its docstrings
disclaimed it; `docs/2026-08-11_channel-wp-laws.md` §4): a
frame-quantified triple whose post pins THE DELIVERED VALUE. The
program is the S1 exemplar with the receive TARGETED — the worker
sends 42, main receives INTO `x` — and the route is the slice-2
protocol layer end to end: the Ψ-protocol invariant
(`chanInvP … (· = .int 42 .int)`) over the MEDIATED carrier
(`LangDM`), the value-protocol laws (`ChanDM`), the delivery-frame
store walk, and the `goTripleC_of_wpDM` exit. Every `.normal`
completion, from ANY admissible heap containing the four `P`-cells,
leaves `x = 42` — the receiver can only be delivered the physical
buffer head, and the invariant pins every buffered value to 42.

D1-BOTH per the convention: `chanRendezvousValReadoutC` (run-
conditioned first-order readout at the seed, 42 pin included) +
`chanRendezvousValTerminatesNormallyC` (the seeded completion pin via
the kernel certificate, `#eval`-confirmed first). The triple alone
remains run-conditioned (the standing `ChanVacuityWarning` lesson);
the completion pin carries the existence evidence. The ∀-heap safety
half for THIS program is the pool-reachability lane's standing
successor work (P-S4-1 paid the spawn-noop instance this same slice;
a channel-program instance needs protocol content in its pool
invariant — recorded, design note §7).

This module is the same-commit DISCHARGE WITNESS for every ChanDM law:
`wpDM_send_invP`, `wpDM_blocked_send_invP`, `wpDM_recv_invP`,
`wpDM_blocked_recv_invP`, plus the LangDM kit
(`wpDM_pure_det`, `wpDM_spawned_strip`, `wpDM_eval_var`,
`wpDM_store_step`, `wpDM_fork_alloc₁`, `goTripleC_of_wpDM`).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris

/-- Main: spawn the worker on the pre-seeded channel, then receive
INTO `x` (the targeted form — the delivered value lands in the heap). -/
abbrev rdvValProg : Stmt := .seqn
  #[.goStmt (.funcVal ⟨"rdvWorker"⟩ #[]) #[.var "chv"],
    .chanRecv #[.var "x"] (.var "chv") .int]

/-- Main's environment: the channel handle and the receive target. -/
abbrev rdvValEnv : LocalEnv := [[("chv", .base ⟨1⟩), ("x", .base ⟨3⟩)]]

/-- The receive target's cell, before (zero) and after (the pinned 42). -/
abbrev rdvValXCell : HeapCell := ⟨some (.int .int), .int 0 .int⟩
abbrev rdvValXCell42 : HeapCell := ⟨some (.int .int), .int 42 .int⟩

/-- The value protocol: everything this channel carries is 42. -/
abbrev rdvVal42P : GoValue → Prop := fun v => v = .int 42 .int

/-- The precondition: harness ∗ handle ∗ channel-data ∗ target. -/
abbrev rdvValPre : HProp :=
  .sep (.pointsTo 0 rdvHarnessCell)
    (.sep (.pointsTo 1 rdvHandleCell)
      (.sep (.pointsTo 2 rdvChanCell) (.pointsTo 3 rdvValXCell)))

/-- The postcondition: harness ∗ handle ∗ **`x = 42`** (the chanData
cell is surrendered to the invariant, as in S1). -/
abbrev rdvValPost : HProp :=
  .sep (.pointsTo 0 rdvHarnessCell)
    (.sep (.pointsTo 1 rdvHandleCell) (.pointsTo 3 rdvValXCell42))

/-- The invariant namespace. -/
def rdvValN : Namespace := ndot nroot "chanRendezvousVal"

/-- Main's continuation at the receive. -/
abbrev rdvValK : Cont := .seq [] rdvValEnv .stop

/-- The machine's delivery entry for the `x` target (σ-independent —
the `wpDM_recv_invP` `deliverCfg` idiom). -/
def rdvValDeliver (v : GoValue) : Config :=
  .evalE (.ref "x") rdvValEnv
    (.tgtOpK (.chain []) [] [] [] [] .vals [] [v] (.seqn #[]) rdvValEnv rdvValK)

/-- The delivery-entry equation the receive laws consume. -/
theorem rdvValDel (σ : ExecState) (v : GoValue) :
    resumeRecvDelivery σ v true [.var "x"] rdvValEnv rdvValK
      = .ok (rdvValDeliver v, σ) := rfl

/-- `.int 42 .int` is self-normalized (the store's coercion). -/
theorem rdvValNormInt42 (σ : ExecState) :
    normalizeValueForTy σ .int (.int 42 .int) = .ok (.int 42 .int) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]
  decide

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- The delivery-frame walk: store the (Ψ-pinned) 42 into `x` and fall
out to main's terminal — shared by the immediate-drain and
park-then-drain branches. -/
private theorem rdvVal_delivery_walk {P0 P1 : IProp GF}
    (hP0 : P0 = iprop((0 : Nat) ↦ rdvHarnessCell))
    (hP1 : P1 = iprop((1 : Nat) ↦ rdvHandleCell)) :
    P0 ∗ P1 ∗ (3 : Nat) ↦ rdvValXCell
      ⊢ WP (PoolCfgDM.mk (rdvValDeliver (.int 42 .int)))
          @ Stuckness.MaybeStuck ; ⊤
          {{ _v, iprop(P0 ∗ P1 ∗ (3 : Nat) ↦ rdvValXCell42) }} := by
  subst hP0 hP1
  iintro ⟨H0, H1, Hx⟩
  simp only [rdvValDeliver]
  -- evaluate the target reference
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.evalRef rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [strictPlan,
        show rdvValEnv.lookup "x" = some (.base ⟨3⟩) from rfl]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcd1
  -- complete the target ref, enter the stores
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.tgtOpStores rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [completeTargetRef, indexStepCount]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcd2
  -- THE STORE: x := 42
  iapply (wpDM_store_step (a := ⟨3⟩) (oldcell := rdvValXCell)
    (newcell := rdvValXCell42)
    (c₁ := .next (.storeK [] [] (.seqn #[]) rdvValEnv rdvValK))
    (hnv := rfl) (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := by
      intro σ₁ _hf _hm _ht hlook
      have hstore : storeTarget σ₁
          (.chain (.addr (.base ⟨3⟩)) [] []) (.int 42 .int)
          = .ok { σ₁ with
              heap := Heap.set σ₁.heap (.base ⟨3⟩) rdvValXCell42 } := by
        simp [storeTarget, resolveChain, valueAsLoc, storeLoc, hlook,
          rdvValNormInt42 σ₁, Bind.bind, Except.bind, Pure.pure, Except.pure]
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
  -- fall out: storeDone, the empty body, the two seq exits
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.storeDone)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcd3
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqn)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcd4
  simp only [rdvValK, seqCont, List.nil_append, if_true]
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqDone)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcd5
  iapply (wp_value' (v := ()))
  isplitl [H0]
  · iexact H0
  isplitl [H1]
  · iexact H1
  · iexact Hx

set_option maxHeartbeats 3200000 in
/-- **The DM-carrier walk of the value-pinning rendezvous** — the
discharge witness for the whole ChanDM family (module docstring). -/
theorem wpDM_chan_rendezvous_val_witness
    (hprog : GoCoreGS.prog GF = #[rdvWorker])
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) rdvValPre
      ⊢ WP (PoolCfgDM.mk (.exec rdvValProg rdvValEnv .stop))
        @ Stuckness.MaybeStuck ; ⊤ {{ _v, embed (GF := GF) rdvValPost }} := by
  iintro HP
  simp only [rdvValPre, rdvValPost, embed]
  icases HP with ⟨H0, H1, H2, Hx⟩
  -- surrender the chanData cell to the Ψ-protocol invariant
  iapply fupd_wp
  imod inv_alloc rdvValN ⊤ (chanInvP (GF := GF) ⟨2⟩ 0 rdvVal42P) $$ [H2] with Hinv
  · inext
    iexists (#[] : Array GoValue)
    isplitr [H2]
    · ipureintro
      intro v hv
      cases hv
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
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"rdvWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"rdvWorker"⟩ [], σ) from rfl] at happly
        injection happly with hp
        injection hp with hv hσ
        subst hv
        subst hσ
        exact ⟨rfl, rfl⟩
      case evalStrictNullaryPanic op msg hplan happly =>
        simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
        obtain ⟨rfl, -⟩ := hplan
        rw [show applyStrictOp σ (StrictOp.funcValOf ⟨"rdvWorker"⟩) []
            = .ok (GoValue.funcVal ⟨"rdvWorker"⟩ [], σ) from rfl] at happly
        cases happly
      all_goals simp_all [strictPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr4
  iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goCalleeArg rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcr5
  -- main: load the channel handle for the spawn argument
  iapply (wpDM_eval_var (a := ⟨1⟩) (cell := rdvHandleCell) (hres := rfl))
  isplitl [H1]
  · iexact H1
  iintro H1
  -- main: THE ALLOCATING FORK
  iapply (wpDM_fork_alloc₁ rdvChildOf (pcell := rdvParamCell) (hsp := rfl)
    (hspawn := by
      intro σ hf hm ht
      simp +decide [spawnStep, enterFrame, findFunctionIn?, rdvWorker,
        dynamicDispatch?, bindParams, allocDecls, pinResultLocs,
        methodInfoByFuncId?, hf, hm, hprog, hmeths, rdvChildOf, LocalEnv.declare,
        rdvNormChan σ, allocMany, ExecState.alloc, ExecState.freshLoc,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl []
  · -- THE CHILD: send 42 under the protocol (pays Ψ at the push)
    inext
    iintro %pa Hp
    simp only [rdvChildOf]
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
    iintro Hcc2
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStFirst rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc3
    iapply (wpDM_eval_var (a := pa) (cell := rdvParamCell) (hres := rfl))
    isplitl [Hp]
    · iexact Hp
    iintro Hp
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStShift)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc4
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.evalIntLit)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [strictPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcc5
    -- child: THE SEND APPLY under the value protocol
    iapply (wpDM_send_invP (a := ⟨2⟩) (cap := 0) (Ψp := rdvVal42P)
      (v' := .int 42 .int)
      (hN := CoPset.subseteq_top)
      (hnorm := fun σ _ => rdvNorm42 σ)
      (hΨ := rfl))
    isplitl []
    · iexact Hinv
    iintro %c₂ %hc₂
    rcases hc₂ with rfl | rfl
    · -- parked sender: the deposit completes it (Ψ paid again)
      iapply (wpDM_blocked_send_invP (a := ⟨2⟩) (cap := 0) (Ψp := rdvVal42P)
        (hN := CoPset.subseteq_top) (hΨ := rfl))
      isplitl []
      · iexact Hinv
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc6
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.frameFall)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc7
      iapply (wp_value' (v := ()))
      itrivial
    · -- immediate push: same tail
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc8
      iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.frameFall)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcc9
      iapply (wp_value' (v := ()))
      itrivial
  · -- THE PARENT: strip, receive INTO x, deliver, stop
    inext
    iapply wpDM_spawned_strip
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcr6
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqNext)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcr7
    iapply (wpDM_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStFirst rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;>
          simp_all [stmtPlan, chanPlan, syncPlan, targetsPlan, targetPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcr8
    iapply (wpDM_eval_var (a := ⟨1⟩) (cell := rdvHandleCell) (hres := rfl))
    isplitl [H1]
    · iexact H1
    iintro H1
    -- main: THE RECEIVE APPLY under the value protocol
    iapply (wpDM_recv_invP (a := ⟨2⟩) (cap := 0) (Ψp := rdvVal42P)
      (targets := [.var "x"]) (elem := .int)
      (hN := CoPset.subseteq_top)
      (deliverCfg := rdvValDeliver)
      (hdel := rdvValDel))
    isplitl []
    · iexact Hinv
    iintro %c₂ %hc₂
    rcases hc₂ with rfl | ⟨v, rfl, hv⟩
    · -- parked receiver: the drain delivers the Ψ-pinned head
      iapply (wpDM_blocked_recv_invP (a := ⟨2⟩) (cap := 0) (Ψp := rdvVal42P)
        (targets := [.var "x"]) (elem := .int)
        (hN := CoPset.subseteq_top)
        (deliverCfg := rdvValDeliver)
        (hdel := rdvValDel))
      isplitl []
      · iexact Hinv
      iintro %c₃ %hc₃
      obtain ⟨v, rfl, hv⟩ := hc₃
      rw [show v = GoValue.int 42 .int from hv]
      iapply (rdvVal_delivery_walk rfl rfl)
      isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      · iexact Hx
    · -- immediate drain
      rw [show v = GoValue.int 42 .int from hv]
      iapply (rdvVal_delivery_walk rfl rfl)
      isplitl [H0]
      · iexact H0
      isplitl [H1]
      · iexact H1
      · iexact Hx

end

/-- **The frame-quantified value-pinning `GoTripleC`** — every
`.normal` completion from ANY admissible seeded heap leaves
`x = 42` (with the harness and handle intact): the delivered value is
pinned THROUGH the protocol layer, compositionally. Run-conditioned as
always; the completion pin below carries the existence evidence. -/
theorem chanRendezvousValTripleC :
    GoTripleC [] #[rdvWorker] #[] rdvValEnv rdvValPre rdvValProg rdvValPost :=
  goTripleC_of_wpDM (fun hprog hmeths _htypes =>
    wpDM_chan_rendezvous_val_witness hprog hmeths)

/-- The seeded state for the D1 pair. -/
def rdvValSeed : ExecState :=
  { types := [], functions := #[rdvWorker], methods := #[],
    heap := [(.base ⟨0⟩, rdvHarnessCell), (.base ⟨1⟩, rdvHandleCell),
             (.base ⟨2⟩, rdvChanCell), (.base ⟨3⟩, rdvValXCell)],
    nextAddr := 4 }

/-- ONE HALF of the witness pair: the run-conditioned first-order
readout at the seed — **including the 42 pin**: every `.normal` pool
completion leaves `loadLoc σf x = 42`. -/
theorem chanRendezvousValReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel rdvValEnv rdvValSeed ch rdvValProg
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 0 .int)
        ∧ loadLoc σf (.base ⟨1⟩) = .ok (.chan ⟨some (.base ⟨2⟩)⟩)
        ∧ loadLoc σf (.base ⟨3⟩) = .ok (.int 42 .int) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf rdvValSeed.heap) rdvValPre := by
    show sat (((((∅ : Heaplet).insert 3 rdvValXCell).insert 2
      rdvChanCell).insert 1 rdvHandleCell).insert 0 rdvHarnessCell) rdvValPre
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
  have hsplit := InitialSplit.noFrame (P := rdvValPre)
    (hp := rdvValSeed.heap) (na := 4)
    (funcs := #[rdvWorker]) (env₀ := rdvValEnv) (prog := rdvValProg)
    hsat (by decide +kernel)
  have hres := chanRendezvousValTripleC _ 4 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hsub, _hF, hsatQ⟩ := hres
  obtain ⟨h₁, h₂, hs₁, hs₂, -, hcover⟩ := hsatQ
  obtain ⟨h₂₁, h₂₂, hs₂₁, hs₂₂, -, hcover₂⟩ := hs₂
  have hget0 : hQ.get? 0 = some rdvHarnessCell := by
    rw [hs₁] at hcover
    exact (hcover 0 rdvHarnessCell).mpr
      (Or.inl (by rw [heaplet_get?_insert_self]))
  have hget1 : hQ.get? 1 = some rdvHandleCell := by
    rw [hs₂₁] at hcover₂
    exact (hcover 1 rdvHandleCell).mpr
      (Or.inr ((hcover₂ 1 rdvHandleCell).mpr
        (Or.inl (by rw [heaplet_get?_insert_self]))))
  have hget3 : hQ.get? 3 = some rdvValXCell42 := by
    rw [hs₂₂] at hcover₂
    exact (hcover 3 rdvValXCell42).mpr
      (Or.inr ((hcover₂ 3 rdvValXCell42).mpr
        (Or.inr (by rw [heaplet_get?_insert_self]))))
  refine ⟨?_, ?_, ?_⟩
  · have hg := hsub 0 rdvHarnessCell hget0
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg
  · have hg := hsub 1 rdvHandleCell hget1
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg
  · have hg := hsub 3 rdvValXCell42 hget3
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg

/-- The completion half's kernel certificate: every schedule completes
at main's `.normal` with the three cells at their pinned values —
`x = 42` included ("every schedule" = every REGISTRY-POINT schedule — the settled S4 NPDRF caption, docs/2026-08-11_npdrf-reduction.md §6; sub-registry transfer is unproved). (`#eval`-confirmed before `decide`, per doctrine.) -/
theorem chanRendezvousValAllStreamsCert :
    allStreamsOkPool
      (fun σf =>
        match loadLoc σf (.base ⟨0⟩), loadLoc σf (.base ⟨1⟩),
            loadLoc σf (.base ⟨3⟩) with
        | .ok (.int 0 .int), .ok (.chan ⟨some (.base ⟨2⟩)⟩),
            .ok (.int 42 .int) => true
        | _, _, _ => false)
      500 ⟨#[.exec rdvValProg rdvValEnv .stop], rdvValSeed, 0⟩ {} = true := by
  decide +kernel

/-- THE OTHER HALF of the witness pair: the seeded completion pin. -/
theorem chanRendezvousValTerminatesNormallyC :
    TerminatesNormallyC rdvValEnv rdvValSeed rdvValProg := by
  refine ⟨500, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool chanRendezvousValAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Iris
