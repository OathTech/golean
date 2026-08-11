import GoLeanProofs.ChanD
import GoLeanProofs.Specs.GoldenQuorumWP
import GoLean.GoCore.MultiStreams

/-!
# The channel-rendezvous exemplar (channel-logic arc slice 1, item 2)

THE EXEMPLAR, hand-proved through the channel WP laws — the route the
design note (`docs/2026-08-11_channel-wp-laws.md` §4) fixes: laws →
wpD derivation → `goTripleC_of_wpD` exit → a frame-quantified
`GoTripleC` on a program that GENUINELY communicates on a channel
across goroutines, plus the D1-BOTH pair (run-conditioned first-order
readout + seeded completion pin).

The program (`chanRendezvousProg`): main spawns `rdvWorker` on a
pre-seeded unbuffered channel and receives-and-discards (`<-chv`, the
join-signal idiom); the worker sends 42. The channel handle and data
cells arrive through the PRECONDITION (an `InitialSplit`-strength
frame-quantified pre — the makeChan walk is deliberately not part of
this exemplar; note §4 records the choice), and the chanData cell is
surrendered to an Iris invariant at the head of the WP walk, which is
why the postcondition covers only the harness and handle cells (the
triple's `Q` side is intuitionistic).

**What the triple does and does not say** (stated per the note §4;
SCOPED at the S1 audit fix round): every `.normal` completion, from
ANY admissible heap containing the three `P`-cells, leaves the
harness and handle cells intact. The triple ALONE is run-conditioned
and therefore compatible with a program that never communicates
(`deadlockRecvTripleC` in `Specs/ChanVacuityWarning.lean` is the
standing demonstration) — what distinguishes THIS bundle is the
COMPLETION PIN below: every schedule reaches main's `.normal`, and
for this program a `.normal` completion requires the real rendezvous
(the machine's only routes past main's park are the pairing with the
worker's send or the corresponding wake). The WALK — not the triple's
statement — is what exercises the park/pair/release law positions.
The bundle says NOTHING about the value 42
(the protocol layer, slice 2 — the fork/join GOLDEN certificates
carry seeded 42-verdicts beside this) and nothing about ∀-heap
deadlock-freedom (`ProgressExecC`, the pool-reachability lane,
P-S4-1). The completion half of the D1 pair below is the SEEDED
kernel certificate, exactly the `spawnNoop`/`forkJoin` house idiom.

This module is the same-commit DISCHARGE WITNESS for every law it
walks: `wpD_send_rendezvous_inv`, `wpD_recv_nil_rendezvous_inv`,
`wpD_blocked_send_rendezvous_inv`, `wpD_blocked_recv_nil_rendezvous_inv`,
`wpD_fork_alloc₁`, `wpD_eval_var`, `wpD_det_step_keep` (via
`wpD_eval_var`), alongside the LangD kit (`wpD_pure_det`,
`wpD_spawned_strip`, `goTripleC_of_wpD`).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Surface

namespace GoLean.Iris

/-- The rendezvous worker: send 42 on the channel parameter. -/
def rdvWorker : Func := {
  id := ⟨"rdvWorker"⟩,
  args := #[{ id := "ch", typ := .chan .both .int }],
  results := #[],
  body := .seqn #[.chanSend (.var "ch") (.intLit 42) .int]
}

/-- Main: spawn the worker on the pre-seeded channel, then
receive-and-discard (the join signal). -/
abbrev chanRendezvousProg : Stmt := .seqn
  #[.goStmt (.funcVal ⟨"rdvWorker"⟩ #[]) #[.var "chv"],
    .chanRecv #[] (.var "chv") .int]

/-- Main's environment: `chv` at base 1 (the handle cell). -/
abbrev rdvEnv : LocalEnv := [[("chv", .base ⟨1⟩)]]

/-- The harness cell (never touched by any channel machinery). -/
abbrev rdvHarnessCell : HeapCell := ⟨some (.int .int), .int 0 .int⟩

/-- The channel-handle cell: `chv`'s value, pointing at the data cell. -/
abbrev rdvHandleCell : HeapCell :=
  ⟨some (.chan .both .int), .chan ⟨some (.base ⟨2⟩)⟩⟩

/-- The channel DATA cell: unbuffered, open, empty — the rendezvous
shape the invariant pins (`makeChan` allocates exactly this, untyped). -/
abbrev rdvChanCell : HeapCell := ⟨none, .chanData #[] 0 false⟩

/-- The precondition: harness ∗ handle ∗ channel-data. -/
abbrev rdvPre : HProp :=
  .sep (.pointsTo 0 rdvHarnessCell)
    (.sep (.pointsTo 1 rdvHandleCell) (.pointsTo 2 rdvChanCell))

/-- The postcondition: harness ∗ handle (the data cell is surrendered
to the invariant — module docstring). -/
abbrev rdvPost : HProp :=
  .sep (.pointsTo 0 rdvHarnessCell) (.pointsTo 1 rdvHandleCell)

/-- The invariant namespace for the exemplar's channel. -/
def rdvN : Namespace := ndot nroot "chanRendezvous"

/-- The worker's parameter cell (allocated by the spawn's
`bindParams`: the handle value, normalized at the declared type). -/
abbrev rdvParamCell : HeapCell :=
  ⟨some (.chan .both .int), .chan ⟨some (.base ⟨2⟩)⟩⟩

/-- The child configuration as a function of the machine-chosen
parameter address (`wpD_fork_alloc₁`'s `∀ pa` discipline). -/
def rdvChildOf (pa : Addr) : Config :=
  .exec (.seqn #[.chanSend (.var "ch") (.intLit 42) .int])
    [[("ch", .base pa)]] (.frame [] [] [] [] .stop false)

/-- The untyped `42` literal normalizes at `int` (σ-independent; the
send law's `hnorm` premise at the exemplar's value). -/
theorem rdvNorm42 (σ : ExecState) :
    normalizeValueForTy σ .int
      (.int ((IntKind.unbounded "integer").normalize 42) (.unbounded "integer"))
      = .ok (.int 42 .int) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]
  decide

/-- The channel handle rides through parameter normalization at the
declared channel type (σ-independent; feeds the fork's `hspawn`). -/
theorem rdvNormChan (σ : ExecState) :
    normalizeValueForTy σ (.chan .both .int)
      (.chan ⟨some (.base ⟨2⟩)⟩) = .ok (.chan ⟨some (.base ⟨2⟩)⟩) := by
  simp only [normalizeValueForTy]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp [normalizeValueForTyFuel]

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

set_option maxHeartbeats 3200000 in
/-- **The D-carrier walk of the rendezvous program** — main and the
spawned worker both, through the channel laws under the invariant
allocated from the pre's chanData cell. The discharge witness for the
rendezvous law family (module docstring). -/
theorem wpD_chan_rendezvous_witness
    (hprog : GoCoreGS.prog GF = #[rdvWorker])
    (hmeths : GoCoreGS.methods GF = #[]) :
    embed (GF := GF) rdvPre
      ⊢ WP (PoolCfgD.mk (.exec chanRendezvousProg rdvEnv .stop))
        {{ _v, embed (GF := GF) rdvPost }} := by
  iintro HP
  simp only [rdvPre, rdvPost, embed]
  icases HP with ⟨H0, H1, H2⟩
  -- surrender the chanData cell to the invariant
  iapply fupd_wp
  imod inv_alloc rdvN ⊤ (iprop((2 : Nat) ↦ rdvChanCell)) $$ [H2] with Hinv
  · inext
    iexact H2
  icases Hinv with #Hinv
  imodintro
  -- main: seqn entry (pure det)
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqn)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred1
  simp only [seqCont]
  -- main: seq head → the go statement
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.seqNext)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred2
  -- main: goStmt entry (pure det)
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goStmtEntry)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred3
  -- main: the callee literal evaluates (nullary strict op, pure det)
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
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
  iintro Hcred4
  -- main: shift to the spawn argument (pure det)
  iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
    (hstep := fun σ => Step.goCalleeArg rfl)
    (hdet := by
      intro σ c₂ σ₂ sq
      cases sq <;> simp_all))
  iapply fupd_intro
  inext
  iapply fupd_intro
  iintro Hcred5
  -- main: load the channel handle (the handle cell rides through)
  iapply (wpD_eval_var (a := ⟨1⟩) (cell := rdvHandleCell) (hres := rfl))
  isplitl [H1]
  · iexact H1
  iintro H1
  -- main: THE ALLOCATING FORK
  iapply (wpD_fork_alloc₁ rdvChildOf (pcell := rdvParamCell) (hsp := rfl)
    (hspawn := by
      intro σ hf hm ht
      simp +decide [spawnStep, enterFrame, findFunctionIn?, rdvWorker,
        dynamicDispatch?, bindParams, allocDecls, pinResultLocs,
        methodInfoByFuncId?, hf, hm, hprog, hmeths, rdvChildOf, LocalEnv.declare,
        rdvNormChan σ, allocMany, ExecState.alloc, ExecState.freshLoc,
        Bind.bind, Except.bind, Pure.pure, Except.pure]))
  isplitl []
  · -- THE CHILD: the worker's frame — send 42, park/pair, fall out
    inext
    iintro %pa Hp
    simp only [rdvChildOf]
    -- child: seqn entry
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqn)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred6
    simp only [seqCont]
    -- child: seq head → the send statement
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqNext)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred7
    -- child: chanSend entry (pure det)
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStFirst rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [stmtPlan, chanPlan, syncPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred8
    -- child: load the channel parameter
    iapply (wpD_eval_var (a := pa) (cell := rdvParamCell) (hres := rfl))
    isplitl [Hp]
    · iexact Hp
    iintro Hp
    -- child: shift to the value operand (pure det)
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStShift)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred9
    -- child: the 42 literal (pure det)
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.evalIntLit)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all [strictPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred10
    -- child: THE SEND APPLY (park or pair — the rendezvous law)
    iapply (wpD_send_rendezvous_inv (a := ⟨2⟩) (cell := rdvChanCell)
      (v' := .int 42 .int)
      (hN := CoPset.subseteq_top) (hcv := rfl)
      (hnorm := fun σ _ => rdvNorm42 σ))
    isplitl []
    · iexact Hinv
    iintro %c₂ %hc₂
    rcases hc₂ with rfl | rfl
    · -- parked sender: release to .next (the parked law, Löb inside)
      iapply (wpD_blocked_send_rendezvous_inv (a := ⟨2⟩) (cell := rdvChanCell)
        (hN := CoPset.subseteq_top) (hcv := rfl))
      isplitl []
      · iexact Hinv
      -- after release: fall through the empty seq and the frame
      iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcred11
      iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.frameFall)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcred12
      iapply (wp_value' (v := ()))
      itrivial
    · -- immediate pairing: same tail
      iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcred13
      iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.frameFall)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all [loadMany, storeMany, Pure.pure, Except.pure]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcred14
      iapply (wp_value' (v := ()))
      itrivial
  · -- THE PARENT: strip the marker, receive, stop
    inext
    iapply wpD_spawned_strip
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred15
    -- main: seq head → the receive statement
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.seqNext)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;> simp_all))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred16
    -- main: chanRecv entry (pure det)
    iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
      (hstep := fun σ => Step.chanStFirst rfl)
      (hdet := by
        intro σ c₂ σ₂ sq
        cases sq <;>
          simp_all [stmtPlan, chanPlan, syncPlan, targetsPlan, targetPlan]))
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro Hcred17
    -- main: load the channel handle again
    iapply (wpD_eval_var (a := ⟨1⟩) (cell := rdvHandleCell) (hres := rfl))
    isplitl [H1]
    · iexact H1
    iintro H1
    -- main: THE RECEIVE APPLY (park or pair — the rendezvous law)
    iapply (wpD_recv_nil_rendezvous_inv (a := ⟨2⟩) (cell := rdvChanCell)
      (hN := CoPset.subseteq_top) (hcv := rfl))
    isplitl []
    · iexact Hinv
    iintro %c₂ %hc₂
    rcases hc₂ with rfl | rfl
    · -- parked receiver: release to .next (the parked law, Löb inside)
      iapply (wpD_blocked_recv_nil_rendezvous_inv (a := ⟨2⟩)
        (cell := rdvChanCell)
        (hN := CoPset.subseteq_top) (hcv := rfl))
      isplitl []
      · iexact Hinv
      iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcred18
      iapply (wp_value' (v := ()))
      isplitl [H0]
      · iexact H0
      · iexact H1
    · -- immediate pairing: deliver and stop
      iapply (wpD_pure_det (hsp := rfl) (hsc := rfl) (hblk := rfl) (hpos := rfl)
        (hstep := fun σ => Step.seqDone)
        (hdet := by
          intro σ c₂ σ₂ sq
          cases sq <;> simp_all))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hcred19
      iapply (wp_value' (v := ()))
      isplitl [H0]
      · iexact H0
      · iexact H1

end

/-- **The frame-quantified `GoTripleC` on the rendezvous program** —
the first triple through the D-pipe whose program communicates on a
channel across goroutines (the exit consumes the pairing simulation;
this program's own traces exercise spawn, park, pairing, and release).
Scope per the module docstring: heap preservation, not the delivered
value; the safety half remains P-S4-1's lane. -/
theorem chanRendezvousTripleC :
    GoTripleC [] #[rdvWorker] #[] rdvEnv rdvPre chanRendezvousProg rdvPost :=
  goTripleC_of_wpD (fun hprog hmeths _htypes =>
    wpD_chan_rendezvous_witness hprog hmeths)

/-- The seeded state for the D1 pair. -/
def rdvSeed : ExecState :=
  { types := [], functions := #[rdvWorker], methods := #[],
    heap := [(.base ⟨0⟩, rdvHarnessCell), (.base ⟨1⟩, rdvHandleCell),
             (.base ⟨2⟩, rdvChanCell)],
    nextAddr := 3 }

/-- ONE HALF of the witness pair (the run-conditioned readout): at the
concrete seed every `InitialSplit` premise of `chanRendezvousTripleC`
discharges, and the triple reads back first-order — every `.normal`
pool completion of the rendezvous program leaves the harness and
handle cells intact. Interpreter vocabulary only; the completion half
is `chanRendezvousTerminatesNormallyC` below (the house D1-BOTH
form). -/
theorem chanRendezvousReadoutC :
    ∀ (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices),
      execProg fuel rdvEnv rdvSeed ch chanRendezvousProg
        = .ok (.normal σf, ch') →
      loadLoc σf (.base ⟨0⟩) = .ok (.int 0 .int)
        ∧ loadLoc σf (.base ⟨1⟩) = .ok (.chan ⟨some (.base ⟨2⟩)⟩) := by
  intro fuel ch σf ch' hrun
  have hsat : sat (heapletOf rdvSeed.heap) rdvPre := by
    show sat ((((∅ : Heaplet).insert 2 rdvChanCell).insert 1
      rdvHandleCell).insert 0 rdvHarnessCell) rdvPre
    refine sat_sep_insert ?_ (sat_sep_insert ?_ rfl)
    · rw [heaplet_get?_insert_ne (by omega),
        heaplet_get?_insert_ne (by omega),
        heaplet_get?_empty]
    · rw [heaplet_get?_insert_ne (by omega),
        heaplet_get?_empty]
  have hsplit := InitialSplit.noFrame (P := rdvPre)
    (hp := rdvSeed.heap) (na := 3)
    (funcs := #[rdvWorker]) (env₀ := rdvEnv) (prog := chanRendezvousProg)
    hsat (by decide +kernel)
  have hres := chanRendezvousTripleC _ 3 _ ∅ hsplit fuel ch σf ch' hrun
  obtain ⟨hQ, _hd, hsub, _hF, hsatQ⟩ := hres
  obtain ⟨h₁, h₂, hs₁, hs₂, -, hcover⟩ := hsatQ
  -- extract the two cells' bindings from the split
  have hget0 : hQ.get? 0 = some rdvHarnessCell := by
    rw [hs₁] at hcover
    exact (hcover 0 rdvHarnessCell).mpr
      (Or.inl (by
        rw [heaplet_get?_insert_self]))
  have hget1 : hQ.get? 1 = some rdvHandleCell := by
    rw [hs₂] at hcover
    exact (hcover 1 rdvHandleCell).mpr
      (Or.inr (by
        rw [heaplet_get?_insert_self]))
  constructor
  · have hg := hsub 0 rdvHarnessCell hget0
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg
  · have hg := hsub 1 rdvHandleCell hget1
    rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at hg
    exact loadLoc_base_of_lookup hg

/-- The completion half's kernel certificate: every schedule of the
rendezvous program completes at main's `.normal` with both cells
intact, within the stated fuel. (`#eval`-confirmed before `decide`,
per doctrine.) -/
theorem chanRendezvousAllStreamsCert :
    allStreamsOkPool
      (fun σf =>
        match loadLoc σf (.base ⟨0⟩), loadLoc σf (.base ⟨1⟩) with
        | .ok (.int 0 .int), .ok (.chan ⟨some (.base ⟨2⟩)⟩) => true
        | _, _ => false)
      400 ⟨#[.exec chanRendezvousProg rdvEnv .stop], rdvSeed, 0⟩ {} = true := by
  decide +kernel

/-- THE OTHER HALF of the witness pair: the seeded completion pin —
the rendezvous program COMPLETES at main's `.normal` on every choice
stream past one fuel bound (the `forkJoinTerminatesNormallyC` idiom).
Together with `chanRendezvousReadoutC` this is the non-vacuity
discharge for `chanRendezvousTripleC`: the runs exist AND every one
satisfies the triple's readout. Seed-concrete; the ∀-heap safety half
stays the recorded P-S4-1 debt. -/
theorem chanRendezvousTerminatesNormallyC :
    TerminatesNormallyC rdvEnv rdvSeed chanRendezvousProg := by
  refine ⟨400, fun fuel hfuel ch => ?_⟩
  obtain ⟨σf, ch', hrun, -⟩ :=
    execProgLoop_ok_of_allStreamsOkPool chanRendezvousAllStreamsCert ch
  exact ⟨σf, ch', execProgLoop_mono hrun hfuel⟩

end GoLean.Iris
