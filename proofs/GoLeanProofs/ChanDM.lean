import GoLeanProofs.LangDM

/-!
# The channel VALUE-PROTOCOL laws on the mediated carrier
(channel-logic arc, slice 2 — design note
`docs/2026-08-11_channel-protocol-layer.md` §3)

The Ψ-protocol tier: the channel cell lives in an Iris invariant
TOGETHER with a per-element value predicate over its buffer
(`chanInvP` — tier 1 of §3b, the option TAKEN: the exemplar's
protocol is a pure predicate, and on the mediated carrier a pure
per-element invariant is enough to PIN DELIVERED VALUES, the claim
slice 1 could not make). What send and recv atomically exchange:

- a SEND (arriving or parked) completes ONLY by physically pushing its
  normalized value into the buffer (`StepDM` has no phantom completion
  for `.base`-parked senders) — the law demands `Ψp v'` and folds it
  into the invariant;
- a RECEIVE (arriving or parked) is delivered ONLY the physical buffer
  head — the law hands the continuation `Ψp v` for the delivered `v`.

The invariant pins the machine-real UNTYPED cell (`declaredTy = none`
— what `makeChan` allocates; the S1 close-law precedent), the OPEN
shape (`closed = false`; close-protocols are the recorded tier-2
ghost, P-CL2-3), and an arbitrary capacity — the laws below are the
BUFFERED forms too (P-CL1-1's honest statement, makeable here: a
parked sender's completion implies its value entered the buffer).

Because `Ψp` is a `Prop`-predicate, every branch obligation is PURE:
the laws take `Ψp v'` as a plain hypothesis and hand back
`⌜… ∧ Ψp v⌝` — no big-op machinery, no ghost names. The
`IProp`-valued per-element form and the auth-ghost logical-contents
tier (`own_chan`-style, HoCAP atomic updates) are the recorded growth
path (design note §3b option (b), P-CL2-3), to land with a consumer
that needs more than a per-message predicate.

The parked-receive law is stated at `.MaybeStuck` — a parked receiver
on an empty open cell is IRREDUCIBLE on this carrier by design (no
spins, no phantom releases; design note §2c). Everything else is
stuckness-generic; the parked-SEND law's reducibility witness is the
always-available deposit.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.BI

namespace GoLean.Iris

/-- The buffer head splits off the erased tail (the drain algebra's
membership hinge). -/
theorem array_toList_head_erase {buf : Array GoValue} {v : GoValue}
    (h : buf[0]? = some v) :
    buf.toList = v :: (buf.eraseIdx! 0).toList := by
  have hlt : 0 < buf.size := by
    have := (Array.getElem?_eq_some_iff.mp h).1
    omega
  have hv : buf.toList[0]? = some v := by
    rw [← Array.getElem?_toList] at h
    exact h
  cases hl : buf.toList with
  | nil =>
    rw [hl] at hv
    cases hv
  | cons x xs =>
    rw [hl] at hv
    injection hv with hv
    subst hv
    simp only [Array.eraseIdx!, dif_pos hlt]
    rw [show (buf.eraseIdx 0 hlt).toList = buf.toList.eraseIdx 0 from
      Array.toList_eraseIdx]
    rw [hl]
    rfl

/-! ## The Ψ-protocol invariant -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- **The channel value-protocol invariant** (tier 1, design note
§3a): the physical cell — machine-real untyped shape, OPEN, capacity
`cap` — plus the PURE per-element protocol `Ψp` over its buffer. -/
abbrev chanInvP (a : Addr) (cap : Nat) (Ψp : GoValue → Prop) : IProp GF :=
  iprop(∃ buf : Array GoValue,
    ⌜∀ v, v ∈ buf.toList → Ψp v⌝
      ∗ a.id ↦ (⟨none, .chanData buf cap false⟩ : HeapCell))

end

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}
variable {N : Namespace} {a : Addr} {cap : Nat} {Ψp : GoValue → Prop}

set_option maxHeartbeats 1600000 in
/-- **SEND at the apply position under the value protocol.** The
outcome set: the PARK (cell full) and the PUSH (`.next k` with the
value physically in the buffer — the machine's enqueue when there is
room, the carrier's cap-relaxed deposit always). The closed-panic
branch is refuted by the invariant's open shape; there is NO phantom
pure-control completion on this carrier (`pairArriveNB` cannot fire
at a `.base` cell). The sender pays `Ψp v'` (a pure hypothesis),
which the invariant absorbs on the push branch. -/
theorem wpDM_send_invP {elem : Ty} {vv v' : GoValue} {env : LocalEnv} {k : Cont}
    (hN : ↑N ⊆ E)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ elem vv = .ok v')
    (hΨ : Ψp v') :
    Iris.inv N (chanInvP a cap Ψp)
      ∗ (∀ c' : Config,
          ⌜c' = .blockedSend (some (.base a)) v' k ∨ c' = .next k⌝ -∗
          WP (PoolCfgDM.mk c') @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV vv
          (.chanStK (.send elem) [.chan ⟨some (.base a)⟩] [] env k)))
          @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with HIin
  icases HIin with ⟨%buf, %hbufΨ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id
      = some (⟨none, .chanData buf cap false⟩ : HeapCell)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a)
      = some (⟨none, .chanData buf cap false⟩ : HeapCell) := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hcell : chanCell σ₁ (.base a) = .ok (buf, cap, false) := by
    unfold chanCell
    simp [loadLoc, hlook, Bind.bind, Except.bind]
  have hst : storeLoc σ₁ (.base a) (.chanData (buf.push v') cap false)
      = .ok (setCell σ₁ a ⟨none, .chanData (buf.push v') cap false⟩) :=
    storeLoc_chanData_ok hlook
  have happly : applyChanOp σ₁ (.send elem)
      ((vv :: [GoValue.chan ⟨some (.base a)⟩]).reverse) env k
      = .ok (if buf.size < cap
          then (.next k, setCell σ₁ a ⟨none, .chanData (buf.push v') cap false⟩)
          else (.blockedSend (some (.base a)) v' k, σ₁)) := by
    by_cases hroom : buf.size < cap
    · simp [applyChanOp, valueAsChan, hnorm σ₁ htypes, hcell, hst, hroom,
        Bind.bind, Except.bind]
    · simp [applyChanOp, valueAsChan, hnorm σ₁ htypes, hcell, hroom,
        Bind.bind, Except.bind]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.next k⟩, _, [],
        GoPrimStepDM.step (.sendDeposit rfl hlook (hnorm σ₁ htypes))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : ((c₂ = Config.blockedSend (some (.base a)) v' k ∧ σ₂ = σ₁)
        ∨ (c₂ = Config.next k
            ∧ σ₂ = setCell σ₁ a ⟨none, .chanData (buf.push v') cap false⟩))
      ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq =>
          cases sq with
          | chanStApply h =>
            rw [happly] at h
            by_cases hroom : buf.size < cap
            · rw [if_pos hroom] at h
              injection h with h
              injection h with h1 h2
              exact ⟨.inr ⟨h1.symm, h2.symm⟩, by simp⟩
            · rw [if_neg hroom] at h
              injection h with h
              injection h with h1 h2
              exact ⟨.inl ⟨h1.symm, h2.symm⟩, by simp⟩
          | chanStApplyPanic h =>
            rw [happly] at h
            cases h
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' _ => simp [isBlockedConfig] at hblk'
      | pairReleaseNB hblk' _ _ => simp [isBlockedConfig] at hblk'
      | sendDeposit hclv' hlk' hn' =>
        simp only [chanValueLoc, Option.some.injEq, Loc.base.injEq] at hclv'
        subst hclv'
        rw [hlook] at hlk'
        injection hlk' with hlk'
        injection hlk' with hdt hval
        injection hval with hb hc hcl
        subst hdt; subst hb; subst hc
        rw [hnorm σ₁ htypes] at hn'
        injection hn' with hn'
        subst hn'
        exact ⟨.inr ⟨rfl, rfl⟩, by simp⟩
      | pairArriveNB hti hblc hpair hidx hnb happ' hproj =>
        exfalso
        rcases hpair with hsg | ⟨os, sel, hm, -⟩
        · have hplan := arrivalCases_chanStK_single hsg
          obtain ⟨chv2, vv2, loc, v''2, buf2, cap2, hvs, hclv2, -, -, hbc, -⟩ :=
            chanArrivalPlan_send_inv_full hplan
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons_append, List.cons.injEq, _root_.and_true] at hvs
          obtain ⟨rfl, rfl, -⟩ := hvs
          simp only [chanValueLoc, Option.some.injEq] at hclv2
          subst hclv2
          subst hbc
          exact absurd (hnb (.base a) rfl) (by simp [locIsBase])
        · exact (arrivalCases_chanStK_not_multi hm).elim
      | selCommitCell hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact (arrivalCases_chanStK_not_multi hm).elim
  obtain ⟨hc, rfl⟩ := hshape
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the PARK: state unchanged, invariant closes with the same buffer
    imod Hclose
    ihave HIc : iprop(▷ chanInvP a cap Ψp) $$ [Hpt]
    · inext
      iexists buf
      isplitr [Hpt]
      · ipureintro
        exact hbufΨ
      · iexact Hpt
    imod HcloseI $$ HIc
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iexact Hσ
      · ipureintro
        exact ⟨hfns, hmeths, htypes, hwf⟩
    isplitl [Hcont]
    · iapply Hcont $$ %(Config.blockedSend (some (.base a)) v' k)
      ipureintro
      exact .inl rfl
    · itrivial
  · -- the PUSH: the cell updates, the invariant absorbs Ψp v'
    imod (genHeap_update
      (v₂ := (⟨none, .chanData (buf.push v') cap false⟩ : HeapCell)))
      $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    ihave HIc : iprop(▷ chanInvP a cap Ψp) $$ [Hpt]
    · inext
      iexists (buf.push v')
      isplitr [Hpt]
      · ipureintro
        intro w hw
        rw [Array.toList_push] at hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hbufΨ w hw
        · rw [List.mem_singleton.mp hw]
          exact hΨ
      · iexact Hpt
    imod HcloseI $$ HIc
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil, setCell]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap a
            ⟨none, .chanData (buf.push v') cap false⟩ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hmeths, htypes, hwf.set_existing hlook⟩
    isplitl [Hcont]
    · iapply Hcont $$ %(Config.next k)
      ipureintro
      exact .inr rfl
    · itrivial

set_option maxHeartbeats 1600000 in
/-- **The PARKED SENDER under the value protocol.** On this carrier a
`.base`-parked sender has NO ∃-release: its only steps are the wake
(push when there is room) and the cap-relaxed deposit — both put the
value PHYSICALLY in the buffer. "Completed ⇒ the value entered the
buffer" holds, the statement P-CL1-1 recorded as unmakeable on
`StepDC`. No Löb, no spin. Reducibility witness: the deposit. -/
theorem wpDM_blocked_send_invP {v' : GoValue} {k : Cont}
    (hN : ↑N ⊆ E) (hΨ : Ψp v') :
    Iris.inv N (chanInvP a cap Ψp)
      ∗ WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgDM.mk (.blockedSend (some (.base a)) v' k)) @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with HIin
  icases HIin with ⟨%buf, %hbufΨ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id
      = some (⟨none, .chanData buf cap false⟩ : HeapCell)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a)
      = some (⟨none, .chanData buf cap false⟩ : HeapCell) := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hcell : chanCell σ₁ (.base a) = .ok (buf, cap, false) := by
    unfold chanCell
    simp [loadLoc, hlook, Bind.bind, Except.bind]
  have hst : storeLoc σ₁ (.base a) (.chanData (buf.push v') cap false)
      = .ok (setCell σ₁ a ⟨none, .chanData (buf.push v') cap false⟩) :=
    storeLoc_chanData_ok hlook
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], ⟨.next k⟩, _, [],
        GoPrimStepDM.step (.parkedSendDeposit hlook)⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : c₂ = Config.next k
      ∧ σ₂ = setCell σ₁ a ⟨none, .chanData (buf.push v') cap false⟩
      ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' hres =>
        simp only [resumeThread] at hres
        rw [hcell] at hres
        simp only [bind_eq_ok] at hres
        obtain ⟨⟨b2, c2p, cl2⟩, hcc, hres⟩ := hres
        simp only [Except.ok.injEq, Prod.mk.injEq] at hcc
        obtain ⟨rfl, rfl, rfl⟩ := hcc
        simp only [Bool.false_eq_true, if_false] at hres
        by_cases hroom : buf.size < cap
        · rw [if_pos hroom] at hres
          simp only [bind_eq_ok] at hres
          obtain ⟨s', hst', hres⟩ := hres
          rw [hst] at hst'
          injection hst' with hst'
          subst hst'
          simp only [Pure.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at hres
          exact ⟨hres.1.symm, hres.2.symm, by simp⟩
        · rw [if_neg hroom] at hres
          simp [throw, throwThe, MonadExceptOf.throw] at hres
      | pairArriveNB hti hblc hpair hidx hnb happ' hproj =>
        simp [isBlockedConfig] at hblc
      | selCommitCell hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact absurd (arrivalCases_blocked rfl hm) (by simp)
      | parkedSendDeposit hlk' =>
        rw [hlook] at hlk'
        injection hlk' with hlk'
        injection hlk' with hdt hval
        injection hval with hb hc hcl
        subst hdt; subst hb; subst hc
        exact ⟨rfl, rfl, by simp⟩
      | pairReleaseNB hblk' hrel _ =>
        simp [parkedReleaseNB] at hrel
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  imod (genHeap_update
    (v₂ := (⟨none, .chanData (buf.push v') cap false⟩ : HeapCell)))
    $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  ihave HIc : iprop(▷ chanInvP a cap Ψp) $$ [Hpt]
  · inext
    iexists (buf.push v')
    isplitr [Hpt]
    · ipureintro
      intro w hw
      rw [Array.toList_push] at hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hbufΨ w hw
      · rw [List.mem_singleton.mp hw]
        exact hΨ
    · iexact Hpt
  imod HcloseI $$ HIc
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil, setCell]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap a
          ⟨none, .chanData (buf.push v') cap false⟩ kk).symm)) $$ Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf.set_existing hlook⟩
  isplitl [Hcont]
  · iexact Hcont
  · itrivial

set_option maxHeartbeats 3200000 in
/-- **TARGETED RECEIVE at the apply position under the value
protocol** (P-CL1-5 closes: targeted delivery, the delivered value
PINNED). Outcomes: the PARK (empty buffer) or the DRAIN of the
physical head — the continuation receives `Ψp v` for the delivered
`v`, which is what makes a 42-pinning postcondition provable.
`deliverCfg`/`hdel` follow the `wpD_fork_alloc₁` caller-supplied-shape
idiom: the machine's own delivery entry, σ-independent. -/
theorem wpDM_recv_invP {targets : List Assignee} {elem : Ty}
    {env : LocalEnv} {k : Cont}
    (hN : ↑N ⊆ E)
    (deliverCfg : GoValue → Config)
    (hdel : ∀ (σ : ExecState) (v : GoValue),
      resumeRecvDelivery σ v true targets env k = .ok (deliverCfg v, σ)) :
    Iris.inv N (chanInvP a cap Ψp)
      ∗ (∀ c' : Config,
          ⌜c' = .blockedRecv (some (.base a)) targets elem env k
            ∨ ∃ v, c' = deliverCfg v ∧ Ψp v⌝ -∗
          WP (PoolCfgDM.mk c') @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV (.chan ⟨some (.base a)⟩)
          (.chanStK (.recv targets elem) [] [] env k))) @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with HIin
  icases HIin with ⟨%buf, %hbufΨ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id
      = some (⟨none, .chanData buf cap false⟩ : HeapCell)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a)
      = some (⟨none, .chanData buf cap false⟩ : HeapCell) := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hcell : chanCell σ₁ (.base a) = .ok (buf, cap, false) := by
    unfold chanCell
    simp [loadLoc, hlook, Bind.bind, Except.bind]
  have happly : applyChanOp σ₁ (.recv targets elem)
      (((GoValue.chan ⟨some (.base a)⟩) :: ([] : List GoValue)).reverse) env k
      = .ok (match buf[0]? with
          | some v => (deliverCfg v,
              setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩)
          | none => (.blockedRecv (some (.base a)) targets elem env k, σ₁)) := by
    cases hbuf : buf[0]? with
    | some v =>
      have hst : storeLoc σ₁ (.base a) (.chanData (buf.eraseIdx! 0) cap false)
          = .ok (setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩) :=
        storeLoc_chanData_ok hlook
      have hdel' := hdel
        (setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩) v
      cases targets with
      | nil =>
        simp only [resumeRecvDelivery, Pure.pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at hdel'
        simp [applyChanOp, valueAsChan, hcell, hbuf, hst, hdel'.1,
          Bind.bind, Except.bind]
      | cons t ts =>
        simp only [resumeRecvDelivery] at hdel'
        simp [applyChanOp, valueAsChan, hcell, hbuf, hst, recvStores,
          Bind.bind, Except.bind]
        exact hdel'
    | none =>
      simp [applyChanOp, valueAsChan, hcell, hbuf, Bind.bind, Except.bind]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · cases hbuf : buf[0]? with
      | some v =>
        refine ⟨[], ⟨deliverCfg v⟩,
          setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩, [],
          GoPrimStepDM.step (.lift (.lift (Step.chanStApply ?_)))⟩
        rw [happly, hbuf]
      | none =>
        refine ⟨[], ⟨.blockedRecv (some (.base a)) targets elem env k⟩, σ₁, [],
          GoPrimStepDM.step (.lift (.lift (Step.chanStApply ?_)))⟩
        rw [happly, hbuf]
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : ((c₂ = Config.blockedRecv (some (.base a)) targets elem env k
          ∧ σ₂ = σ₁ ∧ buf[0]? = none)
        ∨ (∃ v, buf[0]? = some v ∧ c₂ = deliverCfg v
            ∧ σ₂ = setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩))
      ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq =>
          cases sq with
          | chanStApply h =>
            rw [happly] at h
            cases hbuf : buf[0]? with
            | some v =>
              rw [hbuf] at h
              injection h with h
              injection h with h1 h2
              exact ⟨.inr ⟨v, rfl, h1.symm, h2.symm⟩, by simp⟩
            | none =>
              rw [hbuf] at h
              injection h with h
              injection h with h1 h2
              exact ⟨.inl ⟨h1.symm, h2.symm, rfl⟩, by simp⟩
          | chanStApplyPanic h =>
            rw [happly] at h
            cases hbuf : buf[0]? with
            | some v => rw [hbuf] at h; cases h
            | none => rw [hbuf] at h; cases h
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' _ => simp [isBlockedConfig] at hblk'
      | pairReleaseNB hblk' _ _ => simp [isBlockedConfig] at hblk'
      | recvDrain hclv' hlk' hbuf' hres' =>
        simp only [chanValueLoc, Option.some.injEq, Loc.base.injEq] at hclv'
        subst hclv'
        rw [hlook] at hlk'
        injection hlk' with hlk'
        injection hlk' with hdt hval
        injection hval with hb hc hcl
        subst hdt; subst hb; subst hc; subst hcl
        rw [hdel] at hres'
        injection hres' with hres'
        injection hres' with h1 h2
        exact ⟨.inr ⟨_, hbuf', h1.symm, h2.symm⟩, by simp⟩
      | pairArriveNB hti hblc hpair hidx hnb happ' hproj =>
        exfalso
        rcases hpair with hsg | ⟨os, sel, hm, -⟩
        · have hplan := arrivalCases_chanStK_single hsg
          obtain ⟨chv2, loc, buf2, cap2, hvs, hclv2, -, hbc, -⟩ :=
            chanArrivalPlan_recv_inv_full hplan
          simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
            List.cons.injEq, _root_.and_true] at hvs
          obtain ⟨rfl, -⟩ := hvs
          simp only [chanValueLoc, Option.some.injEq] at hclv2
          subst hclv2
          subst hbc
          exact absurd (hnb (.base a) rfl) (by simp [locIsBase])
        · exact (arrivalCases_chanStK_not_multi hm).elim
      | selCommitCell hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact (arrivalCases_chanStK_not_multi hm).elim
  obtain ⟨hc, rfl⟩ := hshape
  rcases hc with ⟨rfl, rfl, hbuf⟩ | ⟨v, hbuf, rfl, rfl⟩
  · -- the PARK: state unchanged
    imod Hclose
    ihave HIc : iprop(▷ chanInvP a cap Ψp) $$ [Hpt]
    · inext
      iexists buf
      isplitr [Hpt]
      · ipureintro
        exact hbufΨ
      · iexact Hpt
    imod HcloseI $$ HIc
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iexact Hσ
      · ipureintro
        exact ⟨hfns, hmeths, htypes, hwf⟩
    isplitl [Hcont]
    · iapply Hcont $$ %(Config.blockedRecv (some (.base a)) targets elem env k)
      ipureintro
      exact .inl rfl
    · itrivial
  · -- the DRAIN: head out, Ψp v delivered to the continuation
    have hsplit := array_toList_head_erase hbuf
    imod (genHeap_update
      (v₂ := (⟨none, .chanData (buf.eraseIdx! 0) cap false⟩ : HeapCell)))
      $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    ihave HIc : iprop(▷ chanInvP a cap Ψp) $$ [Hpt]
    · inext
      iexists (buf.eraseIdx! 0)
      isplitr [Hpt]
      · ipureintro
        intro w hw
        exact hbufΨ w (by rw [hsplit]; exact List.mem_cons_of_mem _ hw)
      · iexact Hpt
    imod HcloseI $$ HIc
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil, setCell]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iapply (genHeapInterp_eqv
          (fun kk => (heapToMap_set_base σ₁.heap a
            ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩ kk).symm)) $$ Hσ
      · ipureintro
        exact ⟨hfns, hmeths, htypes, hwf.set_existing hlook⟩
    isplitl [Hcont]
    · iapply Hcont $$ %(deliverCfg v)
      ipureintro
      exact .inr ⟨v, rfl, hbufΨ v (by rw [hsplit]; exact List.mem_cons_self)⟩
    · itrivial

set_option maxHeartbeats 1600000 in
/-- **The PARKED TARGETED RECEIVER under the value protocol**, at
`.MaybeStuck` — on this carrier a `.base`-parked receiver at an empty
open cell is IRREDUCIBLE (no spins, no phantom releases — design note
§2c), so this law is the one member of the family fixed at
`.MaybeStuck`; its only steps DRAIN the physical head, with `Ψp`
delivered. -/
theorem wpDM_blocked_recv_invP {targets : List Assignee} {elem : Ty}
    {env : LocalEnv} {k : Cont} {Φ : Unit → IProp GF}
    (hN : ↑N ⊆ E)
    (deliverCfg : GoValue → Config)
    (hdel : ∀ (σ : ExecState) (v : GoValue),
      resumeRecvDelivery σ v true targets env k = .ok (deliverCfg v, σ)) :
    Iris.inv N (chanInvP a cap Ψp)
      ∗ (∀ c' : Config, ⌜∃ v, c' = deliverCfg v ∧ Ψp v⌝ -∗
          WP (PoolCfgDM.mk c') @ Stuckness.MaybeStuck ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.blockedRecv (some (.base a)) targets elem env k))
          @ Stuckness.MaybeStuck ; E {{ Φ }} := by
  iintro ⟨#Hinv, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with HIin
  icases HIin with ⟨%buf, %hbufΨ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) a.id
      = some (⟨none, .chanData buf cap false⟩ : HeapCell)⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base a)
      = some (⟨none, .chanData buf cap false⟩ : HeapCell) := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hcell : chanCell σ₁ (.base a) = .ok (buf, cap, false) := by
    unfold chanCell
    simp [loadLoc, hlook, Bind.bind, Except.bind]
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨c₂⟩ := e₂
  have hshape : (∃ v, buf[0]? = some v ∧ c₂ = deliverCfg v
        ∧ σ₂ = setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩)
      ∧ eₜ = [] := by
    cases Hstep with
    | step st =>
      cases st with
      | lift ste =>
        cases ste with
        | lift sq => cases sq
        | spawn hsp' _ => simp [spawnPlan] at hsp'
      | wake hblk' hres =>
        simp only [resumeThread] at hres
        rw [hcell] at hres
        simp only [bind_eq_ok] at hres
        obtain ⟨⟨b2, c2p, cl2⟩, hcc, hres⟩ := hres
        simp only [Except.ok.injEq, Prod.mk.injEq] at hcc
        obtain ⟨rfl, rfl, rfl⟩ := hcc
        cases hbuf : buf[0]? with
        | some v =>
          rw [hbuf] at hres
          simp only [bind_eq_ok] at hres
          obtain ⟨s', hst', hres⟩ := hres
          have hst : storeLoc σ₁ (.base a)
              (.chanData (buf.eraseIdx! 0) cap false)
              = .ok (setCell σ₁ a ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩) :=
            storeLoc_chanData_ok hlook
          rw [hst] at hst'
          injection hst' with hst'
          subst hst'
          rw [hdel] at hres
          injection hres with hres
          injection hres with h1 h2
          exact ⟨⟨v, rfl, h1.symm, h2.symm⟩, by simp⟩
        | none =>
          rw [hbuf] at hres
          simp only [Bool.false_eq_true, if_false] at hres
          simp [throw, throwThe, MonadExceptOf.throw] at hres
      | parkedRecvDrain hlk' hbuf' hres' =>
        rw [hlook] at hlk'
        injection hlk' with hlk'
        injection hlk' with hdt hval
        injection hval with hb hc hcl
        subst hdt; subst hb; subst hc; subst hcl
        rw [hdel] at hres'
        injection hres' with hres'
        injection hres' with h1 h2
        exact ⟨⟨_, hbuf', h1.symm, h2.symm⟩, by simp⟩
      | pairArriveNB hti hblc hpair hidx hnb happ' hproj =>
        simp [isBlockedConfig] at hblc
      | selCommitCell hex _ =>
        obtain ⟨th, ii, os, sel, hti, hm, -⟩ := hex
        exact absurd (arrivalCases_blocked rfl hm) (by simp)
      | pairReleaseNB hblk' hrel _ =>
        simp [parkedReleaseNB] at hrel
  obtain ⟨⟨v, hbuf, rfl, rfl⟩, rfl⟩ := hshape
  have hsplit := array_toList_head_erase hbuf
  imod (genHeap_update
    (v₂ := (⟨none, .chanData (buf.eraseIdx! 0) cap false⟩ : HeapCell)))
    $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  ihave HIc : iprop(▷ chanInvP a cap Ψp) $$ [Hpt]
  · inext
    iexists (buf.eraseIdx! 0)
    isplitr [Hpt]
    · ipureintro
      intro w hw
      exact hbufΨ w (by rw [hsplit]; exact List.mem_cons_of_mem _ hw)
    · iexact Hpt
  imod HcloseI $$ HIc
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil, setCell]
  isplitl [Hσ]
  · isplitl [Hσ]
    · iapply (genHeapInterp_eqv
        (fun kk => (heapToMap_set_base σ₁.heap a
          ⟨none, .chanData (buf.eraseIdx! 0) cap false⟩ kk).symm)) $$ Hσ
    · ipureintro
      exact ⟨hfns, hmeths, htypes, hwf.set_existing hlook⟩
  isplitl [Hcont]
  · iapply Hcont $$ %(deliverCfg v)
    ipureintro
    exact ⟨v, rfl, hbufΨ v (by rw [hsplit]; exact List.mem_cons_self)⟩
  · itrivial

end

end GoLean.Iris
