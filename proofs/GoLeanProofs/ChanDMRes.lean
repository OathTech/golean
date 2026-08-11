import GoLeanProofs.ChanDM

/-!
# The channel RESOURCE-TRANSFER laws on the mediated carrier
(channel-logic arc, slice 3 — design note
`docs/2026-08-11_channel-resource-tier.md` §1)

The `IProp`-valued per-element tier (P-CL2-3's first form, dsp its
named flagship consumer): the channel cell lives in an Iris invariant
together with a per-element RESOURCE `Ψ : GoValue → IProp` over its
buffer — the `[∗list]` shape the slice-2 note sketched. What send and
recv atomically exchange is now OWNERSHIP:

- a SEND (arriving or parked) PAYS `Ψ v'` — a resource, e.g. the
  points-to of the cell its message points at — which the invariant's
  big-op absorbs at the push (the carrier guarantees every completion
  IS a push: no phantom completions for `.base`-parked senders,
  slice-2 §2b rule 11);
- a RECEIVE (arriving or parked) is DELIVERED `Ψ v` for the physical
  buffer head `v`: ownership enters the receiving thread's walk with
  the message — the move a pure `Ψp` provably cannot make (slice-2
  §6 obstacle 1), and the defining move of a session protocol.

The pure tier (`chanInvP`, `wpDM_*_invP`) is UNTOUCHED and remains the
cheaper interface for pure protocols; it is the degenerate case
`Ψ v := ⌜Ψp v⌝` (`chanInv_pure_eqv` below). The invariant pins the
machine-real untyped OPEN cell exactly as `chanInvP` does.

**The timeless restriction.** The laws require `[∀ v, Timeless (Ψ v)]`:
opening the invariant yields `▷ chanInv`, and the proofs strip the
later by timelessness (the pure tier got this for free). Points-to,
pure facts, `metaInfo`, and separations thereof are all timeless —
this covers every protocol this arc states, including the flagship's.
A later-credit generalization for genuinely higher-order Ψ (e.g. a
nested WP) is parked as P-CL3-3 with no current consumer.

The parked-receive law is stated at `.MaybeStuck` (carrier
irreducibility of parked-empty configs — slice-2 §2c, unchanged).
Everything else is stuckness-generic; the parked-SEND law's
reducibility witness is the always-available deposit.

Same-commit witness for the four laws (+ `wpDM_fork_alloc₂`):
`Specs/ChanTransfer.lean` — the mini-dsp
resource-transfer exemplar (the child writes 42 into main's cell and
sends the pointer back; main's post re-owns the cell at 42, which it
can obtain ONLY through the message resource).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open Iris.ProgramLogic.Language.Notation
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open Iris.BI

namespace GoLean.Iris

/-! ## The resource-protocol invariant -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]

/-- **The channel resource-protocol invariant** (design note §1): the
physical cell — machine-real untyped shape, OPEN, capacity `cap` —
plus the per-element RESOURCE `Ψ` over its buffer. -/
abbrev chanInv (a : Addr) (cap : Nat) (Ψ : GoValue → IProp GF) : IProp GF :=
  iprop(∃ buf : Array GoValue,
    ([∗list] v ∈ buf.toList, Ψ v)
      ∗ a.id ↦ (⟨none, .chanData buf cap false⟩ : HeapCell))

/-- The buffer big-op is timeless when `Ψ` is (pointwise). -/
instance chanBuf_timeless {Ψ : GoValue → IProp GF} [∀ v, Timeless (Ψ v)]
    {l : List GoValue} : Timeless (iprop([∗list] v ∈ l, Ψ v)) :=
  BigSepL.bigSepL_timeless (fun _ => inferInstance)

/-- Absorb a paid `Ψ v'` into the pushed buffer's big-op. -/
theorem chanBuf_push {Ψ : GoValue → IProp GF} {buf : Array GoValue}
    {v' : GoValue} :
    ([∗list] v ∈ buf.toList, Ψ v) ∗ Ψ v'
      ⊢ [∗list] v ∈ (buf.push v').toList, Ψ v := by
  rw [Array.toList_push]
  exact (sep_mono .rfl (BigSepL.bigSepL_singleton
    (Φ := fun _ v => Ψ v) (x := v')).2).trans BigSepL.bigSepL_append.2

/-- Split the head's `Ψ v` off the drained buffer's big-op. -/
theorem chanBuf_head {Ψ : GoValue → IProp GF} {buf : Array GoValue}
    {v : GoValue} (h : buf[0]? = some v) :
    ([∗list] w ∈ buf.toList, Ψ w)
      ⊢ Ψ v ∗ [∗list] w ∈ (buf.eraseIdx! 0).toList, Ψ w := by
  rw [array_toList_head_erase h]
  exact BigSepL.bigSepL_cons.1

/-- **The pure tier is the degenerate case** (design note §1): at
`Ψ v := ⌜Ψp v⌝` the resource invariant is the pure one. -/
theorem chanInv_pure_eqv {a : Addr} {cap : Nat} {Ψp : GoValue → Prop} :
    chanInv (GF := GF) a cap (fun v => iprop(⌜Ψp v⌝))
      ⊣⊢ chanInvP a cap Ψp := by
  refine exists_congr fun buf => ?_
  refine sep_congr ?_ .rfl
  exact BigSepL.bigSepL_pure.trans
    ⟨pure_mono fun h v hv => by
      obtain ⟨k, hget⟩ := List.mem_iff_getElem?.mp hv
      exact h k v hget,
     pure_mono fun h k x hget => h x (List.mem_iff_getElem?.mpr ⟨k, hget⟩)⟩

end

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}
variable {N : Namespace} {a : Addr} {cap : Nat} {Ψ : GoValue → IProp GF}
variable [∀ v, Timeless (Ψ v)]

set_option maxHeartbeats 1600000 in
/-- **SEND at the apply position under the resource protocol.** The
outcome set: the PARK (cell full — the paid `Ψ v'` RETURNS to the
continuation, to be re-paid at the parked-send law) and the PUSH
(`.next k` with the value physically in the buffer and `Ψ v'`
absorbed by the invariant). The closed-panic branch is refuted by the
invariant's open shape; no phantom completion exists on this carrier. -/
theorem wpDM_send_inv {elem : Ty} {vv v' : GoValue} {env : LocalEnv} {k : Cont}
    (hN : ↑N ⊆ E)
    (hnorm : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      normalizeValueForTy σ elem vv = .ok v') :
    Iris.inv N (chanInv a cap Ψ)
      ∗ Ψ v'
      ∗ (∀ c' : Config,
          (iprop(⌜c' = .blockedSend (some (.base a)) v' k⌝ ∗ Ψ v')
            ∨ ⌜c' = .next k⌝) -∗
          WP (PoolCfgDM.mk c') @ s ; E {{ Φ }})
      ⊢ WP (PoolCfgDM.mk (.retV vv
          (.chanStK (.send elem) [.chan ⟨some (.base a)⟩] [] env k)))
          @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, HΨ, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with HIin
  icases HIin with ⟨%buf, HbufΨ, Hpt⟩
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
  · -- the PARK: state unchanged, invariant closes with the same buffer,
    -- the paid Ψ v' returns to the continuation
    imod Hclose
    ihave HIc : iprop(▷ chanInv a cap Ψ) $$ [HbufΨ Hpt]
    · inext
      iexists buf
      isplitl [HbufΨ]
      · iexact HbufΨ
      · iexact Hpt
    imod HcloseI $$ HIc
    imodintro
    simp only [Algebra.BigOpL.bigOpL_nil]
    isplitl [Hσ]
    · isplitl [Hσ]
      · iexact Hσ
      · ipureintro
        exact ⟨hfns, hmeths, htypes, hwf⟩
    isplitl [Hcont HΨ]
    · iapply Hcont $$ %(Config.blockedSend (some (.base a)) v' k)
      ileft
      isplitr [HΨ]
      · ipureintro
        rfl
      · iexact HΨ
    · itrivial
  · -- the PUSH: the cell updates, the invariant absorbs Ψ v'
    imod (genHeap_update
      (v₂ := (⟨none, .chanData (buf.push v') cap false⟩ : HeapCell)))
      $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    ihave HIc : iprop(▷ chanInv a cap Ψ) $$ [HbufΨ HΨ Hpt]
    · inext
      iexists (buf.push v')
      isplitr [Hpt]
      · iapply chanBuf_push
        isplitl [HbufΨ]
        · iexact HbufΨ
        · iexact HΨ
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
      iright
      ipureintro
      rfl
    · itrivial

set_option maxHeartbeats 1600000 in
/-- **The PARKED SENDER under the resource protocol.** On this carrier
a `.base`-parked sender has NO ∃-release: its only steps are the wake
(push when there is room) and the cap-relaxed deposit — both put the
value physically in the buffer, and both absorb the paid `Ψ v'`.
Reducibility witness: the deposit. -/
theorem wpDM_blocked_send_inv {v' : GoValue} {k : Cont}
    (hN : ↑N ⊆ E) :
    Iris.inv N (chanInv a cap Ψ)
      ∗ Ψ v'
      ∗ WP (PoolCfgDM.mk (.next k)) @ s ; E {{ Φ }}
      ⊢ WP (PoolCfgDM.mk (.blockedSend (some (.base a)) v' k)) @ s ; E {{ Φ }} := by
  iintro ⟨#Hinv, HΨ, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hpins⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hpins
  imod (inv_acc hN) $$ Hinv with ⟨HI, HcloseI⟩
  imod HI with HIin
  icases HIin with ⟨%buf, HbufΨ, Hpt⟩
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
  ihave HIc : iprop(▷ chanInv a cap Ψ) $$ [HbufΨ HΨ Hpt]
  · inext
    iexists (buf.push v')
    isplitr [Hpt]
    · iapply chanBuf_push
      isplitl [HbufΨ]
      · iexact HbufΨ
      · iexact HΨ
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
/-- **TARGETED RECEIVE at the apply position under the resource
protocol.** Outcomes: the PARK (empty buffer) or the DRAIN of the
physical head — the continuation RECEIVES the resource `Ψ v` for the
delivered `v`: ownership transfers into the receiving thread with the
message. `deliverCfg`/`hdel` follow the established caller-supplied-
shape idiom.

**Scoped to OPEN channels (`closed = false`), by `chanInv`.** These
two outcomes are exhaustive only because the invariant pins the open
cell shape: on a CLOSED channel the machine delivers the element
type's ZERO value with `ok = false` (`Multi.lean`'s receive arms) —
no message, no `Ψ`. Close-protocols are the P-CL2-3 tier; a law for
them restates these outcomes at a `closed`-generic invariant. -/
theorem wpDM_recv_inv {targets : List Assignee} {elem : Ty}
    {env : LocalEnv} {k : Cont}
    (hN : ↑N ⊆ E)
    (deliverCfg : GoValue → Config)
    (hdel : ∀ (σ : ExecState) (v : GoValue),
      resumeRecvDelivery σ v true targets env k = .ok (deliverCfg v, σ)) :
    Iris.inv N (chanInv a cap Ψ)
      ∗ (∀ c' : Config,
          (iprop(⌜c' = .blockedRecv (some (.base a)) targets elem env k⌝)
            ∨ iprop(∃ v, ⌜c' = deliverCfg v⌝ ∗ Ψ v)) -∗
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
  icases HIin with ⟨%buf, HbufΨ, Hpt⟩
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
    ihave HIc : iprop(▷ chanInv a cap Ψ) $$ [HbufΨ Hpt]
    · inext
      iexists buf
      isplitl [HbufΨ]
      · iexact HbufΨ
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
      ileft
      ipureintro
      rfl
    · itrivial
  · -- the DRAIN: head out, Ψ v DELIVERED to the continuation
    icases (chanBuf_head hbuf) $$ HbufΨ with ⟨HΨv, HbufΨ⟩
    imod (genHeap_update
      (v₂ := (⟨none, .chanData (buf.eraseIdx! 0) cap false⟩ : HeapCell)))
      $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
    imod Hclose
    ihave HIc : iprop(▷ chanInv a cap Ψ) $$ [HbufΨ Hpt]
    · inext
      iexists (buf.eraseIdx! 0)
      isplitl [HbufΨ]
      · iexact HbufΨ
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
    isplitl [Hcont HΨv]
    · iapply Hcont $$ %(deliverCfg v)
      iright
      iexists v
      isplitr [HΨv]
      · ipureintro
        rfl
      · iexact HΨv
    · itrivial

set_option maxHeartbeats 1600000 in
/-- **The PARKED TARGETED RECEIVER under the resource protocol**, at
`.MaybeStuck` — parked-empty configs are irreducible on this carrier
by design; its only steps DRAIN the physical head, with the resource
`Ψ v` delivered.

**Scoped to OPEN channels (`closed = false`), by `chanInv`.** The
drain is the only step only under the invariant's open shape: the
machine's `.blockedRecv` arm on a CLOSED empty channel resumes the
parked receiver with the element type's ZERO value and `ok = false`
(`Multi.lean`), delivering no message and no `Ψ`. Close-protocols are
the P-CL2-3 tier (S2 §2c's closed-zero forward warning). -/
theorem wpDM_blocked_recv_inv {targets : List Assignee} {elem : Ty}
    {env : LocalEnv} {k : Cont} {Φ : Unit → IProp GF}
    (hN : ↑N ⊆ E)
    (deliverCfg : GoValue → Config)
    (hdel : ∀ (σ : ExecState) (v : GoValue),
      resumeRecvDelivery σ v true targets env k = .ok (deliverCfg v, σ)) :
    Iris.inv N (chanInv a cap Ψ)
      ∗ (∀ c' : Config, (iprop(∃ v, ⌜c' = deliverCfg v⌝ ∗ Ψ v)) -∗
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
  icases HIin with ⟨%buf, HbufΨ, Hpt⟩
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
  icases (chanBuf_head hbuf) $$ HbufΨ with ⟨HΨv, HbufΨ⟩
  imod (genHeap_update
    (v₂ := (⟨none, .chanData (buf.eraseIdx! 0) cap false⟩ : HeapCell)))
    $$ [$Hσ $Hpt] with ⟨Hσ, Hpt⟩
  imod Hclose
  ihave HIc : iprop(▷ chanInv a cap Ψ) $$ [HbufΨ Hpt]
  · inext
    iexists (buf.eraseIdx! 0)
    isplitl [HbufΨ]
    · iexact HbufΨ
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
  isplitl [Hcont HΨv]
  · iapply Hcont $$ %(deliverCfg v)
    iexists v
    isplitr [HΨv]
    · ipureintro
      rfl
    · iexact HΨv
  · itrivial

end

end GoLean.Iris
