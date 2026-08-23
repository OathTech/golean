import VerdiCompat.MatchIndexAllEntries

/-!
# THE W-F CAP: StateMachineSafetyProof.v — state-machine safety at base level

Campaign Arc 3 unit 15(c), 1:1 against
`RaftProofs/StateMachineSafetyProof.v` (3,199 lines) @ a3375e8 plus its
two in-file interface deliverables (`Raft/MaxIndexSanityInterface.v`,
`Raft/CommitRecordedCommittedInterface.v` — neither has a proof file of
its own; both are proved HERE, exactly upstream).

The architecture: three invariants ride ONE combined induction
(`everything`) at the MSG-ghost layer through the PRIMED msg principle
(unit 13) — `lifted_maxIndex_sanity` (watermarks below maxIndex),
`commit_invariant` (host and in-flight commit indices point at
committed entries), and base `state_machine_safety` of the double
deghost (re-established each step from SMS-prime + the freshly-proved
commit invariant, unit 14's `state_machine_safety'` consumed through
`msg_simulation_1`). The exits descend by the unit-15 reghosting
(`msg_lower_prop` / GAP-8): **`state_machine_safety_invariant`** (BASE
— the last T3 head, discharging Properties.lean's declared
`StateMachineSafetyStatement`), `maxIndex_sanity_invariant` (BASE), and
`commit_recorded_committed_invariant` (refined).

Statement notes: `lifted_directly_committed`/`lifted_committed`
(upstream :958-969) are definitionally `directly_committed`/`committed`
of `mgv_deghost` (the state ghost is untouched by the wire ghost), so
upstream's four transfer lemmas (:1017-1065) are identity-shaped here;
kept as named theorems for 1:1 citation.
-/

namespace VerdiCompat
namespace Raft

section StateMachineSafety
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "MsgNet" =>
  Network (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "MsgPacket" =>
  Packet (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" =>
  Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" =>
  Packet (raft_base_params (P := P)) raft_multi_params

/-! ## The two in-file interfaces' statements -/

/-- `MaxIndexSanityInterface.v:8-10` (`maxIndex_lastApplied`). -/
def maxIndex_lastApplied (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).lastApplied ≤ maxIndex (net.nwState h).log

/-- `MaxIndexSanityInterface.v:12-14` (`maxIndex_commitIndex`). -/
def maxIndex_commitIndex (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).commitIndex ≤ maxIndex (net.nwState h).log

/-- `MaxIndexSanityInterface.v:16-17` (`maxIndex_sanity`). -/
def maxIndex_sanity (net : RaftNet) : Prop :=
  maxIndex_lastApplied net ∧ maxIndex_commitIndex net

/-- `CommitRecordedCommittedInterface.v:12-15`
(`commit_recorded_committed`). -/
def commit_recorded_committed (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    commit_recorded (deghost net) h e →
    committed net e (net.nwState h).2.currentTerm

/-! ## The msg-layer invariants (`StateMachineSafetyProof.v:90-93,958-987`) -/

/-- `StateMachineSafetyProof.v:90-93` (`lifted_maxIndex_sanity`). -/
def lifted_maxIndex_sanity (net : MsgNet) : Prop :=
  (∀ h : name (P := P),
    (net.nwState h).2.lastApplied ≤ maxIndex (net.nwState h).2.log) ∧
  (∀ h : name (P := P),
    (net.nwState h).2.commitIndex ≤ maxIndex (net.nwState h).2.log)

/-- `StateMachineSafetyProof.v:958-962` (`lifted_directly_committed`) —
definitionally `directly_committed (mgv_deghost net)`. -/
def lifted_directly_committed (net : MsgNet) (e : entry (P := P)) : Prop :=
  ∃ quorum : List (name (P := P)),
    quorum.Nodup ∧
    quorum.length > div2 (nodes (P := P)).length ∧
    ∀ h ∈ quorum, (e.eTerm, e) ∈ (net.nwState h).1.allEntries

/-- `StateMachineSafetyProof.v:964-969` (`lifted_committed`). -/
def lifted_committed (net : MsgNet) (e : entry (P := P)) (t : term) : Prop :=
  ∃ (h : name (P := P)) (e' : entry (P := P)),
    e'.eTerm ≤ t ∧
    lifted_directly_committed net e' ∧
    e.eIndex ≤ e'.eIndex ∧
    e ∈ (net.nwState h).2.log ∧
    e' ∈ (net.nwState h).2.log

/-- `StateMachineSafetyProof.v:971-975` (`commit_invariant_host`). -/
def commit_invariant_host (net : MsgNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (net.nwState h).2.log →
    e.eIndex ≤ (net.nwState h).2.commitIndex →
    lifted_committed net e (net.nwState h).2.currentTerm

/-- `StateMachineSafetyProof.v:977-983` (`commit_invariant_nw`): an
in-flight AppendEntries' leaderCommit only covers committed entries of
its payload. -/
def commit_invariant_nw (net : MsgNet) : Prop :=
  ∀ (p : MsgPacket) (t : term) (lid : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (lci : logIndex)
    (e : entry (P := P)),
    p ∈ net.nwPackets →
    p.pBody.2 = .AppendEntries t lid pli plt es lci →
    e ∈ p.pBody.1 →
    e.eIndex ≤ lci →
    lifted_committed net e t

/-- `StateMachineSafetyProof.v:985-987` (`commit_invariant`). -/
def commit_invariant (net : MsgNet) : Prop :=
  commit_invariant_host net ∧ commit_invariant_nw net

/-! ## The transfer bridges
(`StateMachineSafetyProof.v:58-85,999-1091,2837-2862`) -/

/-- `StateMachineSafetyProof.v:1017-1027`
(`lifted_directly_committed_directly_committed`) — identity-shaped
(the wire ghost never touches state). -/
theorem lifted_directly_committed_directly_committed {net : MsgNet}
    {e : entry (P := P)} (h : lifted_directly_committed net e) :
    directly_committed (mgv_deghost net) e := h

/-- `StateMachineSafetyProof.v:1029-1040`
(`directly_committed_lifted_directly_committed`). -/
theorem directly_committed_lifted_directly_committed {net : MsgNet}
    {e : entry (P := P)} (h : directly_committed (mgv_deghost net) e) :
    lifted_directly_committed net e := h

/-- `StateMachineSafetyProof.v:1042-1052` (`lifted_committed_committed`). -/
theorem lifted_committed_committed {net : MsgNet} {e : entry (P := P)}
    {t : term} (h : lifted_committed net e t) :
    committed (mgv_deghost net) e t := h

/-- `StateMachineSafetyProof.v:1054-1064` (`committed_lifted_committed`). -/
theorem committed_lifted_committed {net : MsgNet} {e : entry (P := P)}
    {t : term} (h : committed (mgv_deghost net) e t) :
    lifted_committed net e t := h

/-- `StateMachineSafetyProof.v:999-1015`
(`msg_lifted_lastApplied_le_commitIndex`): unit 12's base watermark
fact imported through both erasures. -/
theorem msg_lifted_lastApplied_le_commitIndex :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ h : name (P := P),
        (net.nwState h).2.lastApplied ≤ (net.nwState h).2.commitIndex :=
  fun net hreach h =>
    msg_lift_prop_all_the_way _ lastApplied_le_commitIndex_invariant net
      hreach h

/-- `StateMachineSafetyProof.v:1078-1091`
(`commit_invariant_lower_commit_recorded_committed`): the commit
invariant delivers `commit_recorded_committed` of the deghost. -/
theorem commit_invariant_lower_commit_recorded_committed {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    (hci : commit_invariant net) :
    commit_recorded_committed (mgv_deghost net) := by
  intro h e hcr
  obtain ⟨hin, hle⟩ := hcr
  replace hin : e ∈ (net.nwState h).2.log := hin
  replace hle : e.eIndex ≤ (net.nwState h).2.lastApplied ∨
    e.eIndex ≤ (net.nwState h).2.commitIndex := hle
  have hle' : e.eIndex ≤ (net.nwState h).2.commitIndex := by
    rcases hle with hle | hle
    · exact Nat.le_trans hle (msg_lifted_lastApplied_le_commitIndex net
        hreach h)
    · exact hle
  exact lifted_committed_committed (hci.1 h e hin hle')

/-- `StateMachineSafetyProof.v:69-85` (`state_machine_safety_deghost`):
commit-recorded-committed + SMS-prime give base state-machine safety of
the deghost. -/
theorem state_machine_safety_deghost {net : RefinedNet}
    (hcrc : commit_recorded_committed net)
    (hsms' : state_machine_safety' net) :
    state_machine_safety (deghost net) := by
  obtain ⟨hhost', hnw'⟩ := hsms'
  constructor
  · -- host half
    intro h h' e e' hcr hcr' hidx
    exact hhost' e e' _ _ (hcrc h e hcr) (hcrc h' e' hcr') hidx
  · -- nw half
    intro h p t lid pli plt es ci e hp hbody hge hcr
    replace hp : p ∈ net.nwPackets.map deghost_packet := hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hnw' q t lid pli plt es ci e _ hq hbody (hcrc h e hcr) hge

/-- `StateMachineSafetyProof.v:2837-2850` (`maxIndex_sanity_lift`). -/
theorem maxIndex_sanity_lift {net : MsgNet}
    (h : maxIndex_sanity (deghost (mgv_deghost net))) :
    lifted_maxIndex_sanity net :=
  ⟨fun h0 => h.1 h0, fun h0 => h.2 h0⟩

/-- `StateMachineSafetyProof.v:2852-2862` (`maxIndex_sanity_lower`). -/
theorem maxIndex_sanity_lower {net : MsgNet}
    (h : lifted_maxIndex_sanity net) :
    maxIndex_sanity (deghost (mgv_deghost net)) :=
  ⟨fun h0 => h.1 h0, fun h0 => h.2 h0⟩

/-! ## The `lifted_maxIndex_sanity` induction
(`StateMachineSafetyProof.v:95-956`) -/

omit O in
/-- `StateMachineSafetyProof.v:244-251` (`max_min_thing`). -/
theorem max_min_thing {a b c : Nat} (h : a ≤ c) : max a (min b c) ≤ c :=
  Nat.max_le.mpr ⟨h, Nat.min_le_right ..⟩

omit O R in
/-- Upper bound for a `foldl max` (the `fold_left_maximum` cluster's
face this file needs, `StateMachineSafetyProof.v:775-843`). -/
theorem foldl_max_le {l : List Nat} {z b : Nat} (hz : z ≤ b)
    (hl : ∀ x ∈ l, x ≤ b) : l.foldl max z ≤ b := by
  induction l generalizing z with
  | nil => exact hz
  | cons a l ih =>
    exact ih (Nat.max_le.mpr ⟨hz, hl a (List.mem_cons_self ..)⟩)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx))

/-- `doLeader` keeps `commitIndex` below the (sorted) log's maxIndex:
`advanceCommitIndex` folds `max` over indices of the leader's OWN
entries. -/
theorem doLeader_commitIndex_bound {st : raft_data (P := P)}
    {me : name (P := P)} {os d' ms}
    (h : doLeader st me = (os, d', ms)) (hs : sorted st.log)
    (hci : st.commitIndex ≤ maxIndex st.log) :
    d'.commitIndex ≤ maxIndex st.log := by
  have hbound : ∀ x ∈ (((findGtIndex st.log st.commitIndex).filter
      (fun e => (st.currentTerm == e.eTerm) && (st.commitIndex <? e.eIndex) &&
        haveQuorum st me e.eIndex)).map entry.eIndex), x ≤ maxIndex st.log := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact maxIndex_is_max hs (findGtIndex_in (List.mem_filter.mp he).1)
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  all_goals first
    | exact hci
    | exact foldl_max_le hci hbound

/-- `handleAppendEntries` `commitIndex` shape: untouched, or
`max old (min leaderCommit (maxIndex newlog))`. -/
theorem handleAppendEntries_commitIndex (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d m}
    (h : handleAppendEntries me st t lid pli plt es ci = (d, m)) :
    d.commitIndex = st.commitIndex ∨
    d.commitIndex = max st.commitIndex (min ci (maxIndex d.log)) := by
  have hadv := advanceCurrentTerm_la_ci st t
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | exact Or.inl rfl
    | exact Or.inl hadv.2
    | exact Or.inr rfl

/-- THE WATERMARK CORE of the append_entries case
(`StateMachineSafetyProof.v:479-723`, both halves' shared argument): a
watermark below the old log's maxIndex stays below the new log's. The
too-short-payload escape is refuted by base state-machine safety
(`hsms`, the `everything` coupling): the host entry AT the payload's
maxIndex is commit-recorded, so the in-flight request must cover it —
but its term would have to match the payload's maxTerm, which
`haveNewEntries` denies. -/
theorem lifted_maxIndex_AE_core {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    (hsms : state_machine_safety (deghost (mgv_deghost net)))
    {p : MsgPacket} {t : term} {n : name (P := P)} {pli : logIndex}
    {plt : term} {es : List (entry (P := P))} {ci : logIndex}
    {d : raft_data (P := P)} {m : msg (P := P)}
    (hp_in : p ∈ net.nwPackets)
    (hbody : p.pBody.2 = .AppendEntries t n pli plt es ci)
    (hae : handleAppendEntries p.pDst (net.nwState p.pDst).2 t n pli plt
      es ci = (d, m))
    {W : logIndex}
    (hWlog : W ≤ maxIndex (net.nwState p.pDst).2.log)
    (hWwm : W ≤ (net.nwState p.pDst).2.lastApplied ∨
      W ≤ (net.nwState p.pDst).2.commitIndex) :
    W ≤ maxIndex d.log := by
  rcases handleAppendEntries_accept_detail p.pDst (net.nwState p.pDst).2
      t n pli plt es ci hae with hsame | ⟨-, hctd, hnew, hshape⟩
  · rw [hsame]
    exact hWlog
  · have hsorted := mgv_lifted_entries_sorted net hreach p.pDst
    have hcont := mgv_lifted_entries_contiguous net hreach p.pDst
    have hcontes := mgv_lifted_entries_contiguous_nw net hreach p t n pli
      plt es ci hp_in hbody
    have hsortedes : sorted es :=
      entries_sorted_nw_invariant (mgv_deghost net)
        (msg_simulation_1 net hreach) (mgv_deghost_packet p) t n pli plt
        es ci (List.mem_map_of_mem hp_in) hbody
    obtain ⟨hesne, hfind⟩ := haveNewEntries_true hnew
    obtain ⟨x, hx, hxi, hxt⟩ := maxIndex_non_empty hesne
    have hplix : pli < x.eIndex := hcontes.2 x hx
    have hplimax : pli < maxIndex es := hxi ▸ hplix
    have hct_le : (net.nwState p.pDst).2.currentTerm ≤ t := by
      obtain ⟨-, hcts, -, -⟩ := handleAppendEntries_spec p.pDst
        (net.nwState p.pDst).2 t n pli plt es ci hae
      rcases hcts with ⟨hcteq, -⟩ | ⟨hlt, -⟩
      · rw [← hcteq, hctd]
        exact Nat.le_refl _
      · rw [hctd] at hlt
        exact Nat.le_of_lt hlt
    -- the shared contradiction: the watermark cannot outrun the payload
    have hfalse : maxIndex es < W → False := by
      intro hltW
      have hpos : 0 < maxIndex es := Nat.lt_of_le_of_lt (Nat.zero_le pli)
        hplimax
      obtain ⟨y, hyi, hy⟩ := hcont.1 (maxIndex es)
        ⟨hpos, Nat.le_trans (Nat.le_of_lt hltW) hWlog⟩
      rcases hfind with hnone | ⟨em, hsome, hemt⟩
      · exact (findAtIndex_None hsorted hnone hy) hyi
      · obtain ⟨hem_in, hemi⟩ := findAtIndex_elim hsome
        have hcr : commit_recorded (deghost (mgv_deghost net)) p.pDst em := by
          refine ⟨hem_in, ?_⟩
          have hemW : em.eIndex ≤ W := by
            rw [hemi]
            exact Nat.le_of_lt hltW
          exact hWwm.imp (Nat.le_trans hemW) (Nat.le_trans hemW)
        have hp2 : deghost_packet (mgv_deghost_packet p)
            ∈ (deghost (mgv_deghost net)).nwPackets :=
          List.mem_map_of_mem (List.mem_map_of_mem hp_in)
        rcases hsms.2 p.pDst (deghost_packet (mgv_deghost_packet p)) t n
            pli plt es ci em hp2 hbody hct_le hcr with h1 | ⟨h2, -⟩ | h3 | h4
        · rw [hemi] at h1
          exact Nat.lt_irrefl _ (Nat.lt_trans h1 hplimax)
        · rw [hemi] at h2
          rw [h2] at hplimax
          exact Nat.lt_irrefl _ hplimax
        · rw [hemi] at h3
          exact Nat.lt_irrefl _ h3
        · have hemx : em = x := uniqueIndices_elim_eq
            (sorted_uniqueIndices hsortedes) h4 hx (hemi.trans hxi.symm)
          rw [hemx] at hemt
          exact hemt hxt
    rcases hshape with ⟨hpli0, hlog⟩ | ⟨e0, he0, he0i, -, hlog⟩
    · -- scratch: the new log IS the payload
      rw [hlog]
      by_cases hWes : W ≤ maxIndex es
      · exact hWes
      · exact absurd (hfalse (Nat.lt_of_not_le hWes)) not_false
    · -- splice
      rw [hlog]
      by_cases hWpli : W ≤ pli
      · rcases maxIndex_app es (removeAfterIndex (net.nwState p.pDst).2.log
            pli) with happ | ⟨happ, -⟩
        · rw [happ]
          exact Nat.le_trans hWpli (Nat.le_of_lt hplimax)
        · rw [happ, maxIndex_removeAfterIndex hsorted he0 he0i]
          exact hWpli
      · by_cases hWes : W ≤ maxIndex es
        · rcases maxIndex_app es (removeAfterIndex
              (net.nwState p.pDst).2.log pli) with happ | ⟨happ, hesnil⟩
          · rw [happ]
            exact hWes
          · exact absurd hesnil hesne
        · exact absurd (hfalse (Nat.lt_of_not_le hWes)) not_false

/-- `StateMachineSafetyProof.v:479-723`
(`lifted_maxIndex_sanity_append_entries`) — the custom-premise form
`everything`'s AE case consumes (base SMS of the double deghost rides
along, exactly upstream). -/
theorem lifted_maxIndex_sanity_append_entries {xs : List (MsgPacket)}
    {p : MsgPacket} {ys : List (MsgPacket)} {net : MsgNet}
    {st' : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    {ps' : List (MsgPacket)} {gd : electionsData (P := P)}
    {d : raft_data (P := P)} {m : msg (P := P)} {t : term}
    {n : name (P := P)} {pli : logIndex} {plt : term}
    {es : List (entry (P := P))} {ci : logIndex}
    (hae : handleAppendEntries p.pDst (net.nwState p.pDst).2 t n pli plt
      es ci = (d, m))
    (hbody : p.pBody.2 = .AppendEntries t n pli plt es ci)
    (hP : lifted_maxIndex_sanity net)
    (hsms : state_machine_safety (deghost (mgv_deghost net)))
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    (hpkts : net.nwPackets = xs ++ p :: ys)
    (hst : ∀ h, st' h = update net.nwState p.pDst (gd, d) h) :
    lifted_maxIndex_sanity (⟨ps', st'⟩ : MsgNet) := by
  obtain ⟨hla, hci⟩ := hP
  have hp_in : p ∈ net.nwPackets := by
    rw [hpkts]
    exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hlaeq := (handleAppendEntries_la_ci p.pDst (net.nwState p.pDst).2
    t n pli plt es ci hae).1
  constructor
  · -- lastApplied half
    intro h0
    show (st' h0).2.lastApplied ≤ maxIndex (st' h0).2.log
    rw [hst h0]
    by_cases heq : h0 = p.pDst
    · rw [heq, update_same]
      show d.lastApplied ≤ maxIndex d.log
      rw [hlaeq]
      exact lifted_maxIndex_AE_core hreach hsms hp_in hbody hae (hla p.pDst)
        (Or.inl (Nat.le_refl _))
    · rw [update_neq _ _ heq]
      exact hla h0
  · -- commitIndex half
    intro h0
    show (st' h0).2.commitIndex ≤ maxIndex (st' h0).2.log
    rw [hst h0]
    by_cases heq : h0 = p.pDst
    · rw [heq, update_same]
      show d.commitIndex ≤ maxIndex d.log
      have hcore : (net.nwState p.pDst).2.commitIndex ≤ maxIndex d.log :=
        lifted_maxIndex_AE_core hreach hsms hp_in hbody hae (hci p.pDst)
          (Or.inr (Nat.le_refl _))
      rcases handleAppendEntries_commitIndex p.pDst (net.nwState p.pDst).2
          t n pli plt es ci hae with hcieq | hcieq
      · rw [hcieq]
        exact hcore
      · rw [hcieq]
        exact max_min_thing hcore
    · rw [update_neq _ _ heq]
      exact hci h0

/-- `StateMachineSafetyProof.v:95-100,199-277,723-956` — the ten
remaining `lifted_maxIndex_sanity` obligations, in raw unprimed
obligation form (exactly upstream's statements). -/
theorem lifted_maxIndex_sanity_init :
    msg_refined_raft_net_invariant_init (P := P) lifted_maxIndex_sanity :=
  ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

private theorem lms_of_update {net : MsgNet}
    {st' : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    {ps' : List (MsgPacket)} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : lifted_maxIndex_sanity net)
    (hst : ∀ h, st' h = update net.nwState u (gd, d) h)
    (hd : d.lastApplied ≤ maxIndex d.log ∧
      d.commitIndex ≤ maxIndex d.log) :
    lifted_maxIndex_sanity (⟨ps', st'⟩ : MsgNet) := by
  constructor
  · intro h0
    show (st' h0).2.lastApplied ≤ maxIndex (st' h0).2.log
    rw [hst h0]
    by_cases heq : h0 = u
    · rw [heq, update_same]
      exact hd.1
    · rw [update_neq _ _ heq]
      exact hP.1 h0
  · intro h0
    show (st' h0).2.commitIndex ≤ maxIndex (st' h0).2.log
    rw [hst h0]
    by_cases heq : h0 = u
    · rw [heq, update_same]
      exact hd.2
    · rw [update_neq _ _ heq]
      exact hP.2 h0

theorem lifted_maxIndex_sanity_client_request :
    msg_refined_raft_net_invariant_client_request (P := P)
      lifted_maxIndex_sanity := by
  intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
  obtain ⟨hla, hci⟩ := handleClientRequest_la_ci h (net.nwState h).2
    client id c hcr
  have hmax : maxIndex (net.nwState h).2.log ≤ maxIndex d.log := by
    rcases handleClientRequest_log_full h (net.nwState h).2 client id c
        hcr with ⟨-, hlog⟩ | ⟨-, hds⟩
    · rw [hlog]
      show maxIndex (net.nwState h).2.log ≤ maxIndex (net.nwState h).2.log + 1
      exact Nat.le_succ _
    · rw [hds]
      exact Nat.le_refl _
  exact lms_of_update hP hst
    ⟨by rw [hla]; exact Nat.le_trans (hP.1 h) hmax,
     by rw [hci]; exact Nat.le_trans (hP.2 h) hmax⟩

theorem lifted_maxIndex_sanity_timeout :
    msg_refined_raft_net_invariant_timeout (P := P)
      lifted_maxIndex_sanity := by
  intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
  obtain ⟨hla, hci⟩ := handleTimeout_la_ci h (net.nwState h).2 hto
  obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
  exact lms_of_update hP hst
    ⟨by rw [hla, hlog]; exact hP.1 h, by rw [hci, hlog]; exact hP.2 h⟩

theorem lifted_maxIndex_sanity_append_entries_reply :
    msg_refined_raft_net_invariant_append_entries_reply (P := P)
      lifted_maxIndex_sanity := by
  intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
    hpkts hst hps
  obtain ⟨hla, hci⟩ := handleAppendEntriesReply_la_ci p.pDst
    (net.nwState p.pDst).2 p.pSrc t es res haer
  have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
    p.pSrc t es res haer
  exact lms_of_update hP hst
    ⟨by rw [hla, hlog]; exact hP.1 p.pDst,
     by rw [hci, hlog]; exact hP.2 p.pDst⟩

theorem lifted_maxIndex_sanity_request_vote :
    msg_refined_raft_net_invariant_request_vote (P := P)
      lifted_maxIndex_sanity := by
  intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP _hreach
    hpkts hst hps
  obtain ⟨hla, hci⟩ := handleRequestVote_la_ci p.pDst
    (net.nwState p.pDst).2 t p.pSrc lli llt hrv
  have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t
    p.pSrc lli llt hrv
  exact lms_of_update hP hst
    ⟨by rw [hla, hlog]; exact hP.1 p.pDst,
     by rw [hci, hlog]; exact hP.2 p.pDst⟩

theorem lifted_maxIndex_sanity_request_vote_reply :
    msg_refined_raft_net_invariant_request_vote_reply (P := P)
      lifted_maxIndex_sanity := by
  intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts hst
    hps
  obtain ⟨hla, hci⟩ := handleRequestVoteReply_la_ci p.pDst
    (net.nwState p.pDst).2 p.pSrc t v
  have hlog : (handleRequestVoteReply p.pDst (net.nwState p.pDst).2
      p.pSrc t v).log = (net.nwState p.pDst).2.log :=
    handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2 p.pSrc t v
  rw [hrvr] at hla hci hlog
  exact lms_of_update hP hst
    ⟨by rw [hla, hlog]; exact hP.1 p.pDst,
     by rw [hci, hlog]; exact hP.2 p.pDst⟩

theorem lifted_maxIndex_sanity_do_leader :
    msg_refined_raft_net_invariant_do_leader (P := P)
      lifted_maxIndex_sanity := by
  intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
  obtain ⟨hla, -⟩ := doLeader_la_ci d h hdl
  obtain ⟨-, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
  have hd2 : (net.nwState h).2 = d := by rw [hstate]
  have hsorted : sorted d.log := by
    rw [← hd2]
    exact mgv_lifted_entries_sorted net hreach h
  have hbound := doLeader_commitIndex_bound hdl hsorted
    (by rw [← hd2]; exact hP.2 h)
  exact lms_of_update hP hst
    ⟨by rw [hla, hlog, ← hd2]; exact hP.1 h,
     by rw [hlog]; exact hbound⟩

theorem lifted_maxIndex_sanity_do_generic_server :
    msg_refined_raft_net_invariant_do_generic_server (P := P)
      lifted_maxIndex_sanity := by
  intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
  obtain ⟨hci, hla⟩ := doGenericServer_la_ci h d hgs
  obtain ⟨hlog, -, -, -, -, -⟩ := doGenericServer_spec h d hgs
  have hd2 : (net.nwState h).2 = d := by rw [hstate]
  refine lms_of_update hP hst ⟨?_, ?_⟩
  · rcases hla with hla | hla
    · rw [hla, hlog, ← hd2]
      exact hP.1 h
    · rw [hla, hlog, ← hd2]
      exact hP.2 h
  · rw [hci, hlog, ← hd2]
    exact hP.2 h

theorem lifted_maxIndex_sanity_state_same_packet_subset :
    msg_refined_raft_net_invariant_state_same_packet_subset (P := P)
      lifted_maxIndex_sanity := by
  intro net net' hstates hsubp hP _hreach
  constructor
  · intro h
    rw [← hstates h]
    exact hP.1 h
  · intro h
    rw [← hstates h]
    exact hP.2 h

theorem lifted_maxIndex_sanity_reboot :
    msg_refined_raft_net_invariant_reboot (P := P)
      lifted_maxIndex_sanity := by
  intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
  have hd2 : (net.nwState h).2 = d := by rw [hstate]
  constructor
  · intro h0
    rw [hst h0]
    by_cases heq : h0 = h
    · rw [heq, update_same]
      show d'.lastApplied ≤ maxIndex d'.log
      rw [← hrb]
      show d.lastApplied ≤ maxIndex d.log
      rw [← hd2]
      exact hP.1 h
    · rw [update_neq _ _ heq]
      exact hP.1 h0
  · intro h0
    rw [hst h0]
    by_cases heq : h0 = h
    · rw [heq, update_same]
      show d'.commitIndex ≤ maxIndex d'.log
      rw [← hrb]
      show d.commitIndex ≤ maxIndex d.log
      rw [← hd2]
      exact hP.2 h
    · rw [update_neq _ _ heq]
      exact hP.2 h0

end StateMachineSafety

end Raft
end VerdiCompat
