import VerdiCompat.LeaderLogs

/-!
# The creation ring — every entry's term was created by an election

Campaign Arc 3 unit 5 (the feasible slice of LeaderCompletenessProof.v's
import closure; the log-matching-blocked members are GAP-7 in the arc
log): 1:1 against the sources @ a3375e8 —

- `term_was_created` (`Raft/RefinementCommonDefinitions.v:20-23`),
  `in_any_log` and `every_entry_was_created`
  (`Raft/EveryEntryWasCreatedInterface.v`), proved via the
  `in_any_log` strengthening exactly as
  `RaftProofs/EveryEntryWasCreatedProof.v` ("the only time new entries
  come into the system is on a leader, and leaders have leaderLogs in
  their term");
- the BASE `logs_sorted` conjunction (`Raft/SortedInterface.v`) and
  `votesWithLog_sorted` (`Raft/VotesWithLogSortedInterface.v`);
- `current_term_gt_zero` / `terms_and_indices_from_one_log` /
  `terms_and_indices_from_one`
  (`Raft/CurrentTermGtZeroInterface.v`,
  `Raft/TermsAndIndicesFromOneLogInterface.v`,
  `Raft/TermsAndIndicesFromOneInterface.v`);
- `votesWithLog_term_sanity` (`Raft/VotesWithLogTermSanityInterface.v`)
  and `leaderLogs_candidate_entries`
  (`Raft/LeaderLogsCandidateEntriesInterface.v`).

Statements 1:1 with the Interface files; proofs re-derived through the
ported principles.
-/

namespace VerdiCompat
namespace Raft

section CreationRing
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-! ## every_entry_was_created -/

/-- `RefinementCommonDefinitions.v:20-23` (`term_was_created`): some
node recorded a leaderLog at `t` — an election at `t` was won. -/
def term_was_created (net : RefinedNet) (t : term) : Prop :=
  ∃ (h : name (P := P)) (ll : List (entry (P := P))),
    (t, ll) ∈ (net.nwState h).1.leaderLogs

/-- `EveryEntryWasCreatedInterface.v:15-24` (`in_any_log`): the entry is
in a node's log, in flight in an AppendEntries, or in a leaderLog. -/
inductive in_any_log (net : RefinedNet) (e : entry (P := P)) : Prop
  | in_log : ∀ h : name (P := P),
      e ∈ (net.nwState h).2.log → in_any_log net e
  | in_aer : ∀ (p : RefinedPacket) (es : List (entry (P := P))),
      p ∈ net.nwPackets → mEntries p.pBody = some es → e ∈ es →
      in_any_log net e
  | in_ll : ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState h).1.leaderLogs → e ∈ ll → in_any_log net e

/-- `EveryEntryWasCreatedInterface.v:9-13` (`every_entry_was_created`). -/
def every_entry_was_created (net : RefinedNet) : Prop :=
  ∀ (e : entry (P := P)) (t : term) (h : name (P := P))
    (l : List (entry (P := P))),
    (t, l) ∈ (net.nwState h).1.leaderLogs → e ∈ l →
    term_was_created net e.eTerm

/-- `EveryEntryWasCreatedProof.v:23-26` (`in_any_log_term_was_created`),
the inductive strengthening. -/
def in_any_log_term_was_created (net : RefinedNet) : Prop :=
  ∀ e : entry (P := P), in_any_log net e → term_was_created net e.eTerm

/-- `EveryEntryWasCreatedProof.v:33-43` (`term_was_created_preserved`),
specialized to an update whose ghost keeps old leaderLogs. -/
theorem term_was_created_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hpres : ∀ (t : term) (ll : List (entry (P := P))),
       (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    {t : term} (h : term_was_created net t) : term_was_created net' t := by
  obtain ⟨hh, ll, hmem⟩ := h
  refine ⟨hh, ll, ?_⟩
  rw [hst hh]
  by_cases heq : hh = u
  · subst heq
    rw [update_same]
    exact hpres t ll hmem
  · rw [update_neq _ _ heq]
    exact hmem

/-- `EveryEntryWasCreatedProof.v:367-385`
(`in_any_log_term_was_created_invariant`). -/
theorem in_any_log_term_was_created_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      in_any_log_term_was_created net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: no entries anywhere
    intro e hany
    cases hany with
    | in_log h hmem => exact nomatch hmem
    | in_aer p es hp _hme _hmem => exact nomatch hp
    | in_ll h t ll hll _hmem => exact nomatch hll
  · -- client_request: THE creation step — a leader's fresh entry is at
    -- its own term, which leaders_have_leaderLogs certifies
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
      e hany
    obtain ⟨-, hct, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState h).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      subst hgd
      rw [(update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.2]
      exact hmem
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d.log := hmem
        rcases handleClientRequest_log h0 (net.nwState h0).2 client id c hcr
          e hmem with hold | ⟨hterm, hldr⟩
        · exact term_was_created_of_update hst hpres
            (hP e (in_any_log.in_log h0 hold))
        · -- fresh entry: its term is the leader's, and the leader has a
          -- leaderLog there
          obtain ⟨ll, hll⟩ := leaders_have_leaderLogs_invariant net hreach h0
            hldr
          refine term_was_created_of_update hst hpres ⟨h0, ll, ?_⟩
          rw [hterm]
          exact hll
      · rw [update_neq _ _ heq] at hmem
        exact term_was_created_of_update hst hpres
          (hP e (in_any_log.in_log h0 hmem))
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact term_was_created_of_update hst hpres
          (hP e (in_any_log.in_aer p0 es0 hold hme hmem))
      · rw [hl] at hnew
        exact nomatch hnew
    | in_ll h0 t0 ll0 hll hmem =>
      replace hll : (t0, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t0, ll0) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_client_request_ghost h0 (net.nwState h0)
          client id c).2.2.2] at hll
        exact term_was_created_of_update hst
          (by
            intro t1 ll1 hmem1
            rw [(update_elections_data_client_request_ghost h0
              (net.nwState h0) client id c).2.2.2]
            exact hmem1)
          (hP e (in_any_log.in_ll h0 t0 ll0 hll hmem))
      · rw [update_neq _ _ heq] at hll
        exact term_was_created_of_update hst hpres
          (hP e (in_any_log.in_ll h0 t0 ll0 hll hmem))
  · -- timeout: log unchanged, only RequestVotes sent, ghost leaderLogs
    -- unchanged
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps e hany
    obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState h).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      subst hgd
      rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d.log := hmem
        rw [hlog] at hmem
        exact in_any_log.in_log h0 hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact in_any_log.in_aer p0 es0 hold hme hmem
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        have hqm := handleTimeout_messages h (net.nwState h).2 hto q hq
        rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
          at hme
        exact nomatch hme
    | in_ll h0 t0 ll0 hll hmem =>
      replace hll : (t0, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t0, ll0) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_timeout_ghost h0 (net.nwState h0)).1]
          at hll
        exact in_any_log.in_ll h0 t0 ll0 hll hmem
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t0 ll0 hll hmem
  · -- append_entries: accepted entries came in with the (old, in-flight)
    -- packet
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd hbody hP
      _hreach hpkts hst hps e hany
    obtain ⟨-, -, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es
        ci hae
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      subst hgd
      rw [(update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t0 n0 pli plt es ci).2.2.2]
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d.log := hmem
        rcases handleAppendEntries_log p.pDst (net.nwState p.pDst).2 t0 n0
          pli plt es ci hae e hmem with hold | ⟨hes, -⟩
        · exact in_any_log.in_log p.pDst hold
        · exact in_any_log.in_aer p es hpmem (by rw [hbody]; rfl) hes
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact in_any_log.in_aer p0 es0
          (hpkts ▸ mem_of_mem_remove_middle hold) hme hmem
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl,
          hm] at hme
        exact nomatch hme
    | in_ll h0 t1 ll0 hll hmem =>
      replace hll : (t1, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_appendEntries_ghost p.pDst (net.nwState p.pDst)
          t0 n0 pli plt es ci).2.2.2] at hll
        exact in_any_log.in_ll p.pDst t1 ll0 hll hmem
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
  · -- append_entries_reply: log unchanged, nothing sent, ghost unchanged
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach
      hpkts hst hps e hany
    obtain ⟨-, -, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0
        es res haer
    have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
      p.pSrc t0 es res haer
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      subst hgd
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d.log := hmem
        rw [hlog] at hmem
        exact in_any_log.in_log p.pDst hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact in_any_log.in_aer p0 es0
          (hpkts ▸ mem_of_mem_remove_middle hold) hme hmem
      · rw [hl] at hnew
        exact nomatch hnew
    | in_ll h0 t1 ll0 hll hmem =>
      replace hll : (t1, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        subst hgd
        exact in_any_log.in_ll p.pDst t1 ll0 hll hmem
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
  · -- request_vote: log unchanged, reply carries no entries, ghost
    -- leaderLogs unchanged
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps e hany
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t0
      p.pSrc lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t0 p.pSrc
        lli llt (net.nwState p.pDst)).2.1]
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d.log := hmem
        rw [hlog] at hmem
        exact in_any_log.in_log p.pDst hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact in_any_log.in_aer p0 es0
          (hpkts ▸ mem_of_mem_remove_middle hold) hme hmem
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl,
          hm] at hme
        exact nomatch hme
    | in_ll h0 t1 ll0 hll hmem =>
      replace hll : (t1, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t0 p.pSrc
          lli llt (net.nwState p.pDst)).2.1] at hll
        exact in_any_log.in_ll p.pDst t1 ll0 hll hmem
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
  · -- request_vote_reply: a fresh leaderLog snapshots the winner's own
    -- (unchanged) log
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP _hreach hpkts hst
      hps e hany
    subst hrvr
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
      p.pSrc t0 v
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState p.pDst).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      subst hgd
      exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
        p.pSrc t0 v (net.nwState p.pDst) hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈
          (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0
            v).log := hmem
        rw [hlog] at hmem
        exact in_any_log.in_log p.pDst hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      exact in_any_log.in_aer p0 es0
        (hpkts ▸ mem_of_mem_remove_middle (hps p0 hp0)) hme hmem
    | in_ll h0 t1 ll0 hll hmem =>
      replace hll : (t1, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        subst hgd
        rcases leaderLogs_update_elections_data_RVR hll
          with hold | ⟨-, -, -, hl2⟩
        · exact in_any_log.in_ll p.pDst t1 ll0 hold hmem
        · -- the fresh snapshot IS the winner's unchanged log
          rw [hl2, hlog] at hmem
          exact in_any_log.in_log p.pDst hmem
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
  · -- do_leader: replicated entries come from the sender's own log
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps e hany
    obtain ⟨-, -, -, -, hlog, hmsgs⟩ := doLeader_spec d h hdl
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState h).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      rw [hstate] at hmem
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d'.log := hmem
        rw [hlog] at hmem
        refine in_any_log.in_log h0 ?_
        rw [hstate]
        exact hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact in_any_log.in_aer p0 es0 hold hme hmem
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨pi, pt, ci0, es1, hqm, hes⟩ := doLeader_messages d h hdl q hq
        rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
          at hme
        injection hme with hme
        subst hme
        refine in_any_log.in_log h ?_
        rw [hstate]
        exact hes e hmem
    | in_ll h0 t1 ll0 hll hmem =>
      replace hll : (t1, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        refine in_any_log.in_ll h0 t1 ll0 ?_ hmem
        rw [hstate]
        exact hll
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
  · -- do_generic_server: log unchanged, nothing sent
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps e hany
    obtain ⟨hlog, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState h).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      rw [hstate] at hmem
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      replace hmem : e ∈ (st' h0).2.log := hmem
      rw [hst h0] at hmem
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ d'.log := hmem
        rw [hlog] at hmem
        refine in_any_log.in_log h0 ?_
        rw [hstate]
        exact hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      rcases hps p0 hp0 with hold | hnew
      · exact in_any_log.in_aer p0 es0 hold hme hmem
      · rw [hms] at hnew
        exact nomatch hnew
    | in_ll h0 t1 ll0 hll hmem =>
      replace hll : (t1, ll0) ∈ (st' h0).1.leaderLogs := hll
      rw [hst h0] at hll
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        refine in_any_log.in_ll h0 t1 ll0 ?_ hmem
        rw [hstate]
        exact hll
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach e hany
    have htrace : in_any_log net e := by
      cases hany with
      | in_log h0 hmem =>
        rw [← hstates h0] at hmem
        exact in_any_log.in_log h0 hmem
      | in_aer p0 es0 hp0 hme hmem =>
        exact in_any_log.in_aer p0 es0 (hpkts p0 hp0) hme hmem
      | in_ll h0 t1 ll0 hll hmem =>
        rw [← hstates h0] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem
    obtain ⟨hh, ll, hmem⟩ := hP e htrace
    refine ⟨hh, ll, ?_⟩
    rw [← hstates hh]
    exact hmem
  · -- reboot: log and leaderLogs survive; packets unchanged
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts e hany
    subst hrb
    have hpres : ∀ (t1 : term) (ll1 : List (entry (P := P))),
        (t1, ll1) ∈ (net.nwState h).1.leaderLogs →
        (t1, ll1) ∈ gd.leaderLogs := by
      intro t1 ll1 hmem
      rw [hstate] at hmem
      exact hmem
    refine term_was_created_of_update hst hpres (hP e ?_)
    cases hany with
    | in_log h0 hmem =>
      rw [hst h0] at hmem
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hmem
        replace hmem : e ∈ (reboot d).log := hmem
        replace hmem : e ∈ d.log := hmem
        refine in_any_log.in_log h0 ?_
        rw [hstate]
        exact hmem
      · rw [update_neq _ _ heq] at hmem
        exact in_any_log.in_log h0 hmem
    | in_aer p0 es0 hp0 hme hmem =>
      refine in_any_log.in_aer p0 es0 ?_ hme hmem
      rw [hpkts]
      exact hp0
    | in_ll h0 t1 ll0 hll hmem =>
      rw [hst h0] at hll
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t1, ll0) ∈ gd.leaderLogs := hll
        refine in_any_log.in_ll h0 t1 ll0 ?_ hmem
        rw [hstate]
        exact hll
      · rw [update_neq _ _ heq] at hll
        exact in_any_log.in_ll h0 t1 ll0 hll hmem

/-- `EveryEntryWasCreatedProof.v:387-392` (the interface's first field):
leaderLog entries in particular. -/
theorem every_entry_was_created_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      every_entry_was_created net :=
  fun net hreach e t h l hll hel =>
    in_any_log_term_was_created_invariant net hreach e
      (in_any_log.in_ll h t l hll hel)

/-- `EveryEntryWasCreatedProof.v:387-392` (the interface's second
field): any entry anywhere. -/
theorem every_entry_was_created_in_any_log_invariant :
    ∀ (net : RefinedNet) (e : entry (P := P)),
      refined_raft_intermediate_reachable (P := P) net →
      in_any_log net e → term_was_created net e.eTerm :=
  fun net e hreach hany =>
    in_any_log_term_was_created_invariant net hreach e hany

/-! ## Sorted-log machinery (`CommonTheorems.v` slices, constructive) -/

omit O in
/-- `SortedProof.v:250-260` (`sorted_append`). -/
theorem sorted_append {l l' : List (entry (P := P))}
    (hs : sorted l) (hs' : sorted l')
    (hgt : ∀ e ∈ l, ∀ e' ∈ l', e.eIndex > e'.eIndex)
    (hge : ∀ e ∈ l, ∀ e' ∈ l', e.eTerm ≥ e'.eTerm) :
    sorted (l ++ l') := by
  induction l with
  | nil => exact hs'
  | cons a as ih =>
    obtain ⟨ha, has⟩ := hs
    refine ⟨?_, ih has (fun e he => hgt e (List.mem_cons_of_mem _ he))
      (fun e he => hge e (List.mem_cons_of_mem _ he))⟩
    intro e' he'
    rcases List.mem_append.mp he' with he' | he'
    · exact ha e' he'
    · exact ⟨hgt a (List.mem_cons_self ..) e' he',
        hge a (List.mem_cons_self ..) e' he'⟩

omit O in
/-- `SortedProof.v:262-274` (`sorted_index_term`). -/
theorem sorted_index_term {l : List (entry (P := P))} {e e' : entry (P := P)}
    (hle : e.eIndex ≤ e'.eIndex) (hs : sorted l)
    (he : e ∈ l) (he' : e' ∈ l) : e.eTerm ≤ e'.eTerm := by
  induction l with
  | nil => exact nomatch he
  | cons a as ih =>
    obtain ⟨ha, has⟩ := hs
    rcases List.mem_cons.mp he with heq | he2
    · rcases List.mem_cons.mp he' with heq' | he2'
      · rw [heq, heq']
        exact Nat.le_refl _
      · exfalso
        obtain ⟨hgt, -⟩ := ha e' he2'
        rw [← heq] at hgt
        exact absurd hle (Nat.not_le_of_lt hgt)
    · rcases List.mem_cons.mp he' with heq' | he2'
      · obtain ⟨-, hge⟩ := ha e he2
        rw [heq']
        exact hge
      · exact ih has he2 he2'

omit O in
/-- `CommonTheorems.v:104` (`removeAfterIndex_sorted`). -/
theorem removeAfterIndex_sorted {l : List (entry (P := P))} {i : logIndex}
    (hs : sorted l) : sorted (removeAfterIndex l i) := by
  induction l with
  | nil => exact trivial
  | cons a as ih =>
    obtain ⟨ha, has⟩ := hs
    unfold removeAfterIndex
    split
    · exact ⟨ha, has⟩
    · exact ih has

omit O in
/-- `CommonTheorems.v:180` (`removeAfterIndex_In_le`). -/
theorem removeAfterIndex_In_le {l : List (entry (P := P))} {i : logIndex}
    {e : entry (P := P)} (hs : sorted l)
    (he : e ∈ removeAfterIndex l i) : e.eIndex ≤ i := by
  induction l with
  | nil => exact nomatch he
  | cons a as ih =>
    obtain ⟨ha, has⟩ := hs
    unfold removeAfterIndex at he
    split at he
    · rename_i hle
      simp only [Nat.ble_eq] at hle
      rcases List.mem_cons.mp he with rfl | he
      · exact hle
      · exact Nat.le_trans (Nat.le_of_lt (ha e he).1) hle
    · exact ih has he

omit O in
/-- `CommonTheorems.v` (`maxIndex_is_max`). -/
theorem maxIndex_is_max {l : List (entry (P := P))} {e : entry (P := P)}
    (hs : sorted l) (he : e ∈ l) : e.eIndex ≤ maxIndex l := by
  cases l with
  | nil => exact nomatch he
  | cons a as =>
    obtain ⟨ha, -⟩ := hs
    rcases List.mem_cons.mp he with rfl | he
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (ha e he).1

omit O in
/-- `CommonTheorems.v:505` (`findGtIndex_necessary`). -/
theorem findGtIndex_necessary {l : List (entry (P := P))} {i : logIndex}
    {e : entry (P := P)} :
    e ∈ findGtIndex l i → e ∈ l ∧ e.eIndex > i := by
  induction l with
  | nil => exact fun h => nomatch h
  | cons a as ih =>
    intro he
    unfold findGtIndex at he
    split at he
    · rename_i hgt
      simp only [Nat.blt_eq] at hgt
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨List.mem_cons_self .., hgt⟩
      · obtain ⟨hmem, hi⟩ := ih he
        exact ⟨List.mem_cons_of_mem _ hmem, hi⟩
    · exact nomatch he

omit O in
/-- `sorted` survives `findGtIndex` (upstream routes this through
`subseq_findGtIndex` + `sorted_subseq`; direct induction here). -/
theorem sorted_findGtIndex {l : List (entry (P := P))} {i : logIndex}
    (hs : sorted l) : sorted (findGtIndex l i) := by
  induction l with
  | nil => exact trivial
  | cons a as ih =>
    obtain ⟨ha, has⟩ := hs
    unfold findGtIndex
    split
    · refine ⟨?_, ih has⟩
      intro e' he'
      exact ha e' (findGtIndex_necessary he').1
    · exact trivial

omit O in
/-- `CommonTheorems.v` (`findAtIndex_elim`). -/
theorem findAtIndex_elim {l : List (entry (P := P))} {i : logIndex}
    {e : entry (P := P)} :
    findAtIndex l i = some e → e ∈ l ∧ e.eIndex = i := by
  induction l with
  | nil => exact fun h => nomatch h
  | cons a as ih =>
    intro h
    unfold findAtIndex at h
    split at h
    · rename_i heq
      simp only [beq_iff_eq] at heq
      injection h with h
      subst h
      exact ⟨List.mem_cons_self .., heq⟩
    · split at h
      · exact nomatch h
      · obtain ⟨hmem, hi⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hmem, hi⟩

omit O in
/-- `SpecLemmas.v:149-175` (`handleAppendEntries_log`), the detailed
shape the sorted proof needs: unchanged, wholesale replacement at
`pli = 0`, or append onto the truncation at a matching entry. -/
theorem handleAppendEntries_log_cases (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m)) :
    st'.log = st.log ∨
    (pli = 0 ∧ st'.log = es) ∨
    (∃ e, e ∈ st.log ∧ e.eIndex = pli ∧ e.eTerm = plt ∧
      st'.log = es ++ removeAfterIndex st.log pli) := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntries at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl rfl
  · split at h
    · rename_i hpli
      simp only [beq_iff_eq] at hpli
      split at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inr (Or.inl ⟨hpli, rfl⟩)
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl hadv.2.1
    · split at h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl
      · rename_i e0 hfind
        split at h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inl rfl
        · rename_i hterm
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
            ne_eq, Decidable.not_not] at hterm
          obtain ⟨hmem, hidx⟩ := findAtIndex_elim hfind
          split at h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine Or.inr (Or.inr ⟨e0, hmem, hidx, ?_, ?_⟩)
            · rw [hterm]
            · show es ++ removeAfterIndex st.log pli
                = es ++ removeAfterIndex st.log pli
              rfl
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact Or.inl hadv.2.1

omit O in
/-- `SortedProof.v:441-466` (`doLeader_messages`), the sorted-side
detail: every replica message carries a sorted, `> pli`, `≥ plt` slice
of the leader's own log. -/
theorem doLeader_messages_sorted (st : raft_data (P := P))
    (me : name (P := P)) {os st' ms}
    (h : doLeader st me = (os, st', ms)) (hs : sorted st.log) :
    ∀ q ∈ ms, ∀ (t : term) (lid : name (P := P)) (pli : logIndex)
      (plt : term) (es : List (entry (P := P))) (ci : logIndex),
      q.2 = msg.AppendEntries (P := P) t lid pli plt es ci →
      sorted es ∧ (∀ e ∈ es, e.eIndex > pli) ∧ (∀ e ∈ es, e.eTerm ≥ plt) := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, -, rfl⟩ := h
  all_goals intro q hq t lid pli plt es ci hbody
  · simp only [List.mem_map] at hq
    obtain ⟨node, -, rfl⟩ := hq
    unfold replicaMessage at hbody
    simp only [] at hbody
    injection hbody with h1 h2 h3 h4 h5 h6
    subst h3
    subst h5
    refine ⟨sorted_findGtIndex hs, fun e he => (findGtIndex_necessary he).2,
      ?_⟩
    intro e he
    obtain ⟨hmem, hgt⟩ := findGtIndex_necessary he
    subst h4
    split
    · rename_i e'' hfind
      obtain ⟨hmem'', hidx''⟩ := findAtIndex_elim hfind
      show e''.eTerm ≤ e.eTerm
      refine sorted_index_term ?_ hs hmem'' hmem
      rw [hidx'']
      exact Nat.le_of_lt hgt
    · exact Nat.zero_le _
  · exact nomatch hq
  · exact nomatch hq

/-! ## The BASE logs_sorted conjunction -/

/-- `SortedInterface.v:9-11` (`logs_sorted_host`). -/
def logs_sorted_host (net : RaftNet) : Prop :=
  ∀ h : name (P := P), sorted (net.nwState h).log

/-- `SortedInterface.v:13-17` (`logs_sorted_nw`). -/
def logs_sorted_nw (net : RaftNet) : Prop :=
  ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (n : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (c : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es c →
    sorted es

/-- `SortedInterface.v:19-24` (`packets_gt_prevIndex`). -/
def packets_gt_prevIndex (net : RaftNet) : Prop :=
  ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (n : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (c : logIndex) (e : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es c →
    e ∈ es → e.eIndex > pli

/-- `SortedInterface.v:26-31` (`packets_ge_prevTerm`). -/
def packets_ge_prevTerm (net : RaftNet) : Prop :=
  ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (n : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (c : logIndex) (e : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es c →
    e ∈ es → e.eTerm ≥ plt

/-- `SortedInterface.v:33-35` (`logs_sorted`). -/
def logs_sorted (net : RaftNet) : Prop :=
  logs_sorted_host net ∧ logs_sorted_nw net ∧
  packets_gt_prevIndex net ∧ packets_ge_prevTerm net

/-- `SortedProof.v:276-309` (`handleAppendEntries_logs_sorted`): an
accepted append splices sorted incoming entries above the (sorted)
truncated log — the `sorted_append` argument. -/
theorem handleAppendEntries_logs_sorted {net : RaftNet}
    {p : Packet (raft_base_params (P := P)) raft_multi_params}
    {t : term} {n : name (P := P)} {pli : logIndex} {plt : term}
    {es : List (entry (P := P))} {ci : logIndex} {st' m}
    (hls : logs_sorted net)
    (hae : handleAppendEntries p.pDst (net.nwState p.pDst) t n pli plt es ci
      = (st', m))
    (hbody : p.pBody = .AppendEntries t n pli plt es ci)
    (hp : p ∈ net.nwPackets) :
    sorted st'.log := by
  obtain ⟨hhost, hnw, hgt, hge⟩ := hls
  rcases handleAppendEntries_log_cases p.pDst (net.nwState p.pDst) t n pli
    plt es ci hae with hold | ⟨-, hnew⟩ | ⟨e0, hmem0, hidx0, hterm0, happ⟩
  · rw [hold]
    exact hhost p.pDst
  · rw [hnew]
    exact hnw p t n pli plt es ci hp hbody
  · rw [happ]
    refine sorted_append (hnw p t n pli plt es ci hp hbody)
      (removeAfterIndex_sorted (hhost p.pDst)) ?_ ?_
    · intro e he e' he'
      have hle' := removeAfterIndex_In_le (hhost p.pDst) he'
      exact Nat.lt_of_le_of_lt hle' (hgt p t n pli plt es ci e hp hbody he)
    · intro e he e' he'
      have hle' := removeAfterIndex_In_le (hhost p.pDst) he'
      have hmem' := removeAfterIndex_in he'
      have hterm' : e'.eTerm ≤ e0.eTerm := by
        refine sorted_index_term ?_ (hhost p.pDst) hmem' hmem0
        rw [hidx0]
        exact hle'
      refine Nat.le_trans ?_ (hge p t n pli plt es ci e hp hbody he)
      rw [← hterm0]
      exact hterm'

/-- `SortedProof.v:57-75` (`handleClientRequest_logs_sorted`): the fresh
entry's index tops the log and its term bounds every entry
(`no_entries_past_current_term`). -/
theorem handleClientRequest_logs_sorted {net : RaftNet}
    {h : name (P := P)} {client : R.clientId} {id : Nat} {c : P.input}
    {out st' l}
    (hcr : handleClientRequest h (net.nwState h) client id c = (out, st', l))
    (hreach : raft_intermediate_reachable (P := P) net)
    (hhost : logs_sorted_host net) :
    sorted st'.log := by
  unfold handleClientRequest at hcr
  split at hcr
  · rename_i hty
    simp only [Prod.mk.injEq] at hcr
    obtain ⟨-, rfl, -⟩ := hcr
    show sorted (⟨h, client, id, maxIndex (net.nwState h).log + 1,
      (net.nwState h).currentTerm, c⟩ :: (net.nwState h).log)
    refine ⟨?_, hhost h⟩
    intro e' he'
    constructor
    · show e'.eIndex < maxIndex (net.nwState h).log + 1
      exact Nat.lt_succ_of_le (maxIndex_is_max (hhost h) he')
    · show e'.eTerm ≤ (net.nwState h).currentTerm
      obtain ⟨hh, -⟩ := no_entries_past_current_term_invariant net hreach
      exact hh h e' he'
  · simp only [Prod.mk.injEq] at hcr
    obtain ⟨-, rfl, -⟩ := hcr
    exact hhost h

/-- `SortedProof.v:549-567` (`logs_sorted_invariant`) — BASE layer. -/
theorem logs_sorted_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net → logs_sorted net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨fun h => trivial, ?_, ?_, ?_⟩
    · intro p t n pli plt es c hp _hbody
      exact nomatch hp
    · intro p t n pli plt es c e hp _hbody _he
      exact nomatch hp
    · intro p t n pli plt es c e hp _hbody _he
      exact nomatch hp
  · -- client_request: no packets; the fresh entry keeps the host sorted
    intro h net st' ps' out d l client id c hcr hP hreach hst hps
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    obtain ⟨-, -, -, -, hl⟩ := handleClientRequest_spec h (net.nwState h)
      client id c hcr
    have hpk : ∀ p' ∈ ps', p' ∈ net.nwPackets := by
      intro p' hp'
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hl] at hnew
        exact nomatch hnew
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · exact handleClientRequest_logs_sorted hcr hreach hhost
      · exact hhost h0
    · intro p t n pli plt es c hp hbody
      exact hnw p t n pli plt es c (hpk p hp) hbody
    · intro p t n pli plt es c e hp hbody he
      exact hgt p t n pli plt es c e (hpk p hp) hbody he
    · intro p t n pli plt es c e hp hbody he
      exact hge p t n pli plt es c e (hpk p hp) hbody he
  · -- timeout: log unchanged; only RequestVotes sent
    intro net h st' ps' out d l hto hP _hreach hst hps
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    obtain ⟨hlog, -, hmsg⟩ := handleTimeout_spec h (net.nwState h) hto
    have hpk : ∀ (p' : Packet (raft_base_params (P := P)) raft_multi_params)
        (t : term) (n : name (P := P)) pli plt
        (es : List (entry (P := P))) c,
        p' ∈ ps' → p'.pBody = .AppendEntries t n pli plt es c →
        p' ∈ net.nwPackets := by
      intro p' t n pli plt es c hp' hbody
      rcases hps p' hp' with hold | hnew
      · exact hold
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', cid, lli, llt, heqm⟩ := hmsg q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = q.2 from rfl, heqm] at hbody
        exact nomatch hbody
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rw [hlog]
        exact hhost h
      · exact hhost h0
    · intro p t n pli plt es c hp hbody
      exact hnw p t n pli plt es c (hpk p t n pli plt es c hp hbody) hbody
    · intro p t n pli plt es c e hp hbody he
      exact hgt p t n pli plt es c e (hpk p t n pli plt es c hp hbody) hbody
        he
    · intro p t n pli plt es c e hp hbody he
      exact hge p t n pli plt es c e (hpk p t n pli plt es c hp hbody) hbody
        he
  · -- append_entries: the accept splice stays sorted; the reply is an
    -- AppendEntriesReply
    intro xs p ys net st' ps' d m t0 n0 pli plt es ci hae hbody hP _hreach
      hpkts hst hps
    have hP' := hP
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    obtain ⟨-, -, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst) t0 n0 pli plt es
        ci hae
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hpk : ∀ (p' : Packet (raft_base_params (P := P)) raft_multi_params)
        (t : term) (n : name (P := P)) pli' plt'
        (es'' : List (entry (P := P))) c,
        p' ∈ ps' → p'.pBody = .AppendEntries t n pli' plt' es'' c →
        p' ∈ net.nwPackets := by
      intro p' t n pli' plt' es'' c hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rename_i heq
        subst heq
        exact handleAppendEntries_logs_sorted hP' hae hbody hpmem
      · exact hhost h0
    · intro p' t n pli' plt' es'' c hp' hbody'
      exact hnw p' t n pli' plt' es'' c
        (hpk p' t n pli' plt' es'' c hp' hbody') hbody'
    · intro p' t n pli' plt' es'' c e hp' hbody' he
      exact hgt p' t n pli' plt' es'' c e
        (hpk p' t n pli' plt' es'' c hp' hbody') hbody' he
    · intro p' t n pli' plt' es'' c e hp' hbody' he
      exact hge p' t n pli' plt' es'' c e
        (hpk p' t n pli' plt' es'' c hp' hbody') hbody' he
  · -- append_entries_reply: log unchanged, nothing sent
    intro xs p ys net st' ps' d m t0 es res haer _hbody hP _hreach hpkts hst
      hps
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst) p.pSrc t0 es res haer
    have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst)
      p.pSrc t0 es res haer
    have hpk : ∀ p' ∈ ps', p' ∈ net.nwPackets := by
      intro p' hp'
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · rw [hl] at hnew
        exact nomatch hnew
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rw [hlog]
        exact hhost p.pDst
      · exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      exact hnw p' t n pli plt es' c (hpk p' hp') hbody'
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hgt p' t n pli plt es' c e (hpk p' hp') hbody' he
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hge p' t n pli plt es' c e (hpk p' hp') hbody' he
  · -- request_vote: log unchanged; the reply is a RequestVoteReply
    intro xs p ys net st' ps' d m t0 cid lli llt hrv _hbody hP _hreach hpkts
      hst hps
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst) t0 p.pSrc
      lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst) t0 p.pSrc lli llt hrv
    have hpk : ∀ (p' : Packet (raft_base_params (P := P)) raft_multi_params)
        (t : term) (n : name (P := P)) pli plt
        (es' : List (entry (P := P))) c,
        p' ∈ ps' → p'.pBody = .AppendEntries t n pli plt es' c →
        p' ∈ net.nwPackets := by
      intro p' t n pli plt es' c hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rw [hlog]
        exact hhost p.pDst
      · exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      exact hnw p' t n pli plt es' c
        (hpk p' t n pli plt es' c hp' hbody') hbody'
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hgt p' t n pli plt es' c e
        (hpk p' t n pli plt es' c hp' hbody') hbody' he
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hge p' t n pli plt es' c e
        (hpk p' t n pli plt es' c hp' hbody') hbody' he
  · -- request_vote_reply: log unchanged, packets shrink
    intro xs p ys net st' ps' d t0 v hrvr _hbody hP _hreach hpkts hst hps
    subst hrvr
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst)
      p.pSrc t0 v
    have hpk : ∀ p' ∈ ps', p' ∈ net.nwPackets := by
      intro p' hp'
      exact hpkts ▸ mem_of_mem_remove_middle (hps p' hp')
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rw [hlog]
        exact hhost p.pDst
      · exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      exact hnw p' t n pli plt es' c (hpk p' hp') hbody'
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hgt p' t n pli plt es' c e (hpk p' hp') hbody' he
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hge p' t n pli plt es' c e (hpk p' hp') hbody' he
  · -- do_leader: replica messages carry sorted slices of a sorted log
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    obtain ⟨-, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
    have hsd : sorted d.log := by
      have := hhost h
      rw [hstate] at this
      exact this
    have hmsg := doLeader_messages_sorted d h hdl hsd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rw [hlog]
        exact hsd
      · exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hnw p' t n pli plt es' c hold hbody'
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        exact (hmsg q hq t n pli plt es' c hbody').1
    · intro p' t n pli plt es' c e hp' hbody' he
      rcases hps p' hp' with hold | hnew
      · exact hgt p' t n pli plt es' c e hold hbody' he
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        exact (hmsg q hq t n pli plt es' c hbody').2.1 e he
    · intro p' t n pli plt es' c e hp' hbody' he
      rcases hps p' hp' with hold | hnew
      · exact hge p' t n pli plt es' c e hold hbody' he
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        exact (hmsg q hq t n pli plt es' c hbody').2.2 e he
  · -- do_generic_server: log unchanged, nothing sent
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    obtain ⟨hlog, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hpk : ∀ p' ∈ ps', p' ∈ net.nwPackets := by
      intro p' hp'
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hms] at hnew
        exact nomatch hnew
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (st' h0).log
      rw [hst h0]
      unfold update
      split
      · rw [hlog]
        have := hhost h
        rw [hstate] at this
        exact this
      · exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      exact hnw p' t n pli plt es' c (hpk p' hp') hbody'
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hgt p' t n pli plt es' c e (hpk p' hp') hbody' he
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hge p' t n pli plt es' c e (hpk p' hp') hbody' he
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      rw [← hstates h0]
      exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      exact hnw p' t n pli plt es' c (hpkts p' hp') hbody'
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hgt p' t n pli plt es' c e (hpkts p' hp') hbody' he
    · intro p' t n pli plt es' c e hp' hbody' he
      exact hge p' t n pli plt es' c e (hpkts p' hp') hbody' he
  · -- reboot: log survives, packets unchanged
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    subst hrb
    obtain ⟨hhost, hnw, hgt, hge⟩ := hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      show sorted (net'.nwState h0).log
      rw [hst h0]
      unfold update
      split
      · show sorted (reboot d).log
        show sorted d.log
        have := hhost h
        rw [hstate] at this
        exact this
      · exact hhost h0
    · intro p' t n pli plt es' c hp' hbody'
      rw [← hpkts] at hp'
      exact hnw p' t n pli plt es' c hp' hbody'
    · intro p' t n pli plt es' c e hp' hbody' he
      rw [← hpkts] at hp'
      exact hgt p' t n pli plt es' c e hp' hbody' he
    · intro p' t n pli plt es' c e hp' hbody' he
      rw [← hpkts] at hp'
      exact hge p' t n pli plt es' c e hp' hbody' he

/-! ## votesWithLog elim lemmas (`RefinementSpecLemmas.v` /
`VotesWithLogSortedProof.v` shapes) -/

omit O in
/-- Every member of a RequestVote-updated `votesWithLog` is old, or the
fresh record at the responder's new term with its (unchanged) log. -/
theorem update_elections_data_requestVote_votesWithLog_elim
    {me src : name (P := P)} {t : term} {cand : name (P := P)}
    {lli : logIndex} {llt : term}
    {st : electionsData (P := P) × raft_data (P := P)} {st' m}
    (h : handleRequestVote me st.2 t cand lli llt = (st', m))
    {t' : term} {h' : name (P := P)} {vl : List (entry (P := P))}
    (hin : (t', h', vl) ∈
      (update_elections_data_requestVote me src t cand lli llt st).votesWithLog) :
    (t', h', vl) ∈ st.1.votesWithLog ∨
    (t' = st'.currentTerm ∧ vl = st'.log) := by
  unfold update_elections_data_requestVote at hin
  rw [h] at hin
  simp only [] at hin
  repeat' split at hin
  all_goals first
    | exact Or.inl hin
    | (rcases List.mem_cons.mp hin with heq | hin
       · injection heq with h1 h2
         injection h2 with h2 h3
         exact Or.inr ⟨h1, h3⟩
       · exact Or.inl hin)

omit O in
/-- Every member of a timeout-updated `votesWithLog` is old, or the
fresh self-record at the candidacy's new term with its (unchanged) log. -/
theorem update_elections_data_timeout_votesWithLog_elim
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l))
    {t' : term} {h' : name (P := P)} {vl : List (entry (P := P))}
    (hin : (t', h', vl) ∈ (update_elections_data_timeout me st).votesWithLog) :
    (t', h', vl) ∈ st.1.votesWithLog ∨
    (t' = st'.currentTerm ∧ vl = st'.log) := by
  rcases update_elections_data_timeout_votesWithLog_votesReceived h
    with ⟨-, hvwl, -⟩ | ⟨-, hvwl, -⟩
  · rw [hvwl] at hin
    exact Or.inl hin
  · rw [hvwl] at hin
    rcases List.mem_cons.mp hin with heq | hin
    · injection heq with h1 h2
      injection h2 with h2 h3
      exact Or.inr ⟨h1, h3⟩
    · exact Or.inl hin

/-- `VotesWithLogSortedProof.v:45-55` (`sorted_host_lifted`) — a
`lift_prop` consumer. -/
theorem sorted_host_lifted :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ h : name (P := P), sorted (net.nwState h).2.log := by
  intro net hreach h
  have := (lift_prop _ logs_sorted_invariant net hreach).1 h
  rw [deghost_spec] at this
  exact this

/-! ## votesWithLog_sorted and votesWithLog_term_sanity -/

/-- `VotesWithLogSortedInterface.v:9-12` (`votesWithLog_sorted`). -/
def votesWithLog_sorted (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (h' : name (P := P))
    (vl : List (entry (P := P))),
    (t, h', vl) ∈ (net.nwState h).1.votesWithLog → sorted vl

/-- `VotesWithLogTermSanityInterface.v:8-12` (`votesWithLog_term_sanity`). -/
def votesWithLog_term_sanity (net : RefinedNet) : Prop :=
  ∀ (t : term) (l : name (P := P)) (hs : List (entry (P := P)))
    (h : name (P := P)),
    (t, l, hs) ∈ (net.nwState h).1.votesWithLog →
    t ≤ (net.nwState h).2.currentTerm

/-- Shared step helper for the two votesWithLog invariants: every ghost
update leaves votesWithLog alone or extends it with a record carrying
the updated node's NEW term and a sorted log. -/
theorem votesWithLog_facts_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (helim : ∀ (t' : term) (h' : name (P := P)) (vl : List (entry (P := P))),
       (t', h', vl) ∈ gd.votesWithLog →
       (t', h', vl) ∈ (net.nwState u).1.votesWithLog ∨
       (t' = d.currentTerm ∧ sorted vl))
    (hle : (net.nwState u).2.currentTerm ≤ d.currentTerm) :
    (votesWithLog_sorted net → votesWithLog_sorted net') ∧
    (votesWithLog_term_sanity net → votesWithLog_term_sanity net') := by
  constructor
  · intro hP h t h' vl hin
    rw [hst h] at hin
    by_cases heq : h = u
    · subst heq
      rw [update_same] at hin
      replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
      rcases helim t h' vl hin with hold | ⟨-, hs⟩
      · exact hP _ t h' vl hold
      · exact hs
    · rw [update_neq _ _ heq] at hin
      exact hP h t h' vl hin
  · intro hP t l hs h hin
    replace hin : (t, l, hs) ∈ (net'.nwState h).1.votesWithLog := hin
    rw [hst h] at hin
    rw [hst h]
    by_cases heq : h = u
    · subst heq
      rw [update_same] at hin ⊢
      replace hin : (t, l, hs) ∈ gd.votesWithLog := hin
      rcases helim t l hs hin with hold | ⟨heqt, -⟩
      · exact Nat.le_trans (hP t l hs _ hold) hle
      · rw [heqt]
        exact Nat.le_refl _
    · rw [update_neq _ _ heq] at hin ⊢
      exact hP t l hs h hin

/-- `VotesWithLogSortedProof.v:198-215` (`votesWithLog_sorted_invariant`)
and `VotesWithLogTermSanityProof.v:53-88`
(`votesWithLog_term_sanity_invariant`), proved together — the
per-handler elim facts are shared. -/
theorem votesWithLog_sorted_and_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votesWithLog_sorted net ∧ votesWithLog_term_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_⟩
    · intro h t h' vl hin
      exact nomatch hin
    · intro t l hs h hin
      exact nomatch hin
  · -- client_request: no new record; term unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    obtain ⟨-, hct, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        subst hgd
        rw [(update_elections_data_client_request_ghost h (net.nwState h)
          client id c).2.1] at hin
        exact Or.inl hin)
      (hct ▸ Nat.le_refl _)
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- timeout: the fresh self-record carries the node's own sorted log
    intro net h st' ps' gd out d l hto hgd hP hreach hst _hps
    obtain ⟨hlog, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hle : (net.nwState h).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · rw [hc]
        exact Nat.le_succ _
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        subst hgd
        rcases update_elections_data_timeout_votesWithLog_elim hto hin
          with hold | ⟨heqt, heqvl⟩
        · exact Or.inl hold
        · refine Or.inr ⟨heqt, ?_⟩
          rw [heqvl, hlog]
          exact sorted_host_lifted net hreach h)
      hle
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- append_entries: no new record; term grows
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps
    obtain ⟨-, hcases, -, -⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es
        ci hae
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        subst hgd
        rw [(update_elections_data_appendEntries_ghost p.pDst
          (net.nwState p.pDst) t0 n0 pli plt es ci).2.1] at hin
        exact Or.inl hin)
      hle
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- append_entries_reply: ghost unchanged; term grows
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, hcases, -⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es
        res haer
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -, -⟩ | ⟨hc, -, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        subst hgd
        exact Or.inl hin)
      hle
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- request_vote: the fresh grant records the responder's sorted log
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP hreach
      _hpkts hst _hps
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt
        hrv
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t0 p.pSrc
      lli llt hrv
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        subst hgd
        rcases update_elections_data_requestVote_votesWithLog_elim hrv hin
          with hold | ⟨heqt, heqvl⟩
        · exact Or.inl hold
        · refine Or.inr ⟨heqt, ?_⟩
          rw [heqvl, hlog]
          exact sorted_host_lifted net hreach p.pDst)
      hle
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- request_vote_reply: ghost votesWithLog unchanged; term grows
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP _hreach _hpkts hst
      _hps
    subst hrvr
    obtain ⟨hcases, -, -, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v rfl
    have hle : (net.nwState p.pDst).2.currentTerm
        ≤ (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0
            v).currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        subst hgd
        rw [(update_elections_data_requestVoteReply_votes p.pDst p.pSrc t0 v
          (net.nwState p.pDst)).2.1] at hin
        exact Or.inl hin)
      hle
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- do_leader: ghost rides along; term unchanged
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hc, -, -, -, -, -⟩ := doLeader_spec d h hdl
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        rw [hstate]
        exact Or.inl hin)
      (by rw [hstate, hc]; exact Nat.le_refl _)
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨-, -, hc, -, -, -⟩ := doGenericServer_spec h d hgs
    have hfacts := votesWithLog_facts_of_update (net' := (⟨ps', st'⟩ : RefinedNet))
      hst (fun t' h' vl hin => by
        rw [hstate]
        exact Or.inl hin)
      (by rw [hstate, hc]; exact Nat.le_refl _)
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach
    refine ⟨?_, ?_⟩
    · intro h t h' vl hin
      rw [← hstates h] at hin
      exact hP.1 h t h' vl hin
    · intro t l hs h hin
      rw [← hstates h] at hin
      rw [← hstates h]
      exact hP.2 t l hs h hin
  · -- reboot: ghost and term survive
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    subst hrb
    have hfacts := votesWithLog_facts_of_update
      hst (fun t' h' vl hin => by
        rw [hstate]
        exact Or.inl hin)
      (by rw [hstate]; exact Nat.le_refl _)
    exact ⟨hfacts.1 hP.1, hfacts.2 hP.2⟩

/-- `VotesWithLogSortedInterface.v:14-19`'s field. -/
theorem votesWithLog_sorted_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votesWithLog_sorted net :=
  fun net hreach => (votesWithLog_sorted_and_term_sanity_invariant net hreach).1

/-- `VotesWithLogTermSanityInterface.v:13-19`'s field. -/
theorem votesWithLog_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votesWithLog_term_sanity net :=
  fun net hreach => (votesWithLog_sorted_and_term_sanity_invariant net hreach).2

/-! ## current_term_gt_zero (BASE) -/

/-- `CurrentTermGtZeroInterface.v:8-11` (`current_term_gt_zero`). -/
def current_term_gt_zero (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).type ≠ .Follower → 1 ≤ (net.nwState h).currentTerm

/-- `CurrentTermGtZeroProof.v:113-136` (`current_term_gt_zero_invariant`):
a non-follower's term passed through a candidacy's `+1` at some point. -/
theorem current_term_gt_zero_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      current_term_gt_zero net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: everyone a follower
    intro h hty
    exact absurd rfl hty
  · -- client_request
    intro h net st' ps' out d l client id c hcr hP _hreach hst _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨htyd, hct, -, -, -⟩ :=
        handleClientRequest_spec h (net.nwState h) client id c hcr
      rw [hct]
      rw [htyd] at hty
      exact hP h hty
    · exact hP h0
  · -- timeout: a candidacy's term is old+1 ≥ 1
    intro net h st' ps' out d l hto hP _hreach hst _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h) hto
      rcases hcases with ⟨hct, hcty, -, -⟩ | ⟨hct, -, -, -, -⟩
      · rw [hct]
        rw [hcty] at hty
        exact hP h hty
      · rw [hct]
        exact Nat.succ_le_succ (Nat.zero_le _)
    · exact hP h0
  · -- append_entries: unchanged term needs the old fact; a grown term
    -- is ≥ 1 outright
    intro xs p ys net st' ps' d m t0 n0 pli plt es ci hae _hbody hP _hreach
      _hpkts hst _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨-, hcases, htycase, -⟩ :=
        handleAppendEntries_spec p.pDst (net.nwState p.pDst) t0 n0 pli plt es
          ci hae
      rcases hcases with ⟨hct, -⟩ | ⟨hlt, -⟩
      · rw [hct]
        rcases htycase with hcty | hcty
        · rw [hcty] at hty
          exact hP p.pDst hty
        · exact absurd hcty hty
      · exact Nat.one_le_iff_ne_zero.mpr (by
          intro h0eq
          rw [h0eq] at hlt
          exact Nat.not_lt_zero _ hlt)
    · exact hP h0
  · -- append_entries_reply
    intro xs p ys net st' ps' d m t0 es res haer _hbody hP _hreach _hpkts hst
      _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨-, hcases, -⟩ :=
        handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst) p.pSrc t0 es
          res haer
      rcases hcases with ⟨hct, -, hcty⟩ | ⟨-, -, hcty⟩
      · rw [hct]
        rw [hcty] at hty
        exact hP p.pDst hty
      · exact absurd hcty hty
    · exact hP h0
  · -- request_vote
    intro xs p ys net st' ps' d m t0 cid lli llt hrv _hbody hP _hreach _hpkts
      hst _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨-, hle, hcases, -⟩ :=
        handleRequestVote_spec p.pDst (net.nwState p.pDst) t0 p.pSrc lli llt
          hrv
      rcases hcases with ⟨hct, hcty⟩ | hcty
      · rw [hct]
        rw [hcty] at hty
        exact hP p.pDst hty
      · exact absurd hcty hty
    · exact hP h0
  · -- request_vote_reply: a grown term is ≥ 1; an unchanged one traces
    -- through the candidate/leader correlations
    intro xs p ys net st' ps' d t0 v hrvr _hbody hP _hreach _hpkts hst _hps h0
    subst hrvr
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨hcases, -, hcand, hleader⟩ :=
        handleRequestVoteReply_spec p.pDst (net.nwState p.pDst) p.pSrc t0 v rfl
      rcases hcases with ⟨hct, -⟩ | ⟨hlt, -⟩
      · rw [hct]
        replace hty :
          (handleRequestVoteReply p.pDst (net.nwState p.pDst) p.pSrc t0
            v).type ≠ .Follower := hty
        rcases hty2 : (handleRequestVoteReply p.pDst (net.nwState p.pDst)
          p.pSrc t0 v).type with _ | _ | _
        · exact absurd hty2 hty
        · obtain ⟨hcty, -⟩ := hcand hty2
          exact hP p.pDst (by rw [hcty]; exact fun heq => nomatch heq)
        · rcases hleader hty2 with heqd | ⟨hcty, -, -⟩
          · refine hP p.pDst ?_
            rw [← heqd, hty2]
            exact fun heq => nomatch heq
          · exact hP p.pDst (by rw [hcty]; exact fun heq => nomatch heq)
      · exact Nat.one_le_iff_ne_zero.mpr (by
          intro h0eq
          rw [h0eq] at hlt
          exact Nat.not_lt_zero _ hlt)
    · exact hP h0
  · -- do_leader
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨hct, -, hcty, -, -, -⟩ := doLeader_spec d h hdl
      rw [hct]
      rw [hcty] at hty
      have := hP h
      rw [hstate] at this
      exact this hty
    · exact hP h0
  · -- do_generic_server
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst _hps h0
    show (st' h0).type ≠ .Follower → 1 ≤ (st' h0).currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨-, hcty, hct, -, -, -⟩ := doGenericServer_spec h d hgs
      rw [hct]
      rw [hcty] at hty
      have := hP h
      rw [hstate] at this
      exact this hty
    · exact hP h0
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h0
    rw [← hstates h0]
    exact hP h0
  · -- reboot: a rebooted node is a follower
    intro net net' d h d' hrb hP _hreach hstate hst _hpkts h0
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hrb
      exact absurd rfl hty
    · exact hP h0

/-! ## terms_and_indices_from_one (base log + ghost) -/

omit O in
/-- `handleClientRequest_log` with the fresh entry's index made
explicit. -/
theorem handleClientRequest_log_index (me : name (P := P))
    (st : raft_data (P := P)) (client : R.clientId) (id : Nat) (c : P.input)
    {out st' l} (h : handleClientRequest me st client id c = (out, st', l)) :
    ∀ e ∈ st'.log, e ∈ st.log ∨
      (e.eTerm = st.currentTerm ∧ e.eIndex = maxIndex st.log + 1 ∧
       st.type = .Leader) := by
  unfold handleClientRequest at h
  split at h
  · rename_i hty
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inr ⟨rfl, rfl, hty⟩
    · exact Or.inl he
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact fun e he => Or.inl he

/-- `TermsAndIndicesFromOneLogInterface.v:9-11`
(`terms_and_indices_from_one_log`). -/
def terms_and_indices_from_one_log (net : RaftNet) : Prop :=
  ∀ h : name (P := P), terms_and_indices_from_one (net.nwState h).log

/-- `TermsAndIndicesFromOneLogInterface.v:13-17`
(`terms_and_indices_from_one_log_nw`). -/
def terms_and_indices_from_one_log_nw (net : RaftNet) : Prop :=
  ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    terms_and_indices_from_one es

/-- `TermsAndIndicesFromOneLogProof.v` (both interface fields, proved
together) — BASE layer; the creation step's entry is at the leader's
`≥ 1` term (`current_term_gt_zero`) and a `≥ 1` fresh index. -/
theorem terms_and_indices_from_one_log_and_nw_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      terms_and_indices_from_one_log net ∧
      terms_and_indices_from_one_log_nw net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_⟩
    · intro h e he
      exact nomatch he
    · intro p t lid pli plt es ci hp _hbody
      exact nomatch hp
  · -- client_request: the creation step
    intro h net st' ps' out d l client id c hcr hP hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, -, -, hl⟩ := handleClientRequest_spec h (net.nwState h)
      client id c hcr
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rcases handleClientRequest_log_index h (net.nwState h) client id c
          hcr e he with hold | ⟨hterm, hidx, hldr⟩
        · exact hhost h e hold
        · constructor
          · show e.eTerm ≥ 1
            rw [hterm]
            exact current_term_gt_zero_invariant net hreach h
              (by rw [hldr]; exact fun heq => nomatch heq)
          · show e.eIndex ≥ 1
            rw [hidx]
            exact Nat.succ_le_succ (Nat.zero_le _)
      · exact hhost h0 e
    · intro p t lid pli plt es ci hp hbody
      rcases hps p hp with hold | hnew
      · exact hnw p t lid pli plt es ci hold hbody
      · rw [hl] at hnew
        exact nomatch hnew
  · -- timeout
    intro net h st' ps' out d l hto hP _hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, -, hmsg⟩ := handleTimeout_spec h (net.nwState h) hto
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        exact hhost h e he
      · exact hhost h0 e
    · intro p t lid pli plt es ci hp hbody
      rcases hps p hp with hold | hnew
      · exact hnw p t lid pli plt es ci hold hbody
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', cid, lli, llt, heqm⟩ := hmsg q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = q.2 from rfl, heqm] at hbody
        exact nomatch hbody
  · -- append_entries: accepted entries came off the wire
    intro xs p ys net st' ps' d m t0 n0 pli plt es ci hae hbody0 hP _hreach
      hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst) t0 n0 pli plt es
        ci hae
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rcases handleAppendEntries_log p.pDst (net.nwState p.pDst) t0 n0 pli
          plt es ci hae e he with hold | ⟨hes, -⟩
        · exact hhost p.pDst e hold
        · exact hnw p t0 n0 pli plt es ci hpmem hbody0 e hes
      · exact hhost h0 e
    · intro p' t lid pli' plt' es'' ci' hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hnw p' t lid pli' plt' es'' ci'
          (hpkts ▸ mem_of_mem_remove_middle hold) hbody'
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
  · -- append_entries_reply
    intro xs p ys net st' ps' d m t0 es res haer _hbody hP _hreach hpkts hst
      hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst) p.pSrc t0 es res haer
    have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst)
      p.pSrc t0 es res haer
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        exact hhost p.pDst e he
      · exact hhost h0 e
    · intro p' t lid pli plt es' ci hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hnw p' t lid pli plt es' ci
          (hpkts ▸ mem_of_mem_remove_middle hold) hbody'
      · rw [hl] at hnew
        exact nomatch hnew
  · -- request_vote
    intro xs p ys net st' ps' d m t0 cid lli llt hrv _hbody hP _hreach hpkts
      hst hps
    obtain ⟨hhost, hnw⟩ := hP
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst) t0 p.pSrc
      lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst) t0 p.pSrc lli llt hrv
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        exact hhost p.pDst e he
      · exact hhost h0 e
    · intro p' t lid pli plt es' ci hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hnw p' t lid pli plt es' ci
          (hpkts ▸ mem_of_mem_remove_middle hold) hbody'
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
  · -- request_vote_reply
    intro xs p ys net st' ps' d t0 v hrvr _hbody hP _hreach hpkts hst hps
    subst hrvr
    obtain ⟨hhost, hnw⟩ := hP
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst)
      p.pSrc t0 v
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        exact hhost p.pDst e he
      · exact hhost h0 e
    · intro p' t lid pli plt es' ci hp' hbody'
      exact hnw p' t lid pli plt es' ci
        (hpkts ▸ mem_of_mem_remove_middle (hps p' hp')) hbody'
  · -- do_leader: replicated entries come from the (bounded) log
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        have := hhost h e
        rw [hstate] at this
        exact this he
      · exact hhost h0 e
    · intro p' t lid pli plt es' ci hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hnw p' t lid pli plt es' ci hold hbody'
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨pi, pt, ci0, es1, heqm, hes⟩ := doLeader_messages d h hdl q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = q.2 from rfl, heqm] at hbody'
        injection hbody' with h1 h2 h3 h4 h5 h6
        subst h5
        intro e he
        have := hhost h e
        rw [hstate] at this
        exact this (hes e he)
  · -- do_generic_server
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → _
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        have := hhost h e
        rw [hstate] at this
        exact this he
      · exact hhost h0 e
    · intro p' t lid pli plt es' ci hp' hbody'
      rcases hps p' hp' with hold | hnew
      · exact hnw p' t lid pli plt es' ci hold hbody'
      · rw [hms] at hnew
        exact nomatch hnew
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    obtain ⟨hhost, hnw⟩ := hP
    refine ⟨?_, ?_⟩
    · intro h0 e he
      rw [← hstates h0] at he
      exact hhost h0 e he
    · intro p' t lid pli plt es' ci hp' hbody'
      exact hnw p' t lid pli plt es' ci (hpkts p' hp') hbody'
  · -- reboot
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    subst hrb
    obtain ⟨hhost, hnw⟩ := hP
    refine ⟨?_, ?_⟩
    · intro h0 e
      rw [hst h0]
      unfold update
      split
      · intro he
        replace he : e ∈ d.log := he
        have := hhost h e
        rw [hstate] at this
        exact this he
      · exact hhost h0 e
    · intro p' t lid pli plt es' ci hp' hbody'
      rw [← hpkts] at hp'
      exact hnw p' t lid pli plt es' ci hp' hbody'

/-- The lifted host form (`TermsAndIndicesFromOneProof.v:24-32`,
`lifted_terms_and_indices_from_one_log`) — a `lift_prop` consumer. -/
theorem tai_log_lifted :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ h : name (P := P),
        terms_and_indices_from_one (net.nwState h).2.log := by
  intro net hreach h
  have := (lift_prop _ (fun net hr =>
    (terms_and_indices_from_one_log_and_nw_invariant net hr).1) net hreach) h
  rw [deghost_spec] at this
  exact this

/-- `TermsAndIndicesFromOneInterface.v:10-13`
(`terms_and_indices_from_one_vwl`). -/
def terms_and_indices_from_one_vwl (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (h' : name (P := P))
    (vl : List (entry (P := P))),
    (t, h', vl) ∈ (net.nwState h).1.votesWithLog →
    terms_and_indices_from_one vl

/-- `TermsAndIndicesFromOneInterface.v:15-18`
(`terms_and_indices_from_one_ll`). -/
def terms_and_indices_from_one_ll (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P))),
    (t, ll) ∈ (net.nwState h).1.leaderLogs →
    terms_and_indices_from_one ll

/-- `TermsAndIndicesFromOneProof.v` (`terms_and_indices_from_one_invariant`):
every recorded vote-log and leaderLog snapshot is a node's own
(lifted-bounded) log at record time. -/
theorem terms_and_indices_from_one_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      terms_and_indices_from_one_vwl net ∧ terms_and_indices_from_one_ll net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_⟩
    · intro h t h' vl hin
      exact nomatch hin
    · intro h t ll hin
      exact nomatch hin
  · -- client_request: neither record changes
    intro h net st' ps' gd out d l client id c _hcr hgd hP _hreach hst _hps
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        subst hgd
        rw [(update_elections_data_client_request_ghost h0 (net.nwState h0)
          client id c).2.1] at hin
        exact hP.1 h0 t h' vl hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        rw [(update_elections_data_client_request_ghost h0 (net.nwState h0)
          client id c).2.2.2] at hin
        exact hP.2 h0 t ll hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- timeout: the self-record carries the node's own bounded log
    intro net h st' ps' gd out d l hto hgd hP hreach hst _hps
    obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        subst hgd
        rcases update_elections_data_timeout_votesWithLog_elim hto hin
          with hold | ⟨-, heqvl⟩
        · exact hP.1 h0 t h' vl hold
        · rw [heqvl, hlog]
          exact tai_log_lifted net hreach h0
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        rw [(update_elections_data_timeout_ghost h0 (net.nwState h0)).1]
          at hin
        exact hP.2 h0 t ll hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- append_entries: neither record changes
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci _hae hgd _hbody hP
      _hreach _hpkts hst _hps
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        subst hgd
        rw [(update_elections_data_appendEntries_ghost p.pDst
          (net.nwState p.pDst) t0 n0 pli plt es ci).2.1] at hin
        exact hP.1 p.pDst t h' vl hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        rw [(update_elections_data_appendEntries_ghost p.pDst
          (net.nwState p.pDst) t0 n0 pli plt es ci).2.2.2] at hin
        exact hP.2 p.pDst t ll hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- append_entries_reply: ghost unchanged
    intro xs p ys net st' ps' gd d m t0 es res _haer hgd _hbody hP _hreach
      _hpkts hst _hps
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        subst hgd
        exact hP.1 p.pDst t h' vl hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        exact hP.2 p.pDst t ll hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- request_vote: the grant records the responder's bounded log
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP hreach
      _hpkts hst _hps
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t0
      p.pSrc lli llt hrv
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        subst hgd
        rcases update_elections_data_requestVote_votesWithLog_elim hrv hin
          with hold | ⟨-, heqvl⟩
        · exact hP.1 p.pDst t h' vl hold
        · rw [heqvl, hlog]
          exact tai_log_lifted net hreach p.pDst
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t0
          p.pSrc lli llt (net.nwState p.pDst)).2.1] at hin
        exact hP.2 p.pDst t ll hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- request_vote_reply: the win snapshots the winner's bounded log
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP hreach _hpkts hst
      _hps
    subst hrvr
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
      p.pSrc t0 v
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        subst hgd
        rw [(update_elections_data_requestVoteReply_votes p.pDst p.pSrc t0 v
          (net.nwState p.pDst)).2.1] at hin
        exact hP.1 p.pDst t h' vl hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        rcases leaderLogs_update_elections_data_RVR hin
          with hold | ⟨-, -, -, hl2⟩
        · exact hP.2 p.pDst t ll hold
        · rw [hl2, hlog]
          exact tai_log_lifted net hreach p.pDst
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- do_leader: ghost rides along
    intro net st' ps' gd d h os d' ms _hdl hP _hreach hstate hst _hps
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        refine hP.1 h0 t h' vl ?_
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        refine hP.2 h0 t ll ?_
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h _hgs hP _hreach hstate hst _hps
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      replace hin : (t, h', vl) ∈ (st' h0).1.votesWithLog := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        refine hP.1 h0 t h' vl ?_
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        refine hP.2 h0 t ll ?_
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      rw [← hstates h0] at hin
      exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      rw [← hstates h0] at hin
      exact hP.2 h0 t ll hin
  · -- reboot: ghost survives
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    subst hrb
    refine ⟨?_, ?_⟩
    · intro h0 t h' vl hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, h', vl) ∈ gd.votesWithLog := hin
        refine hP.1 h0 t h' vl ?_
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq] at hin
        exact hP.1 h0 t h' vl hin
    · intro h0 t ll hin
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        refine hP.2 h0 t ll ?_
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq] at hin
        exact hP.2 h0 t ll hin

/-! ## leaderLogs_candidateEntries -/

/-- `LeaderLogsCandidateEntriesInterface.v:9-13`
(`leaderLogs_candidateEntries`): every entry of every leaderLog is a
candidate entry. -/
def leaderLogs_candidateEntries (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)) (t : term)
    (ll : List (entry (P := P))),
    (t, ll) ∈ (net.nwState h).1.leaderLogs → e ∈ ll →
    candidateEntries e net.nwState

/-- `LeaderLogsCandidateEntriesProof.v:262-281`
(`leaderLogs_candidateEntries_invariant`): unit 3's per-handler
candidateEntries transport lemmas carry the witness; the fresh win
snapshot is the winner's own log, whose entries `candidate_entries`
certifies. -/
theorem leaderLogs_candidateEntries_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_candidateEntries net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h e t ll hll _he
    exact nomatch hll
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
      h0 e t ll hll he
    obtain ⟨htyd, hctd, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_client_request_ghost h0 (net.nwState h0)
          client id c).2.2.2] at hll
        exact hP h0 e t ll hll he
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    subst hgd
    refine candidateEntries_update_same
      (update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.1 hctd htyd hce
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP hreach hst _hps
      h0 e t ll hll he
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_timeout_ghost h0 (net.nwState h0)).1]
          at hll
        exact hP h0 e t ll hll he
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    subst hgd
    exact handleTimeout_preserves_candidateEntries hreach hto hce
  · -- append_entries
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps h0 e t ll hll he
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_appendEntries_ghost p.pDst
          (net.nwState p.pDst) t0 n0 pli plt es ci).2.2.2] at hll
        exact hP p.pDst e t ll hll he
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    subst hgd
    exact handleAppendEntries_preserves_candidateEntries hae hce
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach
      _hpkts hst _hps h0 e t ll hll he
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        subst hgd
        exact hP p.pDst e t ll hll he
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    subst hgd
    exact handleAppendEntriesReply_preserves_candidateEntries haer hce
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP
      _hreach _hpkts hst _hps h0 e t ll hll he
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        subst hgd
        rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t0
          p.pSrc lli llt (net.nwState p.pDst)).2.1] at hll
        exact hP p.pDst e t ll hll he
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    subst hgd
    exact handleRequestVote_preserves_candidateEntries hrv hce
  · -- request_vote_reply: the fresh snapshot's entries are the winner's
    -- own log entries — candidate_entries certifies them
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP hreach _hpkts hst
      _hps h0 e t ll hll he
    subst hrvr
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
      p.pSrc t0 v
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        subst hgd
        rcases leaderLogs_update_elections_data_RVR hll
          with hold | ⟨-, -, -, hl2⟩
        · exact hP p.pDst e t ll hold he
        · -- fresh snapshot = winner's (unchanged) log
          rw [hl2, hlog] at he
          exact (candidate_entries_invariant net hreach).1 p.pDst e he
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    subst hgd
    exact handleRequestVoteReply_preserves_candidateEntries hreach hce
  · -- do_leader: cronies/type/term untouched
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
      h0 e t ll hll he
    obtain ⟨hct, -, hcty, -, -, -⟩ := doLeader_spec d h hdl
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        refine hP h0 e t ll ?_ he
        rw [hstate]
        exact hll
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    refine candidateEntries_update_same ?_ ?_ ?_ hce
    · rw [hstate]
    · rw [hstate, hct]
    · rw [hstate, hcty]
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps
      h0 e t ll hll he
    obtain ⟨-, hcty, hct, -, -, -⟩ := doGenericServer_spec h d hgs
    replace hll : (t, ll) ∈ (st' h0).1.leaderLogs := hll
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        refine hP h0 e t ll ?_ he
        rw [hstate]
        exact hll
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    refine candidateEntries_update_same ?_ ?_ ?_ hce
    · rw [hstate]
    · rw [hstate, hct]
    · rw [hstate, hcty]
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h0 e t ll hll he
    rw [← hstates h0] at hll
    have hce := hP h0 e t ll hll he
    exact candidateEntries_ext (fun h => (hstates h).symm ▸ rfl) hce
  · -- reboot: the follower type discharges the witness implication
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
      h0 e t ll hll he
    subst hrb
    rw [hst h0] at hll
    have hce : candidateEntries e net.nwState := by
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hll
        replace hll : (t, ll) ∈ gd.leaderLogs := hll
        refine hP h0 e t ll ?_ he
        rw [hstate]
        exact hll
      · rw [update_neq _ _ heq] at hll
        exact hP h0 e t ll hll he
    refine candidateEntries_ext hst ?_
    obtain ⟨x, hw, himp⟩ := hce
    by_cases hxh : x = h
    · subst hxh
      refine ⟨x, ?_, ?_⟩
      · rw [update_same]
        show wonElection (dedup (gd.cronies e.eTerm)) = true
        rw [hstate] at hw
        exact hw
      · rw [update_same]
        intro _hct
        show (reboot d).type ≠ serverType.Candidate
        exact fun heq => nomatch heq
    · refine ⟨x, ?_, ?_⟩
      · rw [update_neq _ _ hxh]
        exact hw
      · rw [update_neq _ _ hxh]
        exact himp

end CreationRing

end Raft
end VerdiCompat
