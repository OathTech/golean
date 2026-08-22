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

end CreationRing

end Raft
end VerdiCompat
