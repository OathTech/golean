import VerdiCompat.CandidateEntries

/-!
# The leaderLogs ring — one leaderLog per term

Campaign Arc 3 unit 4: the `leaderLogs` slice of the
leader-completeness lattice, 1:1 against the sources @ a3375e8 —

- `requestVote_term_sanity` (`Raft/RequestVoteTermSanityInterface.v`),
  `votedFor_term_sanity` (`Raft/VotedForTermSanityInterface.v`),
  `requestVoteReply_term_sanity`
  (`Raft/RequestVoteReplyTermSanityInterface.v`),
  `requestVote_maxIndex_maxTerm`
  (`Raft/RequestVoteMaxIndexMaxTermInterface.v`) — the message/vote
  term-sanity leaves;
- `votes_votesWithLog_correspond`
  (`Raft/VotesVotesWithLogCorrespondInterface.v`);
- `candidate_term_gt_log` (`Raft/CandidateTermGtLogInterface.v`, BASE
  layer) and the three `leaderLogs_term_sanity` invariants
  (`Raft/LeaderLogsTermSanityInterface.v`) — the first real
  `lift_prop` consumer;
- `leaders_have_leaderLogs` (`Raft/LeadersHaveLeaderLogsInterface.v`);
- the moreUpToDate chain: `votedFor_moreUpToDate`
  (`Raft/VotedForMoreUpToDateInterface.v`),
  `requestVoteReply_moreUpToDate`
  (`Raft/RequestVoteReplyMoreUpToDateInterface.v`),
  `votesReceived_moreUpToDate`
  (`Raft/VotesReceivedMoreUpToDateInterface.v`);
- `leaderLogs_votesWithLog` (`Raft/LeaderLogsVotesWithLogInterface.v`);
- **`one_leaderLog_per_term`** (`Raft/OneLeaderLogPerTermInterface.v`) —
  the ring's exit theorem — and the `leader_completeness` STATEMENT
  (`Raft/LeaderCompletenessInterface.v`, defs only; its proof is a
  later arc's).

Statements 1:1 with the Interface files; proofs re-derived through the
ported induction principles (Ltac does not port).
-/

namespace VerdiCompat
namespace Raft

section LeaderLogsRing
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-! ## requestVote_term_sanity (nw leaf) -/

/-- `RequestVoteTermSanityInterface.v:9-13` (`requestVote_term_sanity`):
every in-flight RequestVote's term is bounded by its sender's current
term. -/
def requestVote_term_sanity (net : RefinedNet) : Prop :=
  ∀ (t : term) (h : name (P := P)) (mi : logIndex) (mt : term)
    (p : RefinedPacket),
    p ∈ net.nwPackets → p.pBody = .RequestVote t h mi mt →
    t ≤ (net.nwState p.pSrc).2.currentTerm

/-- `RequestVoteTermSanityProof.v:174-189`
(`requestVote_term_sanity_invariant`). -/
theorem requestVote_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      requestVote_term_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: no packets
    intro t h0 mi mt p hp _hbody
    exact nomatch hp
  · -- client_request: no packets sent, term unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
      t0 h0 mi mt p' hp' hbody
    obtain ⟨-, hct, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hl] at hnew
        exact nomatch hnew
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq] at hPh
      rw [hct]
      exact hPh
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- timeout: new RequestVotes carry exactly the new term
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
      t0 h0 mi mt p' hp' hbody
    obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hle : (net.nwState h).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
      · exact hct ▸ Nat.le_refl _
      · rw [hct]
        exact Nat.le_succ _
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rcases hps p' hp' with hold | hnew
    · rw [hst p'.pSrc]
      unfold update
      split
      · rename_i heq
        have hPh := hP t0 h0 mi mt p' hold hbody
        rw [heq] at hPh
        exact Nat.le_trans hPh hle
      · exact hP t0 h0 mi mt p' hold hbody
    · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
      have hqm := handleTimeout_messages h (net.nwState h).2 hto q hq
      rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
        at hbody
      injection hbody with h1 h2 h3 h4
      subst h1
      rw [hst h]
      unfold update
      split
      · exact Nat.le_refl _
      · rename_i hne
        exact absurd rfl hne
  · -- append_entries: reply is an AppendEntriesReply; term grows
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody0 hP
      _hreach hpkts hst hps t0 h0 mi mt p' hp' hbody
    obtain ⟨-, hcases, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt es
        ci hae
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
      · exact hct ▸ Nat.le_refl _
      · exact Nat.le_of_lt hct
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl, hm]
          at hbody
        exact nomatch hbody
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- append_entries_reply: nothing sent; term grows
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody0 hP _hreach
      hpkts hst hps t0 h0 mi mt p' hp' hbody
    obtain ⟨-, hcases, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t es
        res haer
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hct, -, -⟩ | ⟨hct, -, -⟩
      · exact hct ▸ Nat.le_refl _
      · exact Nat.le_of_lt hct
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · rw [hl] at hnew
        exact nomatch hnew
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- request_vote: reply is a RequestVoteReply; term grows
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody0 hP _hreach
      hpkts hst hps t0 h0 mi mt p' hp' hbody
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl, hm]
          at hbody
        exact nomatch hbody
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- request_vote_reply: packets only shrink; term grows
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody0 hP _hreach hpkts hst
      hps t0 h0 mi mt p' hp' hbody
    subst hrvr
    obtain ⟨hcases, -, -, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t v rfl
    have hle : (net.nwState p.pDst).2.currentTerm
        ≤ (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t v).currentTerm := by
      rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
      · exact hct ▸ Nat.le_refl _
      · exact Nat.le_of_lt hct
    have hp'' : p' ∈ net.nwPackets :=
      hpkts ▸ mem_of_mem_remove_middle (hps p' hp')
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- do_leader: only AppendEntries sent; term unchanged
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
      t0 h0 mi mt p' hp' hbody
    obtain ⟨hct, -, -, -, -, hmsgs⟩ := doLeader_spec d h hdl
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', lid, pli, plt, es, ci, hqm⟩ := hmsgs q hq
        rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
          at hbody
        exact nomatch hbody
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq, hstate] at hPh
      rw [hct]
      exact hPh
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- do_generic_server: nothing sent; term unchanged
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
      t0 h0 mi mt p' hp' hbody
    obtain ⟨-, -, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hms] at hnew
        exact nomatch hnew
    show t0 ≤ (st' p'.pSrc).2.currentTerm
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq, hstate] at hPh
      rw [hct]
      exact hPh
    · exact hP t0 h0 mi mt p' hp'' hbody
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach t0 h0 mi mt p' hp' hbody
    rw [← hstates p'.pSrc]
    exact hP t0 h0 mi mt p' (hpkts p' hp') hbody
  · -- reboot: term survives, packets unchanged
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
      t0 h0 mi mt p' hp' hbody
    have hp'' : p' ∈ net.nwPackets := by
      rw [hpkts]
      exact hp'
    rw [hst p'.pSrc]
    unfold update
    split
    · rename_i heq
      subst hrb
      show t0 ≤ (reboot d).currentTerm
      have hPh := hP t0 h0 mi mt p' hp'' hbody
      rw [heq, hstate] at hPh
      exact hPh
    · exact hP t0 h0 mi mt p' hp'' hbody

/-! ## votes_votesWithLog_correspond -/

/-- `VotesVotesWithLogCorrespondInterface.v:9-13` (`votes_votesWithLog`). -/
def votes_votesWithLog (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (h' : name (P := P))
    (vl : List (entry (P := P))),
    (t, h', vl) ∈ (net.nwState h).1.votesWithLog →
    (t, h') ∈ (net.nwState h).1.votes

/-- `VotesVotesWithLogCorrespondInterface.v:15-18` (`votesWithLog_votes`). -/
def votesWithLog_votes (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (h' : name (P := P)),
    (t, h') ∈ (net.nwState h).1.votes →
    ∃ vl, (t, h', vl) ∈ (net.nwState h).1.votesWithLog

/-- `VotesVotesWithLogCorrespondInterface.v:20-21`
(`votes_votesWithLog_correspond`). -/
def votes_votesWithLog_correspond (net : RefinedNet) : Prop :=
  votes_votesWithLog net ∧ votesWithLog_votes net

/-- `VotesVotesWithLogCorrespondProof.v:12-36`
(`votes_votesWithLog_correspond_cases`): the step helper — every ghost
update either leaves votes/votesWithLog alone or extends both in
lockstep. -/
theorem votes_votesWithLog_correspond_of_update {net net' : RefinedNet}
    {h : name (P := P)} {gd d}
    (hP : votes_votesWithLog_correspond net)
    (hst : ∀ h', net'.nwState h' = update net.nwState h (gd, d) h')
    (hgd : (gd.votes = (net.nwState h).1.votes ∧
            gd.votesWithLog = (net.nwState h).1.votesWithLog) ∨
           (∃ tn nn vl, gd.votes = (tn, nn) :: (net.nwState h).1.votes ∧
            gd.votesWithLog = (tn, nn, vl) :: (net.nwState h).1.votesWithLog)) :
    votes_votesWithLog_correspond net' := by
  obtain ⟨hvv, hvwv⟩ := hP
  constructor
  · intro h0 t h' vl hin
    rw [hst h0] at hin ⊢
    unfold update at hin ⊢
    split at hin
    · rename_i heq
      rw [if_pos heq]
      show (t, h') ∈ gd.votes
      rcases hgd with ⟨hv, hw⟩ | ⟨tn, nn, wvl, hv, hw⟩
      · rw [hw] at hin
        rw [hv]
        exact hvv h t h' vl hin
      · rw [hw] at hin
        rw [hv]
        rcases List.mem_cons.mp hin with heq' | hin
        · injection heq' with e1 e2
          injection e2 with e2 e3
          subst e1
          subst e2
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hvv h t h' vl hin)
    · rename_i hne
      rw [if_neg hne]
      exact hvv h0 t h' vl hin
  · intro h0 t h' hin
    rw [hst h0] at hin ⊢
    unfold update at hin ⊢
    split at hin
    · rename_i heq
      rw [if_pos heq]
      show ∃ vl, (t, h', vl) ∈ gd.votesWithLog
      rcases hgd with ⟨hv, hw⟩ | ⟨tn, nn, wvl, hv, hw⟩
      · rw [hv] at hin
        rw [hw]
        exact hvwv h t h' hin
      · rw [hv] at hin
        rw [hw]
        rcases List.mem_cons.mp hin with heq' | hin
        · injection heq' with e1 e2
          subst e1
          subst e2
          exact ⟨wvl, List.mem_cons_self ..⟩
        · obtain ⟨vl, hvl⟩ := hvwv h t h' hin
          exact ⟨vl, List.mem_cons_of_mem _ hvl⟩
    · rename_i hne
      rw [if_neg hne]
      exact hvwv h0 t h' hin

/-- `VotesVotesWithLogCorrespondProof.v:50-77`
(`votes_votesWithLog_correspond_invariant`). -/
theorem votes_votesWithLog_correspond_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votes_votesWithLog_correspond net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    exact ⟨fun h t h' vl hin => (nomatch hin), fun h t h' hin => (nomatch hin)⟩
  · -- client_request
    intro h net st' ps' gd out d l client id c _hcr hgd hP _hreach hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    subst hgd
    obtain ⟨hv, hw, -, -⟩ :=
      update_elections_data_client_request_ghost h (net.nwState h) client id c
    exact Or.inl ⟨hv, hw⟩
  · -- timeout
    intro net h st' ps' gd out d l _hto hgd hP _hreach hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    subst hgd
    exact update_elections_data_timeout_lockstep h (net.nwState h)
  · -- append_entries
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci _hae hgd _hbody hP
      _hreach _hpkts hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    subst hgd
    obtain ⟨hv, hw, -, -⟩ :=
      update_elections_data_appendEntries_ghost p.pDst (net.nwState p.pDst)
        t n0 pli plt es ci
    exact Or.inl ⟨hv, hw⟩
  · -- append_entries_reply (ghost unchanged)
    intro xs p ys net st' ps' gd d m t es res _haer hgd _hbody hP _hreach
      _hpkts hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    subst hgd
    exact Or.inl ⟨rfl, rfl⟩
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt _hrv hgd _hbody hP _hreach
      _hpkts hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    subst hgd
    exact update_elections_data_requestVote_lockstep p.pDst p.pSrc t p.pSrc
      lli llt (net.nwState p.pDst)
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v _hrvr hgd _hbody hP _hreach _hpkts hst
      _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    subst hgd
    obtain ⟨hv, hw, -⟩ := update_elections_data_requestVoteReply_votes p.pDst
      p.pSrc t v (net.nwState p.pDst)
    exact Or.inl ⟨hv, hw⟩
  · -- do_leader (ghost rides along)
    intro net st' ps' gd d h os d' ms _hdl hP _hreach hstate hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    rw [hstate]
    exact Or.inl ⟨rfl, rfl⟩
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h _hgs hP _hreach hstate hst _hps
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    rw [hstate]
    exact Or.inl ⟨rfl, rfl⟩
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach
    obtain ⟨hvv, hvwv⟩ := hP
    constructor
    · intro h0 t h' vl hin
      rw [← hstates h0] at hin ⊢
      exact hvv h0 t h' vl hin
    · intro h0 t h' hin
      rw [← hstates h0] at hin ⊢
      exact hvwv h0 t h' hin
  · -- reboot (ghost survives)
    intro net net' gd d h d' _hrb hP _hreach hstate hst _hpkts
    refine votes_votesWithLog_correspond_of_update hP hst ?_
    rw [hstate]
    exact Or.inl ⟨rfl, rfl⟩

/-! ## leaders_have_leaderLogs -/

/-- `LeadersHaveLeaderLogsInterface.v:8-12` (`leaders_have_leaderLogs`):
every leader has a leaderLog recorded at its current term. -/
def leaders_have_leaderLogs (net : RefinedNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).2.type = .Leader →
    ∃ ll, ((net.nwState h).2.currentTerm, ll) ∈ (net.nwState h).1.leaderLogs

/-- `LeadersHaveLeaderLogsProof.v:137-152`
(`leaders_have_leaderLogs_invariant`). -/
theorem leaders_have_leaderLogs_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaders_have_leaderLogs net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: everyone a follower
    intro h hty
    exact nomatch hty
  · -- client_request: type/term/leaderLogs unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hgd
      obtain ⟨hty0, hct, -, -, -⟩ :=
        handleClientRequest_spec h (net.nwState h).2 client id c hcr
      rw [(update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.2]
      show ∃ ll, (d.currentTerm, ll) ∈ (net.nwState h).1.leaderLogs
      rw [hct]
      rw [hty0] at hty
      exact hP h hty
    · exact hP h0
  · -- timeout: a leader only heartbeats
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hgd
      rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
      show ∃ ll, (d.currentTerm, ll) ∈ (net.nwState h).1.leaderLogs
      obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
      rcases hcases with ⟨hct, hty0, -, -⟩ | ⟨-, hty0, -, -, -⟩
      · rw [hct]
        rw [hty0] at hty
        exact hP h hty
      · rw [hty0] at hty
        exact nomatch hty
    · exact hP h0
  · -- append_entries: a leader must have rejected (state untouched)
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hgd
      have hd : d = (net.nwState p.pDst).2 :=
        handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst).2 t n0 pli plt es ci hae
          (by rw [hty]; exact fun heq => nomatch heq)
      rw [(update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci).2.2.2]
      show ∃ ll, (d.currentTerm, ll) ∈ (net.nwState p.pDst).1.leaderLogs
      rw [hd] at hty ⊢
      exact hP p.pDst hty
    · exact hP h0
  · -- append_entries_reply: leader ⇒ type/term unchanged; ghost unchanged
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      _hpkts hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hgd
      obtain ⟨-, hcases, -⟩ :=
        handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t
          es res haer
      rcases hcases with ⟨hct, -, hty0⟩ | ⟨-, -, hty0⟩
      · show ∃ ll, (d.currentTerm, ll) ∈ (net.nwState p.pDst).1.leaderLogs
        rw [hct]
        rw [hty0] at hty
        exact hP p.pDst hty
      · rw [hty0] at hty
        exact nomatch hty
    · exact hP h0
  · -- request_vote: leader ⇒ type/term unchanged; leaderLogs unchanged
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP _hreach
      _hpkts hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hgd
      obtain ⟨-, -, hcases, -⟩ :=
        handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
          hrv
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t p.pSrc
        lli llt (net.nwState p.pDst)).2.1]
      show ∃ ll, (d.currentTerm, ll) ∈ (net.nwState p.pDst).1.leaderLogs
      rcases hcases with ⟨hct, hty0⟩ | hty0
      · rw [hct]
        rw [hty0] at hty
        exact hP p.pDst hty
      · rw [hty0] at hty
        exact nomatch hty
    · exact hP h0
  · -- request_vote_reply: a standing leader keeps its old leaderLog; a
    -- fresh winner just snapshotted one
    intro xs p ys net st' ps' gd d t v hrvr hgd hbody hP _hreach _hpkts hst
      _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hgd
      subst hrvr
      obtain ⟨-, -, -, hleader⟩ :=
        handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t v
          rfl
      rcases hleader hty with hd | ⟨hcand, -, hct⟩
      · -- standing leader: state unchanged, old leaderLog survives
        obtain ⟨ll, hll⟩ := hP p.pDst (by rw [← hd]; exact hty)
        refine ⟨ll, ?_⟩
        show ((handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t
          v).currentTerm, ll) ∈ _
        rw [hd]
        exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
          p.pSrc t v (net.nwState p.pDst) hll
      · -- fresh winner: the snapshot is the witness
        exact ⟨(handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t
            v).log,
          update_elections_data_requestVoteReply_leaderLogs_intro p.pDst
            p.pSrc t v (net.nwState p.pDst) hcand hty⟩
    · exact hP h0
  · -- do_leader: type/term unchanged, ghost rides along
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨hct, -, hty0, -, -, -⟩ := doLeader_spec d h hdl
      rw [hty0] at hty
      have := hP h
      rw [hstate] at this
      show ∃ ll, (d'.currentTerm, ll) ∈ gd.leaderLogs
      rw [hct]
      exact this hty
    · exact hP h0
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps h0
    show (st' h0).2.type = .Leader →
      ∃ ll, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨-, hty0, hct, -, -, -⟩ := doGenericServer_spec h d hgs
      rw [hty0] at hty
      have := hP h
      rw [hstate] at this
      show ∃ ll, (d'.currentTerm, ll) ∈ gd.leaderLogs
      rw [hct]
      exact this hty
    · exact hP h0
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h0
    rw [← hstates h0]
    exact hP h0
  · -- reboot: a rebooted node is a follower
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts h0
    rw [hst h0]
    unfold update
    split
    · intro hty
      subst hrb
      exact nomatch hty
    · exact hP h0

end LeaderLogsRing

end Raft
end VerdiCompat
