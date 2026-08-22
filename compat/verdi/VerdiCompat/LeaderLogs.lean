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

/-! ## votedFor_term_sanity -/

/-- `VotedForTermSanityInterface.v:8-13` (`votedFor_term_sanity`): a
recorded `votedFor` at the voter's current term bounds the votee's
term. -/
def votedFor_term_sanity (net : RefinedNet) : Prop :=
  ∀ (t : term) (h h' : name (P := P)),
    (net.nwState h').2.currentTerm = t →
    (net.nwState h').2.votedFor = some h →
    t ≤ (net.nwState h).2.currentTerm
/-- Step helper for `votedFor_term_sanity`: an update at `u` preserves
the invariant if it never shrinks `u`'s term and every vote it reports
is the old one at the old term, or is directly bounded by the votee's
NEW term. -/
theorem votedFor_term_sanity_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : votedFor_term_sanity net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hle : (net.nwState u).2.currentTerm ≤ d.currentTerm)
    (hvote : ∀ hh : name (P := P), d.votedFor = some hh →
       ((net.nwState u).2.votedFor = some hh ∧
        d.currentTerm = (net.nwState u).2.currentTerm) ∨
       d.currentTerm ≤ (update net.nwState u (gd, d) hh).2.currentTerm) :
    votedFor_term_sanity net' := by
  intro t hh hh' hct hvf
  rw [hst hh'] at hct hvf
  rw [hst hh]
  by_cases heq' : hh' = u
  · subst heq'
    rw [update_same] at hct hvf
    replace hct : d.currentTerm = t := hct
    replace hvf : d.votedFor = some hh := hvf
    rcases hvote hh hvf with ⟨hvold, hcold⟩ | hnew
    · have hb := hP t hh hh' (by rw [← hcold]; exact hct) hvold
      by_cases heq2 : hh = hh'
      · subst heq2
        rw [update_same]
        exact Nat.le_trans hb hle
      · rw [update_neq _ _ heq2]
        exact hb
    · rw [hct] at hnew
      exact hnew
  · rw [update_neq _ _ heq'] at hct hvf
    have hb := hP t hh hh' hct hvf
    by_cases heq2 : hh = u
    · subst heq2
      rw [update_same]
      exact Nat.le_trans hb hle
    · rw [update_neq _ _ heq2]
      exact hb

/-- `VotedForTermSanityProof.v:153-168` (`votedFor_term_sanity_invariant`). -/
theorem votedFor_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votedFor_term_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: nobody voted
    intro t hh hh' _hct hvf
    exact nomatch hvf
  · -- client_request: term and vote unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    obtain ⟨-, hctd, hvfd, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    refine votedFor_term_sanity_of_update hP hst (hctd ▸ Nat.le_refl _) ?_
    intro hh hvf
    rw [hvfd] at hvf
    exact Or.inl ⟨hvf, hctd⟩
  · -- timeout: a fresh candidacy is a self-vote at its own new term
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps
    obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hle : (net.nwState h).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · rw [hc]
        exact Nat.le_succ _
    refine votedFor_term_sanity_of_update hP hst hle ?_
    intro hh hvf
    rcases hcases with ⟨hc, -, hv, -⟩ | ⟨-, -, hv, -, -⟩
    · rw [hv] at hvf
      exact Or.inl ⟨hvf, hc⟩
    · -- self-vote: the votee IS the updated node
      rw [hv] at hvf
      injection hvf with hvf
      subst hvf
      right
      rw [update_same]
      exact Nat.le_refl _
  · -- append_entries: vote preserved or cleared; term grows
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps
    obtain ⟨-, hcases, -, -⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es
        ci hae
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    refine votedFor_term_sanity_of_update hP hst hle ?_
    intro hh hvf
    rcases hcases with ⟨hc, hv⟩ | ⟨-, hv⟩
    · rw [hv] at hvf
      exact Or.inl ⟨hvf, hc⟩
    · rw [hv] at hvf
      exact nomatch hvf
  · -- append_entries_reply: same shape
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, hcases, -⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es
        res haer
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -, -⟩ | ⟨hc, -, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    refine votedFor_term_sanity_of_update hP hst hle ?_
    intro hh hvf
    rcases hcases with ⟨hc, hv, -⟩ | ⟨-, hv, -⟩
    · rw [hv] at hvf
      exact Or.inl ⟨hvf, hc⟩
    · rw [hv] at hvf
      exact nomatch hvf
  · -- request_vote: a fresh grant's term is bounded by the candidate's
    -- own term via requestVote_term_sanity
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd hbody hP hreach
      hpkts hst _hps
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt
        hrv
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hts := requestVote_term_sanity_invariant net hreach t0 cid lli llt p
      hpmem hbody
    refine votedFor_term_sanity_of_update hP hst hle ?_
    intro hh hvf
    rcases update_elections_data_requestVote_votedFor hrv hvf
      with ⟨hvold, hcold⟩ | ⟨heqc, hctnew, -, -⟩
    · exact Or.inl ⟨hvold, hcold⟩
    · -- fresh grant to p.pSrc at the request's term
      subst heqc
      right
      rw [hctnew]
      by_cases hsrc : p.pSrc = p.pDst
      · rw [hsrc, update_same]
        refine Nat.le_trans ?_ hle
        rw [← hsrc]
        exact hts
      · rw [update_neq _ _ hsrc]
        exact hts
  · -- request_vote_reply: vote preserved or cleared; term grows
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
    refine votedFor_term_sanity_of_update hP hst hle ?_
    intro hh hvf
    rcases hcases with ⟨hc, hv⟩ | ⟨-, hv⟩
    · rw [hv] at hvf
      exact Or.inl ⟨hvf, hc⟩
    · rw [hv] at hvf
      exact nomatch hvf
  · -- do_leader: term and vote unchanged
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hctd, hvfd, -, -, -, -⟩ := doLeader_spec d h hdl
    refine votedFor_term_sanity_of_update hP hst ?_ ?_
    · rw [hstate, hctd]
      exact Nat.le_refl _
    · intro hh hvf
      rw [hvfd] at hvf
      left
      rw [hstate]
      exact ⟨hvf, hctd⟩
  · -- do_generic_server: term and vote unchanged
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨-, -, hctd, -, hvfd, -⟩ := doGenericServer_spec h d hgs
    refine votedFor_term_sanity_of_update hP hst ?_ ?_
    · rw [hstate, hctd]
      exact Nat.le_refl _
    · intro hh hvf
      rw [hvfd] at hvf
      left
      rw [hstate]
      exact ⟨hvf, hctd⟩
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach t hh hh' hct hvf
    rw [← hstates hh'] at hct hvf
    rw [← hstates hh]
    exact hP t hh hh' hct hvf
  · -- reboot: term and vote survive the crash
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    subst hrb
    refine votedFor_term_sanity_of_update hP hst ?_ ?_
    · rw [hstate]
      exact Nat.le_refl _
    · intro hh hvf
      replace hvf : d.votedFor = some hh := hvf
      left
      rw [hstate]
      exact ⟨hvf, rfl⟩

/-! ## requestVoteReply_term_sanity -/

/-- `RequestVoteReplyTermSanityInterface.v:10-14`
(`requestVoteReply_term_sanity`): every in-flight granted reply's term
is bounded by its destination's (the candidate's) current term. -/
def requestVoteReply_term_sanity (net : RefinedNet) : Prop :=
  ∀ (t : term) (p : RefinedPacket),
    p ∈ net.nwPackets → p.pBody = .RequestVoteReply t true →
    t ≤ (net.nwState p.pDst).2.currentTerm

/-- `RequestVoteReplyTermSanityProof.v:186-201`
(`requestVoteReply_term_sanity_invariant`): a grant is issued at exactly
the request's term, and the request's term was bounded by the
candidate's — so the bound survives every step. -/
theorem requestVoteReply_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      requestVoteReply_term_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro t p hp _hbody
    exact nomatch hp
  · -- client_request: no packets, term unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
      t p' hp' hbody
    obtain ⟨-, hct, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hl] at hnew
        exact nomatch hnew
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq] at hPh
      rw [hct]
      exact hPh
    · exact hP t p' hp'' hbody
  · -- timeout: only RequestVotes sent; term grows
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps t p' hp' hbody
    obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hle : (net.nwState h).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · rw [hc]
        exact Nat.le_succ _
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        have hqm := handleTimeout_messages h (net.nwState h).2 hto q hq
        rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
          at hbody
        exact nomatch hbody
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t p' hp'' hbody
  · -- append_entries: reply is an AppendEntriesReply; term grows
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody0 hP
      _hreach hpkts hst hps t p' hp' hbody
    obtain ⟨-, hcases, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es
        ci hae
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl, hm]
          at hbody
        exact nomatch hbody
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t p' hp'' hbody
  · -- append_entries_reply: nothing sent; term grows
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody0 hP _hreach
      hpkts hst hps t p' hp' hbody
    obtain ⟨-, hcases, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es
        res haer
    have hle : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hcases with ⟨hc, -, -⟩ | ⟨hc, -, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · rw [hl] at hnew
        exact nomatch hnew
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t p' hp'' hbody
  · -- request_vote: the interesting case — the emitted grant carries
    -- exactly the request's term, bounded by the candidate's
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd hbody0 hP hreach
      hpkts hst hps t p' hp' hbody
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt
        hrv
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hts := requestVote_term_sanity_invariant net hreach t0 cid lli llt p
      hpmem hbody0
    rcases hps p' hp' with hold | hnew
    · -- old packet: term growth at the destination
      have hp'' : p' ∈ net.nwPackets := hpkts ▸ mem_of_mem_remove_middle hold
      show t ≤ (st' p'.pDst).2.currentTerm
      rw [hst p'.pDst]
      unfold update
      split
      · rename_i heq
        have hPh := hP t p' hp'' hbody
        rw [heq] at hPh
        exact Nat.le_trans hPh hle
      · exact hP t p' hp'' hbody
    · -- the fresh reply: a grant at the request's term
      subst hnew
      rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl]
        at hbody
      rw [hbody] at hrv
      obtain ⟨rfl, -, -, -⟩ :=
        handleRequestVote_grant p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli
          llt hrv
      show t ≤ (st' p.pSrc).2.currentTerm
      rw [hst p.pSrc]
      unfold update
      split
      · rename_i heq
        refine Nat.le_trans ?_ hle
        rw [← heq]
        exact hts
      · exact hts
  · -- request_vote_reply: packets shrink; term grows
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody0 hP _hreach hpkts hst
      hps t p' hp' hbody
    subst hrvr
    obtain ⟨hcases, -, -, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v rfl
    have hle : (net.nwState p.pDst).2.currentTerm
        ≤ (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0
            v).currentTerm := by
      rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
    have hp'' : p' ∈ net.nwPackets :=
      hpkts ▸ mem_of_mem_remove_middle (hps p' hp')
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq] at hPh
      exact Nat.le_trans hPh hle
    · exact hP t p' hp'' hbody
  · -- do_leader: only AppendEntries sent; term unchanged
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
      t p' hp' hbody
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
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq, hstate] at hPh
      rw [hct]
      exact hPh
    · exact hP t p' hp'' hbody
  · -- do_generic_server: nothing sent; term unchanged
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
      t p' hp' hbody
    obtain ⟨-, -, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hms] at hnew
        exact nomatch hnew
    show t ≤ (st' p'.pDst).2.currentTerm
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      have hPh := hP t p' hp'' hbody
      rw [heq, hstate] at hPh
      rw [hct]
      exact hPh
    · exact hP t p' hp'' hbody
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach t p' hp' hbody
    rw [← hstates p'.pDst]
    exact hP t p' (hpkts p' hp') hbody
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts t p' hp' hbody
    have hp'' : p' ∈ net.nwPackets := by
      rw [hpkts]
      exact hp'
    rw [hst p'.pDst]
    unfold update
    split
    · rename_i heq
      subst hrb
      show t ≤ (reboot d).currentTerm
      have hPh := hP t p' hp'' hbody
      rw [heq, hstate] at hPh
      exact hPh
    · exact hP t p' hp'' hbody

/-! ## requestVote_maxIndex_maxTerm -/

/-- `RequestVoteMaxIndexMaxTermInterface.v:10-17`
(`requestVote_maxIndex_maxTerm`): a candidate's own in-flight
RequestVote at its current term reports exactly its log's
maxIndex/maxTerm. -/
def requestVote_maxIndex_maxTerm (net : RefinedNet) : Prop :=
  ∀ (t : term) (h : name (P := P)) (p : RefinedPacket) (n : name (P := P))
    (mi : logIndex) (mt : term),
    (net.nwState h).2.currentTerm = t →
    (net.nwState h).2.type = .Candidate →
    p ∈ net.nwPackets → p.pBody = .RequestVote t n mi mt →
    p.pSrc = h →
    maxIndex (net.nwState h).2.log = mi ∧ maxTerm (net.nwState h).2.log = mt

/-- `RequestVoteMaxIndexMaxTermProof.v:177-192`
(`requestVote_maxIndex_maxTerm_invariant`). -/
theorem requestVote_maxIndex_maxTerm_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      requestVote_maxIndex_maxTerm net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro t h0 p n mi mt _hct _hty hp _hbody _hsrc
    exact nomatch hp
  · -- client_request: a candidate's request is refused — state untouched
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
      t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨htyd, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hl] at hnew
        exact nomatch hnew
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = h
    · subst heq
      rw [update_same] at hct hty ⊢
      have hd : d = (net.nwState h0).2 :=
        handleClientRequest_not_leader h0 (net.nwState h0).2 client id c hcr
          (by
            rw [← htyd]
            replace hty : d.type = .Candidate := hty
            rw [hty]
            exact fun heq => nomatch heq)
      replace hct : d.currentTerm = t := hct
      replace hty : d.type = .Candidate := hty
      rw [hd] at hct hty
      show maxIndex d.log = mi ∧ maxTerm d.log = mt
      rw [hd]
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- timeout: fresh RequestVotes report the fresh log; stale ones
    -- contradict term sanity
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
      t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨hlog, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    rcases hps p' hp' with hold | hnew
    · -- old packet
      by_cases heq : h0 = h
      · subst heq
        rw [update_same] at hct hty ⊢
        replace hct : d.currentTerm = t := hct
        replace hty : d.type = .Candidate := hty
        rcases hcases with ⟨hc, hcty, -, -⟩ | ⟨hc, -, -, -, -⟩
        · -- state unchanged
          show maxIndex d.log = mi ∧ maxTerm d.log = mt
          rw [hlog]
          rw [hc] at hct
          rw [hcty] at hty
          exact hP t h0 p' n mi mt hct hty hold hbody hsrc
        · -- fresh candidacy: an OLD RequestVote at the NEW term is
          -- impossible — its term was bounded by the old current term
          exfalso
          have hts := requestVote_term_sanity_invariant net hreach t n mi mt
            p' hold hbody
          rw [hsrc] at hts
          rw [← hct] at hts
          rw [hc] at hts
          exact Nat.not_succ_le_self _ hts
      · rw [update_neq _ _ heq] at hct hty ⊢
        exact hP t h0 p' n mi mt hct hty hold hbody hsrc
    · -- fresh RequestVote from the new candidate
      rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
      have hqm := handleTimeout_messages h (net.nwState h).2 hto q hq
      replace hsrc : h = h0 := hsrc
      subst hsrc
      rw [update_same] at hct hty ⊢
      rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
        at hbody
      injection hbody with h1 h2 h3 h4
      exact ⟨h3, h4⟩
  · -- append_entries: a candidate must have rejected — state untouched
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody0 hP
      _hreach hpkts hst hps t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨-, -, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es
        ci hae
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl, hm]
          at hbody
        exact nomatch hbody
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at hct hty ⊢
      replace hct : d.currentTerm = t := hct
      replace hty : d.type = .Candidate := hty
      have hd : d = (net.nwState p.pDst).2 :=
        handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
          (by rw [hty]; exact fun heq => nomatch heq)
      rw [hd] at hct hty
      show maxIndex d.log = mi ∧ maxTerm d.log = mt
      rw [hd]
      exact hP t p.pDst p' n mi mt hct hty hp'' hbody hsrc
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- append_entries_reply: candidate ⇒ everything unchanged
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody0 hP _hreach
      hpkts hst hps t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨-, hcases, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es
        res haer
    have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
      p.pSrc t0 es res haer
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · rw [hl] at hnew
        exact nomatch hnew
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at hct hty ⊢
      replace hct : d.currentTerm = t := hct
      replace hty : d.type = .Candidate := hty
      rcases hcases with ⟨hc, -, hcty⟩ | ⟨-, -, hcty⟩
      · rw [hc] at hct
        rw [hcty] at hty
        show maxIndex d.log = mi ∧ maxTerm d.log = mt
        rw [hlog]
        exact hP t p.pDst p' n mi mt hct hty hp'' hbody hsrc
      · rw [hcty] at hty
        exact nomatch hty
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- request_vote: candidate ⇒ type/term unchanged; log untouched
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody0 hP
      _hreach hpkts hst hps t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨-, -, hcases, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt
        hrv
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t0 p.pSrc
      lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hpkts ▸ mem_of_mem_remove_middle hold
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ : RefinedPacket).pBody = m from rfl, hm]
          at hbody
        exact nomatch hbody
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at hct hty ⊢
      replace hct : d.currentTerm = t := hct
      replace hty : d.type = .Candidate := hty
      rcases hcases with ⟨hc, hcty⟩ | hcty
      · rw [hc] at hct
        rw [hcty] at hty
        show maxIndex d.log = mi ∧ maxTerm d.log = mt
        rw [hlog]
        exact hP t p.pDst p' n mi mt hct hty hp'' hbody hsrc
      · rw [hcty] at hty
        exact nomatch hty
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- request_vote_reply: candidate ⇒ was candidate at same term
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody0 hP _hreach hpkts hst
      hps t h0 p' n mi mt hct hty hp' hbody hsrc
    subst hrvr
    obtain ⟨-, -, hcand, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v rfl
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
      p.pSrc t0 v
    have hp'' : p' ∈ net.nwPackets :=
      hpkts ▸ mem_of_mem_remove_middle (hps p' hp')
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at hct hty ⊢
      replace hct :
        (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0
          v).currentTerm = t := hct
      replace hty :
        (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0
          v).type = .Candidate := hty
      obtain ⟨hcty, hc⟩ := hcand hty
      rw [hc] at hct
      show maxIndex (handleRequestVoteReply p.pDst (net.nwState p.pDst).2
        p.pSrc t0 v).log = mi ∧ maxTerm (handleRequestVoteReply p.pDst
        (net.nwState p.pDst).2 p.pSrc t0 v).log = mt
      rw [hlog]
      exact hP t p.pDst p' n mi mt hct hcty hp'' hbody hsrc
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- do_leader: only AppendEntries sent; state facts unchanged
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
      t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨hc, -, hcty, -, hlog, hmsgs⟩ := doLeader_spec d h hdl
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', lid, pli, plt, es, ci, hqm⟩ := hmsgs q hq
        rw [show (⟨h, q.1, q.2⟩ : RefinedPacket).pBody = q.2 from rfl, hqm]
          at hbody
        exact nomatch hbody
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = h
    · subst heq
      rw [update_same] at hct hty ⊢
      replace hct : d'.currentTerm = t := hct
      replace hty : d'.type = .Candidate := hty
      rw [hc] at hct
      rw [hcty] at hty
      have hP' := hP t h0 p' n mi mt (by rw [hstate]; exact hct)
        (by rw [hstate]; exact hty) hp'' hbody hsrc
      rw [hstate] at hP'
      show maxIndex d'.log = mi ∧ maxTerm d'.log = mt
      rw [hlog]
      exact hP'
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- do_generic_server: nothing sent; state facts unchanged
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
      t h0 p' n mi mt hct hty hp' hbody hsrc
    obtain ⟨hlog, hcty, hc, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hp'' : p' ∈ net.nwPackets := by
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hms] at hnew
        exact nomatch hnew
    replace hct : (st' h0).2.currentTerm = t := hct
    replace hty : (st' h0).2.type = .Candidate := hty
    show maxIndex (st' h0).2.log = mi ∧ maxTerm (st' h0).2.log = mt
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = h
    · subst heq
      rw [update_same] at hct hty ⊢
      replace hct : d'.currentTerm = t := hct
      replace hty : d'.type = .Candidate := hty
      rw [hc] at hct
      rw [hcty] at hty
      have hP' := hP t h0 p' n mi mt (by rw [hstate]; exact hct)
        (by rw [hstate]; exact hty) hp'' hbody hsrc
      rw [hstate] at hP'
      show maxIndex d'.log = mi ∧ maxTerm d'.log = mt
      rw [hlog]
      exact hP'
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach t h0 p' n mi mt hct hty hp' hbody
      hsrc
    rw [← hstates h0] at hct hty ⊢
    exact hP t h0 p' n mi mt hct hty (hpkts p' hp') hbody hsrc
  · -- reboot: a rebooted node is a follower, not a candidate
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
      t h0 p' n mi mt hct hty hp' hbody hsrc
    have hp'' : p' ∈ net.nwPackets := by
      rw [hpkts]
      exact hp'
    rw [hst h0] at hct hty ⊢
    by_cases heq : h0 = h
    · subst heq
      rw [update_same] at hty
      subst hrb
      exact nomatch hty
    · rw [update_neq _ _ heq] at hct hty ⊢
      exact hP t h0 p' n mi mt hct hty hp'' hbody hsrc

/-! ## candidate_term_gt_log (BASE layer) -/

/-- `CandidateTermGtLogInterface.v:8-11` (`candidate_term_gt_log`):
a candidate's term is strictly above every entry in its log. -/
def candidate_term_gt_log (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).type = .Candidate →
    ∀ e ∈ (net.nwState h).log, (net.nwState h).currentTerm > e.eTerm

/-- `CandidateTermGtLogProof.v:113-131` (`candidate_term_gt_log_invariant`)
— BASE-layer, third real instantiation of the base principle; the
timeout case rides `no_entries_past_current_term_invariant` exactly as
upstream's `tsi`. -/
theorem candidate_term_gt_log_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      candidate_term_gt_log net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: everyone a follower
    intro h hty
    exact nomatch hty
  · -- client_request: a candidate's request is refused — state untouched
    intro h net st' ps' out d l client id c hcr hP _hreach hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      obtain ⟨htyd, -, -, -, -⟩ :=
        handleClientRequest_spec h (net.nwState h) client id c hcr
      have hd : d = net.nwState h :=
        handleClientRequest_not_leader h (net.nwState h) client id c hcr
          (by rw [← htyd, hty]; exact fun heq => nomatch heq)
      rw [hd]
      rw [hd] at hty
      exact hP h hty
    · exact hP h0
  · -- timeout: a fresh candidacy's term is above the whole (bounded) log
    intro net h st' ps' out d l hto hP hreach hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty e he
      obtain ⟨hlog, hcases, -⟩ := handleTimeout_spec h (net.nwState h) hto
      rw [hlog] at he
      rcases hcases with ⟨hc, hcty, -, -⟩ | ⟨hc, -, -, -, -⟩
      · rw [hc]
        rw [hcty] at hty
        exact hP h hty e he
      · rw [hc]
        obtain ⟨hhost, -⟩ := no_entries_past_current_term_invariant net hreach
        exact Nat.lt_succ_of_le (hhost h e he)
    · exact hP h0
  · -- append_entries: a candidate must have rejected
    intro xs p ys net st' ps' d m t0 n0 pli plt es ci hae _hbody hP _hreach
      _hpkts hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty
      have hd : d = net.nwState p.pDst :=
        handleAppendEntries_reject_of_not_follower p.pDst (net.nwState p.pDst)
          t0 n0 pli plt es ci hae (by rw [hty]; exact fun heq => nomatch heq)
      rw [hd]
      rw [hd] at hty
      exact hP p.pDst hty
    · exact hP h0
  · -- append_entries_reply: candidate ⇒ term/type/log unchanged
    intro xs p ys net st' ps' d m t0 es res haer _hbody hP _hreach _hpkts hst
      _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty e he
      obtain ⟨-, hcases, -⟩ :=
        handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst) p.pSrc t0 es
          res haer
      have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst)
        p.pSrc t0 es res haer
      rw [hlog] at he
      rcases hcases with ⟨hc, -, hcty⟩ | ⟨-, -, hcty⟩
      · rw [hc]
        rw [hcty] at hty
        exact hP p.pDst hty e he
      · rw [hcty] at hty
        exact nomatch hty
    · exact hP h0
  · -- request_vote: candidate ⇒ term/type unchanged; log untouched
    intro xs p ys net st' ps' d m t0 cid lli llt hrv _hbody hP _hreach _hpkts
      hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty e he
      obtain ⟨-, -, hcases, -⟩ :=
        handleRequestVote_spec p.pDst (net.nwState p.pDst) t0 p.pSrc lli llt
          hrv
      have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst) t0 p.pSrc
        lli llt hrv
      rw [hlog] at he
      rcases hcases with ⟨hc, hcty⟩ | hcty
      · rw [hc]
        rw [hcty] at hty
        exact hP p.pDst hty e he
      · rw [hcty] at hty
        exact nomatch hty
    · exact hP h0
  · -- request_vote_reply: candidate ⇒ was candidate at the same term
    intro xs p ys net st' ps' d t0 v hrvr _hbody hP _hreach _hpkts hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty e he
      subst hrvr
      obtain ⟨-, -, hcand, -⟩ :=
        handleRequestVoteReply_spec p.pDst (net.nwState p.pDst) p.pSrc t0 v rfl
      have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst)
        p.pSrc t0 v
      rw [hlog] at he
      obtain ⟨hcty, hc⟩ := hcand hty
      rw [hc]
      exact hP p.pDst hcty e he
    · exact hP h0
  · -- do_leader: term/type/log unchanged
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty e he
      obtain ⟨hc, -, hcty, -, hlog, -⟩ := doLeader_spec d h hdl
      rw [hlog] at he
      rw [hc]
      rw [hcty] at hty
      have := hP h
      rw [hstate] at this
      exact this hty e he
    · exact hP h0
  · -- do_generic_server: term/type/log unchanged
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst _hps h0
    show (st' h0).type = .Candidate →
      ∀ e ∈ (st' h0).log, (st' h0).currentTerm > e.eTerm
    rw [hst h0]
    unfold update
    split
    · intro hty e he
      obtain ⟨hlog, hcty, hc, -, -, -⟩ := doGenericServer_spec h d hgs
      rw [hlog] at he
      rw [hc]
      rw [hcty] at hty
      have := hP h
      rw [hstate] at this
      exact this hty e he
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
      exact nomatch hty
    · exact hP h0

/-! ## The leaderLogs_term_sanity trio -/

/-- `LeaderLogsTermSanityInterface.v:9-13` (`leaderLogs_term_sanity`):
every entry of a recorded leaderLog is strictly below its term. -/
def leaderLogs_term_sanity (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P)))
    (e : entry (P := P)),
    (t, ll) ∈ (net.nwState h).1.leaderLogs → e ∈ ll → e.eTerm < t

/-- `LeaderLogsTermSanityInterface.v:15-18`
(`leaderLogs_currentTerm_sanity`). -/
def leaderLogs_currentTerm_sanity (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P))),
    (t, ll) ∈ (net.nwState h).1.leaderLogs →
    t ≤ (net.nwState h).2.currentTerm

/-- `LeaderLogsTermSanityInterface.v:20-24`
(`leaderLogs_currentTerm_sanity_candidate`). -/
def leaderLogs_currentTerm_sanity_candidate (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P))),
    (t, ll) ∈ (net.nwState h).1.leaderLogs →
    (net.nwState h).2.type = .Candidate →
    t < (net.nwState h).2.currentTerm

/-- `LeaderLogsTermSanityProof.v:32-41` (`leaderLogs_term_sanity_unchanged`). -/
theorem leaderLogs_term_sanity_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : leaderLogs_term_sanity net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs) :
    leaderLogs_term_sanity net' := by
  intro h t ll e hin he
  rw [hst h] at hin
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hin
    replace hin : (t, ll) ∈ gd.leaderLogs := hin
    rw [hgd] at hin
    exact hP _ t ll e hin he
  · rw [update_neq _ _ heq] at hin
    exact hP h t ll e hin he

/-- `LeaderLogsTermSanityProof.v:50-62`
(`leaderLogs_term_sanity_request_vote_reply`) folded into
`LeaderLogsTermSanityProof.v:73-91` (`leaderLogs_term_sanity_invariant`):
the only step that grows leaderLogs snapshots a CANDIDATE's log, and a
candidate's term is above its whole log — the lifted base
`candidate_term_gt_log`, the first real `lift_prop` consumer. -/
theorem leaderLogs_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_term_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h t ll e hin _he
    exact nomatch hin
  · -- client_request
    intro h net st' ps' gd out d l client id c _hcr hgd hP _hreach hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2
  · -- timeout
    intro net h st' ps' gd out d l _hto hgd hP _hreach hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_timeout_ghost h (net.nwState h)).1
  · -- append_entries
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci _hae hgd _hbody hP
      _hreach _hpkts hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t0 n0 pli plt es ci).2.2.2
  · -- append_entries_reply (ghost unchanged)
    intro xs p ys net st' ps' gd d m t0 es res _haer hgd _hbody hP _hreach
      _hpkts hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    subst hgd
    rfl
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt _hrv hgd _hbody hP
      _hreach _hpkts hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t0 p.pSrc
      lli llt (net.nwState p.pDst)).2.1
  · -- request_vote_reply: THE case — the win snapshot
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP hreach _hpkts hst
      _hps
    intro h t ll e hin he
    replace hin : (t, ll) ∈ (st' h).1.leaderLogs := hin
    rw [hst h] at hin
    by_cases heq : h = p.pDst
    · subst heq
      rw [update_same] at hin
      replace hin : (t, ll) ∈ gd.leaderLogs := hin
      subst hgd
      rcases leaderLogs_update_elections_data_RVR hin
        with hold | ⟨hty', hcand, rfl, rfl⟩
      · exact hP _ t ll e hold he
      · -- new snapshot: candidate's log, term unchanged, entries below
        subst hrvr
        obtain ⟨-, -, -, hleader⟩ :=
          handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0
            v rfl
        rcases hleader hty' with heqd | ⟨hcandty, -, hc⟩
        · -- "unchanged" leader contradicts the candidate premise
          exfalso
          rw [← heqd] at hcand
          rw [hty'] at hcand
          exact nomatch hcand
        · have hlog := handleRequestVoteReply_log p.pDst
            (net.nwState p.pDst).2 p.pSrc t0 v
          rw [hlog] at he
          have hctg := lift_prop _ candidate_term_gt_log_invariant net hreach
          have := hctg p.pDst (by rw [deghost_spec]; exact hcandty) e
            (by rw [deghost_spec]; exact he)
          rw [deghost_spec] at this
          rw [hc]
          exact this
    · rw [update_neq _ _ heq] at hin
      exact hP h t ll e hin he
  · -- do_leader (ghost rides along)
    intro net st' ps' gd d h os d' ms _hdl hP _hreach hstate hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    rw [hstate]
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h _hgs hP _hreach hstate hst _hps
    refine leaderLogs_term_sanity_of_update hP hst ?_
    rw [hstate]
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h t ll e hin he
    rw [← hstates h] at hin
    exact hP h t ll e hin he
  · -- reboot (ghost survives)
    intro net net' gd d h d' _hrb hP _hreach hstate hst _hpkts
    refine leaderLogs_term_sanity_of_update hP hst ?_
    rw [hstate]

/-- `LeaderLogsTermSanityProof.v:100-112`
(`leaderLogs_currentTerm_sanity_unchanged`). -/
theorem leaderLogs_currentTerm_sanity_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : leaderLogs_currentTerm_sanity net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs)
    (hle : (net.nwState u).2.currentTerm ≤ d.currentTerm) :
    leaderLogs_currentTerm_sanity net' := by
  intro h t ll hin
  rw [hst h] at hin
  rw [hst h]
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hin ⊢
    replace hin : (t, ll) ∈ gd.leaderLogs := hin
    rw [hgd] at hin
    exact Nat.le_trans (hP _ t ll hin) hle
  · rw [update_neq _ _ heq] at hin ⊢
    exact hP h t ll hin

/-- `LeaderLogsTermSanityProof.v:215-233`
(`leaderLogs_currentTerm_sanity_invariant`). -/
theorem leaderLogs_currentTerm_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_currentTerm_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h t ll hin
    exact nomatch hin
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    obtain ⟨-, hc, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ (hc ▸ Nat.le_refl _)
    subst hgd
    exact (update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps
    obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_timeout_ghost h (net.nwState h)).1
    · rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · rw [hc]
        exact Nat.le_succ _
  · -- append_entries
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps
    obtain ⟨-, hcases, -, -⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es
        ci hae
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t0 n0 pli plt es ci).2.2.2
    · rcases hcases with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, hcases, -⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es
        res haer
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ ?_
    · subst hgd
      rfl
    · rcases hcases with ⟨hc, -, -⟩ | ⟨hc, -, -⟩
      · exact hc ▸ Nat.le_refl _
      · exact Nat.le_of_lt hc
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt
        hrv
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ hle
    subst hgd
    exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t0 p.pSrc
      lli llt (net.nwState p.pDst)).2.1
  · -- request_vote_reply: old bound grows; the fresh snapshot is at the
    -- winner's own term
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
    intro h t ll hin
    replace hin : (t, ll) ∈ (st' h).1.leaderLogs := hin
    show t ≤ (st' h).2.currentTerm
    rw [hst h] at hin
    rw [hst h]
    by_cases heq : h = p.pDst
    · subst heq
      rw [update_same] at hin ⊢
      replace hin : (t, ll) ∈ gd.leaderLogs := hin
      subst hgd
      rcases leaderLogs_update_elections_data_RVR hin
        with hold | ⟨-, -, rfl, -⟩
      · exact Nat.le_trans (hP _ t ll hold) hle
      · exact Nat.le_refl _
    · rw [update_neq _ _ heq] at hin ⊢
      exact hP h t ll hin
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hc, -, -, -, -, -⟩ := doLeader_spec d h hdl
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ ?_
    · rw [hstate]
    · rw [hstate, hc]
      exact Nat.le_refl _
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨-, -, hc, -, -, -⟩ := doGenericServer_spec h d hgs
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ ?_
    · rw [hstate]
    · rw [hstate, hc]
      exact Nat.le_refl _
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h t ll hin
    rw [← hstates h] at hin
    rw [← hstates h]
    exact hP h t ll hin
  · -- reboot (term survives)
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    subst hrb
    refine leaderLogs_currentTerm_sanity_of_update hP hst ?_ ?_
    · rw [hstate]
    · rw [hstate]
      exact Nat.le_refl _

/-- `LeaderLogsTermSanityProof.v:243-255`
(`leaderLogs_currentTerm_sanity_candidate_unchanged`). -/
theorem leaderLogs_currentTerm_sanity_candidate_of_update
    {net net' : RefinedNet} {u : name (P := P)} {gd : electionsData (P := P)}
    {d : raft_data (P := P)}
    (hP : leaderLogs_currentTerm_sanity_candidate net)
    (hcts : leaderLogs_currentTerm_sanity net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs)
    (hty : d.type = .Candidate →
      ((net.nwState u).2.type = .Candidate ∧
       d.currentTerm = (net.nwState u).2.currentTerm) ∨
      (net.nwState u).2.currentTerm < d.currentTerm) :
    leaderLogs_currentTerm_sanity_candidate net' := by
  intro h t ll hin htyp
  rw [hst h] at hin htyp
  rw [hst h]
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hin htyp ⊢
    replace hin : (t, ll) ∈ gd.leaderLogs := hin
    replace htyp : d.type = .Candidate := htyp
    rw [hgd] at hin
    rcases hty htyp with ⟨htyo, hc⟩ | hlt
    · show t < d.currentTerm
      rw [hc]
      exact hP _ t ll hin htyo
    · exact Nat.lt_of_le_of_lt (hcts _ t ll hin) hlt
  · rw [update_neq _ _ heq] at hin htyp ⊢
    exact hP h t ll hin htyp

/-- `LeaderLogsTermSanityProof.v:355-372`
(`leaderLogs_currentTerm_sanity_candidate_invariant`). -/
theorem leaderLogs_currentTerm_sanity_candidate_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_currentTerm_sanity_candidate net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h t ll hin _hty
    exact nomatch hin
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst _hps
    obtain ⟨htyd, hc, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · subst hgd
      exact (update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.2
    · intro htyp
      exact Or.inl ⟨htyd ▸ htyp, hc⟩
  · -- timeout: a fresh candidacy strictly grows the term
    intro net h st' ps' gd out d l hto hgd hP hreach hst _hps
    obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · subst hgd
      exact (update_elections_data_timeout_ghost h (net.nwState h)).1
    · intro htyp
      rcases hcases with ⟨hc, hcty, -, -⟩ | ⟨hc, -, -, -, -⟩
      · exact Or.inl ⟨hcty ▸ htyp, hc⟩
      · right
        rw [hc]
        exact Nat.lt_succ_self _
  · -- append_entries: candidate ⇒ rejected, state untouched
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      hreach _hpkts hst _hps
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · subst hgd
      exact (update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t0 n0 pli plt es ci).2.2.2
    · intro htyp
      have hd : d = (net.nwState p.pDst).2 :=
        handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
          (by rw [htyp]; exact fun heq => nomatch heq)
      rw [hd] at htyp
      left
      refine ⟨htyp, ?_⟩
      rw [hd]
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP hreach
      _hpkts hst _hps
    obtain ⟨-, hcases, -⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es
        res haer
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · subst hgd
      rfl
    · intro htyp
      rcases hcases with ⟨hc, -, hcty⟩ | ⟨-, -, hcty⟩
      · rw [hcty] at htyp
        exact Or.inl ⟨htyp, hc⟩
      · rw [hcty] at htyp
        exact nomatch htyp
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP hreach
      _hpkts hst _hps
    obtain ⟨-, -, hcases, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt
        hrv
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · subst hgd
      exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t0
        p.pSrc lli llt (net.nwState p.pDst)).2.1
    · intro htyp
      rcases hcases with ⟨hc, hcty⟩ | hcty
      · rw [hcty] at htyp
        exact Or.inl ⟨htyp, hc⟩
      · rw [hcty] at htyp
        exact nomatch htyp
  · -- request_vote_reply: a candidate did NOT just win — old entries only
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP _hreach _hpkts hst
      _hps
    subst hrvr
    obtain ⟨-, -, hcand, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v rfl
    intro h t ll hin htyp
    replace hin : (t, ll) ∈ (st' h).1.leaderLogs := hin
    replace htyp : (st' h).2.type = .Candidate := htyp
    show t < (st' h).2.currentTerm
    rw [hst h] at hin htyp
    rw [hst h]
    by_cases heq : h = p.pDst
    · subst heq
      rw [update_same] at hin htyp ⊢
      replace hin : (t, ll) ∈ gd.leaderLogs := hin
      replace htyp : (handleRequestVoteReply p.pDst (net.nwState p.pDst).2
        p.pSrc t0 v).type = .Candidate := htyp
      subst hgd
      obtain ⟨htyo, hc⟩ := hcand htyp
      rcases leaderLogs_update_elections_data_RVR hin
        with hold | ⟨hty', -, -, -⟩
      · show t < (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc
          t0 v).currentTerm
        rw [hc]
        exact hP _ t ll hold htyo
      · rw [hty'] at htyp
        exact nomatch htyp
    · rw [update_neq _ _ heq] at hin htyp ⊢
      exact hP h t ll hin htyp
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst _hps
    obtain ⟨hc, -, hcty, -, -, -⟩ := doLeader_spec d h hdl
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · rw [hstate]
    · intro htyp
      rw [hcty] at htyp
      left
      rw [hstate]
      exact ⟨htyp, hc⟩
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP hreach hstate hst _hps
    obtain ⟨-, hcty, hc, -, -, -⟩ := doGenericServer_spec h d hgs
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · rw [hstate]
    · intro htyp
      rw [hcty] at htyp
      left
      rw [hstate]
      exact ⟨htyp, hc⟩
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h t ll hin htyp
    rw [← hstates h] at hin htyp
    rw [← hstates h]
    exact hP h t ll hin htyp
  · -- reboot: a rebooted node is a follower
    intro net net' gd d h d' hrb hP hreach hstate hst _hpkts
    subst hrb
    refine leaderLogs_currentTerm_sanity_candidate_of_update hP
      (leaderLogs_currentTerm_sanity_invariant net hreach) hst ?_ ?_
    · rw [hstate]
    · intro htyp
      exact nomatch htyp

end LeaderLogsRing

end Raft
end VerdiCompat
