import VerdiCompat.GhostLogs

/-!
# The W-D refined/base files toward the state-machine-safety cap

Campaign Arc 3 unit 14 (closure in the arc log's unit-14 opening
entry), 1:1 against the sources @ a3375e8:

- `NoAppendEntriesRepliesToSelfProof.v` (155L, BASE) — no in-flight
  AppendEntriesReply is addressed to its own sender (the AE case rides
  unit 12's `no_append_entries_to_self` on the consumed request);
- `NoAppendEntriesToLeaderProof.v` (111L, BASE via `lower_prop`) — no
  in-flight AppendEntries targets a leader at its own term (the
  sender's and receiver's leaderLogs at that term collide via
  `one_leaderLog_per_term_host`, then the packet is to-self);
- `MatchIndexLeaderProof.v` (146L, BASE) — a leader's own matchIndex
  slot is exactly its maxIndex;
- `PrevLogCandidateEntriesTermProof.v`'s consumer
  `PrevLogLeaderSublogProof.v` (378L, BASE) — a same-term leader
  resolves every in-flight positive prevLog position in its own log
  (the RVR fresh-win case dies on the lowered
  `candidateEntriesTerm` witness);
- `StateMachineSafetyPrimeProof.v` (518L, refined) — the ghost-layer
  statement of state-machine safety (host' ∧ nw'), from
  leader_completeness + the log-matching lattice.
-/

namespace VerdiCompat
namespace Raft

section SafetyPrime
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" =>
  Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" =>
  Packet (raft_base_params (P := P)) raft_multi_params

/-! ## no_append_entries_replies_to_self
(`Raft/NoAppendEntriesRepliesToSelfInterface.v`, BASE) -/

/-- `NoAppendEntriesRepliesToSelfInterface.v:8-13`. -/
def no_append_entries_replies_to_self (net : RaftNet) : Prop :=
  ∀ (p : RaftPacket) (t : term) (es : List (entry (P := P))) (r : Bool),
    p ∈ net.nwPackets → p.pBody = .AppendEntriesReply t es r →
    p.pDst = p.pSrc → False

/-- `NoAppendEntriesRepliesToSelfProof.v:140-155`
(`no_append_entries_replies_to_self_invariant`, BASE): only the
AppendEntries handler mints replies, and its reply inverts a request
that `no_append_entries_to_self` already bars from being to-self. -/
theorem no_append_entries_replies_to_self_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      no_append_entries_replies_to_self net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro p t es r hp _ _
    exact nomatch hp
  · -- client_request: no packets
    intro h net st' ps' out d l client id c hcr hP _hreach hst hps
    obtain ⟨-, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h) client id c hcr
    intro p0 t es r hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t es r hold hbody0 hdst0
    · rw [hl] at hnew
      simp [send_packets] at hnew
  · -- timeout: only RequestVotes
    intro net h st' ps' out d l hto hP _hreach hst hps
    obtain ⟨-, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h) hto
    intro p0 t es r hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t es r hold hbody0 hdst0
    · obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m1 hm1
      replace hbody0 : m1.2 = msg.AppendEntriesReply t es r := hbody0
      rw [hq2] at hbody0
      exact nomatch hbody0
  · -- append_entries: the reply inverts a request that is not to-self
    intro xs p ys net st' ps' d m t n0 pli plt es ci hae hbody hP hreach
      hpkts hst hps
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · refine hP p0 t0 es0 r0 ?_ hbody0 hdst0
      rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · rw [hnew] at hdst0
      replace hdst0 : p.pSrc = p.pDst := hdst0
      exact no_append_entries_to_self_invariant net hreach p t n0 pli plt
        es ci hp_in hbody hdst0.symm
  · -- append_entries_reply: no messages
    intro xs p ys net st' ps' d m t es res haer _hbody hP _hreach hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst) p.pSrc t es res haer
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · refine hP p0 t0 es0 r0 ?_ hbody0 hdst0
      rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · rw [hl] at hnew
      simp [send_packets] at hnew
  · -- request_vote: the reply is a RequestVoteReply
    intro xs p ys net st' ps' d m t cid lli llt hrv _hbody hP _hreach hpkts
      hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst) t p.pSrc lli llt hrv
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · refine hP p0 t0 es0 r0 ?_ hbody0 hdst0
      rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · rw [hnew] at hbody0
      replace hbody0 : m = msg.AppendEntriesReply t0 es0 r0 := hbody0
      rw [hmshape] at hbody0
      exact nomatch hbody0
  · -- request_vote_reply: no sends
    intro xs p ys net st' ps' d t v hrvr _hbody hP _hreach hpkts hst hps
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    refine hP p0 t0 es0 r0 ?_ hbody0 hdst0
    rw [hpkts]
    exact mem_of_mem_remove_middle (hps p0 hp0)
  · -- do_leader: only AppendEntries requests
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨-, -, -, -, -, hmsgs⟩ := doLeader_spec d h hdl
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t0 es0 r0 hold hbody0 hdst0
    · obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t3, l3, p3, p4, e3, c3, hq2⟩ := hmsgs m1 hm1
      replace hbody0 : m1.2 = msg.AppendEntriesReply t0 es0 r0 := hbody0
      rw [hq2] at hbody0
      exact nomatch hbody0
  · -- do_generic_server: no messages
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t0 es0 r0 hold hbody0 hdst0
    · rw [hms] at hnew
      simp [send_packets] at hnew
  · -- state_same_packet_subset
    intro net net' _hstates hpk hP _hreach
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    exact hP p0 t0 es0 r0 (hpk p0 hp0) hbody0 hdst0
  · -- reboot: packets unchanged
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    intro p0 t0 es0 r0 hp0 hbody0 hdst0
    rw [← hpkts] at hp0
    exact hP p0 t0 es0 r0 hp0 hbody0 hdst0

/-! ## no_append_entries_to_leader
(`Raft/NoAppendEntriesToLeaderInterface.v`, BASE via `lower_prop`) -/

/-- `NoAppendEntriesToSelfProof.v` lifted to the refined layer
(upstream's `no_append_entries_to_self'_invariant`,
`NoAppendEntriesToLeaderProof.v:29-64`). -/
theorem no_append_entries_to_self_refined :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (p : RefinedPacket) (t : term) (n : name (P := P))
        (pli : logIndex) (plt : term) (es : List (entry (P := P)))
        (ci : logIndex),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
        p.pDst = p.pSrc → False := by
  intro net hreach p t n pli plt es ci hp hbody hdst
  exact lift_prop _ no_append_entries_to_self_invariant net hreach
    (deghost_packet p) t n pli plt es ci (List.mem_map_of_mem hp) hbody
    hdst

/-- `NoAppendEntriesToLeaderProof.v:66-80`
(`no_append_entries_to_leader_invariant'`): the refined argument — the
receiving leader's snapshot (`leaders_have_leaderLogs`) and the
sender's (`append_entries_came_from_leaders`) collide at the packet's
term (`one_leaderLog_per_term_host`), making the packet to-self. -/
theorem no_append_entries_to_leader_refined :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (p : RefinedPacket) (t : term) (n : name (P := P))
        (pli : logIndex) (plt : term) (es : List (entry (P := P)))
        (ci : logIndex),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
        (net.nwState p.pDst).2.type = .Leader →
        (net.nwState p.pDst).2.currentTerm = t →
        False := by
  intro net hreach p t n pli plt es ci hp hbody hty hct
  obtain ⟨ll, hll⟩ := leaders_have_leaderLogs_invariant net hreach p.pDst
    hty
  rw [hct] at hll
  obtain ⟨ll', hll'⟩ := append_entries_came_from_leaders_invariant net
    hreach p t n pli plt es ci hp hbody
  have hdst : p.pDst = p.pSrc :=
    one_leaderLog_per_term_host_invariant net hreach p.pDst p.pSrc t ll
      ll' hll hll'
  exact no_append_entries_to_self_refined net hreach p t n pli plt es ci
    hp hbody hdst

/-- `NoAppendEntriesToLeaderInterface.v:8-15`
(`no_append_entries_to_leader`), delivered at BASE level via
`lower_prop` (upstream's instance body). -/
theorem no_append_entries_to_leader_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      ∀ (p : RaftPacket) (t : term) (n : name (P := P)) (pli : logIndex)
        (plt : term) (es : List (entry (P := P))) (ci : logIndex),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
        (net.nwState p.pDst).type = .Leader →
        (net.nwState p.pDst).currentTerm = t →
        False := by
  refine lower_prop _ ?_
  intro rnet hR p t n pli plt es ci hp hbody hty hct
  replace hp : p ∈ rnet.nwPackets.map deghost_packet := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact no_append_entries_to_leader_refined rnet hR q t n pli plt es ci
    hq hbody hty hct

/-! ## match_index_leader (`Raft/MatchIndexLeaderInterface.v`, BASE) -/

/-- `MatchIndexLeaderInterface.v:8-13` (`match_index_leader`): a
leader's own matchIndex slot is exactly its maxIndex. -/
def match_index_leader (net : RaftNet) : Prop :=
  ∀ leader : name (P := P),
    (net.nwState leader).type = .Leader →
    assoc_default (net.nwState leader).matchIndex leader 0 =
      maxIndex (net.nwState leader).log

/-- The transport (upstream's per-case `matchIndex_preserved`
rewriting, factored as in slice 69). -/
theorem match_index_leader_of_update {net : RaftNet}
    {ps' : List (Packet (raft_base_params (P := P)) raft_multi_params)}
    {st' : name (P := P) → raft_data (P := P)} {u : name (P := P)}
    {d : raft_data (P := P)}
    (hP : match_index_leader net)
    (hst : ∀ h', st' h' = update net.nwState u d h')
    (hd : d.type = .Leader →
      (net.nwState u).type = .Leader ∧
      d.matchIndex = (net.nwState u).matchIndex ∧
      d.log = (net.nwState u).log) :
    match_index_leader (⟨ps', st'⟩ : RaftNet) := by
  intro leader hty
  replace hty : (st' leader).type = .Leader := hty
  show assoc_default (st' leader).matchIndex leader 0 =
    maxIndex (st' leader).log
  rw [hst leader]
  rw [hst leader] at hty
  by_cases heq : leader = u
  · rw [heq, update_same] at hty ⊢
    obtain ⟨hty0, hmi, hlog⟩ := hd hty
    rw [hmi, hlog]
    exact hP u hty0
  · rw [update_neq _ _ heq] at hty ⊢
    exact hP leader hty

/-- `MatchIndexLeaderProof.v:120-146` (`match_index_leader_invariant`,
BASE): the client-request and election cases re-establish the equality
outright; the append-entries-reply case rides
`no_append_entries_replies_to_self` — the reply's sender slot is never
the leader's own. -/
theorem match_index_leader_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      match_index_leader net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro leader hty
    exact nomatch hty
  · -- client_request: the fresh entry's index is recorded at the own slot
    intro h net st' ps' out d l client id c hcr hP _hreach hst _hps
    obtain ⟨htyd, -, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h) client id c hcr
    intro leader hty
    replace hty : (st' leader).type = .Leader := hty
    show assoc_default (st' leader).matchIndex leader 0 =
      maxIndex (st' leader).log
    rw [hst leader]
    rw [hst leader] at hty
    by_cases heq : leader = h
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      have hty0 : (net.nwState h).type = .Leader := by
        rw [← htyd]
        exact hty
      rcases handleClientRequest_matchIndex h (net.nwState h) client id c
        hcr with ⟨hmax, hmi⟩ | ⟨hmi, -⟩
      · rw [hmi, hmax]
        exact hP h hty0
      · rw [hmi, assoc_set_same_default]
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP leader hty
  · -- timeout
    intro net h st' ps' out d l hto hP _hreach hst _hps
    obtain ⟨hlog, hbr, -⟩ := handleTimeout_spec h (net.nwState h) hto
    refine match_index_leader_of_update hP hst ?_
    intro htyl
    rcases hbr with ⟨-, hty, -, -⟩ | ⟨-, hty, -, -, -⟩
    · rw [hty] at htyl
      exact ⟨htyl, handleTimeout_matchIndex h (net.nwState h) hto, hlog⟩
    · rw [hty] at htyl
      exact nomatch htyl
  · -- append_entries: a standing leader rejected
    intro xs p ys net st' ps' d m t n0 pli plt es ci hae _hbody hP _hreach
      _hpkts hst _hps
    refine match_index_leader_of_update hP hst ?_
    intro htyl
    have hd : d = net.nwState p.pDst :=
      handleAppendEntries_reject_of_not_follower p.pDst (net.nwState p.pDst)
        t n0 pli plt es ci hae (by rw [htyl]; exact fun heq => nomatch heq)
    rw [hd]
    exact ⟨by rw [← hd]; exact htyl, rfl, rfl⟩
  · -- append_entries_reply: the bumped slot is never the leader's own
    intro xs p ys net st' ps' d m t es res haer hbody hP hreach hpkts hst
      _hps
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    intro leader hty
    replace hty : (st' leader).type = .Leader := hty
    show assoc_default (st' leader).matchIndex leader 0 =
      maxIndex (st' leader).log
    rw [hst leader]
    rw [hst leader] at hty
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      obtain ⟨htyeq, hlogd, hcases⟩ := handleAppendEntriesReply_matchIndex
        p.pDst (net.nwState p.pDst) p.pSrc t es res haer hty
      have hty0 : (net.nwState p.pDst).type = .Leader := by
        rw [htyeq]
        exact hty
      rw [hlogd]
      rcases hcases with hsame | ⟨-, -, hset⟩
      · rw [hsame]
        exact hP p.pDst hty0
      · rw [hset]
        by_cases hsrc : p.pDst = p.pSrc
        · exact absurd hsrc (fun hss =>
            no_append_entries_replies_to_self_invariant net hreach p t es
              res hp_in hbody hss)
        · rw [assoc_set_diff_default _ _ _ _ _ hsrc]
          exact hP p.pDst hty0
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP leader hty
  · -- request_vote
    intro xs p ys net st' ps' d m t cid lli llt hrv _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, -, hbr, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst) t p.pSrc lli llt
        hrv
    refine match_index_leader_of_update hP hst ?_
    intro htyl
    rcases hbr with ⟨-, hty⟩ | hty
    · rw [hty] at htyl
      exact ⟨htyl,
        handleRequestVote_matchIndex p.pDst (net.nwState p.pDst) t p.pSrc
          lli llt hrv,
        handleRequestVote_log p.pDst (net.nwState p.pDst) t p.pSrc lli llt
          hrv⟩
    · have : serverType.Follower = .Leader := hty.symm.trans htyl
      exact nomatch this
  · -- request_vote_reply: a fresh win records its own maxIndex
    intro xs p ys net st' ps' d t v hrvr _hbody hP _hreach _hpkts hst _hps
    have hlogd : d.log = (net.nwState p.pDst).log := by
      rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst) p.pSrc
        t v
    intro leader hty
    replace hty : (st' leader).type = .Leader := hty
    show assoc_default (st' leader).matchIndex leader 0 =
      maxIndex (st' leader).log
    rw [hst leader]
    rw [hst leader] at hty
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      rcases handleRequestVoteReply_matchIndex p.pDst (net.nwState p.pDst)
        p.pSrc t v hrvr hty with ⟨hty0, hmi⟩ | hmi
      · rw [hmi, hlogd]
        exact hP p.pDst hty0
      · rw [hmi, hlogd, assoc_set_same_default]
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP leader hty
  · -- do_leader
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨-, -, hty, -, hlog, -⟩ := doLeader_spec d h hdl
    refine match_index_leader_of_update hP hst ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨by rw [hstate]; exact htyl, ?_, ?_⟩
    · rw [doLeader_matchIndex d h hdl, hstate]
    · rw [hlog, hstate]
  · -- do_generic_server
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨hlog, hty, -, -, -, -⟩ := doGenericServer_spec h d hgs
    refine match_index_leader_of_update hP hst ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨by rw [hstate]; exact htyl, ?_, ?_⟩
    · rw [doGenericServer_matchIndex h d hgs, hstate]
    · rw [hlog, hstate]
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach
    intro leader hty
    replace hty : (net'.nwState leader).type = .Leader := hty
    show assoc_default (net'.nwState leader).matchIndex leader 0 =
      maxIndex (net'.nwState leader).log
    rw [← hstates leader] at hty ⊢
    exact hP leader hty
  · -- reboot: a rebooted node is a follower
    intro net net' d h d' hrb hP _hreach hstate hst _hpkts
    refine match_index_leader_of_update hP hst ?_
    intro htyl
    rw [← hrb] at htyl
    exact nomatch htyl

/-! ## prevLog_leader_sublog (`Raft/PrevLogLeaderSublogInterface.v`,
BASE) — unit 13's `prevLog_candidateEntriesTerm` pays off: the RVR
fresh-win case dies on the lowered candidateEntriesTerm witness. -/

/-- `RefinementCommonTheorems.v`-style term twin of
`wonElection_candidateEntries_rvr` (LogMatching.lean): a node that
wins via a consumed grant at a `candidateEntriesTerm`-witnessed term
is not a candidate. Same proof with `t'` for `e.eTerm`. -/
theorem wonElection_candidateEntriesTerm_rvr {net : RefinedNet}
    (hvc : votes_correct net) (hcc : cronies_correct net)
    {t' : term} (hce : candidateEntriesTerm t' net.nwState)
    {q : RefinedPacket} (hq : q ∈ net.nwPackets)
    (hbody : q.pBody = .RequestVoteReply t' true)
    (hct : (net.nwState q.pDst).2.currentTerm = t')
    (hwon : wonElection
      (dedup (q.pSrc :: (net.nwState q.pDst).2.votesReceived)) = true) :
    (net.nwState q.pDst).2.type ≠ .Candidate := by
  obtain ⟨hovpt, -, -⟩ := hvc
  obtain ⟨hvrc, hcv, hvnw, -⟩ := hcc
  obtain ⟨x, hwx, himp⟩ := hce
  intro hcand
  have hvsrc : (t', q.pDst) ∈ (net.nwState q.pSrc).1.votes :=
    hvnw q t' hbody hq
  obtain ⟨c, hcx, hch⟩ := wonElection_one_in_common _ _ hwx hwon
  have hv1 : (t', x) ∈ (net.nwState c).1.votes := hcv t' x c hcx
  have hxd : x = q.pDst := by
    rcases List.mem_cons.mp hch with rfl | hch'
    · exact hovpt q.pSrc t' x q.pDst hv1 hvsrc
    · have hcc2 : c ∈ (net.nwState q.pDst).1.cronies
          (net.nwState q.pDst).2.currentTerm :=
        hvrc q.pDst c hch' (Or.inr hcand)
      rw [hct] at hcc2
      have hv2 : (t', q.pDst) ∈ (net.nwState c).1.votes :=
        hcv t' q.pDst c hcc2
      exact hovpt c t' x q.pDst hv1 hv2
  rw [hxd] at himp
  exact himp hct hcand

/-- `PrevLogLeaderSublogProof.v:167-230`
(`prevLog_candidateEntriesTerm_lowered`, with upstream's
`candidateEntriesTerm_lowered` wrapper def flattened into the
implication chain — the lane's `candidate_entries_lowered_rvr`
presentation): at BASE level, a node that wins via a consumed grant at
the prevLogTerm of some in-flight positive-prevLog AppendEntries is
not a candidate. -/
theorem prevLog_candidateEntriesTerm_lowered :
    ∀ net, raft_intermediate_reachable (P := P) net →
      ∀ (p p' : RaftPacket) (t : term) (lid : name (P := P))
        (pli : logIndex) (plt : term) (es : List (entry (P := P)))
        (ci : logIndex),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
        0 < plt →
        p' ∈ net.nwPackets → p'.pBody = .RequestVoteReply plt true →
        (net.nwState p'.pDst).currentTerm = plt →
        wonElection
          (dedup (p'.pSrc :: (net.nwState p'.pDst).votesReceived)) = true →
        (net.nwState p'.pDst).type ≠ .Candidate := by
  refine lower_prop _ ?_
  intro rnet hR p p' t lid pli plt es ci hp hbody hplt hp' hbody' hct hwon
  have hvc := votes_correct_invariant rnet hR
  have hcc := cronies_correct_invariant rnet hR
  replace hp : p ∈ rnet.nwPackets.map deghost_packet := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  replace hp' : p' ∈ rnet.nwPackets.map deghost_packet := hp'
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hp'
  exact wonElection_candidateEntriesTerm_rvr hvc hcc
    (prevLog_candidateEntriesTerm_invariant rnet hR q t lid pli plt es ci
      hq hbody hplt)
    hq' hbody' hct hwon

/-- `PrevLogLeaderSublogInterface.v:8-19` (`prevLog_leader_sublog`). -/
def prevLog_leader_sublog (net : RaftNet) : Prop :=
  ∀ (leader : name (P := P)) (p : RaftPacket) (t : term)
    (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex),
    (net.nwState leader).type = .Leader →
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    (net.nwState leader).currentTerm = plt →
    0 < pli → 0 < plt →
    ∃ ple : entry (P := P), ple.eIndex = pli ∧ ple.eTerm = plt ∧
      ple ∈ (net.nwState leader).log

/-- The transport: type demotions, same-term leaders, growing logs,
and no fresh AppendEntries. -/
theorem prevLog_leader_sublog_of_update {net : RaftNet}
    {ps' : List (Packet (raft_base_params (P := P)) raft_multi_params)}
    {st' : name (P := P) → raft_data (P := P)} {u : name (P := P)}
    {d : raft_data (P := P)}
    (hP : prevLog_leader_sublog net)
    (hst : ∀ h', st' h' = update net.nwState u d h')
    (hpk : ∀ p' : Packet (raft_base_params (P := P)) raft_multi_params,
      p' ∈ ps' →
      (∃ t lid pli plt es ci,
        p'.pBody = msg.AppendEntries (P := P) t lid pli plt es ci) →
      p' ∈ net.nwPackets)
    (hd : d.type = .Leader →
      (net.nwState u).type = .Leader ∧
      d.currentTerm = (net.nwState u).currentTerm ∧
      (∀ e ∈ (net.nwState u).log, e ∈ d.log)) :
    prevLog_leader_sublog (⟨ps', st'⟩ : RaftNet) := by
  intro leader p t lid pli plt es ci hty hp hbody hct hpli hplt
  replace hty : (st' leader).type = .Leader := hty
  replace hct : (st' leader).currentTerm = plt := hct
  replace hp : p ∈ ps' := hp
  have hpold : p ∈ net.nwPackets :=
    hpk p hp ⟨t, lid, pli, plt, es, ci, hbody⟩
  show ∃ ple : entry (P := P), ple.eIndex = pli ∧ ple.eTerm = plt ∧
    ple ∈ (st' leader).log
  rw [hst leader] at hty hct ⊢
  by_cases heq : leader = u
  · rw [heq, update_same] at hty hct ⊢
    obtain ⟨hty0, hctd, hsub⟩ := hd hty
    rw [hctd] at hct
    obtain ⟨ple, h1, h2, h3⟩ := hP u p t lid pli plt es ci hty0 hpold
      hbody hct hpli hplt
    exact ⟨ple, h1, h2, hsub ple h3⟩
  · rw [update_neq _ _ heq] at hty hct ⊢
    exact hP leader p t lid pli plt es ci hty hpold hbody hct hpli hplt

/-- `PrevLogLeaderSublogProof.v:340-360`
(`prevLog_leader_sublog_invariant`, BASE): a same-term leader resolves
every in-flight positive prevLog position in its own log. The RVR
fresh-win case is the `prevLog_candidateEntriesTerm` payoff; the
doLeader creation case reads the pivot off the sender's log and moves
it to the claiming leader via `leader_sublog` (host). -/
theorem prevLog_leader_sublog_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      prevLog_leader_sublog net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro leader p t lid pli plt es ci hty hp _ _ _ _
    exact nomatch hp
  · -- client_request: the leader's log grows; no packets
    intro h net st' ps' out d l client id c hcr hP _hreach hst hps
    obtain ⟨htyd, hctd, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h) client id c hcr
    refine prevLog_leader_sublog_of_update hP hst ?_ ?_
    · intro p' hp' _
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hl] at hnew
        simp [send_packets] at hnew
    · intro htyl
      refine ⟨by rw [← htyd]; exact htyl, hctd, ?_⟩
      intro e he
      rcases handleClientRequest_log_full h (net.nwState h) client id c
        hcr with ⟨-, hlog⟩ | ⟨-, heqd⟩
      · rw [hlog]
        exact List.mem_cons_of_mem _ he
      · rw [heqd]
        exact he
  · -- timeout
    intro net h st' ps' out d l hto hP _hreach hst hps
    obtain ⟨hlog, hbr, hmsgs⟩ := handleTimeout_spec h (net.nwState h) hto
    refine prevLog_leader_sublog_of_update hP hst ?_ ?_
    · intro p' hp' hAE
      rcases hps p' hp' with hold | hnew
      · exact hold
      · exfalso
        obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hnew
        obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m1 hm1
        obtain ⟨t0, lid, pli, plt, es, ci, hbody⟩ := hAE
        replace hbody : m1.2 = msg.AppendEntries t0 lid pli plt es ci :=
          hbody
        rw [hq2] at hbody
        exact nomatch hbody
    · intro htyl
      rcases hbr with ⟨hct, hty, -, -⟩ | ⟨-, hty, -, -, -⟩
      · rw [hty] at htyl
        exact ⟨htyl, hct, fun e he => by rw [hlog]; exact he⟩
      · rw [hty] at htyl
        exact nomatch htyl
  · -- append_entries: a standing leader rejected
    intro xs p ys net st' ps' d m t n0 pli plt es ci hae _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst) t n0 pli plt es
        ci hae
    refine prevLog_leader_sublog_of_update hP hst ?_ ?_
    · intro p' hp' hAE
      rcases hps p' hp' with hold | hnew
      · rw [hpkts]
        exact mem_of_mem_remove_middle hold
      · exfalso
        obtain ⟨t0, lid, pli2, plt2, es2, ci2, hbody⟩ := hAE
        rw [hnew] at hbody
        replace hbody : m = msg.AppendEntries t0 lid pli2 plt2 es2 ci2 :=
          hbody
        rw [hmshape] at hbody
        exact nomatch hbody
    · intro htyl
      have hd : d = net.nwState p.pDst :=
        handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst) t n0 pli plt es ci hae
          (by rw [htyl]; exact fun heq => nomatch heq)
      rw [hd]
      exact ⟨by rw [← hd]; exact htyl, rfl, fun e he => he⟩
  · -- append_entries_reply
    intro xs p ys net st' ps' d m t es res haer _hbody hP _hreach hpkts
      hst hps
    obtain ⟨-, hcases, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst) p.pSrc t es res haer
    have hlogd := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst)
      p.pSrc t es res haer
    refine prevLog_leader_sublog_of_update hP hst ?_ ?_
    · intro p' hp' _
      rcases hps p' hp' with hold | hnew
      · rw [hpkts]
        exact mem_of_mem_remove_middle hold
      · rw [hl] at hnew
        simp [send_packets] at hnew
    · intro htyl
      rcases hcases with ⟨hct, -, hty⟩ | ⟨-, -, hty⟩
      · rw [hty] at htyl
        exact ⟨htyl, hct, fun e he => by rw [hlogd]; exact he⟩
      · rw [hty] at htyl
        exact nomatch htyl
  · -- request_vote
    intro xs p ys net st' ps' d m t cid lli llt hrv _hbody hP _hreach
      hpkts hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst) t p.pSrc lli llt hrv
    obtain ⟨-, -, hbr, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst) t p.pSrc lli llt
        hrv
    have hlogd := handleRequestVote_log p.pDst (net.nwState p.pDst) t
      p.pSrc lli llt hrv
    refine prevLog_leader_sublog_of_update hP hst ?_ ?_
    · intro p' hp' hAE
      rcases hps p' hp' with hold | hnew
      · rw [hpkts]
        exact mem_of_mem_remove_middle hold
      · exfalso
        obtain ⟨t0, lid, pli2, plt2, es2, ci2, hbody⟩ := hAE
        rw [hnew] at hbody
        replace hbody : m = msg.AppendEntries t0 lid pli2 plt2 es2 ci2 :=
          hbody
        rw [hmshape] at hbody
        exact nomatch hbody
    · intro htyl
      rcases hbr with ⟨hct, hty⟩ | hty
      · rw [hty] at htyl
        exact ⟨htyl, hct, fun e he => by rw [hlogd]; exact he⟩
      · have : serverType.Follower = .Leader := hty.symm.trans htyl
        exact nomatch this
  · -- request_vote_reply: the fresh-win case dies on the lowered witness
    intro xs p ys net st' ps' d t v hrvr hbody hP hreach hpkts hst hps
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    intro leader p0 t0 lid pli plt es ci hty hp0 hbody0 hct hpli hplt
    replace hty : (st' leader).type = .Leader := hty
    replace hct : (st' leader).currentTerm = plt := hct
    replace hp0 : p0 ∈ ps' := hp0
    have hp0old : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    show ∃ ple : entry (P := P), ple.eIndex = pli ∧ ple.eTerm = plt ∧
      ple ∈ (st' leader).log
    rw [hst leader] at hty hct ⊢
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty hct ⊢
      rcases handleRequestVoteReply_RVR_spec p.pDst (net.nwState p.pDst)
        p.pSrc t v hrvr with hsame | ⟨htyF, -, -⟩ |
        ⟨hctd, hlogd, hwon | htyd⟩
      · rw [hsame] at hty hct ⊢
        exact hP p.pDst p0 t0 lid pli plt es ci hty hp0old hbody0 hct
          hpli hplt
      · rw [htyF] at hty
        exact nomatch hty
      · -- fresh win at plt: the candidateEntriesTerm witness forbids it
        obtain ⟨htyC, -, hv, hcteq, hwon'⟩ := hwon
        exfalso
        have ht_plt : t = plt := by
          rw [← hcteq, ← hctd]
          exact hct
        refine prevLog_candidateEntriesTerm_lowered net hreach p0 p t0
          lid pli plt es ci hp0old hbody0 hplt hp_in ?_ ?_ hwon' htyC
        · rw [hbody, hv, ht_plt]
        · rw [hcteq, ht_plt]
      · rw [htyd] at hty
        rw [hlogd]
        rw [hctd] at hct
        exact hP p.pDst p0 t0 lid pli plt es ci hty hp0old hbody0 hct
          hpli hplt
    · rw [update_neq _ _ heq] at hty hct ⊢
      exact hP leader p0 t0 lid pli plt es ci hty hp0old hbody0 hct hpli
        hplt
  · -- do_leader: the creation case — the pivot moves via leader_sublog
    intro net st' ps' d h os d' ms hdl hP hreach hstate hst hps
    obtain ⟨hctd, -, htyd, -, hlogd, -⟩ := doLeader_spec d h hdl
    intro leader p0 t0 lid pli plt es ci hty hp0 hbody0 hct hpli hplt
    replace hty : (st' leader).type = .Leader := hty
    replace hct : (st' leader).currentTerm = plt := hct
    replace hp0 : p0 ∈ ps' := hp0
    show ∃ ple : entry (P := P), ple.eIndex = pli ∧ ple.eTerm = plt ∧
      ple ∈ (st' leader).log
    rcases hps p0 hp0 with hold | hnew
    · -- old packet: transport (type/ct/log all preserved at h)
      rw [hst leader] at hty hct ⊢
      by_cases heq : leader = h
      · rw [heq, update_same] at hty hct ⊢
        rw [htyd] at hty
        rw [hctd] at hct
        have hty0 : (net.nwState h).type = .Leader := by
          rw [hstate]
          exact hty
        have hct0 : (net.nwState h).currentTerm = plt := by
          rw [hstate]
          exact hct
        obtain ⟨ple, h1, h2, h3⟩ := hP h p0 t0 lid pli plt es ci hty0
          hold hbody0 hct0 hpli hplt
        refine ⟨ple, h1, h2, ?_⟩
        rw [hlogd]
        show ple ∈ d.log
        rw [← hstate]
        exact h3
      · rw [update_neq _ _ heq] at hty hct ⊢
        exact hP leader p0 t0 lid pli plt es ci hty hold hbody0 hct hpli
          hplt
    · -- fresh replica: the findAtIndex pivot, moved by leader_sublog
      obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨pli3, ci3, hq2⟩ := doLeader_messages_full d h hdl m1 hm1
      replace hbody0 : m1.2 = msg.AppendEntries t0 lid pli plt es ci :=
        hbody0
      rw [hq2] at hbody0
      injection hbody0 with f1 f2 f3 f4 f5 f6
      cases hfind : findAtIndex d.log pli3 with
      | none =>
        simp only [hfind] at f4
        rw [← f4] at hplt
        exact absurd hplt (Nat.lt_irrefl 0)
      | some e =>
        simp only [hfind] at f4
        obtain ⟨hemem, hei⟩ := findAtIndex_elim hfind
        have he' : e ∈ (net.nwState h).log := by
          rw [hstate]
          exact hemem
        have hlsub := (leader_sublog_invariant_invariant net hreach).1
        rw [hst leader] at hty hct ⊢
        by_cases heq : leader = h
        · rw [heq, update_same] at hty hct ⊢
          refine ⟨e, by rw [hei]; exact f3, f4, ?_⟩
          rw [hlogd]
          exact hemem
        · rw [update_neq _ _ heq] at hty hct ⊢
          refine ⟨e, by rw [hei]; exact f3, f4, ?_⟩
          exact hlsub leader e h hty he' (by rw [hct, ← f4])
  · -- do_generic_server
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hlog, hty, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    refine prevLog_leader_sublog_of_update hP hst ?_ ?_
    · intro p' hp' _
      rcases hps p' hp' with hold | hnew
      · exact hold
      · rw [hms] at hnew
        simp [send_packets] at hnew
    · intro htyl
      rw [hty] at htyl
      refine ⟨by rw [hstate]; exact htyl, ?_, ?_⟩
      · rw [hct, hstate]
      · intro e he
        rw [hlog]
        rw [hstate] at he
        exact he
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    intro leader p0 t0 lid pli plt es ci hty hp0 hbody0 hct hpli hplt
    replace hty : (net'.nwState leader).type = .Leader := hty
    replace hct : (net'.nwState leader).currentTerm = plt := hct
    show ∃ ple : entry (P := P), ple.eIndex = pli ∧ ple.eTerm = plt ∧
      ple ∈ (net'.nwState leader).log
    rw [← hstates leader] at hty hct ⊢
    exact hP leader p0 t0 lid pli plt es ci hty (hpkts p0 hp0) hbody0 hct
      hpli hplt
  · -- reboot: a rebooted node is a follower
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    intro leader p0 t0 lid pli plt es ci hty hp0 hbody0 hct hpli hplt
    replace hty : (net'.nwState leader).type = .Leader := hty
    replace hct : (net'.nwState leader).currentTerm = plt := hct
    rw [← hpkts] at hp0
    show ∃ ple : entry (P := P), ple.eIndex = pli ∧ ple.eTerm = plt ∧
      ple ∈ (net'.nwState leader).log
    rw [hst leader] at hty hct ⊢
    by_cases heq : leader = h
    · rw [heq, update_same] at hty
      rw [← hrb] at hty
      exact nomatch hty
    · rw [update_neq _ _ heq] at hty hct ⊢
      exact hP leader p0 t0 lid pli plt es ci hty hp0 hbody0 hct hpli
        hplt

end SafetyPrime
end Raft
end VerdiCompat
