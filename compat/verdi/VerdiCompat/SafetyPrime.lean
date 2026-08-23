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

end SafetyPrime
end Raft
end VerdiCompat
