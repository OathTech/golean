import VerdiCompat.SafetyLeaves

/-!
# The W-C ghost chain: GhostLogCorrect + GhostLogsLogProperties

Campaign Arc 3 unit 13 (closure + primed-site decision in the arc
log's unit-13 opening entry), 1:1 against the sources @ a3375e8 — the
msg-ghost principle's FIRST REAL CONSUMERS:

- `GhostLogCorrectProof.v` (275L) — every in-flight AppendEntries'
  ghost log CONTEXTUALIZES its own payload: either a from-scratch send
  (`pli = 0`, entries = the whole ghost log) or the prevLog pivot sits
  in the ghost log and the entries are exactly its `findGtIndex` tail.
  Uses the UNPRIMED principle; the invariant is packet-only, so every
  non-creating handler transports trivially and `doLeader` is the one
  real case (`nextIndex_sanity` at the msg layer resolves the pivot).
- `GhostLogsLogPropertiesProof.v` (201L) — the higher-order snapshot
  principle for ghost logs: ANY reachability-closed log property holds
  of every in-flight ghost log. THE PRIMED PRINCIPLE'S FIRST CONSUMER
  (and its §3.3 discharge witness): a fresh packet's ghost is the
  POST-state's log, so the successor net's reachability premise is
  load-bearing — the pre-state route is structurally unavailable
  (decision logged, unit-13 opening).

Base/refined facts import through `msg_simulation_1`; `mgv_deghost`
leaves `nwState` untouched, so the lifted statements are definitional
over the msg net's own state.
-/

namespace VerdiCompat
namespace Raft

section GhostLogs
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "MsgNet" =>
  Network (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params
local notation "MsgPacket" =>
  Packet (raft_msg_refined_base_params (P := P)) raft_msg_refined_multi_params

/-- Elimination for membership in a ghost-attached send batch: the
packet is the sender's, its ghost is the writing state's log, its
message is one of the batch. -/
theorem mem_send_ghost_elim {src : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)}
    {l : List (name (P := P) × msg (P := P))} {p : MsgPacket}
    (hp : p ∈ send_packets src (add_ghost_msg src st l)) :
    ∃ m ∈ l, p = (⟨src, m.1, (write_ghost_log src st, m.2)⟩ : MsgPacket) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨m1, hm1, rfl⟩ := List.mem_map.mp hq
  exact ⟨m1, hm1, rfl⟩

/-! ## ghost_log_correct (`Raft/GhostLogCorrectInterface.v` /
`RaftProofs/GhostLogCorrectProof.v`) -/

/-- `GhostLogCorrectInterface.v:8-19` (`ghost_log_correct`). -/
def ghost_log_correct (net : MsgNet) : Prop :=
  ∀ (p : MsgPacket) (l : ghost_log (P := P)) (t : term)
    (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets →
    (p.pBody : ghost_log (P := P) × msg (P := P)).2
      = .AppendEntries t lid pli plt es ci →
    (p.pBody : ghost_log (P := P) × msg (P := P)).1 = l →
    (pli = 0 ∧ plt = 0 ∧ es = l) ∨
    ((∃ e : entry (P := P), e.eIndex = pli ∧ e.eTerm = plt ∧ e ∈ l) ∧
     es = findGtIndex l pli)

/-- `GhostLogCorrectProof.v:139-197` (`ghost_log_correct_do_leader`'s
message analysis), extracted: a `doLeader` replica message over a
reachable leader state satisfies the ghost-log-correct disjunction
against that state's own log. The `pli = 0` side rides host
positivity + `sorted_findGtIndex_0`; the positive side is
`nextIndex_sanity` (lifted through `msg_simulation_1` — `mgv_deghost`
preserves the state definitionally). -/
theorem doLeader_message_ghost_log_correct {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    {h : name (P := P)} {gd : electionsData (P := P)}
    {d : raft_data (P := P)} {os d' ms}
    (hstate : net.nwState h = (gd, d))
    (hdl : doLeader d h = (os, d', ms))
    {m : name (P := P) × msg (P := P)} (hm : m ∈ ms)
    {t : term} {lid : name (P := P)} {pli : logIndex} {plt : term}
    {es : List (entry (P := P))} {ci : logIndex}
    (hbody : m.2 = .AppendEntries t lid pli plt es ci) :
    (pli = 0 ∧ plt = 0 ∧ es = d.log) ∨
    ((∃ e : entry (P := P), e.eIndex = pli ∧ e.eTerm = plt ∧ e ∈ d.log) ∧
     es = findGtIndex d.log pli) := by
  have hR := msg_simulation_1 net hreach
  have hpos : ∀ e ∈ d.log, e.eIndex > 0 := by
    intro e he
    refine entries_gt_0_invariant (mgv_deghost net) hR h e ?_
    show e ∈ (net.nwState h).2.log
    rw [hstate]
    exact he
  have hsort : sorted d.log := by
    have hs : sorted (net.nwState h).2.log :=
      entries_sorted_invariant (mgv_deghost net) hR h
    rw [hstate] at hs
    exact hs
  have htyL : d.type = .Leader := doLeader_messages_leader d h hdl hm
  obtain ⟨host, hq2⟩ := doLeader_messages_nextIndex d h hdl m hm
  rw [hq2] at hbody
  injection hbody with f1 f2 f3 f4 f5 f6
  by_cases hpli : Nat.pred (getNextIndex d host) = 0
  · -- from-scratch send: prevLog at the origin
    rw [hpli] at f3 f4 f5
    refine Or.inl ⟨f3.symm, ?_, ?_⟩
    · -- plt = 0: findAtIndex at 0 cannot resolve (indices are positive)
      cases hfind : findAtIndex d.log 0 with
      | none =>
        simp only [hfind] at f4
        exact f4.symm
      | some e =>
        obtain ⟨hemem, hei⟩ := findAtIndex_elim hfind
        have := hpos e hemem
        rw [hei] at this
        exact absurd this (Nat.lt_irrefl 0)
    · -- es = the whole ghost log
      rw [← f5, sorted_findGtIndex_0 hpos hsort]
  · -- positive prevLog: the pivot resolves in the leader's own log
    have hne : Nat.pred (getNextIndex (net.nwState h).2 host) ≠ 0 := by
      rw [hstate]
      exact hpli
    have htyL' : ((mgv_deghost net).nwState h).2.type = .Leader := by
      show (net.nwState h).2.type = .Leader
      rw [hstate]
      exact htyL
    obtain ⟨e, hfind⟩ := nextIndex_sanity (mgv_deghost net) hR h host htyL'
      hne
    have hfind2 : findAtIndex d.log (Nat.pred (getNextIndex d host))
        = some e := by
      have hf : findAtIndex (net.nwState h).2.log
          (Nat.pred (getNextIndex (net.nwState h).2 host)) = some e := hfind
      rw [hstate] at hf
      exact hf
    obtain ⟨hemem, hei⟩ := findAtIndex_elim hfind2
    simp only [hfind2] at f4
    refine Or.inr ⟨⟨e, ?_, ?_, hemem⟩, ?_⟩
    · rw [hei, f3]
    · rw [f4]
    · rw [← f5, ← f3]

/-- The single-reply handlers' fresh packet (`AppendEntries`/
`RequestVote` obligations name it explicitly): its ghost is the
written log. -/
theorem reply_packet_ghost {dst src : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {m : msg (P := P)} :
    ((⟨dst, src, (write_ghost_log dst st, m)⟩ : MsgPacket).pBody :
      ghost_log (P := P) × msg (P := P)).1 = st.2.log := rfl

/-- `GhostLogCorrectProof.v:243-275` (`ghost_log_correct_invariant`,
via the UNPRIMED principle — this file's one packet-creating case is
`doLeader`). -/
theorem ghost_log_correct_invariant :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      ghost_log_correct net := by
  refine msg_refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro p l t lid pli plt es ci hp _ _
    exact nomatch hp
  · -- client_request: no packets sent
    intro h net st' ps' gd out d l0 client id c hcr hgd hP _hreach hst hps
    obtain ⟨-, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro p0 l t lid pli plt es ci hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hl] at h1
        simp [send_packets, add_ghost_msg] at h1
    exact hP p0 l t lid pli plt es ci hold hbody0 hgl0
  · -- timeout: only RequestVotes
    intro net h st' ps' gd out d l0 hto hgd hP _hreach hst hps
    obtain ⟨-, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
    intro p0 l t lid pli plt es ci hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim h1
        obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m1 hm1
        replace hbody0 : m1.2 = msg.AppendEntries t lid pli plt es ci :=
          hbody0
        rw [hq2] at hbody0
        exact nomatch hbody0
    exact hP p0 l t lid pli plt es ci hold hbody0 hgl0
  · -- append_entries: the reply is an AppendEntriesReply
    intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n pli plt
        es ci hae
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 lid pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 hold hbody0 hgl0
  · -- append_entries_reply: no messages
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · rw [hl] at h1
        simp [send_packets, add_ghost_msg] at h1
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 hold hbody0 hgl0
  · -- request_vote: the reply is a RequestVoteReply
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 lid pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 hold hbody0 hgl0
  · -- request_vote_reply: no sends
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 hold hbody0 hgl0
  · -- do_leader: THE case
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
    obtain ⟨-, -, -, -, hlogd, -⟩ := doLeader_spec d h hdl
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 l t0 lid pli2 plt2 es2 ci2 hold hbody0 hgl0
    · obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim hnew
      replace hbody0 : m1.2 = msg.AppendEntries t0 lid pli2 plt2 es2 ci2 :=
        hbody0
      have hgl : l = d.log := by
        rw [← hgl0]
        show d'.log = d.log
        exact hlogd
      rw [hgl]
      exact doLeader_message_ghost_log_correct hreach hstate hdl hm1 hbody0
  · -- do_generic_server: no messages
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hms] at h1
        simp [send_packets, add_ghost_msg] at h1
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 hold hbody0 hgl0
  · -- state_same_packet_subset
    intro net net' _hstates hsub hP _hreach
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 (hsub p0 hp0) hbody0 hgl0
  · -- reboot: packets unchanged
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    intro p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0
    rw [← hpkts] at hp0
    exact hP p0 l t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hgl0

end GhostLogs
end Raft
end VerdiCompat
