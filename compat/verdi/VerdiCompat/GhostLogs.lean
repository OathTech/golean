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

/-! ## log_properties_hold_on_ghost_logs
(`Raft/GhostLogsLogPropertiesInterface.v` /
`RaftProofs/GhostLogsLogPropertiesProof.v`) — the higher-order snapshot
principle for ghost logs, and THE PRIMED PRINCIPLE'S FIRST CONSUMER
(its §3.3 discharge witness: all eleven obligations instantiated on a
real invariant). A fresh packet's ghost is the POST-state's log; the
successor net's reachability premise is what lets an abstract
reachability-closed property apply to it. -/

/-- `GhostLogsLogPropertiesInterface.v:8-11` (`msg_log_property`): a
log property that holds of every node's log in every msg-reachable
net. -/
def msg_log_property (Pr : List (entry (P := P)) → Prop) : Prop :=
  ∀ (net : MsgNet) (h : name (P := P)),
    msg_refined_raft_intermediate_reachable net →
    Pr (net.nwState h).2.log

/-- `GhostLogsLogPropertiesInterface.v:13-16`
(`log_properties_hold_on_ghost_logs`). -/
def log_properties_hold_on_ghost_logs (net : MsgNet) : Prop :=
  ∀ (Pr : List (entry (P := P)) → Prop) (p : MsgPacket),
    msg_log_property Pr → p ∈ net.nwPackets →
    Pr (p.pBody : ghost_log (P := P) × msg (P := P)).1

/-- `GhostLogsLogPropertiesProof.v:174-196`
(`log_properties_hold_on_ghost_logs_invariant`), via
**`msg_refined_raft_net_invariant'`** — upstream's own assembly: the
packet-creating obligations primed, `request_vote_reply`/`subset`/
`reboot` through their `_weak` bridges. -/
theorem log_properties_hold_on_ghost_logs_invariant :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      log_properties_hold_on_ghost_logs net := by
  refine msg_refined_raft_net_invariant' ?_ ?_ ?_ ?_ ?_ ?_
    (msg_refined_raft_net_invariant_request_vote_reply'_weak ?_) ?_ ?_
    (msg_refined_raft_net_invariant_subset'_weak ?_)
    (msg_refined_raft_net_invariant_reboot'_weak ?_)
  · -- init
    intro Pr p _hprop hp
    exact nomatch hp
  · -- client_request'
    intro h net st' ps' gd out d l client id c _hcr _hgd hP _hreach
      hreach' hst hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact hP Pr p0 hprop hold
    · have h2 : Pr ((st' h).2.log) := hprop ⟨ps', st'⟩ h hreach'
      rw [hst h, update_same] at h2
      rw [ghost_of_send hnew]
      exact h2
  · -- timeout'
    intro net h st' ps' gd out d l _hto _hgd hP _hreach hreach' hst hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact hP Pr p0 hprop hold
    · have h2 : Pr ((st' h).2.log) := hprop ⟨ps', st'⟩ h hreach'
      rw [hst h, update_same] at h2
      rw [ghost_of_send hnew]
      exact h2
  · -- append_entries': the fresh reply carries the post-state's log
    intro xs p ys net st' ps' gd d m t n pli plt es ci _hae _hgd _hbody
      hP _hreach hreach' hpkts hst hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine hP Pr p0 hprop ?_
      rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · have h2 : Pr ((st' p.pDst).2.log) := hprop ⟨ps', st'⟩ p.pDst hreach'
      rw [hst p.pDst, update_same] at h2
      rw [hnew]
      exact h2
  · -- append_entries_reply'
    intro xs p ys net st' ps' gd d m t es res _haer _hgd _hbody hP _hreach
      hreach' hpkts hst hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine hP Pr p0 hprop ?_
      rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · have h2 : Pr ((st' p.pDst).2.log) := hprop ⟨ps', st'⟩ p.pDst hreach'
      rw [hst p.pDst, update_same] at h2
      rw [ghost_of_send hnew]
      exact h2
  · -- request_vote'
    intro xs p ys net st' ps' gd d m t cid lli llt _hrv _hgd _hbody hP
      _hreach hreach' hpkts hst hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine hP Pr p0 hprop ?_
      rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · have h2 : Pr ((st' p.pDst).2.log) := hprop ⟨ps', st'⟩ p.pDst hreach'
      rw [hst p.pDst, update_same] at h2
      rw [hnew]
      exact h2
  · -- request_vote_reply (unprimed, via the weak bridge): no sends
    intro xs p ys net st' ps' gd d t v _hrvr _hgd _hbody hP _hreach hpkts
      hst hps
    intro Pr p0 hprop hp0
    refine hP Pr p0 hprop ?_
    rw [hpkts]
    exact mem_of_mem_remove_middle (hps p0 hp0)
  · -- do_leader'
    intro net st' ps' gd d h os d' ms _hdl hP _hreach hreach' _hstate hst
      hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact hP Pr p0 hprop hold
    · have h2 : Pr ((st' h).2.log) := hprop ⟨ps', st'⟩ h hreach'
      rw [hst h, update_same] at h2
      rw [ghost_of_send hnew]
      exact h2
  · -- do_generic_server'
    intro net st' ps' gd d os d' ms h _hgs hP _hreach hreach' _hstate hst
      hps
    intro Pr p0 hprop hp0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact hP Pr p0 hprop hold
    · have h2 : Pr ((st' h).2.log) := hprop ⟨ps', st'⟩ h hreach'
      rw [hst h, update_same] at h2
      rw [ghost_of_send hnew]
      exact h2
  · -- state_same_packet_subset (unprimed)
    intro net net' _hstates hsub hP _hreach
    intro Pr p0 hprop hp0
    exact hP Pr p0 hprop (hsub p0 hp0)
  · -- reboot (unprimed): packets unchanged
    intro net net' gd d h d' _hrb hP _hreach _hstate _hst hpkts
    intro Pr p0 hprop hp0
    rw [← hpkts] at hp0
    exact hP Pr p0 hprop hp0

/-! ## ghost_log_allEntries (`Raft/GhostLogAllEntriesInterface.v` /
`RaftProofs/GhostLogAllEntriesProof.v`) — every entry of every
in-flight ghost log is recorded (at some term) in the SENDER's
allEntries. The second primed-principle consumer: a fresh packet's
ghost is the post-state's log, whose entries are recorded by the
lifted `in_log_in_all_entries` AT THE SUCCESSOR NET. -/

/-- `GhostLogAllEntriesProof.v:18-39`
(`lifted_in_log_in_all_entries_invariant`): unit 12's refined
invariant imported through `msg_simulation_1` (definitional
`nwState`). -/
theorem lifted_in_log_in_all_entries :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ (h : name (P := P)) (e : entry (P := P)),
        e ∈ (net.nwState h).2.log →
        ∃ t, (t, e) ∈ (net.nwState h).1.allEntries :=
  fun net hreach =>
    in_log_in_all_entries_invariant (mgv_deghost net)
      (msg_simulation_1 net hreach)

/-- `GhostLogAllEntriesInterface.v:8-14` (`ghost_log_allEntries`). -/
def ghost_log_allEntries (net : MsgNet) : Prop :=
  ∀ (p : MsgPacket) (e : entry (P := P)),
    p ∈ net.nwPackets →
    e ∈ (p.pBody : ghost_log (P := P) × msg (P := P)).1 →
    ∃ t, (t, e) ∈ (net.nwState p.pSrc).1.allEntries

/-- Sender-side transport: allEntries only grow at the updated node. -/
theorem glae_transport {net : MsgNet}
    {st' : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    {u : name (P := P)} {gd : electionsData (P := P)}
    {d : raft_data (P := P)}
    (hst : ∀ h', st' h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (e : entry (P := P)),
      (t, e) ∈ (net.nwState u).1.allEntries → (t, e) ∈ gd.allEntries)
    {src : name (P := P)} {e : entry (P := P)}
    (hex : ∃ t, (t, e) ∈ (net.nwState src).1.allEntries) :
    ∃ t, (t, e) ∈ (st' src).1.allEntries := by
  obtain ⟨t, ht⟩ := hex
  exact ⟨t, update_proj_mem hst (fun s => s.1.allEntries)
    (fun x hx => hgrow x.1 x.2 hx) ht⟩

/-- `GhostLogAllEntriesProof.v:246-268` (`ghost_log_allEntries_invariant`,
via the PRIMED principle — upstream's own assembly). -/
theorem ghost_log_allEntries_invariant :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      ghost_log_allEntries net := by
  refine msg_refined_raft_net_invariant' ?_ ?_ ?_ ?_ ?_ ?_
    (msg_refined_raft_net_invariant_request_vote_reply'_weak ?_) ?_ ?_
    (msg_refined_raft_net_invariant_subset'_weak ?_)
    (msg_refined_raft_net_invariant_reboot'_weak ?_)
  · -- init
    intro p e hp _
    exact nomatch hp
  · -- client_request'
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach
      hreach' hst hps
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine glae_transport hst ?_ (hP p0 e hold he)
      intro t0 e0 hin
      rw [hgd]
      rcases update_elections_data_client_request_allEntries_cases h
        (net.nwState h) client id c with hsame | ⟨t1, e1, hcons, -⟩
      · rw [hsame]
        exact hin
      · rw [hcons]
        exact List.mem_cons_of_mem _ hin
    · obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim hnew
      have hlog : e ∈ ((⟨ps', st'⟩ : MsgNet).nwState h).2.log := by
        show e ∈ (st' h).2.log
        rw [hst h, update_same]
        exact he
      exact lifted_in_log_in_all_entries ⟨ps', st'⟩ hreach' h e hlog
  · -- timeout'
    intro net h st' ps' gd out d l hto hgd hP _hreach hreach' hst hps
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine glae_transport hst ?_ (hP p0 e hold he)
      intro t0 e0 hin
      rw [hgd, (update_elections_data_timeout_ghost h (net.nwState h)).2]
      exact hin
    · obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim hnew
      have hlog : e ∈ ((⟨ps', st'⟩ : MsgNet).nwState h).2.log := by
        show e ∈ (st' h).2.log
        rw [hst h, update_same]
        exact he
      exact lifted_in_log_in_all_entries ⟨ps', st'⟩ hreach' h e hlog
  · -- append_entries'
    intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd _hbody hP
      _hreach hreach' hpkts hst hps
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · have hold2 : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle hold
      refine glae_transport hst ?_ (hP p0 e hold2 he)
      intro t0 e0 hin
      rw [hgd]
      rcases update_elections_data_appendEntries_allEntries_cases p.pDst
        (net.nwState p.pDst) t n pli plt es ci with hsame | ⟨t1, happ⟩
      · rw [hsame]
        exact hin
      · rw [happ]
        exact List.mem_append.mpr (Or.inr hin)
    · rw [hnew] at he
      have hlog : e ∈ ((⟨ps', st'⟩ : MsgNet).nwState p.pDst).2.log := by
        show e ∈ (st' p.pDst).2.log
        rw [hst p.pDst, update_same]
        exact he
      have hres := lifted_in_log_in_all_entries ⟨ps', st'⟩ hreach' p.pDst
        e hlog
      rw [hnew]
      exact hres
  · -- append_entries_reply': no sends
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hreach' hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · have hold2 : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle hold
      refine glae_transport hst ?_ (hP p0 e hold2 he)
      intro t0 e0 hin
      rw [hgd]
      exact hin
    · rw [hl] at hnew
      simp [send_packets, add_ghost_msg] at hnew
  · -- request_vote'
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hreach' hpkts hst hps
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · have hold2 : p0 ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle hold
      refine glae_transport hst ?_ (hP p0 e hold2 he)
      intro t0 e0 hin
      rw [hgd, (update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.2]
      exact hin
    · rw [hnew] at he
      have hlog : e ∈ ((⟨ps', st'⟩ : MsgNet).nwState p.pDst).2.log := by
        show e ∈ (st' p.pDst).2.log
        rw [hst p.pDst, update_same]
        exact he
      have hres := lifted_in_log_in_all_entries ⟨ps', st'⟩ hreach' p.pDst
        e hlog
      rw [hnew]
      exact hres
  · -- request_vote_reply (unprimed): no sends
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    refine glae_transport hst ?_ (hP p0 e hold he)
    intro t0 e0 hin
    rw [hgd]
    rw [(update_elections_data_requestVoteReply_votes p.pDst p.pSrc t v
      (net.nwState p.pDst)).2.2]
    exact hin
  · -- do_leader'
    intro net st' ps' gd d h os d' ms hdl hP _hreach hreach' hstate hst
      hps
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine glae_transport hst ?_ (hP p0 e hold he)
      intro t0 e0 hin
      have hgd : gd = (net.nwState h).1 := by rw [hstate]
      rw [hgd]
      exact hin
    · obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim hnew
      have hlog : e ∈ ((⟨ps', st'⟩ : MsgNet).nwState h).2.log := by
        show e ∈ (st' h).2.log
        rw [hst h, update_same]
        exact he
      exact lifted_in_log_in_all_entries ⟨ps', st'⟩ hreach' h e hlog
  · -- do_generic_server': no messages
    intro net st' ps' gd d os d' ms h hgs hP _hreach hreach' hstate hst
      hps
    obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    intro p0 e hp0 he
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine glae_transport hst ?_ (hP p0 e hold he)
      intro t0 e0 hin
      have hgd : gd = (net.nwState h).1 := by rw [hstate]
      rw [hgd]
      exact hin
    · rw [hms] at hnew
      simp [send_packets, add_ghost_msg] at hnew
  · -- state_same_packet_subset (unprimed)
    intro net net' hstates hsub hP _hreach
    intro p0 e hp0 he
    obtain ⟨t0, ht0⟩ := hP p0 e (hsub p0 hp0) he
    refine ⟨t0, ?_⟩
    rw [← hstates p0.pSrc]
    exact ht0
  · -- reboot (unprimed): the ghost survives; packets unchanged
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    intro p0 e hp0 he
    rw [← hpkts] at hp0
    obtain ⟨t0, ht0⟩ := hP p0 e hp0 he
    refine ⟨t0, ?_⟩
    rw [hst p0.pSrc]
    by_cases heq : p0.pSrc = h
    · rw [heq, update_same]
      show (t0, e) ∈ gd.allEntries
      rw [show gd = (net.nwState h).1 from by rw [hstate]]
      rw [heq] at ht0
      exact ht0
    · rw [update_neq _ _ heq]
      exact ht0

/-! ## ghost_log_entries_match (`Raft/GhostLogLogMatchingInterface.v` /
`RaftProofs/GhostLogLogMatchingProof.v`) — host logs and in-flight
GHOST logs pairwise satisfy `entries_match`. The whole slice-73/74/78
chain pays off here: `ghost_log_correct` contextualizes the consumed
packet, `log_properties_hold_on_ghost_logs` supplies ghost
sortedness/contiguity, `ghost_log_allEntries` +
`allEntries_leader_sublog` bound the client-request cons. -/

/-- `GhostLogLogMatchingProof.v:102-115` (`lifted_entries_match`, the
msg-level RLML host pair — definitional `nwState`). -/
theorem mgv_lifted_entries_match :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ h h' : name (P := P),
        entries_match (net.nwState h).2.log (net.nwState h').2.log :=
  fun net hreach =>
    entries_match_invariant (mgv_deghost net) (msg_simulation_1 net hreach)

/-- `GhostLogLogMatchingProof.v:59-70` (`lifted_entries_sorted`). -/
theorem mgv_lifted_entries_sorted :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ h : name (P := P), sorted (net.nwState h).2.log :=
  fun net hreach =>
    entries_sorted_invariant (mgv_deghost net) (msg_simulation_1 net hreach)

/-- `GhostLogLogMatchingProof.v:46-58` (`lifted_entries_contiguous`). -/
theorem mgv_lifted_entries_contiguous :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ h : name (P := P),
        contiguous_range_exact_lo (net.nwState h).2.log 0 :=
  fun net hreach =>
    entries_contiguous_invariant (mgv_deghost net)
      (msg_simulation_1 net hreach)

/-- `GhostLogLogMatchingProof.v:78-97` (`lifted_entries_contiguous_nw`). -/
theorem mgv_lifted_entries_contiguous_nw :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ (p : MsgPacket) (t : term) (n : name (P := P)) (pli : logIndex)
        (plt : term) (es : List (entry (P := P))) (ci : logIndex),
        p ∈ net.nwPackets →
        (p.pBody : ghost_log (P := P) × msg (P := P)).2
          = .AppendEntries t n pli plt es ci →
        contiguous_range_exact_lo es pli :=
  fun net hreach p t n pli plt es ci hp hbody =>
    entries_contiguous_nw_invariant (mgv_deghost net)
      (msg_simulation_1 net hreach) (mgv_deghost_packet p) t n pli plt es
      ci (List.mem_map_of_mem hp) hbody

/-- `GhostLogLogMatchingProof.v:118-134`
(`lifted_no_entries_past_current_term_host`). -/
theorem mgv_lifted_nepct_host :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ (h : name (P := P)) (e : entry (P := P)),
        e ∈ (net.nwState h).2.log →
        e.eTerm ≤ (net.nwState h).2.currentTerm :=
  fun net hreach =>
    nepct_host_lifted (mgv_deghost net) (msg_simulation_1 net hreach)

/-- `GhostLogLogMatchingProof.v:162-177`
(`lifted_allEntries_leader_sublog`). -/
theorem mgv_lifted_allEntries_leader_sublog :
    ∀ net : MsgNet, msg_refined_raft_intermediate_reachable (P := P) net →
      ∀ (leader : name (P := P)) (e : entry (P := P)) (h : name (P := P)),
        (net.nwState leader).2.type = .Leader →
        e ∈ (net.nwState h).1.allEntries.map Prod.snd →
        e.eTerm = (net.nwState leader).2.currentTerm →
        e ∈ (net.nwState leader).2.log :=
  fun net hreach =>
    allEntries_leader_sublog_invariant (mgv_deghost net)
      (msg_simulation_1 net hreach)

/-- `GhostLogLogMatchingProof.v:136-145` (`ghost_log_sorted`) — the
higher-order snapshot principle's first payoffs. -/
theorem ghost_log_sorted {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    {p : MsgPacket} (hp : p ∈ net.nwPackets) :
    sorted (p.pBody : ghost_log (P := P) × msg (P := P)).1 :=
  log_properties_hold_on_ghost_logs_invariant net hreach sorted p
    (fun net' h hreach' => mgv_lifted_entries_sorted net' hreach' h) hp

/-- `GhostLogLogMatchingProof.v:147-157` (`ghost_log_contiguous`). -/
theorem ghost_log_contiguous {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    {p : MsgPacket} (hp : p ∈ net.nwPackets) :
    contiguous_range_exact_lo
      (p.pBody : ghost_log (P := P) × msg (P := P)).1 0 :=
  log_properties_hold_on_ghost_logs_invariant net hreach
    (fun l => contiguous_range_exact_lo l 0) p
    (fun net' h hreach' => mgv_lifted_entries_contiguous net' hreach' h) hp

/-- `GhostLogLogMatchingInterface.v:9-13` (`ghost_log_entries_match_host`). -/
def ghost_log_entries_match_host (net : MsgNet) : Prop :=
  ∀ (h : name (P := P)) (p : MsgPacket),
    p ∈ net.nwPackets →
    entries_match (net.nwState h).2.log
      (p.pBody : ghost_log (P := P) × msg (P := P)).1

/-- `GhostLogLogMatchingProof.v:28-32` (`ghost_log_entries_match_nw`). -/
def ghost_log_entries_match_nw (net : MsgNet) : Prop :=
  ∀ p p' : MsgPacket,
    p ∈ net.nwPackets → p' ∈ net.nwPackets →
    entries_match (p.pBody : ghost_log (P := P) × msg (P := P)).1
      (p'.pBody : ghost_log (P := P) × msg (P := P)).1

/-- `GhostLogLogMatchingProof.v:34-36` (`ghost_log_entries_match`). -/
def ghost_log_entries_match (net : MsgNet) : Prop :=
  ghost_log_entries_match_host net ∧ ghost_log_entries_match_nw net

omit O in
/-- `GhostLogLogMatchingProof.v:352-368` (`sorted_entries_match_cons`):
extending the left log with a fresh head preserves `entries_match`
when nothing in the right log matches the head's (index, term). -/
theorem sorted_entries_match_cons {l l' : List (entry (P := P))}
    {e : entry (P := P)}
    (hs : sorted (e :: l)) (hm : entries_match l l')
    (hno : ¬∃ e', e'.eIndex = e.eIndex ∧ e'.eTerm = e.eTerm ∧ e' ∈ l') :
    entries_match (e :: l) l' := by
  intro e1 e1' e'' hidx hterm he1 he1' hle
  obtain ⟨hhead, -⟩ := hs
  rcases List.mem_cons.mp he1 with rfl | he1l
  · exact absurd ⟨e1', hidx.symm, hterm.symm, he1'⟩ hno
  · constructor
    · intro he''
      rcases List.mem_cons.mp he'' with rfl | he''l
      · exfalso
        have := (hhead e1 he1l).1
        exact absurd hle (Nat.not_le.mpr this)
      · exact (hm e1 e1' e'' hidx hterm he1l he1' hle).mp he''l
    · intro he''
      exact List.mem_cons_of_mem _
        ((hm e1 e1' e'' hidx hterm he1l he1' hle).mpr he'')

/-- `GhostLogLogMatchingProof.v:180-208` (`handleAppendEntries_ghost_log`)
— THE engine: an accepted AppendEntries leaves the log equal to the old
log or to the consumed packet's GHOST log (`ghost_log_correct`
contextualizes the payload; the splice case is unit 8's `thing`). -/
theorem handleAppendEntries_ghost_log {net : MsgNet}
    (hreach : msg_refined_raft_intermediate_reachable (P := P) net)
    {p : MsgPacket} {d : raft_data (P := P)} {m : msg (P := P)}
    {t : term} {n : name (P := P)} {pli : logIndex} {plt : term}
    {es : List (entry (P := P))} {ci : logIndex} {h : name (P := P)}
    (hm : entries_match (net.nwState h).2.log
      (p.pBody : ghost_log (P := P) × msg (P := P)).1)
    (hae : handleAppendEntries h (net.nwState h).2 t n pli plt es ci
      = (d, m))
    (hbody : (p.pBody : ghost_log (P := P) × msg (P := P)).2
      = .AppendEntries t n pli plt es ci)
    (hp : p ∈ net.nwPackets) :
    d.log = (net.nwState h).2.log ∨
    d.log = (p.pBody : ghost_log (P := P) × msg (P := P)).1 := by
  have hglc := ghost_log_correct_invariant net hreach p p.pBody.1 t n pli
    plt es ci hp hbody rfl
  have hgs : sorted (p.pBody : ghost_log (P := P) × msg (P := P)).1 :=
    ghost_log_sorted hreach hp
  have hgc : contiguous_range_exact_lo
      (p.pBody : ghost_log (P := P) × msg (P := P)).1 0 :=
    ghost_log_contiguous hreach hp
  rcases handleAppendEntries_accept_detail h (net.nwState h).2 t n pli plt
    es ci hae with hsame | ⟨-, -, hnewe, hshape⟩
  · exact Or.inl hsame
  · obtain ⟨hesne, -⟩ := haveNewEntries_true hnewe
    rcases hshape with ⟨hpli0, hlog⟩ | ⟨e0, he0in, he0i, he0t, hlog⟩
    · -- scratch: the ghost is exactly the payload
      rcases hglc with ⟨-, -, hes⟩ | ⟨⟨x, hxi, -, hxin⟩, hes⟩
      · exact Or.inr (by rw [hlog, hes])
      · -- a ghost pivot at index pli = 0: ghost positivity refutes it
        exfalso
        rw [hpli0] at hxi
        exact absurd (hgc.2 x hxin) (by rw [hxi]; exact Nat.lt_irrefl 0)
    · -- splice: unit 8's `thing` glues the payload onto the kept prefix
      rcases hglc with ⟨hpli0, -, -⟩ | ⟨⟨x, hxi, hxt, hxin⟩, hes⟩
      · -- a host pivot at index pli = 0: host positivity refutes it
        exfalso
        have hpos := (mgv_lifted_entries_contiguous net hreach h).2 e0
          he0in
        rw [he0i, hpli0] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)
      · right
        rw [hlog, ← he0i]
        refine thing (mgv_lifted_entries_sorted net hreach h) hgs hgc hm
          hesne ?_ ?_ he0in hxin (by rw [he0i, hxi]) (by rw [he0t, hxt])
        · rw [hes]
          exact findGtIndex_Prefix _ _
        · rw [he0i]
          exact mgv_lifted_entries_contiguous_nw net hreach p t n pli plt
            es ci hp hbody

/-- `GhostLogLogMatchingProof.v:509-534`
(`ghost_log_entries_match_invariant`), via the PRIMED principle —
upstream's own assembly: `append_entries`/`request_vote` primed (the
fresh reply's ghost is the post-state's log, read at the successor
net), everything else through the `_weak` bridges. -/
theorem ghost_log_entries_match_invariant :
    ∀ net, msg_refined_raft_intermediate_reachable (P := P) net →
      ghost_log_entries_match net := by
  refine msg_refined_raft_net_invariant' ?_
    (msg_refined_raft_net_invariant_client_request'_weak ?_)
    (msg_refined_raft_net_invariant_timeout'_weak ?_) ?_
    (msg_refined_raft_net_invariant_append_entries_reply'_weak ?_) ?_
    (msg_refined_raft_net_invariant_request_vote_reply'_weak ?_)
    (msg_refined_raft_net_invariant_do_leader'_weak ?_)
    (msg_refined_raft_net_invariant_do_generic_server'_weak ?_)
    (msg_refined_raft_net_invariant_subset'_weak ?_)
    (msg_refined_raft_net_invariant_reboot'_weak ?_)
  · -- init
    refine ⟨?_, ?_⟩
    · intro h p hp
      exact nomatch hp
    · intro p p' hp _
      exact nomatch hp
  · -- client_request (unprimed): the fresh cons is bounded by
    -- ghost_log_allEntries + allEntries_leader_sublog
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have holdpk : ∀ p0 : MsgPacket, p0 ∈ ps' → p0 ∈ net.nwPackets := by
      intro p0 hp0
      rcases hps p0 hp0 with hold | hnew
      · exact hold
      · rw [hl] at hnew
        simp [send_packets, add_ghost_msg] at hnew
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      have hold := holdpk p0 hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      rw [hst h0]
      by_cases heq : h0 = h
      · rw [heq, update_same]
        show entries_match d.log
          (p0.pBody : ghost_log (P := P) × msg (P := P)).1
        rcases handleClientRequest_log_full h (net.nwState h).2 client id
          c hcr with ⟨htyL, hlog⟩ | ⟨-, heqd⟩
        · rw [hlog]
          refine sorted_entries_match_cons ?_ (hhost h p0 hold) ?_
          · refine ⟨?_, mgv_lifted_entries_sorted net hreach h⟩
            intro e' he'
            constructor
            · show maxIndex (net.nwState h).2.log + 1 > e'.eIndex
              exact Nat.lt_succ_of_le (maxIndex_is_max
                (mgv_lifted_entries_sorted net hreach h) he')
            · show e'.eTerm ≤ (net.nwState h).2.currentTerm
              exact mgv_lifted_nepct_host net hreach h e' he'
          · rintro ⟨e', hei', het', hein'⟩
            obtain ⟨t0, ht0⟩ := ghost_log_allEntries_invariant net hreach
              p0 e' hold hein'
            have hesub := mgv_lifted_allEntries_leader_sublog net hreach
              h e' p0.pSrc htyL
              (List.mem_map.mpr ⟨(t0, e'), ht0, rfl⟩) het'
            have hle := maxIndex_is_max
              (mgv_lifted_entries_sorted net hreach h) hesub
            rw [hei'] at hle
            exact absurd hle (Nat.not_succ_le_self _)
        · rw [heqd]
          exact hhost h p0 hold
      · rw [update_neq _ _ heq]
        exact hhost h0 p0 hold
    · intro p0 p1 hp0 hp1
      exact hnw p0 p1 (holdpk p0 hp0) (holdpk p1 hp1)
  · -- timeout (unprimed): log-preserving; fresh ghosts are the old log
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hghost : ∀ p0 : MsgPacket, p0 ∈ ps' →
        p0 ∈ net.nwPackets ∨
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
          = (net.nwState h).2.log := by
      intro p0 hp0
      rcases hps p0 hp0 with hold | hnew
      · exact Or.inl hold
      · obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim hnew
        refine Or.inr ?_
        show d.log = (net.nwState h).2.log
        exact hlog
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = h
        · rw [heq, update_same]
          exact hlog
        · rw [update_neq _ _ heq]
      rw [hlog0]
      rcases hghost p0 hp0 with hold | hgh
      · exact hhost h0 p0 hold
      · rw [hgh]
        exact mgv_lifted_entries_match net hreach h0 h
    · intro p0 p1 hp0 hp1
      rcases hghost p0 hp0 with hold0 | hgh0 <;>
        rcases hghost p1 hp1 with hold1 | hgh1
      · exact hnw p0 p1 hold0 hold1
      · rw [hgh1]
        exact entries_match_sym (hhost h p0 hold0)
      · rw [hgh0]
        exact hhost h p1 hold1
      · rw [hgh0, hgh1]
        exact entries_match_refl _
  · -- append_entries (PRIMED): the engine case
    intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd hbody hP
      hreach hreach' hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hglog := handleAppendEntries_ghost_log hreach (hhost p.pDst p
      hp_in) hae hbody hp_in
    have hfresh_log : ((⟨p.pDst, p.pSrc,
        (write_ghost_log p.pDst (gd, d), m)⟩ : MsgPacket).pBody :
        ghost_log (P := P) × msg (P := P)).1 = d.log := rfl
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      rcases hps p0 hp0 with hold | hnew
      · have holdn : p0 ∈ net.nwPackets := by
          rw [hpkts]
          exact mem_of_mem_remove_middle hold
        rw [hst h0]
        by_cases heq : h0 = p.pDst
        · rw [heq, update_same]
          show entries_match d.log
            (p0.pBody : ghost_log (P := P) × msg (P := P)).1
          rcases hglog with hdold | hdghost
          · rw [hdold]
            exact hhost p.pDst p0 holdn
          · rw [hdghost]
            exact hnw p p0 hp_in holdn
        · rw [update_neq _ _ heq]
          exact hhost h0 p0 holdn
      · -- the fresh reply: both sides read off the SUCCESSOR net
        rw [hnew, hfresh_log]
        have hres := mgv_lifted_entries_match ⟨ps', st'⟩ hreach' h0 p.pDst
        have hdst : ((⟨ps', st'⟩ : MsgNet).nwState p.pDst).2.log = d.log := by
          show (st' p.pDst).2.log = d.log
          rw [hst p.pDst, update_same]
        rw [hdst] at hres
        show entries_match (st' h0).2.log d.log
        exact hres
    · intro p0 p1 hp0 hp1
      rcases hps p0 hp0 with hold0 | hnew0 <;>
        rcases hps p1 hp1 with hold1 | hnew1
      · refine hnw p0 p1 ?_ ?_ <;> rw [hpkts]
        · exact mem_of_mem_remove_middle hold0
        · exact mem_of_mem_remove_middle hold1
      · have holdn : p0 ∈ net.nwPackets := by
          rw [hpkts]
          exact mem_of_mem_remove_middle hold0
        rw [hnew1, hfresh_log]
        rcases hglog with hdold | hdghost
        · rw [hdold]
          exact entries_match_sym (hhost p.pDst p0 holdn)
        · rw [hdghost]
          exact entries_match_sym (hnw p p0 hp_in holdn)
      · have holdn : p1 ∈ net.nwPackets := by
          rw [hpkts]
          exact mem_of_mem_remove_middle hold1
        rw [hnew0, hfresh_log]
        rcases hglog with hdold | hdghost
        · rw [hdold]
          exact hhost p.pDst p1 holdn
        · rw [hdghost]
          exact hnw p p1 hp_in holdn
      · rw [hnew0, hnew1, hfresh_log]
        exact entries_match_refl _
  · -- append_entries_reply (unprimed): no sends, log preserved
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP hreach
      hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    have hlogd := handleAppendEntriesReply_log p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    have holdpk : ∀ p0 : MsgPacket, p0 ∈ ps' → p0 ∈ net.nwPackets := by
      intro p0 hp0
      rcases hps p0 hp0 with hold | hnew
      · rw [hpkts]
        exact mem_of_mem_remove_middle hold
      · rw [hl] at hnew
        simp [send_packets, add_ghost_msg] at hnew
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = p.pDst
        · rw [heq, update_same]
          exact hlogd
        · rw [update_neq _ _ heq]
      rw [hlog0]
      exact hhost h0 p0 (holdpk p0 hp0)
    · intro p0 p1 hp0 hp1
      exact hnw p0 p1 (holdpk p0 hp0) (holdpk p1 hp1)
  · -- request_vote (PRIMED, upstream's assembly): log-preserving; the
    -- fresh reply reads off the successor net
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      hreach hreach' hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    have hlogd := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t
      p.pSrc lli llt hrv
    have hfresh_log : ((⟨p.pDst, p.pSrc,
        (write_ghost_log p.pDst (gd, d), m)⟩ : MsgPacket).pBody :
        ghost_log (P := P) × msg (P := P)).1 = d.log := rfl
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = p.pDst
        · rw [heq, update_same]
          exact hlogd
        · rw [update_neq _ _ heq]
      rcases hps p0 hp0 with hold | hnew
      · rw [hlog0]
        refine hhost h0 p0 ?_
        rw [hpkts]
        exact mem_of_mem_remove_middle hold
      · rw [hnew, hfresh_log]
        have hres := mgv_lifted_entries_match ⟨ps', st'⟩ hreach' h0 p.pDst
        have hdst : ((⟨ps', st'⟩ : MsgNet).nwState p.pDst).2.log
            = d.log := by
          show (st' p.pDst).2.log = d.log
          rw [hst p.pDst, update_same]
        rw [hdst] at hres
        show entries_match (st' h0).2.log d.log
        exact hres
    · intro p0 p1 hp0 hp1
      rcases hps p0 hp0 with hold0 | hnew0 <;>
        rcases hps p1 hp1 with hold1 | hnew1
      · refine hnw p0 p1 ?_ ?_ <;> rw [hpkts]
        · exact mem_of_mem_remove_middle hold0
        · exact mem_of_mem_remove_middle hold1
      · have holdn : p0 ∈ net.nwPackets := by
          rw [hpkts]
          exact mem_of_mem_remove_middle hold0
        rw [hnew1, hfresh_log, hlogd]
        exact entries_match_sym (hhost p.pDst p0 holdn)
      · have holdn : p1 ∈ net.nwPackets := by
          rw [hpkts]
          exact mem_of_mem_remove_middle hold1
        rw [hnew0, hfresh_log, hlogd]
        exact hhost p.pDst p1 holdn
      · rw [hnew0, hnew1, hfresh_log]
        exact entries_match_refl _
  · -- request_vote_reply (unprimed): no sends, log preserved
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts
      hst hps
    obtain ⟨hhost, hnw⟩ := hP
    have hlogd : d.log = (net.nwState p.pDst).2.log := by
      rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t v
    have holdpk : ∀ p0 : MsgPacket, p0 ∈ ps' → p0 ∈ net.nwPackets := by
      intro p0 hp0
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = p.pDst
        · rw [heq, update_same]
          exact hlogd
        · rw [update_neq _ _ heq]
      rw [hlog0]
      exact hhost h0 p0 (holdpk p0 hp0)
    · intro p0 p1 hp0 hp1
      exact hnw p0 p1 (holdpk p0 hp0) (holdpk p1 hp1)
  · -- do_leader (unprimed): log-preserving; fresh ghosts = the old log
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, -, -, hlogd, -⟩ := doLeader_spec d h hdl
    have hdlog : d.log = (net.nwState h).2.log := by
      rw [hstate]
    have hghost : ∀ p0 : MsgPacket, p0 ∈ ps' →
        p0 ∈ net.nwPackets ∨
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
          = (net.nwState h).2.log := by
      intro p0 hp0
      rcases hps p0 hp0 with hold | hnew
      · exact Or.inl hold
      · obtain ⟨m1, hm1, rfl⟩ := mem_send_ghost_elim hnew
        refine Or.inr ?_
        show d'.log = (net.nwState h).2.log
        rw [hlogd]
        exact hdlog
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = h
        · rw [heq, update_same]
          show d'.log = (net.nwState h).2.log
          rw [hlogd]
          exact hdlog
        · rw [update_neq _ _ heq]
      rw [hlog0]
      rcases hghost p0 hp0 with hold | hgh
      · exact hhost h0 p0 hold
      · rw [hgh]
        exact mgv_lifted_entries_match net hreach h0 h
    · intro p0 p1 hp0 hp1
      rcases hghost p0 hp0 with hold0 | hgh0 <;>
        rcases hghost p1 hp1 with hold1 | hgh1
      · exact hnw p0 p1 hold0 hold1
      · rw [hgh1]
        exact entries_match_sym (hhost h p0 hold0)
      · rw [hgh0]
        exact hhost h p1 hold1
      · rw [hgh0, hgh1]
        exact entries_match_refl _
  · -- do_generic_server (unprimed): no sends, log preserved
    intro net st' ps' gd d os d' ms h hgs hP hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlogd, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    have holdpk : ∀ p0 : MsgPacket, p0 ∈ ps' → p0 ∈ net.nwPackets := by
      intro p0 hp0
      rcases hps p0 hp0 with hold | hnew
      · exact hold
      · rw [hms] at hnew
        simp [send_packets, add_ghost_msg] at hnew
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      replace hp0 : p0 ∈ ps' := hp0
      show entries_match (st' h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (st' h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = h
        · rw [heq, update_same]
          show d'.log = (net.nwState h).2.log
          rw [hlogd, hstate]
        · rw [update_neq _ _ heq]
      rw [hlog0]
      exact hhost h0 p0 (holdpk p0 hp0)
    · intro p0 p1 hp0 hp1
      exact hnw p0 p1 (holdpk p0 hp0) (holdpk p1 hp1)
  · -- state_same_packet_subset (unprimed)
    intro net net' hstates hsub hP _hreach
    obtain ⟨hhost, hnw⟩ := hP
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      have := hhost h0 p0 (hsub p0 hp0)
      rw [hstates h0] at this
      exact this
    · intro p0 p1 hp0 hp1
      exact hnw p0 p1 (hsub p0 hp0) (hsub p1 hp1)
  · -- reboot (unprimed): log survives; packets unchanged
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    obtain ⟨hhost, hnw⟩ := hP
    refine ⟨?_, ?_⟩
    · intro h0 p0 hp0
      rw [← hpkts] at hp0
      show entries_match (net'.nwState h0).2.log
        (p0.pBody : ghost_log (P := P) × msg (P := P)).1
      have hlog0 : (net'.nwState h0).2.log = (net.nwState h0).2.log := by
        rw [hst h0]
        by_cases heq : h0 = h
        · rw [heq, update_same]
          show (gd, d').2.log = (net.nwState h).2.log
          rw [← hrb]
          show d.log = (net.nwState h).2.log
          rw [hstate]
        · rw [update_neq _ _ heq]
      rw [hlog0]
      exact hhost h0 p0 hp0
    · intro p0 p1 hp0 hp1
      rw [← hpkts] at hp0 hp1
      exact hnw p0 p1 hp0 hp1

end GhostLogs
end Raft
end VerdiCompat
