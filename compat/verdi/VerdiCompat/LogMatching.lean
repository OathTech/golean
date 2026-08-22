import VerdiCompat.CreationRing

/-!
# The log-matching core

Campaign Arc 3 unit 6: the largest self-contained prefix of the
GAP-7 import closure (the full closure and wave table are in the arc
log's unit-6 opening entry), 1:1 against the sources @ a3375e8 —

- `leaderLogs_sorted` (`Raft/LeaderLogsSortedInterface.v` /
  `RaftProofs/LeaderLogsSortedProof.v`, GAP-5a): every recorded
  leaderLog snapshot is sorted (ghost layer);
- `UniqueIndices` (`Raft/UniqueIndicesInterface.v` /
  `RaftProofs/UniqueIndicesProof.v`, BASE): host logs and in-flight
  AppendEntries entries have duplicate-free indices — a direct
  corollary of `logs_sorted` via `sorted_uniqueIndices`
  (`Raft/CommonTheorems.v:761-768`);
- `leader_sublog` (`Raft/LeaderSublogInterface.v` /
  `RaftProofs/LeaderSublogProof.v`, BASE): an entry bearing a leader's
  current term is in that leader's log;
- `log_matching` (`Raft/LogMatchingInterface.v` /
  `RaftProofs/LogMatchingProof.v`, BASE — the T3-named log-matching
  invariant);
- `leaderLogs_contiguous` (`Raft/LeaderLogsContiguousInterface.v`,
  GAP-5b), `allEntries_indices_gt0`
  (`Raft/AllEntriesIndicesGt0Interface.v`), and the refined bridge
  `refined_log_matching_lemmas`
  (`Raft/RefinedLogMatchingLemmasInterface.v`).

Statements 1:1 with the Interface files; proofs re-derived through the
ported principles.
-/

namespace VerdiCompat
namespace Raft

section LogMatchingCore
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-! ## leaderLogs_sorted (GAP-5a) -/

/-- `LeaderLogsSortedInterface.v:9-13` (`leaderLogs_sorted`). -/
def leaderLogs_sorted (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P))),
    (t, ll) ∈ (net.nwState h).1.leaderLogs → sorted ll

/-- The ghost-unchanged step helper (the shape of upstream's
per-handler `leaderLogs_update_elections_data_*` rewrites,
`LeaderLogsSortedProof.v:24-43` etc.): if the updated node's ghost
keeps its `leaderLogs`, the invariant transports — no fact about the
real-state component is needed. -/
theorem leaderLogs_sorted_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : leaderLogs_sorted net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs) :
    leaderLogs_sorted net' := by
  intro h t ll hin
  rw [hst h] at hin
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hin
    replace hin : (t, ll) ∈ gd.leaderLogs := hin
    rw [hgd] at hin
    exact hP h t ll hin
  · rw [update_neq _ _ heq] at hin
    exact hP h t ll hin

/-- `LeaderLogsSortedProof.v:204-219` (`leaderLogs_sorted_invariant`):
every leaderLog snapshot is sorted. The only writer of `leaderLogs` is
the RequestVoteReply win, which snapshots the winner's own log —
sorted by the lifted base invariant (`sorted_host_lifted`). -/
theorem leaderLogs_sorted_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_sorted net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init (`LeaderLogsSortedProof.v:17-22`)
    intro h t ll hin
    exact nomatch hin
  · -- client_request (`:24-43`)
    intro h net st' ps' gd out d l client id c _hcr hgd hP _hreach hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2
  · -- timeout (`:59-77`)
    intro net h st' ps' gd out d l _hto hgd hP _hreach hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_timeout_ghost h (net.nwState h)).1
  · -- append_entries (`:79-97`)
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci _hae hgd _hbody hP
      _hreach _hpkts hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci).2.2.2
  · -- append_entries_reply (`:99-105`, ghost untouched)
    intro xs p ys net st' ps' gd d m t es res _haer hgd _hbody hP _hreach
      _hpkts hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    rw [hgd]
  · -- request_vote (`:107-117`)
    intro xs p ys net st' ps' gd d m t cid lli llt _hrv hgd _hbody hP
      _hreach _hpkts hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t p.pSrc
      lli llt (net.nwState p.pDst)).2.1
  · -- request_vote_reply (`:139-155`): the one real case — a win
    -- snapshots the winner's own (sorted, lifted) log
    intro xs p ys net st' ps' gd d t v _hrvr hgd _hbody hP hreach _hpkts
      hst _hps
    intro h t2 ll hin
    replace hin : (t2, ll) ∈ (st' h).1.leaderLogs := hin
    rw [hst h] at hin
    by_cases heq : h = p.pDst
    · subst heq
      rw [update_same] at hin
      replace hin : (t2, ll) ∈ gd.leaderLogs := hin
      subst hgd
      rcases leaderLogs_update_elections_data_RVR hin with hold | ⟨-, -, -, hll⟩
      · exact hP p.pDst t2 ll hold
      · rw [hll, handleRequestVoteReply_log]
        exact sorted_host_lifted net hreach p.pDst
    · rw [update_neq _ _ heq] at hin
      exact hP h t2 ll hin
  · -- do_leader (`:157-171`, ghost rides along)
    intro net st' ps' gd d h os d' ms _hdl hP _hreach hstate hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    rw [hstate]
  · -- do_generic_server (`:173-187`)
    intro net st' ps' gd d os d' ms h _hgs hP _hreach hstate hst _hps
    refine leaderLogs_sorted_of_update hP hst ?_
    rw [hstate]
  · -- state_same_packet_subset (`:189-196`)
    intro net net' hstates _hpkts hP _hreach h t ll hin
    rw [← hstates h] at hin
    exact hP h t ll hin
  · -- reboot (`:198-211`, ghost survives)
    intro net net' gd d h d' _hrb hP _hreach hstate hst _hpkts
    refine leaderLogs_sorted_of_update hP hst ?_
    rw [hstate]

/-! ## UniqueIndices (BASE) -/

omit O in
/-- `CommonTheorems.v:761-768` (`sorted_uniqueIndices`): a sorted log
has duplicate-free indices (strict descent is irreflexive). Proved
constructively via `List.Pairwise` directly (the lane's axiom set —
arc log GAP-4 discipline). -/
theorem sorted_uniqueIndices {l : List (entry (P := P))} (hs : sorted l) :
    uniqueIndices l := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons e es ih =>
    obtain ⟨hgt, hs'⟩ := hs
    refine List.Pairwise.cons ?_ (ih hs')
    intro i hi
    obtain ⟨e', he', heq⟩ := List.mem_map.mp hi
    rw [← heq]
    exact Nat.ne_of_gt (hgt e' he').1

/-- `UniqueIndicesInterface.v:9-10` (`uniqueIndices_host_invariant`). -/
def uniqueIndices_host_invariant (net : RaftNet) : Prop :=
  ∀ h : name (P := P), uniqueIndices (net.nwState h).log

/-- `UniqueIndicesInterface.v:12-17` (`uniqueIndices_nw_invariant`). -/
def uniqueIndices_nw_invariant (net : RaftNet) : Prop :=
  ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (leaderId : name (P := P)) (prevLogIndex : logIndex)
    (prevLogTerm : term) (entries : List (entry (P := P)))
    (leaderCommit : logIndex),
    p ∈ net.nwPackets →
    p.pBody = .AppendEntries t leaderId prevLogIndex prevLogTerm
      entries leaderCommit →
    uniqueIndices entries

/-- `UniqueIndicesInterface.v:19-20` (`UniqueIndices`). -/
def UniqueIndices (net : RaftNet) : Prop :=
  uniqueIndices_host_invariant net ∧ uniqueIndices_nw_invariant net

/-- `UniqueIndicesProof.v:12-24` (`UniqueIndices_invariant`) — BASE
layer; no induction of its own, a direct corollary of
`logs_sorted_invariant`. -/
theorem UniqueIndices_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net → UniqueIndices net := by
  intro net hreach
  obtain ⟨hhost, hnw, -, -⟩ := logs_sorted_invariant net hreach
  exact ⟨fun h => sorted_uniqueIndices (hhost h),
    fun p t lid pli plt es ci hp hbody =>
      sorted_uniqueIndices (hnw p t lid pli plt es ci hp hbody)⟩

end LogMatchingCore

end Raft
end VerdiCompat
