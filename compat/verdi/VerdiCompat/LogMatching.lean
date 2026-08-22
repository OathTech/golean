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

/-! ## leader_sublog (BASE)

`LeaderSublogInterface.v:8-27` / `LeaderSublogProof.v` (554 lines): an
entry bearing a leader's current term is in that leader's log. The
request-vote-reply case is where election safety does its work: a fresh
win at a term that already has entries would contradict
`CandidateEntries` — delivered at base level through `lower_prop` via
the two `RefinementCommonTheorems.v` lemmas below. -/

/-- `LeaderSublogInterface.v:8-13` (`leader_sublog_host_invariant`). -/
def leader_sublog_host_invariant (net : RaftNet) : Prop :=
  ∀ (leader : name (P := P)) (e : entry (P := P)) (h : name (P := P)),
    (net.nwState leader).type = .Leader →
    e ∈ (net.nwState h).log →
    e.eTerm = (net.nwState leader).currentTerm →
    e ∈ (net.nwState leader).log

/-- `LeaderSublogInterface.v:15-23` (`leader_sublog_nw_invariant`). -/
def leader_sublog_nw_invariant (net : RaftNet) : Prop :=
  ∀ (leader : name (P := P))
    (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) (e : entry (P := P)),
    (net.nwState leader).type = .Leader →
    p ∈ net.nwPackets →
    p.pBody = .AppendEntries t lid pli plt es ci →
    e ∈ es →
    e.eTerm = (net.nwState leader).currentTerm →
    e ∈ (net.nwState leader).log

/-- `LeaderSublogInterface.v:25-27` (`leader_sublog_invariant` the DEF;
upstream overloads the name for the theorem — ours is
`leader_sublog_invariant_invariant`, as upstream's interface field). -/
def leader_sublog_invariant (net : RaftNet) : Prop :=
  leader_sublog_host_invariant net ∧ leader_sublog_nw_invariant net

/-- `RefinementCommonTheorems.v:19-52` (`candidateEntries_wonElection`):
a node that won an election at a candidate entry's term is no longer a
candidate — its winning tally shares a voter with the entry-creator's,
and that voter voted once. -/
theorem candidateEntries_wonElection {net : RefinedNet}
    (hovpt : one_vote_per_term net) (hcv : cronies_votes net)
    (hvrc : votes_received_cronies net) {e : entry (P := P)}
    (hce : candidateEntries e net.nwState) {h : name (P := P)}
    (hct : (net.nwState h).2.currentTerm = e.eTerm)
    (hwon : wonElection (dedup (net.nwState h).2.votesReceived) = true) :
    (net.nwState h).2.type ≠ .Candidate := by
  obtain ⟨x, hwx, himp⟩ := hce
  intro hcand
  obtain ⟨c, hcx, hch⟩ := wonElection_one_in_common _ _ hwx hwon
  have hv1 : (e.eTerm, x) ∈ (net.nwState c).1.votes := hcv e.eTerm x c hcx
  have hcc : c ∈ (net.nwState h).1.cronies (net.nwState h).2.currentTerm :=
    hvrc h c hch (Or.inr hcand)
  rw [hct] at hcc
  have hv2 : (e.eTerm, h) ∈ (net.nwState c).1.votes := hcv e.eTerm h c hcc
  have hxh : x = h := hovpt c e.eTerm x h hv1 hv2
  rw [hxh] at himp
  exact himp hct hcand

/-- `RefinementCommonTheorems.v:54-96` (`wonElection_candidateEntries_rvr`):
same, when the winning tally counts a grant still in flight — `votes_nw`
turns the consumed RequestVoteReply into a recorded vote. -/
theorem wonElection_candidateEntries_rvr {net : RefinedNet}
    (hvc : votes_correct net) (hcc : cronies_correct net)
    {e : entry (P := P)} (hce : candidateEntries e net.nwState)
    {q : RefinedPacket} (hq : q ∈ net.nwPackets)
    (hbody : q.pBody = .RequestVoteReply e.eTerm true)
    (hct : (net.nwState q.pDst).2.currentTerm = e.eTerm)
    (hwon : wonElection
      (dedup (q.pSrc :: (net.nwState q.pDst).2.votesReceived)) = true) :
    (net.nwState q.pDst).2.type ≠ .Candidate := by
  obtain ⟨hovpt, -, -⟩ := hvc
  obtain ⟨hvrc, hcv, hvnw, -⟩ := hcc
  obtain ⟨x, hwx, himp⟩ := hce
  intro hcand
  have hvsrc : (e.eTerm, q.pDst) ∈ (net.nwState q.pSrc).1.votes :=
    hvnw q e.eTerm hbody hq
  obtain ⟨c, hcx, hch⟩ := wonElection_one_in_common _ _ hwx hwon
  have hv1 : (e.eTerm, x) ∈ (net.nwState c).1.votes := hcv e.eTerm x c hcx
  have hxd : x = q.pDst := by
    rcases List.mem_cons.mp hch with rfl | hch'
    · exact hovpt q.pSrc e.eTerm x q.pDst hv1 hvsrc
    · have hcc2 : c ∈ (net.nwState q.pDst).1.cronies
          (net.nwState q.pDst).2.currentTerm :=
        hvrc q.pDst c hch' (Or.inr hcand)
      rw [hct] at hcc2
      have hv2 : (e.eTerm, q.pDst) ∈ (net.nwState c).1.votes :=
        hcv e.eTerm q.pDst c hcc2
      exact hovpt c e.eTerm x q.pDst hv1 hv2
  rw [hxd] at himp
  exact himp hct hcand

/-- `LeaderSublogProof.v:212-236` (`candidate_entries_lowered`): at BASE
level — a node that won at the term of some hosted entry is not a
candidate. `lower_prop` of `candidateEntries_wonElection` over the
election-safety chain's invariants. -/
theorem candidate_entries_lowered :
    ∀ net, raft_intermediate_reachable (P := P) net →
      ∀ (h h' : name (P := P)) (e : entry (P := P)),
        e ∈ (net.nwState h').log →
        (net.nwState h).currentTerm = e.eTerm →
        wonElection (dedup (net.nwState h).votesReceived) = true →
        (net.nwState h).type ≠ .Candidate := by
  refine lower_prop _ ?_
  intro rnet hR h h' e hin hct hwon
  obtain ⟨hovpt, -, -⟩ := votes_correct_invariant rnet hR
  obtain ⟨hvrc, hcv, -, -⟩ := cronies_correct_invariant rnet hR
  obtain ⟨hhost, -⟩ := candidate_entries_invariant rnet hR
  exact candidateEntries_wonElection hovpt hcv hvrc (hhost h' e hin) hct hwon

/-- `LeaderSublogProof.v:257-300` (`candidate_entries_lowered_rvr`):
ditto with the winning tally counting an in-flight grant. -/
theorem candidate_entries_lowered_rvr :
    ∀ net, raft_intermediate_reachable (P := P) net →
      ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
        (h' : name (P := P)) (e : entry (P := P)),
        e ∈ (net.nwState h').log →
        p ∈ net.nwPackets → p.pBody = .RequestVoteReply e.eTerm true →
        (net.nwState p.pDst).currentTerm = e.eTerm →
        wonElection
          (dedup (p.pSrc :: (net.nwState p.pDst).votesReceived)) = true →
        (net.nwState p.pDst).type ≠ .Candidate := by
  refine lower_prop _ ?_
  intro rnet hR p h' e hin hp hbody hct hwon
  have hvc := votes_correct_invariant rnet hR
  have hcc := cronies_correct_invariant rnet hR
  obtain ⟨hhost, -⟩ := candidate_entries_invariant rnet hR
  replace hp : p ∈ rnet.nwPackets.map deghost_packet := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact wonElection_candidateEntries_rvr hvc hcc (hhost h' e hin) hq hbody
    hct hwon

/-- `LeaderSublogProof.v:302-372` (`candidate_entries_lowered_nw`): the
entry source is an in-flight AppendEntries instead of a hosted log. -/
theorem candidate_entries_lowered_nw :
    ∀ net, raft_intermediate_reachable (P := P) net →
      ∀ (h : name (P := P))
        (p : Packet (raft_base_params (P := P)) raft_multi_params)
        (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
        (es : List (entry (P := P))) (ci : logIndex) (e : entry (P := P)),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
        e ∈ es →
        (net.nwState h).currentTerm = e.eTerm →
        wonElection (dedup (net.nwState h).votesReceived) = true →
        (net.nwState h).type ≠ .Candidate := by
  refine lower_prop _ ?_
  intro rnet hR h p t lid pli plt es ci e hp hbody he hct hwon
  obtain ⟨hovpt, -, -⟩ := votes_correct_invariant rnet hR
  obtain ⟨hvrc, hcv, -, -⟩ := cronies_correct_invariant rnet hR
  obtain ⟨-, hnwce⟩ := candidate_entries_invariant rnet hR
  replace hp : p ∈ rnet.nwPackets.map deghost_packet := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact candidateEntries_wonElection hovpt hcv hvrc
    (hnwce q t lid pli plt es ci hq hbody e he) hct hwon

/-- `LeaderSublogProof.v:374-443` (`candidate_entries_lowered_nw_rvr`):
both the entry and the counted grant are in flight. -/
theorem candidate_entries_lowered_nw_rvr :
    ∀ net, raft_intermediate_reachable (P := P) net →
      ∀ (p' p : Packet (raft_base_params (P := P)) raft_multi_params)
        (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
        (es : List (entry (P := P))) (ci : logIndex) (e : entry (P := P)),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
        e ∈ es →
        p' ∈ net.nwPackets → p'.pBody = .RequestVoteReply e.eTerm true →
        (net.nwState p'.pDst).currentTerm = e.eTerm →
        wonElection
          (dedup (p'.pSrc :: (net.nwState p'.pDst).votesReceived)) = true →
        (net.nwState p'.pDst).type ≠ .Candidate := by
  refine lower_prop _ ?_
  intro rnet hR p' p t lid pli plt es ci e hp hbody he hp' hbody' hct hwon
  have hvc := votes_correct_invariant rnet hR
  have hcc := cronies_correct_invariant rnet hR
  obtain ⟨-, hnwce⟩ := candidate_entries_invariant rnet hR
  replace hp : p ∈ rnet.nwPackets.map deghost_packet := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  replace hp' : p' ∈ rnet.nwPackets.map deghost_packet := hp'
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hp'
  exact wonElection_candidateEntries_rvr hvc hcc
    (hnwce q t lid pli plt es ci hq hbody e he) hq' hbody' hct hwon

/-- `LeaderSublogProof.v:85-121` (`leader_sublog_invariant_subset`),
specialized to one-node updates: the invariant transports across a step
that keeps the updated node's log and only demotes its type (a leader
post-step was a leader pre-step at the same term), provided every
surviving AppendEntries packet is old. -/
theorem leader_sublog_of_update {net : RaftNet}
    {ps' : List (Packet (raft_base_params (P := P)) raft_multi_params)}
    {st' : name (P := P) → raft_data (P := P)}
    {u : name (P := P)} {d : raft_data (P := P)}
    (hP : leader_sublog_invariant net)
    (hst : ∀ h', st' h' = update net.nwState u d h')
    (hpkts : ∀ p', p' ∈ ps' →
      (∃ t lid pli plt es ci,
        p'.pBody = msg.AppendEntries (P := P) t lid pli plt es ci) →
      p' ∈ net.nwPackets)
    (hlog : d.log = (net.nwState u).log)
    (hty : d.type = .Leader →
      d.currentTerm = (net.nwState u).currentTerm ∧
      (net.nwState u).type = .Leader) :
    leader_sublog_invariant ⟨ps', st'⟩ := by
  obtain ⟨hh, hn⟩ := hP
  have hlog' : ∀ h, (st' h).log = (net.nwState h).log := by
    intro h
    rw [hst h]
    by_cases heq : h = u
    · rw [heq, update_same]
      exact hlog
    · rw [update_neq _ _ heq]
  have hty' : ∀ h, (st' h).type = .Leader →
      (net.nwState h).type = .Leader ∧
      (net.nwState h).currentTerm = (st' h).currentTerm := by
    intro h hl
    rw [hst h] at hl ⊢
    by_cases heq : h = u
    · rw [heq, update_same] at hl ⊢
      obtain ⟨hct, htyu⟩ := hty hl
      exact ⟨htyu, hct.symm⟩
    · rw [update_neq _ _ heq] at hl ⊢
      exact ⟨hl, rfl⟩
  constructor
  · intro L e h0 htyL hin hterm
    replace htyL : (st' L).type = .Leader := htyL
    replace hin : e ∈ (st' h0).log := hin
    replace hterm : e.eTerm = (st' L).currentTerm := hterm
    show e ∈ (st' L).log
    obtain ⟨htyL0, hct0⟩ := hty' L htyL
    rw [hlog' h0] at hin
    rw [hlog' L]
    exact hh L e h0 htyL0 hin (hterm.trans hct0.symm)
  · intro L p t lid pli plt es ci e htyL hp hbody he hterm
    replace htyL : (st' L).type = .Leader := htyL
    replace hp : p ∈ ps' := hp
    replace hterm : e.eTerm = (st' L).currentTerm := hterm
    show e ∈ (st' L).log
    obtain ⟨htyL0, hct0⟩ := hty' L htyL
    rw [hlog' L]
    exact hn L p t lid pli plt es ci e htyL0
      (hpkts p hp ⟨t, lid, pli, plt, es, ci, hbody⟩) hbody he
      (hterm.trans hct0.symm)

/-- `LeaderSublogProof.v:527-546` (`leader_sublog_invariant_invariant`) —
BASE layer, named as upstream's interface field (the bare name is the
definition above). -/
theorem leader_sublog_invariant_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      leader_sublog_invariant net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init (`LeaderSublogProof.v:520-525`): everyone a follower, no packets
    constructor
    · intro L e h0 htyL _hin _hterm
      exact nomatch htyL
    · intro L p t lid pli plt es ci e _htyL hp _hbody _he _hterm
      exact nomatch hp
  · -- client_request (`:116-138`): the one_leader_per_term case
    intro h net st' ps' out d l client id c hcr hP hreach hst hps
    obtain ⟨htyd, hctd, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h) client id c hcr
    have hcases := handleClientRequest_log h (net.nwState h) client id c hcr
    have hgrow : ∀ e ∈ (net.nwState h).log, e ∈ d.log := by
      intro e he
      unfold handleClientRequest at hcr
      split at hcr
      all_goals simp only [Prod.mk.injEq] at hcr
      all_goals obtain ⟨-, rfl, -⟩ := hcr
      · exact List.mem_cons_of_mem _ he
      · exact he
    have holpt := one_leader_per_term_invariant net hreach
    obtain ⟨hh, hn⟩ := hP
    -- pointwise state facts: log grows only at h; type/term preserved
    have hmem : ∀ L (e' : entry (P := P)),
        e' ∈ (net.nwState L).log → e' ∈ (st' L).log := by
      intro L e' he'
      rw [hst L]
      by_cases heq : L = h
      · rw [heq, update_same]
        rw [heq] at he'
        exact hgrow _ he'
      · rw [update_neq _ _ heq]
        exact he'
    have htyfact : ∀ L, (st' L).type = (net.nwState L).type := by
      intro L
      rw [hst L]
      by_cases heq : L = h
      · rw [heq, update_same]
        exact htyd
      · rw [update_neq _ _ heq]
    have hctfact : ∀ L, (st' L).currentTerm = (net.nwState L).currentTerm := by
      intro L
      rw [hst L]
      by_cases heq : L = h
      · rw [heq, update_same]
        exact hctd
      · rw [update_neq _ _ heq]
    constructor
    · intro L e h0 htyL hin hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hin : e ∈ (st' h0).log := hin
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      rw [htyfact L] at htyL
      rw [hctfact L] at hterm
      rw [hst h0] at hin
      by_cases heq : h0 = h
      · rw [heq, update_same] at hin
        rcases hcases e hin with hold | ⟨hterm2, htyh⟩
        · exact hmem L e (hh L e h htyL hold hterm)
        · -- fresh entry: its term is h's current term and h leads — so L = h
          have hLh : L = h :=
            holpt L h (by rw [← hterm, hterm2]) htyL htyh
          rw [hst L, hLh, update_same]
          exact hin
      · rw [update_neq _ _ heq] at hin
        exact hmem L e (hh L e h0 htyL hin hterm)
    · intro L p t lid pli plt es ci e htyL hp hbody he hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hp : p ∈ ps' := hp
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      rw [htyfact L] at htyL
      rw [hctfact L] at hterm
      have hpold : p ∈ net.nwPackets := by
        rcases hps p hp with h1 | h1
        · exact h1
        · rw [hl] at h1
          simp [send_packets] at h1
      exact hmem L e (hn L p t lid pli plt es ci e htyL hpold hbody he hterm)
  · -- timeout (`:140-156`): only RequestVote messages; candidacy demotes
    intro net h st' ps' out d l hto hP _hreach hst hps
    obtain ⟨hlog, hbr, hmsgs⟩ := handleTimeout_spec h (net.nwState h) hto
    refine leader_sublog_of_update hP hst ?_ hlog ?_
    · intro p' hp' ⟨t', lid, pli, plt, es, ci, hbody⟩
      rcases hps p' hp' with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
        obtain ⟨t2, cid, lli, llt, hq2⟩ := hmsgs m0 hm0
        replace hbody : m0.2 = msg.AppendEntries t' lid pli plt es ci := hbody
        rw [hq2] at hbody
        exact nomatch hbody
    · intro hl
      rcases hbr with ⟨hct, hty, -, -⟩ | ⟨-, hty, -, -, -⟩
      · rw [hty] at hl
        exact ⟨hct, hl⟩
      · rw [hty] at hl
        exact nomatch hl
  · -- append_entries (`:158-174`): a leader must have rejected
    intro xs p ys net st' ps' d m t n0 pli plt es ci hae _hbody hP _hreach
      hpkts hst hps
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst) t n0 pli plt es
        ci hae
    have hlogcases :=
      handleAppendEntries_log p.pDst (net.nwState p.pDst) t n0 pli plt es
        ci hae
    obtain ⟨hh, hn⟩ := hP
    -- membership in the new net's log at L, given membership at base
    have hentry : ∀ L (e' : entry (P := P)), e' ∈ (st' L).log →
        e' ∈ (net.nwState L).log ∨ (e' ∈ es ∧ L = p.pDst) := by
      intro L e' he'
      rw [hst L] at he'
      by_cases heq : L = p.pDst
      · rw [heq, update_same] at he'
        rcases hlogcases e' he' with hold | ⟨hnew, -⟩
        · exact Or.inl (heq ▸ hold)
        · exact Or.inr ⟨hnew, heq⟩
      · rw [update_neq _ _ heq] at he'
        exact Or.inl he'
    constructor
    · intro L e h0 htyL hin hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hin : e ∈ (st' h0).log := hin
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      by_cases hL : L = p.pDst
      · -- the receiver leads afterwards: it rejected, state untouched
        rw [hst L, hL, update_same] at htyL hterm ⊢
        have hd : d = net.nwState p.pDst :=
          handleAppendEntries_reject_of_not_follower p.pDst
            (net.nwState p.pDst) t n0 pli plt es ci hae
            (by rw [htyL]; exact fun heq => nomatch heq)
        rw [hd] at htyL hterm ⊢
        rcases hentry h0 e hin with hold | ⟨hnew, -⟩
        · exact hh p.pDst e h0 htyL hold hterm
        · exact hn p.pDst p t n0 pli plt es ci e htyL hp_in _hbody hnew hterm
      · rw [hst L, update_neq _ _ hL] at htyL hterm ⊢
        rcases hentry h0 e hin with hold | ⟨hnew, -⟩
        · exact hh L e h0 htyL hold hterm
        · exact hn L p t n0 pli plt es ci e htyL hp_in _hbody hnew hterm
    · intro L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq hbody2 he hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hq : q ∈ ps' := hq
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      have hq_old : q ∈ net.nwPackets := by
        rcases hps q hq with h1 | h1
        · rw [hpkts]
          exact mem_of_mem_remove_middle h1
        · exfalso
          rw [h1] at hbody2
          replace hbody2 : m = msg.AppendEntries t2 lid2 pli2 plt2 es2 ci2 :=
            hbody2
          rw [hmshape] at hbody2
          exact nomatch hbody2
      by_cases hL : L = p.pDst
      · rw [hst L, hL, update_same] at htyL hterm ⊢
        have hd : d = net.nwState p.pDst :=
          handleAppendEntries_reject_of_not_follower p.pDst
            (net.nwState p.pDst) t n0 pli plt es ci hae
            (by rw [htyL]; exact fun heq => nomatch heq)
        rw [hd] at htyL hterm ⊢
        exact hn p.pDst q t2 lid2 pli2 plt2 es2 ci2 e htyL hq_old hbody2 he
          hterm
      · rw [hst L, update_neq _ _ hL] at htyL hterm ⊢
        exact hn L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq_old hbody2 he hterm
  · -- append_entries_reply (`:176-192`): log kept, type only demotes,
    -- no messages
    intro xs p ys net st' ps' d m t es res haer _hbody hP _hreach hpkts hst
      hps
    obtain ⟨-, hbr, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst) p.pSrc t es
        res haer
    refine leader_sublog_of_update hP hst ?_
      (handleAppendEntriesReply_log p.pDst (net.nwState p.pDst) p.pSrc t es
        res haer) ?_
    · intro p' hp' _
      rcases hps p' hp' with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · rw [hl] at h1
        simp [send_packets] at h1
    · intro hlead
      rcases hbr with ⟨hct, -, hty⟩ | ⟨-, -, hty⟩
      · rw [hty] at hlead
        exact ⟨hct, hlead⟩
      · have : serverType.Follower = .Leader := hty.symm.trans hlead
        exact nomatch this
  · -- request_vote (`:194-210`): log kept, type only demotes, reply is RVR
    intro xs p ys net st' ps' d m t cid lli llt hrv _hbody hP _hreach hpkts
      hst hps
    obtain ⟨-, -, hbr, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst) t p.pSrc lli llt hrv
    obtain ⟨t'', v'', hmshape⟩ :=
      handleRequestVote_reply_shape p.pDst (net.nwState p.pDst) t p.pSrc lli
        llt hrv
    refine leader_sublog_of_update hP hst ?_
      (handleRequestVote_log p.pDst (net.nwState p.pDst) t p.pSrc lli llt
        hrv) ?_
    · intro p' hp' ⟨t2, lid2, pli2, plt2, es2, ci2, hbody2⟩
      rcases hps p' hp' with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody2
        replace hbody2 : m = msg.AppendEntries t2 lid2 pli2 plt2 es2 ci2 :=
          hbody2
        rw [hmshape] at hbody2
        exact nomatch hbody2
    · intro hlead
      rcases hbr with ⟨hct, hty⟩ | hty
      · rw [hty] at hlead
        exact ⟨hct, hlead⟩
      · have : serverType.Follower = .Leader := hty.symm.trans hlead
        exact nomatch this
  · -- request_vote_reply (`:445-473`): THE case — a fresh win at an
    -- entry-bearing term contradicts CandidateEntries, lowered
    intro xs p ys net st' ps' d t v hrvr _hbody hP hreach hpkts hst hps
    have hlogd : d.log = (net.nwState p.pDst).log := by
      rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst) p.pSrc t v
    obtain ⟨-, -, -, hlead4⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst) p.pSrc t v hrvr
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    obtain ⟨hh, hn⟩ := hP
    have hlog' : ∀ h, (st' h).log = (net.nwState h).log := by
      intro h
      rw [hst h]
      by_cases heq : h = p.pDst
      · rw [heq, update_same]
        exact hlogd
      · rw [update_neq _ _ heq]
    constructor
    · intro L e h0 htyL hin hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hin : e ∈ (st' h0).log := hin
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      rw [hlog' h0] at hin
      rw [hlog' L]
      by_cases hL : L = p.pDst
      · rw [hst L, hL, update_same] at htyL hterm
        rcases hlead4 htyL with heqd | ⟨hcand, -, -⟩
        · rw [heqd] at htyL hterm
          rw [hL]
          exact hh p.pDst e h0 htyL hin hterm
        · exfalso
          obtain ⟨-, hv, hteq, hctd, -, -, hwon⟩ :=
            handleRequestVoteReply_leader_transition p.pDst
              (net.nwState p.pDst) p.pSrc t v hrvr
              (by rw [hcand]; exact fun heq => nomatch heq) htyL
          have hct2 : (net.nwState p.pDst).currentTerm = e.eTerm := by
            rw [hterm, hctd]
          refine candidate_entries_lowered_rvr net hreach p h0 e hin hp_in
            ?_ hct2 ?_ hcand
          · rw [_hbody, hv]
            rw [← hct2, hteq]
          · exact hwon
      · rw [hst L, update_neq _ _ hL] at htyL hterm
        exact hh L e h0 htyL hin hterm
    · intro L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq hbody2 he hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hq : q ∈ ps' := hq
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      have hq_old : q ∈ net.nwPackets := by
        rw [hpkts]
        exact mem_of_mem_remove_middle (hps q hq)
      rw [hlog' L]
      by_cases hL : L = p.pDst
      · rw [hst L, hL, update_same] at htyL hterm
        rcases hlead4 htyL with heqd | ⟨hcand, -, -⟩
        · rw [heqd] at htyL hterm
          rw [hL]
          exact hn p.pDst q t2 lid2 pli2 plt2 es2 ci2 e htyL hq_old hbody2
            he hterm
        · exfalso
          obtain ⟨-, hv, hteq, hctd, -, -, hwon⟩ :=
            handleRequestVoteReply_leader_transition p.pDst
              (net.nwState p.pDst) p.pSrc t v hrvr
              (by rw [hcand]; exact fun heq => nomatch heq) htyL
          have hct2 : (net.nwState p.pDst).currentTerm = e.eTerm := by
            rw [hterm, hctd]
          refine candidate_entries_lowered_nw_rvr net hreach p q t2 lid2
            pli2 plt2 es2 ci2 e hq_old hbody2 he hp_in ?_ hct2 ?_ hcand
          · rw [_hbody, hv]
            rw [← hct2, hteq]
          · exact hwon
      · rw [hst L, update_neq _ _ hL] at htyL hterm
        exact hn L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq_old hbody2 he hterm
  · -- do_leader (`:122-149`): new AppendEntries carry the leader's own
    -- entries — the host invariant covers them
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hct, -, hty, -, hlog, -⟩ := doLeader_spec d h hdl
    have hmsgs := doLeader_messages d h hdl
    obtain ⟨hh, hn⟩ := hP
    have hlog' : ∀ h', (st' h').log = (net.nwState h').log := by
      intro h'
      rw [hst h']
      by_cases heq : h' = h
      · rw [heq, update_same, hlog, hstate]
      · rw [update_neq _ _ heq]
    have hty' : ∀ h', (st' h').type = (net.nwState h').type := by
      intro h'
      rw [hst h']
      by_cases heq : h' = h
      · rw [heq, update_same, hty, hstate]
      · rw [update_neq _ _ heq]
    have hct' : ∀ h', (st' h').currentTerm = (net.nwState h').currentTerm := by
      intro h'
      rw [hst h']
      by_cases heq : h' = h
      · rw [heq, update_same, hct, hstate]
      · rw [update_neq _ _ heq]
    constructor
    · intro L e h0 htyL hin hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hin : e ∈ (st' h0).log := hin
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      rw [hty' L] at htyL
      rw [hct' L] at hterm
      rw [hlog' h0] at hin
      rw [hlog' L]
      exact hh L e h0 htyL hin hterm
    · intro L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq hbody2 he hterm
      replace htyL : (st' L).type = .Leader := htyL
      replace hq : q ∈ ps' := hq
      replace hterm : e.eTerm = (st' L).currentTerm := hterm
      show e ∈ (st' L).log
      rw [hty' L] at htyL
      rw [hct' L] at hterm
      rw [hlog' L]
      rcases hps q hq with h1 | h1
      · exact hn L q t2 lid2 pli2 plt2 es2 ci2 e htyL h1 hbody2 he hterm
      · -- a fresh AppendEntries: its entries are h's own log entries
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
        obtain ⟨pi, pt, ci3, es3, hbody3, hsub⟩ := hmsgs m0 hm0
        replace hbody2 : m0.2 = msg.AppendEntries t2 lid2 pli2 plt2 es2 ci2 :=
          hbody2
        rw [hbody3] at hbody2
        injection hbody2 with h1 h2 h3 h4 h5 h6
        subst h5
        have hin0 : e ∈ (net.nwState h).log := by
          rw [hstate]
          exact hsub e he
        exact hh L e h htyL hin0 hterm
  · -- do_generic_server (`:475-495`): log/type/term kept, no messages
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hlog, hty, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    refine leader_sublog_of_update hP hst ?_ (by rw [hlog, hstate]) ?_
    · intro p' hp' _
      rcases hps p' hp' with h1 | h1
      · exact h1
      · rw [hms] at h1
        simp [send_packets] at h1
    · intro hlead
      rw [hty, ← hstate] at hlead
      rw [hct, ← hstate]
      exact ⟨rfl, hlead⟩
  · -- state_same_packet_subset (`:497-506`)
    intro net net' hstates hsub hP _hreach
    obtain ⟨hh, hn⟩ := hP
    constructor
    · intro L e h0 htyL hin hterm
      rw [← hstates L] at htyL hterm ⊢
      rw [← hstates h0] at hin
      exact hh L e h0 htyL hin hterm
    · intro L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq hbody2 he hterm
      rw [← hstates L] at htyL hterm ⊢
      exact hn L q t2 lid2 pli2 plt2 es2 ci2 e htyL (hsub q hq) hbody2 he
        hterm
  · -- reboot (`:508-518`): a rebooted node is a follower; log kept
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    obtain ⟨hh, hn⟩ := hP
    have hlog' : ∀ h', (net'.nwState h').log = (net.nwState h').log := by
      intro h'
      rw [hst h']
      by_cases heq : h' = h
      · rw [heq, update_same, ← hrb]
        show (reboot d).log = _
        rw [hstate]
        rfl
      · rw [update_neq _ _ heq]
    have hty' : ∀ h', (net'.nwState h').type = .Leader →
        (net.nwState h').type = .Leader ∧
        (net.nwState h').currentTerm = (net'.nwState h').currentTerm := by
      intro h' hl
      rw [hst h'] at hl ⊢
      by_cases heq : h' = h
      · rw [heq, update_same] at hl
        rw [← hrb] at hl
        exact nomatch hl
      · rw [update_neq _ _ heq] at hl ⊢
        exact ⟨hl, rfl⟩
    constructor
    · intro L e h0 htyL hin hterm
      obtain ⟨htyL0, hct0⟩ := hty' L htyL
      rw [hlog' h0] at hin
      rw [hlog' L]
      exact hh L e h0 htyL0 hin (hterm.trans hct0.symm)
    · intro L q t2 lid2 pli2 plt2 es2 ci2 e htyL hq hbody2 he hterm
      obtain ⟨htyL0, hct0⟩ := hty' L htyL
      rw [hlog' L]
      rw [← hpkts] at hq
      exact hn L q t2 lid2 pli2 plt2 es2 ci2 e htyL0 hq hbody2 he
        (hterm.trans hct0.symm)

/-! ## The log-matching support layer (`CommonTheorems.v` slices)

The `entries_match`/contiguity machinery `LogMatchingProof.v` rides.
Direct constructive inductions, per the lane's axiom-set discipline
(GAP-4); sources cited per lemma. -/

omit O in
/-- `CommonTheorems.v:593-598` (`entries_match_refl`). -/
theorem entries_match_refl (l : List (entry (P := P))) : entries_match l l :=
  fun _ _ _ _ _ _ _ _ => Iff.rfl

omit O in
/-- `CommonTheorems.v:600-612` (`entries_match_sym`). -/
theorem entries_match_sym {xs ys : List (entry (P := P))}
    (h : entries_match xs ys) : entries_match ys xs := by
  intro e e' e'' h1 h2 h3 h4 h5
  exact (h e' e e'' h1.symm h2.symm h4 h3 (h1 ▸ h5)).symm

omit O in
/-- `CommonTheorems.v:12-22` (`uniqueIndices_elim_eq`). -/
theorem uniqueIndices_elim_eq {xs : List (entry (P := P))}
    {x y : entry (P := P)} (hu : uniqueIndices xs) (hx : x ∈ xs)
    (hy : y ∈ xs) (heq : x.eIndex = y.eIndex) : x = y := by
  induction xs with
  | nil => exact nomatch hx
  | cons a l ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hu
    rcases List.mem_cons.mp hx with rfl | hx' <;>
      rcases List.mem_cons.mp hy with h | hy'
    · rw [h]
    · exact absurd heq (hhead _ (List.mem_map_of_mem hy'))
    · rw [h] at heq
      exact absurd heq.symm (hhead _ (List.mem_map_of_mem hx'))
    · exact ih htail hx' hy'

omit O in
/-- `CommonTheorems.v:726-739` (`rachet`). -/
theorem rachet {x x' : entry (P := P)} {xs ys : List (entry (P := P))}
    (heq : x.eIndex = x'.eIndex) (hx : x ∈ xs) (hx' : x' ∈ ys)
    (hx'2 : x' ∈ xs) (hu : uniqueIndices xs) : x ∈ ys := by
  rw [uniqueIndices_elim_eq hu hx hx'2 heq]
  exact hx'

omit O in
/-- `CommonTheorems.v:741-757` (`findAtIndex_intro`). -/
theorem findAtIndex_intro {l : List (entry (P := P))} {i : logIndex}
    {e : entry (P := P)} (hs : sorted l) (he : e ∈ l) (hi : e.eIndex = i)
    (hu : uniqueIndices l) : findAtIndex l i = some e := by
  induction l with
  | nil => exact nomatch he
  | cons a as ih =>
    obtain ⟨ha, hs'⟩ := hs
    obtain ⟨hhead, hu'⟩ := List.pairwise_cons.mp hu
    unfold findAtIndex
    split
    · rename_i hcond
      simp only [beq_iff_eq] at hcond
      rcases List.mem_cons.mp he with rfl | he'
      · rfl
      · exact absurd (hcond.trans hi.symm)
          (hhead _ (List.mem_map_of_mem he'))
    · rename_i hne
      simp only [beq_iff_eq] at hne
      rcases List.mem_cons.mp he with rfl | he'
      · exact absurd hi hne
      · split
        · rename_i hlt
          simp only [Nat.blt_eq] at hlt
          have h1 := (ha e he').1
          rw [hi] at h1
          exact absurd hlt (Nat.lt_asymm h1)
        · exact ih hs' he' hu'

omit O in
/-- `CommonTheorems.v:269-280` (`findAtIndex_None`). -/
theorem findAtIndex_None {xs : List (entry (P := P))} {i : logIndex}
    {x : entry (P := P)} (hs : sorted xs) (hfind : findAtIndex xs i = none)
    (hx : x ∈ xs) : x.eIndex ≠ i := by
  induction xs with
  | nil => exact nomatch hx
  | cons a as ih =>
    obtain ⟨ha, hs'⟩ := hs
    unfold findAtIndex at hfind
    split at hfind
    · exact nomatch hfind
    · rename_i hne
      simp only [beq_iff_eq] at hne
      split at hfind
      · rename_i hlt
        simp only [Nat.blt_eq] at hlt
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hne
        · exact Nat.ne_of_lt (Nat.lt_trans (ha x hx').1 hlt)
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact hne
        · exact ih hs' hfind hx'

omit O in
/-- `CommonTheorems.v:540-551` (`findAtIndex_uniq_equal`). -/
theorem findAtIndex_uniq_equal {e e' : entry (P := P)}
    {es : List (entry (P := P))}
    (hfind : findAtIndex es e.eIndex = some e') (he : e ∈ es)
    (hu : uniqueIndices es) : e = e' := by
  obtain ⟨hmem, hidx⟩ := findAtIndex_elim hfind
  exact uniqueIndices_elim_eq hu he hmem hidx.symm

omit O in
/-- `CommonTheorems.v:168-178` (`removeAfterIndex_le_In`). -/
theorem removeAfterIndex_le_In {xs : List (entry (P := P))} {i : logIndex}
    {x : entry (P := P)} (hle : x.eIndex ≤ i) (hx : x ∈ xs) :
    x ∈ removeAfterIndex xs i := by
  induction xs with
  | nil => exact nomatch hx
  | cons a as ih =>
    unfold removeAfterIndex
    split
    · exact hx
    · rename_i hgt
      simp only [Nat.ble_eq] at hgt
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd hle hgt
      · exact ih hx'

omit O in
/-- `CommonTheorems.v:334-347` (`findGtIndex_sufficient`). -/
theorem findGtIndex_sufficient {es : List (entry (P := P))}
    {e : entry (P := P)} {x : logIndex} (hs : sorted es) (he : e ∈ es)
    (hgt : e.eIndex > x) : e ∈ findGtIndex es x := by
  induction es with
  | nil => exact nomatch he
  | cons a as ih =>
    obtain ⟨ha, hs'⟩ := hs
    unfold findGtIndex
    split
    · rcases List.mem_cons.mp he with rfl | he'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hs' he')
    · rename_i hng
      simp only [Nat.blt_eq, Nat.not_lt] at hng
      rcases List.mem_cons.mp he with rfl | he'
      · exact absurd hgt (Nat.not_lt.mpr hng)
      · exact absurd hgt
          (Nat.lt_asymm (Nat.lt_of_lt_of_le (ha e he').1 hng))

omit O in
/-- `CommonTheorems.v:532-538` (`findGtIndex_max`). -/
theorem findGtIndex_max (entries : List (entry (P := P))) (x : logIndex) :
    maxIndex (findGtIndex entries x) ≤ maxIndex entries := by
  cases entries with
  | nil => exact Nat.le_refl _
  | cons a as =>
    unfold findGtIndex
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _

omit O in
/-- `CommonTheorems.v:74-81` (`S_maxIndex_not_in`). -/
theorem S_maxIndex_not_in {l : List (entry (P := P))} {e : entry (P := P)}
    (hs : sorted l) (he : e ∈ l) : e.eIndex ≠ maxIndex l + 1 := by
  exact Nat.ne_of_lt (Nat.lt_succ_of_le (maxIndex_is_max hs he))

omit O in
/-- `CommonTheorems.v:399-405` (`maxIndex_app`). -/
theorem maxIndex_app (l l' : List (entry (P := P))) :
    maxIndex (l ++ l') = maxIndex l ∨
    (maxIndex (l ++ l') = maxIndex l' ∧ l = []) := by
  cases l with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | cons a as => exact Or.inl rfl

omit O in
/-- `CommonTheorems.v:417-434` (`maxIndex_removeAfterIndex`). -/
theorem maxIndex_removeAfterIndex {l : List (entry (P := P))} {i : logIndex}
    {e : entry (P := P)} (hs : sorted l) (he : e ∈ l) (hi : e.eIndex = i) :
    maxIndex (removeAfterIndex l i) = i := by
  induction l with
  | nil => exact nomatch he
  | cons a as ih =>
    obtain ⟨ha, hs'⟩ := hs
    unfold removeAfterIndex
    split
    · rename_i hle
      simp only [Nat.ble_eq] at hle
      show a.eIndex = i
      rcases List.mem_cons.mp he with rfl | he'
      · exact hi
      · have h2 : a.eIndex ≤ e.eIndex := hi.symm ▸ hle
        exact absurd h2 (Nat.not_le.mpr (ha e he').1)
    · rename_i hgt
      simp only [Nat.ble_eq, Nat.not_le] at hgt
      rcases List.mem_cons.mp he with rfl | he'
      · exact absurd hi (Nat.ne_of_gt hgt)
      · exact ih hs' he'

/-- `CommonTheorems.v:349-357` (`contiguous_range_exact_lo`). -/
def contiguous_range_exact_lo (xs : List (entry (P := P)))
    (lo : logIndex) : Prop :=
  (∀ i, lo < i ∧ i ≤ maxIndex xs → ∃ e, entry.eIndex e = i ∧ e ∈ xs) ∧
  (∀ e, e ∈ xs → lo < entry.eIndex e)

omit O in
/-- `CommonTheorems.v:1133-1177` (`entries_match_scratch`) — the
`pli = 0` wholesale-replacement case. (Upstream's hypothesis carries a
vacuous `0 ≠ 0 → …` conjunct; dropped here.) -/
theorem entries_match_scratch {es ys : List (entry (P := P))}
    (hes : sorted es) (huys : uniqueIndices ys)
    (hmatch : ∀ e1 e2, e1.eIndex = e2.eIndex → e1.eTerm = e2.eTerm →
      e1 ∈ es → e2 ∈ ys →
      ∀ e3, e3.eIndex ≤ e1.eIndex → e3 ∈ es → e3 ∈ ys)
    (hcontig : ∀ i, 0 < i ∧ i ≤ maxIndex es → ∃ e, entry.eIndex e = i ∧ e ∈ es)
    (hposy : ∀ y ∈ ys, 0 < y.eIndex) :
    entries_match es ys := by
  intro e e' e'' h1 h2 h3 h4 h5
  constructor
  · intro hin
    exact hmatch e e' h1 h2 h3 h4 e'' h5 hin
  · intro hin
    obtain ⟨x, hxi, hxes⟩ := hcontig e''.eIndex
      ⟨hposy e'' hin, Nat.le_trans h5 (maxIndex_is_max hes h3)⟩
    exact rachet hxi.symm hin hxes
      (hmatch e e' h1 h2 h3 h4 x (Nat.le_trans (Nat.le_of_eq hxi) h5) hxes)
      huys

omit O in
/-- `CommonTheorems.v:1196-1257` (`entries_match_append`) — the
truncate-and-splice case. -/
theorem entries_match_append {xs ys es : List (entry (P := P))}
    {ple : entry (P := P)} {pli : logIndex} {plt : term}
    (hxs : sorted xs) (hys : sorted ys) (hes : sorted es)
    (hm : entries_match xs ys)
    (hmatch : ∀ e1 e2, e1.eIndex = e2.eIndex → e1.eTerm = e2.eTerm →
      e1 ∈ es → e2 ∈ ys →
      (∀ e3, e3.eIndex ≤ e1.eIndex → e3 ∈ es → e3 ∈ ys) ∧
      (pli ≠ 0 → ∃ e4, e4.eIndex = pli ∧ e4.eTerm = plt ∧ e4 ∈ ys))
    (hcontig : ∀ i, pli < i ∧ i ≤ maxIndex es →
      ∃ e, entry.eIndex e = i ∧ e ∈ es)
    (hgt : ∀ e ∈ es, pli < e.eIndex)
    (hfind : findAtIndex xs pli = some ple)
    (hplt : ple.eTerm = plt) (hpli : pli ≠ 0) :
    entries_match (es ++ removeAfterIndex xs pli) ys := by
  obtain ⟨hplemem, hpleidx⟩ := findAtIndex_elim hfind
  intro e e' e'' h1 h2 h3 h4 h5
  constructor
  · intro hin
    rcases List.mem_append.mp h3 with h3' | h3'
    · rcases List.mem_append.mp hin with hin' | hin'
      · -- e, e'' both incoming
        exact (hmatch e e' h1 h2 h3' h4).1 e'' h5 hin'
      · -- e incoming, e'' in the kept prefix: go through the pivot ple
        obtain ⟨e4, he4i, he4t, he4y⟩ := (hmatch e e' h1 h2 h3' h4).2 hpli
        have he''xs := removeAfterIndex_in hin'
        have he''le : e''.eIndex ≤ pli := removeAfterIndex_In_le hxs hin'
        exact (hm ple e4 e'' (hpleidx.trans he4i.symm)
          (hplt.trans he4t.symm) hplemem he4y
          (Nat.le_trans he''le (Nat.le_of_eq hpleidx.symm))).mp he''xs
    · rcases List.mem_append.mp hin with hin' | hin'
      · -- e in the kept prefix but e'' incoming: index order contradicts
        exact absurd
          (Nat.lt_of_lt_of_le (hgt e'' hin')
            (Nat.le_trans h5 (removeAfterIndex_In_le hxs h3')))
          (Nat.lt_irrefl pli)
      · -- both in the kept prefix
        exact (hm e e' e'' h1 h2 (removeAfterIndex_in h3') h4 h5).mp
          (removeAfterIndex_in hin')
  · intro hin
    rcases List.mem_append.mp h3 with h3' | h3'
    · obtain ⟨hall, hex⟩ := hmatch e e' h1 h2 h3' h4
      obtain ⟨e4, he4i, he4t, he4y⟩ := hex hpli
      by_cases hle : e''.eIndex ≤ pli
      · refine List.mem_append.mpr (Or.inr (removeAfterIndex_le_In hle ?_))
        exact (hm ple e4 e'' (hpleidx.trans he4i.symm)
          (hplt.trans he4t.symm) hplemem he4y
          (Nat.le_trans hle (Nat.le_of_eq hpleidx.symm))).mpr hin
      · refine List.mem_append.mpr (Or.inl ?_)
        obtain ⟨x, hxi, hxes⟩ := hcontig e''.eIndex
          ⟨Nat.lt_of_not_le hle,
           Nat.le_trans h5 (maxIndex_is_max hes h3')⟩
        exact rachet hxi.symm hin hxes
          (hall x (Nat.le_trans (Nat.le_of_eq hxi) h5) hxes)
          (sorted_uniqueIndices hys)
    · refine List.mem_append.mpr (Or.inr ?_)
      have hele := removeAfterIndex_In_le hxs h3'
      refine removeAfterIndex_le_In (Nat.le_trans h5 hele) ?_
      exact (hm e e' e'' h1 h2 (removeAfterIndex_in h3') h4 h5).mpr hin

omit O in
/-- `CommonTheorems.v:447-490` (`removeIncorrect_new_contiguous`). -/
theorem removeIncorrect_new_contiguous {new current : List (entry (P := P))}
    {prev : logIndex} {e : entry (P := P)}
    (hs : sorted current)
    (hcur : contiguous_range_exact_lo current 0)
    (hnew : contiguous_range_exact_lo new prev)
    (hecur : e ∈ current) (hei : e.eIndex = prev) :
    contiguous_range_exact_lo (new ++ removeAfterIndex current prev) 0 := by
  constructor
  · intro i ⟨hpos, hle⟩
    by_cases hip : i ≤ prev
    · obtain ⟨x, hxi, hxc⟩ := hcur.1 i
        ⟨hpos, Nat.le_trans hip (hei ▸ maxIndex_is_max hs hecur)⟩
      exact ⟨x, hxi, List.mem_append.mpr
        (Or.inr (removeAfterIndex_le_In (hxi.symm ▸ hip) hxc))⟩
    · rcases maxIndex_app new (removeAfterIndex current prev) with hmax |
        ⟨hmax, hnil⟩
      · rw [hmax] at hle
        obtain ⟨x, hxi, hxn⟩ := hnew.1 i ⟨Nat.lt_of_not_le hip, hle⟩
        exact ⟨x, hxi, List.mem_append.mpr (Or.inl hxn)⟩
      · rw [hmax, maxIndex_removeAfterIndex hs hecur hei] at hle
        exact absurd hle hip
  · intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hnew.2 x hx')
    · exact hcur.2 x (removeAfterIndex_in hx')

/-! ## log_matching (BASE) — the T3-named invariant

`LogMatchingProof.v` (1,521 lines). The statement defs are the P1 port's
(`Properties.lean`: `log_matching_hosts`/`log_matching_nw`/`log_matching`
and the `LogMatchingStatement` transfer target) — proved here, never
redefined (the unit-2 name-collision lesson). -/

/-- `LogMatchingProof.v:47-96` (`log_matching_state_same_packet_subset`):
the whole invariant transports across a step that keeps every log and
introduces no AppendEntries packet. -/
theorem log_matching_state_same_packet_subset {net net' : RaftNet}
    (hP : log_matching net)
    (hlog : ∀ h, (net'.nwState h).log = (net.nwState h).log)
    (hpkts : ∀ p, p ∈ net'.nwPackets →
      (∃ t lid pli plt es ci,
        p.pBody = msg.AppendEntries (P := P) t lid pli plt es ci) →
      p ∈ net.nwPackets) :
    log_matching net' := by
  obtain ⟨⟨hem, hcontig, hpos⟩, hnw⟩ := hP
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro h h'
    rw [hlog h, hlog h']
    exact hem h h'
  · intro h i hi
    rw [hlog h] at hi ⊢
    exact hcontig h i hi
  · intro h e he
    rw [hlog h] at he
    exact hpos h e he
  · intro p t lid pli plt es ci hp hbody
    have hp0 : p ∈ net.nwPackets :=
      hpkts p hp ⟨t, lid, pli, plt, es, ci, hbody⟩
    obtain ⟨h1, h2, h3, h4⟩ := hnw p t lid pli plt es ci hp0 hbody
    refine ⟨?_, h2, h3, ?_⟩
    · intro h e1 e2 he1 he2 hidx hterm
      rw [hlog h] at he2
      obtain ⟨ha, hb⟩ := h1 h e1 e2 he1 he2 hidx hterm
      refine ⟨?_, ?_⟩
      · intro e3 h3le h3in
        rw [hlog h]
        exact ha e3 h3le h3in
      · intro hne
        obtain ⟨e4, h4a, h4b, h4c⟩ := hb hne
        rw [hlog h]
        exact ⟨e4, h4a, h4b, h4c⟩
    · intro p' t' lid' pli' plt' es' ci' hp' hbody'
      exact h4 p' t' lid' pli' plt' es' ci'
        (hpkts p' hp' ⟨t', lid', pli', plt', es', ci', hbody'⟩) hbody'

omit O in
/-- `doLeader`'s messages in full: each is a replica message over the
leader's own (unchanged) log — `AppendEntries` at the leader's current
term whose entries are `findGtIndex log pli` and whose prevLogTerm is
resolved by `findAtIndex log pli`. -/
theorem doLeader_messages_full (st : raft_data (P := P)) (me : name (P := P))
    {os st' ms} (h : doLeader st me = (os, st', ms)) :
    ∀ q ∈ ms, ∃ pli ci,
      q.2 = msg.AppendEntries (P := P) st.currentTerm me pli
        (match findAtIndex st.log pli with
         | some e => e.eTerm
         | none => 0)
        (findGtIndex st.log pli) ci := by
  unfold doLeader at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, -, rfl⟩ := h
  all_goals intro q hq
  · simp only [List.mem_map] at hq
    obtain ⟨node, -, rfl⟩ := hq
    exact ⟨_, _, rfl⟩
  · exact nomatch hq
  · exact nomatch hq

omit O in
/-- Contiguity of a replica packet's entries (`LogMatchingProof.v`'s
doLeader nw clause 2, over the sender's contiguous log). -/
theorem replica_entries_contiguous {L : List (entry (P := P))}
    {pli : logIndex} (hs : sorted L)
    (hcontig : ∀ i, 1 ≤ i ∧ i ≤ maxIndex L →
      ∃ e, entry.eIndex e = i ∧ e ∈ L) :
    ∀ i, pli < i ∧ i ≤ maxIndex (findGtIndex L pli) →
      ∃ e, entry.eIndex e = i ∧ e ∈ findGtIndex L pli := by
  intro i ⟨hgt, hle⟩
  obtain ⟨e, hei, heL⟩ := hcontig i
    ⟨Nat.lt_of_le_of_lt (Nat.zero_le pli) hgt,
     Nat.le_trans hle (findGtIndex_max L pli)⟩
  exact ⟨e, hei, findGtIndex_sufficient hs heL (hei.symm ▸ hgt)⟩

omit O in
/-- A nonempty replica packet's nonzero prevLogIndex resolves to an
actual entry of the sender's log (via contiguity), so its prevLogTerm is
that entry's term. -/
theorem replica_prev_resolves {L : List (entry (P := P))} {pli : logIndex}
    {e1 : entry (P := P)} (hs : sorted L)
    (hcontig : ∀ i, 1 ≤ i ∧ i ≤ maxIndex L →
      ∃ e, entry.eIndex e = i ∧ e ∈ L)
    (he1 : e1 ∈ findGtIndex L pli) (hpli : pli ≠ 0) :
    ∃ ple, findAtIndex L pli = some ple ∧ ple.eIndex = pli ∧ ple ∈ L := by
  obtain ⟨he1L, he1gt⟩ := findGtIndex_necessary he1
  obtain ⟨ple, hplei, hpleL⟩ := hcontig pli
    ⟨Nat.pos_of_ne_zero hpli,
     Nat.le_trans (Nat.le_of_lt he1gt) (maxIndex_is_max hs he1L)⟩
  exact ⟨ple, findAtIndex_intro hs hpleL hplei (sorted_uniqueIndices hs),
    hplei, hpleL⟩

/-- `LogMatchingProof.v:722-749`
(`handleClientRequest_log_matching_hosts_entries_match`): the leader's
log extended by the fresh entry still matches every other host's —
same-term entries elsewhere are already in the leader's log
(`leader_sublog`), and the fresh index tops it. -/
theorem handleClientRequest_entries_match {net : RaftNet}
    {h h' : name (P := P)} {ne : entry (P := P)}
    (hlmh : log_matching_hosts net)
    (hlsh : leader_sublog_host_invariant net)
    (hsh : logs_sorted_host net)
    (hty : (net.nwState h).type = .Leader)
    (hidx : ne.eIndex = maxIndex (net.nwState h).log + 1)
    (hterm : ne.eTerm = (net.nwState h).currentTerm) :
    entries_match (ne :: (net.nwState h).log) (net.nwState h').log := by
  obtain ⟨hem, -, -⟩ := hlmh
  intro e e' e'' h1 h2 h3 h4 h5
  constructor
  · intro hin
    rcases List.mem_cons.mp h3 with rfl | h3'
    · -- e is the fresh entry: its twin e' elsewhere would already be in
      -- the leader's log at an impossible index
      have he'h : e' ∈ (net.nwState h).log :=
        hlsh h e' h' hty h4 (h2.symm.trans hterm)
      exact absurd (h1.symm.trans hidx) (S_maxIndex_not_in (hsh h) he'h)
    · rcases List.mem_cons.mp hin with rfl | hin'
      · -- e'' fresh but bounded by an old entry: impossible index
        have hmax := maxIndex_is_max (hsh h) h3'
        rw [hidx] at h5
        exact absurd (Nat.le_trans h5 hmax) (Nat.not_succ_le_self _)
      · exact (hem h h' e e' e'' h1 h2 h3' h4 h5).mp hin'
  · intro hin
    rcases List.mem_cons.mp h3 with rfl | h3'
    · have he'h : e' ∈ (net.nwState h).log :=
        hlsh h e' h' hty h4 (h2.symm.trans hterm)
      exact absurd (h1.symm.trans hidx) (S_maxIndex_not_in (hsh h) he'h)
    · exact List.mem_cons_of_mem _ ((hem h h' e e' e'' h1 h2 h3' h4 h5).mpr hin)

omit O in
/-- `handleClientRequest`'s exact log shape (the leader branch's fresh
entry, literally). -/
theorem handleClientRequest_log_full (me : name (P := P))
    (st : raft_data (P := P)) (client : R.clientId) (id : Nat) (c : P.input)
    {out st' l} (h : handleClientRequest me st client id c = (out, st', l)) :
    (st.type = .Leader ∧
      st'.log = (⟨me, client, id, maxIndex st.log + 1, st.currentTerm, c⟩ :
        entry (P := P)) :: st.log) ∨
    (st.type ≠ .Leader ∧ st' = st) := by
  unfold handleClientRequest at h
  split at h
  · rename_i hty
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact Or.inl ⟨hty, rfl⟩
  · rename_i hty
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact Or.inr ⟨hty, rfl⟩

/-- `LogMatchingProof.v:793-893` (`client_request_log_matching`). -/
theorem client_request_log_matching :
    raft_net_invariant_client_request (P := P) log_matching := by
  intro h net st' ps' out d l client id c hcr hP hreach hst hps
  obtain ⟨-, -, -, -, hl⟩ :=
    handleClientRequest_spec h (net.nwState h) client id c hcr
  have hpkts : ∀ p', p' ∈ ps' → p' ∈ net.nwPackets := by
    intro p' hp'
    rcases hps p' hp' with h1 | h1
    · exact h1
    · rw [hl] at h1
      simp [send_packets] at h1
  rcases handleClientRequest_log_full h (net.nwState h) client id c hcr with
    ⟨hty, hlogd⟩ | ⟨-, heq⟩
  · -- LEADER: the fresh entry rides leader_sublog + one impossible index
    obtain ⟨⟨hem, hcontig, hpos⟩, hnw⟩ := hP
    obtain ⟨hlsh, hlsn⟩ := leader_sublog_invariant_invariant net hreach
    have hsorted := logs_sorted_invariant net hreach
    have hlog' : ∀ h0, h0 ≠ h → (st' h0).log = (net.nwState h0).log := by
      intro h0 hne
      rw [hst h0, update_neq _ _ hne]
    have hlogh : (st' h).log =
        (⟨h, client, id, maxIndex (net.nwState h).log + 1,
          (net.nwState h).currentTerm, c⟩ : entry (P := P))
          :: (net.nwState h).log := by
      rw [hst h, update_same]
      exact hlogd
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- entries_match, pairwise
      intro h1 h2
      show entries_match (st' h1).log (st' h2).log
      by_cases he1 : h1 = h <;> by_cases he2 : h2 = h
      · rw [he1, he2]
        exact entries_match_refl _
      · rw [he1, hlogh, hlog' h2 he2]
        exact handleClientRequest_entries_match ⟨hem, hcontig, hpos⟩ hlsh
          hsorted.1 hty rfl rfl
      · rw [he2, hlogh, hlog' h1 he1]
        exact entries_match_sym
          (handleClientRequest_entries_match ⟨hem, hcontig, hpos⟩ hlsh
            hsorted.1 hty rfl rfl)
      · rw [hlog' h1 he1, hlog' h2 he2]
        exact hem h1 h2
    · -- contiguity
      intro h0 i hi
      replace hi : 1 ≤ i ∧ i ≤ maxIndex (st' h0).log := hi
      show ∃ e, entry.eIndex e = i ∧ e ∈ (st' h0).log
      by_cases he0 : h0 = h
      · rw [he0, hlogh] at hi ⊢
        replace hi : 1 ≤ i ∧ i ≤ maxIndex (net.nwState h).log + 1 := hi
        rcases Nat.lt_or_ge i (maxIndex (net.nwState h).log + 1) with hlt | hge
        · obtain ⟨e, hei, heL⟩ := hcontig h i ⟨hi.1, Nat.lt_succ_iff.mp hlt⟩
          exact ⟨e, hei, List.mem_cons_of_mem _ heL⟩
        · exact ⟨_, Nat.le_antisymm hge hi.2, List.mem_cons_self ..⟩
      · rw [hlog' h0 he0] at hi ⊢
        exact hcontig h0 i hi
    · -- positivity
      intro h0 e he
      replace he : e ∈ (st' h0).log := he
      by_cases he0 : h0 = h
      · rw [he0, hlogh] at he
        rcases List.mem_cons.mp he with rfl | he'
        · exact Nat.succ_pos _
        · exact hpos h e he'
      · rw [hlog' h0 he0] at he
        exact hpos h0 e he
    · -- nw: every packet is old; only host h's log grew
      intro q t lid pli plt es ci hq hbody
      replace hq : q ∈ ps' := hq
      have hqold := hpkts q hq
      obtain ⟨hc1, hc2, hc3, hc4⟩ := hnw q t lid pli plt es ci hqold hbody
      refine ⟨?_, hc2, hc3, ?_⟩
      · intro h2 e1 e2 he1 he2 hidx hterm
        replace he2 : e2 ∈ (st' h2).log := he2
        by_cases he2h : h2 = h
        · rw [he2h, hlogh] at he2
          rcases List.mem_cons.mp he2 with rfl | he2'
          · -- e2 is the fresh entry: e1 in flight at the leader's term
            -- would already be in the leader's log at an impossible index
            exfalso
            have he1L : e1 ∈ (net.nwState h).log :=
              hlsn h q t lid pli plt es ci e1 hty hqold hbody he1 hterm
            exact absurd hidx (S_maxIndex_not_in (hsorted.1 h) he1L)
          · obtain ⟨ha, hb⟩ := hc1 h e1 e2 he1 he2' hidx hterm
            refine ⟨?_, ?_⟩
            · intro e3 h3le h3in
              show e3 ∈ (st' h2).log
              rw [he2h, hlogh]
              exact List.mem_cons_of_mem _ (ha e3 h3le h3in)
            · intro hne
              obtain ⟨e4, h4a, h4b, h4c⟩ := hb hne
              refine ⟨e4, h4a, h4b, ?_⟩
              show e4 ∈ (st' h2).log
              rw [he2h, hlogh]
              exact List.mem_cons_of_mem _ h4c
        · rw [hlog' h2 he2h] at he2
          obtain ⟨ha, hb⟩ := hc1 h2 e1 e2 he1 he2 hidx hterm
          refine ⟨?_, ?_⟩
          · intro e3 h3le h3in
            show e3 ∈ (st' h2).log
            rw [hlog' h2 he2h]
            exact ha e3 h3le h3in
          · intro hne
            obtain ⟨e4, h4a, h4b, h4c⟩ := hb hne
            refine ⟨e4, h4a, h4b, ?_⟩
            show e4 ∈ (st' h2).log
            rw [hlog' h2 he2h]
            exact h4c
      · intro q' t' lid' pli' plt' es' ci' hq' hbody'
        replace hq' : q' ∈ ps' := hq'
        exact hc4 q' t' lid' pli' plt' es' ci' (hpkts q' hq') hbody'
  · -- non-leader: state unchanged, no messages
    refine log_matching_state_same_packet_subset (net' := ⟨ps', st'⟩) hP ?_ ?_
    · intro h0
      show (st' h0).log = (net.nwState h0).log
      rw [hst h0]
      by_cases he : h0 = h
      · rw [he, update_same, heq]
      · rw [update_neq _ _ he]
    · intro p hp _
      replace hp : p ∈ ps' := hp
      exact hpkts p hp

/-- `LogMatchingProof.v:196-499` (`doLeader_log_matching_nw` +
`do_leader_log_matching`): the leader's replica messages carry slices of
its own log, so every clause reduces to the host invariants. -/
theorem do_leader_log_matching :
    raft_net_invariant_do_leader (P := P) log_matching := by
  intro net st' ps' d h os d' ms hdl hP hreach hstate hst hps
  subst hstate
  obtain ⟨-, -, -, -, hdlog, -⟩ := doLeader_spec _ h hdl
  have hmsgs := doLeader_messages_full _ h hdl
  obtain ⟨⟨hem, hcontig, hpos⟩, hnw⟩ := hP
  have hsorted := logs_sorted_invariant net hreach
  have hLs : sorted (net.nwState h).log := hsorted.1 h
  have hLu : uniqueIndices (net.nwState h).log :=
    (UniqueIndices_invariant net hreach).1 h
  have hLcontig := hcontig h
  have hlog' : ∀ h0, (st' h0).log = (net.nwState h0).log := by
    intro h0
    rw [hst h0]
    by_cases he : h0 = h
    · rw [he, update_same, hdlog]
    · rw [update_neq _ _ he]
  -- packet classification: old, or a replica slice of h's log
  have hclassify : ∀ (q : Packet (raft_base_params (P := P)) raft_multi_params)
      t lid pli plt es ci,
      q ∈ ps' → q.pBody = msg.AppendEntries t lid pli plt es ci →
      q ∈ net.nwPackets ∨
      (es = findGtIndex (net.nwState h).log pli ∧
       plt = (match findAtIndex (net.nwState h).log pli with
              | some e => e.eTerm
              | none => 0)) := by
    intro q t lid pli plt es ci hq hbody
    rcases hps q hq with h1 | h1
    · exact Or.inl h1
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
      obtain ⟨pli0, ci0, hbody0⟩ := hmsgs m0 hm0
      replace hbody : m0.2 = msg.AppendEntries t lid pli plt es ci := hbody
      rw [hbody0] at hbody
      injection hbody with f1 f2 f3 f4 f5 f6
      refine Or.inr ⟨?_, ?_⟩
      · rw [← f5, f3]
      · rw [← f4, f3]
  -- clause 1 of a fresh packet, against any host
  have hfresh1 : ∀ pli (h2 : name (P := P)) (e1 e2 : entry (P := P)),
      e1 ∈ findGtIndex (net.nwState h).log pli →
      e2 ∈ (net.nwState h2).log →
      e1.eIndex = e2.eIndex → e1.eTerm = e2.eTerm →
      (∀ e3, e3.eIndex ≤ e1.eIndex →
        e3 ∈ findGtIndex (net.nwState h).log pli →
        e3 ∈ (net.nwState h2).log) ∧
      (pli ≠ 0 → ∃ e4, e4.eIndex = pli ∧
        e4.eTerm = (match findAtIndex (net.nwState h).log pli with
                    | some e => e.eTerm
                    | none => 0) ∧
        e4 ∈ (net.nwState h2).log) := by
    intro pli h2 e1 e2 he1 he2 hidx hterm
    have he1L := (findGtIndex_necessary he1).1
    have hEM := hem h h2
    constructor
    · intro e3 h3le h3in
      exact (hEM e1 e2 e3 hidx hterm he1L he2 h3le).mp
        (findGtIndex_necessary h3in).1
    · intro hne
      obtain ⟨ple, hfind, hplei, hpleL⟩ :=
        replica_prev_resolves hLs hLcontig he1 hne
      refine ⟨ple, hplei, by rw [hfind], ?_⟩
      exact (hEM e1 e2 ple hidx hterm he1L he2
        (by rw [hplei]
            exact Nat.le_of_lt (findGtIndex_necessary he1).2)).mp hpleL
  -- clause 4, old q against a fresh q'
  have hvs_fresh : ∀ (q : Packet (raft_base_params (P := P)) raft_multi_params)
      t lid pli plt es ci pli',
      q ∈ net.nwPackets → q.pBody = msg.AppendEntries t lid pli plt es ci →
      ∀ e1 e2, e1 ∈ es → e2 ∈ findGtIndex (net.nwState h).log pli' →
        e1.eIndex = e2.eIndex → e1.eTerm = e2.eTerm →
        (∀ e3, pli' < e3.eIndex ∧ e3.eIndex ≤ e1.eIndex → e3 ∈ es →
          e3 ∈ findGtIndex (net.nwState h).log pli') ∧
        (∀ e3, e3 ∈ es → e3.eIndex = pli' →
          e3.eTerm = (match findAtIndex (net.nwState h).log pli' with
                      | some e => e.eTerm
                      | none => 0)) ∧
        (pli ≠ 0 → pli = pli' →
          plt = (match findAtIndex (net.nwState h).log pli' with
                 | some e => e.eTerm
                 | none => 0)) := by
    intro q t lid pli plt es ci pli' hq hbody e1 e2 he1 he2 hidx hterm
    have he2L := (findGtIndex_necessary he2).1
    obtain ⟨hc1, -, -, -⟩ := hnw q t lid pli plt es ci hq hbody
    obtain ⟨ha, hb⟩ := hc1 h e1 e2 he1 he2L hidx hterm
    refine ⟨?_, ?_, ?_⟩
    · intro e3 ⟨h3gt, h3le⟩ h3in
      exact findGtIndex_sufficient hLs (ha e3 h3le h3in) h3gt
    · intro e3 h3in h3idx
      have h3le : e3.eIndex ≤ e1.eIndex := by
        rw [h3idx, hidx]
        exact Nat.le_of_lt (findGtIndex_necessary he2).2
      have hfind : findAtIndex (net.nwState h).log pli' = some e3 :=
        findAtIndex_intro hLs (ha e3 h3le h3in) h3idx hLu
      rw [hfind]
    · intro hne hplieq
      obtain ⟨e4, h4i, h4t, h4L⟩ := hb hne
      have hfind : findAtIndex (net.nwState h).log pli' = some e4 :=
        findAtIndex_intro hLs h4L (hplieq ▸ h4i) hLu
      rw [hfind]
      exact h4t.symm
  -- clause 4, fresh q against an old q'
  have hfresh_vs_old : ∀ pli
      (q' : Packet (raft_base_params (P := P)) raft_multi_params)
      t' lid' pli' plt' es' ci',
      q' ∈ net.nwPackets →
      q'.pBody = msg.AppendEntries t' lid' pli' plt' es' ci' →
      ∀ e1 e2, e1 ∈ findGtIndex (net.nwState h).log pli → e2 ∈ es' →
        e1.eIndex = e2.eIndex → e1.eTerm = e2.eTerm →
        (∀ e3, pli' < e3.eIndex ∧ e3.eIndex ≤ e1.eIndex →
          e3 ∈ findGtIndex (net.nwState h).log pli → e3 ∈ es') ∧
        (∀ e3, e3 ∈ findGtIndex (net.nwState h).log pli →
          e3.eIndex = pli' → e3.eTerm = plt') ∧
        (pli ≠ 0 → pli = pli' →
          (match findAtIndex (net.nwState h).log pli with
           | some e => e.eTerm
           | none => 0) = plt') := by
    intro pli q' t' lid' pli' plt' es' ci' hq' hbody' e1 e2 he1 he2 hidx hterm
    have he1L := (findGtIndex_necessary he1).1
    obtain ⟨hc1', hc2', -, -⟩ := hnw q' t' lid' pli' plt' es' ci' hq' hbody'
    obtain ⟨ha', hb'⟩ := hc1' h e2 e1 he2 he1L hidx.symm hterm.symm
    have hes' : sorted es' :=
      hsorted.2.1 q' t' lid' pli' plt' es' ci' hq' hbody'
    refine ⟨?_, ?_, ?_⟩
    · intro e3 ⟨h3gt, h3le⟩ h3in
      have h3L := (findGtIndex_necessary h3in).1
      obtain ⟨x, hxi, hxes'⟩ := hc2' e3.eIndex
        ⟨h3gt, by
          rw [hidx] at h3le
          exact Nat.le_trans h3le (maxIndex_is_max hes' he2)⟩
      have hxL : x ∈ (net.nwState h).log := ha' x
        (by rw [hxi, ← hidx]; exact h3le) hxes'
      rw [uniqueIndices_elim_eq hLu h3L hxL hxi.symm]
      exact hxes'
    · intro e3 h3in h3idx
      have h3L := (findGtIndex_necessary h3in).1
      rcases Nat.eq_zero_or_pos pli' with rfl | hposi
      · exact absurd h3idx (Nat.ne_of_gt (hpos h e3 h3L))
      · obtain ⟨e4, h4i, h4t, h4L⟩ := hb' (Nat.pos_iff_ne_zero.mp hposi)
        rw [uniqueIndices_elim_eq hLu h3L h4L (h3idx.trans h4i.symm)]
        exact h4t
    · intro hne hplieq
      obtain ⟨ple, hfind, hplei, hpleL⟩ :=
        replica_prev_resolves hLs hLcontig he1 hne
      rw [hfind]
      obtain ⟨e4, h4i, h4t, h4L⟩ := hb' (by rw [← hplieq]; exact hne)
      rw [uniqueIndices_elim_eq hLu hpleL h4L
        (by rw [hplei, h4i, hplieq])]
      exact h4t
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro h1 h2
    show entries_match (st' h1).log (st' h2).log
    rw [hlog' h1, hlog' h2]
    exact hem h1 h2
  · intro h0 i hi
    replace hi : 1 ≤ i ∧ i ≤ maxIndex (st' h0).log := hi
    show ∃ e, entry.eIndex e = i ∧ e ∈ (st' h0).log
    rw [hlog' h0] at hi ⊢
    exact hcontig h0 i hi
  · intro h0 e he
    replace he : e ∈ (st' h0).log := he
    rw [hlog' h0] at he
    exact hpos h0 e he
  · intro q t lid pli plt es ci hq hbody
    replace hq : q ∈ ps' := hq
    rcases hclassify q t lid pli plt es ci hq hbody with hold | ⟨hes, hplt⟩
    · -- OLD packet
      obtain ⟨hc1, hc2, hc3, hc4⟩ := hnw q t lid pli plt es ci hold hbody
      refine ⟨?_, hc2, hc3, ?_⟩
      · intro h2 e1 e2 he1 he2 hidx hterm
        replace he2 : e2 ∈ (st' h2).log := he2
        rw [hlog' h2] at he2
        obtain ⟨ha, hb⟩ := hc1 h2 e1 e2 he1 he2 hidx hterm
        refine ⟨?_, ?_⟩
        · intro e3 h3le h3in
          show e3 ∈ (st' h2).log
          rw [hlog' h2]
          exact ha e3 h3le h3in
        · intro hne
          obtain ⟨e4, h4a, h4b, h4c⟩ := hb hne
          refine ⟨e4, h4a, h4b, ?_⟩
          show e4 ∈ (st' h2).log
          rw [hlog' h2]
          exact h4c
      · intro q' t' lid' pli' plt' es' ci' hq' hbody'
        replace hq' : q' ∈ ps' := hq'
        rcases hclassify q' t' lid' pli' plt' es' ci' hq' hbody' with
          hold' | ⟨hes', hplt'⟩
        · exact hc4 q' t' lid' pli' plt' es' ci' hold' hbody'
        · subst hes'
          subst hplt'
          exact hvs_fresh q t lid pli plt es ci pli' hold hbody
    · -- FRESH packet
      subst hes
      subst hplt
      refine ⟨?_, replica_entries_contiguous hLs hLcontig,
        fun e he => (findGtIndex_necessary he).2, ?_⟩
      · intro h2 e1 e2 he1 he2 hidx hterm
        replace he2 : e2 ∈ (st' h2).log := he2
        rw [hlog' h2] at he2
        obtain ⟨ha, hb⟩ := hfresh1 pli h2 e1 e2 he1 he2 hidx hterm
        refine ⟨?_, ?_⟩
        · intro e3 h3le h3in
          show e3 ∈ (st' h2).log
          rw [hlog' h2]
          exact ha e3 h3le h3in
        · intro hne
          obtain ⟨e4, h4a, h4b, h4c⟩ := hb hne
          refine ⟨e4, h4a, h4b, ?_⟩
          show e4 ∈ (st' h2).log
          rw [hlog' h2]
          exact h4c
      · intro q' t' lid' pli' plt' es' ci' hq' hbody'
        replace hq' : q' ∈ ps' := hq'
        rcases hclassify q' t' lid' pli' plt' es' ci' hq' hbody' with
          hold' | ⟨hes', hplt'⟩
        · exact hfresh_vs_old pli q' t' lid' pli' plt' es' ci' hold' hbody'
        · subst hes'
          subst hplt'
          intro e1 e2 he1 he2 hidx hterm
          refine ⟨?_, ?_, ?_⟩
          · intro e3 ⟨h3gt, h3le⟩ h3in
            exact findGtIndex_sufficient hLs
              (findGtIndex_necessary h3in).1 h3gt
          · intro e3 h3in h3idx
            have hfind : findAtIndex (net.nwState h).log pli' = some e3 :=
              findAtIndex_intro hLs (findGtIndex_necessary h3in).1 h3idx hLu
            rw [hfind]
          · intro hne hplieq
            rw [hplieq]

end LogMatchingCore

end Raft
end VerdiCompat
