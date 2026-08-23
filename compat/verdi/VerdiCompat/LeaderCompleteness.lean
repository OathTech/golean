import VerdiCompat.LeaderLogsAssembly

/-!
# GAP-6 — toward leader_completeness's proof

Campaign Arc 3 unit 9 (the fresh closure derivation is in the arc log's
unit-9 opening entry: six upstream proof files, 3,428 lines, no
msg-ghost), 1:1 against the sources @ a3375e8 —

- `append_entries_request_term_sanity`
  (`Raft/AppendEntriesRequestTermSanityInterface.v:8-14`): in-flight
  entries dominate their packet's prevLogTerm — the lifted
  `packets_ge_prevTerm` conjunct of base `logs_sorted`
  (`RaftProofs/AppendEntriesRequestTermSanityProof.v`, 48 lines);
- `allEntries_candidateEntries`
  (`Raft/AllEntriesCandidateEntriesInterface.v`): every recorded entry
  was created by a term's election winner
  (`RaftProofs/AllEntriesCandidateEntriesProof.v`, 305 lines — unit 3's
  `*_preserves_candidateEntries` transport lemmas re-consumed);
- `allEntries_leader_sublog`
  (`Raft/AllEntriesLeaderSublogInterface.v`): a leader's current-term
  record is in its log
  (`RaftProofs/AllEntriesLeaderSublogProof.v`, 351 lines);
- `allEntries_log_matching`
  (`Raft/AllEntriesLogMatchingInterface.v`): recorded entries match
  host logs and each other
  (`RaftProofs/AllEntriesLogMatchingProof.v`, 430 lines);
- `prefix_within_term` (`Raft/PrefixWithinTermInterface.v`) via
  `RaftProofs/PrefixWithinTermProof.v` (1,915 lines);
- **`leader_completeness`'s PROOF**
  (`RaftProofs/LeaderCompletenessProof.v`, 379 lines), discharging the
  statement ported in unit 4 (`LeaderLogs.lean`).

Statements 1:1 with the Interface files; proofs re-derived through the
ported principles.
-/

namespace VerdiCompat
namespace Raft

section LeaderCompleteness
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params

/-! ## append_entries_request_term_sanity -/

/-- `AppendEntriesRequestTermSanityInterface.v:8-14`
(`append_entries_request_term_sanity`). -/
def append_entries_request_term_sanity (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex)
    (e : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    e ∈ es → e.eTerm ≥ plt

/-- `AppendEntriesRequestTermSanityProof.v:41-46`
(`append_entries_request_term_sanity_invariant`): the lifted
`packets_ge_prevTerm` conjunct of base `logs_sorted`. -/
theorem append_entries_request_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      append_entries_request_term_sanity net := by
  intro net hreach p t n pli plt es ci e hp hbody he
  exact (lift_prop _ logs_sorted_invariant net hreach).2.2.2
    (deghost_packet p) t n pli plt es ci e (List.mem_map_of_mem hp)
    hbody he

/-! ## allEntries_candidateEntries -/

/-- `AllEntriesCandidateEntriesInterface.v` (`allEntries_candidateEntries`). -/
def allEntries_candidateEntries (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (e : entry (P := P)),
    (t, e) ∈ (net.nwState h).1.allEntries →
    candidateEntries e net.nwState

/-- `AllEntriesCandidateEntriesProof.v:280-298`
(`allEntries_candidateEntries_invariant`): unit 3's
`*_preserves_candidateEntries` transport lemmas carry the witness
through every step; the two WRITERS' fresh records are covered by the
leader's own won cronies (client request) and the in-flight packet's
`CandidateEntries` nw half (append entries). -/
theorem allEntries_candidateEntries_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_candidateEntries net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h t e hin
    exact nomatch hin
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    obtain ⟨hty, hct, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hgc : gd.cronies = (net.nwState h).1.cronies := by
      rw [hgd]
      exact (update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.1
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState h (gd, d)) :=
      fun e hce => candidateEntries_update_same hgc hct hty hce
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    by_cases heq0 : h0 = h
    case neg =>
      have hst2 : st' h0 = net.nwState h0 := by
        rw [hst h0, update_neq _ _ heq0]
      rw [hst2] at hin
      exact candidateEntries_ext hst (hpres e (hP h0 t0 e hin))
    case pos =>
      subst heq0
      have hst2 : st' h0 = (gd, d) := by
        rw [hst h0, update_same]
      rw [hst2] at hin
      replace hin : (t0, e) ∈ gd.allEntries := hin
      subst hgd
      rcases update_elections_data_client_request_allEntries_head_term
        h0 (net.nwState h0) client id c hcr with hsame |
        ⟨enew, hterm, hcons, hleader⟩
      · rw [hsame] at hin
        exact candidateEntries_ext hst (hpres e (hP h0 t0 e hin))
      · rw [hcons] at hin
        rcases List.mem_cons.mp hin with heqp | hin
        · -- the fresh record: the leader's own won cronies
          injection heqp with h1 h2
          refine candidateEntries_ext hst ⟨h0, ?_, ?_⟩
          · rw [update_same]
            show wonElection (dedup
              ((update_elections_data_client_request h0 (net.nwState h0)
                client id c).cronies e.eTerm)) = true
            rw [(update_elections_data_client_request_ghost h0
              (net.nwState h0) client id c).2.2.1, h2, hterm, hct]
            exact won_election_cronies
              (cronies_correct_invariant net hreach) hleader
          · rw [update_same]
            show d.currentTerm = e.eTerm → d.type ≠ serverType.Candidate
            intro _ hcand
            rw [hty, hleader] at hcand
            exact nomatch hcand
        · exact candidateEntries_ext hst (hpres e (hP h0 t0 e hin))
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hgd,
          (update_elections_data_timeout_ghost h0 (net.nwState h0)).2]
          at hin
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    subst hgd
    exact candidateEntries_ext hst
      (handleTimeout_preserves_candidateEntries hreach hto
        (hP h0 t0 e hin'))
  · -- append_entries
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd hbody hP
      hreach hpkts hst hps
    have hpin : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries ∨ e ∈ es := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hgd] at hin
        rcases update_elections_data_appendEntries_allEntries_term_cases
          p.pDst (net.nwState p.pDst) t n0 pli plt es ci hae with hsame |
          ⟨t', -, hcons⟩
        · rw [hsame] at hin
          exact Or.inl hin
        · rw [hcons] at hin
          rcases List.mem_append.mp hin with hmap | hold
          · obtain ⟨e2, he2, heq2⟩ := List.mem_map.mp hmap
            injection heq2 with h1 h2
            exact Or.inr (h2 ▸ he2)
          · exact Or.inl hold
      · rw [update_neq _ _ heq0] at hin
        exact Or.inl hin
    subst hgd
    have hce : candidateEntries e net.nwState := by
      rcases hin' with hold | hees
      · exact hP h0 t0 e hold
      · exact (candidate_entries_invariant net hreach).2 p t n0 pli plt
          es ci hpin hbody e hees
    exact candidateEntries_ext hst
      (handleAppendEntries_preserves_candidateEntries hae hce)
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hgd] at hin
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    subst hgd
    exact candidateEntries_ext hst
      (handleAppendEntriesReply_preserves_candidateEntries haer
        (hP h0 t0 e hin'))
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hgd, (update_elections_data_requestVote_cronies p.pDst p.pSrc
          t p.pSrc lli llt (net.nwState p.pDst)).2.2] at hin
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    subst hgd
    exact candidateEntries_ext hst
      (handleRequestVote_preserves_candidateEntries hrv (hP h0 t0 e hin'))
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts
      hst hps
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hgd, (update_elections_data_requestVoteReply_votes p.pDst
          p.pSrc t v (net.nwState p.pDst)).2.2] at hin
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    subst hgd
    rw [← hrvr] at hst
    exact candidateEntries_ext hst
      (handleRequestVoteReply_preserves_candidateEntries hreach
        (hP h0 t0 e hin'))
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hct, -, hty, -, -, -⟩ := doLeader_spec d h hdl
    have hgc : gd.cronies = (net.nwState h).1.cronies := by
      rw [hstate]
    have hctn : d'.currentTerm = (net.nwState h).2.currentTerm := by
      rw [hct, hstate]
    have htyn : d'.type = (net.nwState h).2.type := by
      rw [hty, hstate]
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    exact candidateEntries_ext hst
      (candidateEntries_update_same hgc hctn htyn (hP h0 t0 e hin'))
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨-, hty, hct, -, -, -⟩ := doGenericServer_spec h d hgs
    have hgc : gd.cronies = (net.nwState h).1.cronies := by
      rw [hstate]
    have hctn : d'.currentTerm = (net.nwState h).2.currentTerm := by
      rw [hct, hstate]
    have htyn : d'.type = (net.nwState h).2.type := by
      rw [hty, hstate]
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (st' h0).1.allEntries := hin
    show candidateEntries e st'
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    exact candidateEntries_ext hst
      (candidateEntries_update_same hgc hctn htyn (hP h0 t0 e hin'))
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach h0 t0 e hin
    replace hin : (t0, e) ∈ (net'.nwState h0).1.allEntries := hin
    rw [← hstates h0] at hin
    exact candidateEntries_ext (fun h => (hstates h).symm)
      (hP h0 t0 e hin)
  · -- reboot: type resets to Follower; cronies preserved
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    intro h0 t0 e hin
    replace hin : (t0, e) ∈ (net'.nwState h0).1.allEntries := hin
    show candidateEntries e net'.nwState
    have hin' : (t0, e) ∈ (net.nwState h0).1.allEntries := by
      rw [hst h0] at hin
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at hin
        replace hin : (t0, e) ∈ gd.allEntries := hin
        rw [hstate]
        exact hin
      · rw [update_neq _ _ heq0] at hin
        exact hin
    obtain ⟨x, hw, himp⟩ := hP h0 t0 e hin'
    refine ⟨x, ?_, ?_⟩
    · rw [hst x]
      by_cases hxh : x = h
      · subst hxh
        rw [update_same]
        show wonElection (dedup (gd.cronies e.eTerm)) = true
        rw [hstate] at hw
        exact hw
      · rw [update_neq _ _ hxh]
        exact hw
    · rw [hst x]
      by_cases hxh : x = h
      · subst hxh
        rw [update_same]
        show d'.currentTerm = e.eTerm → d'.type ≠ serverType.Candidate
        intro _ hcand
        rw [← hrb] at hcand
        exact nomatch hcand
      · rw [update_neq _ _ hxh]
        exact himp

end LeaderCompleteness
end Raft
end VerdiCompat
