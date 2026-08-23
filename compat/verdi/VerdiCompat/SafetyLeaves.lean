import VerdiCompat.MsgRefinement

/-!
# The W-B plain leaves of the state-machine-safety closure

Campaign Arc 3 unit 12 (closure re-check in the arc log's unit-12
opening entry), 1:1 against the sources @ a3375e8 — the eight
non-ghost proof files the SMS cap sits on:

- `TransitiveCommitProof.v` (31L) — `committed` is downward closed
  along a shared log (unit 10's `committed` + entries_match);
- `AllEntriesLeaderLogsProof.v` (106L) — the four-conjunct assembly
  interface over already-ported invariants;
- `InLogInAllEntriesProof.v` (175L) / `LogAllEntriesProof.v` (269L) —
  every log entry is recorded (at some term / at its own term when
  current), via the JOINT log/allEntries movement lemmas
  (`RefinementSpecLemmas.v:312-360,404-441`);
- `LastAppliedLeCommitIndexProof.v` (223L, BASE) /
  `MatchIndexSanityProof.v` (254L, BASE) /
  `NoAppendEntriesToSelfProof.v` (148L, BASE) — applied/commit/match
  watermark sanity and the no-self-AE fact;
- `PrevLogCandidateEntriesTermProof.v` (489L) — every positive
  prevLogTerm has an election-winner witness
  (`candidateEntriesTerm`, the term-level twin of unit 3's
  `candidateEntries`).
-/

namespace VerdiCompat
namespace Raft

section SafetyLeaves
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" =>
  Network (raft_base_params (P := P)) raft_multi_params
local notation "RaftPacket" =>
  Packet (raft_base_params (P := P)) raft_multi_params

/-! ## The joint log/allEntries movement lemmas
(`RefinementSpecLemmas.v:312-360` and `:404-441` — the correlation the
lane's separate cases lemmas lose, ported on first need) -/

omit O in
/-- A `true` AppendEntries reply leaves the responder exactly at the
request's term (the accept guard forces `currentTerm ≤ t`, and
`advanceCurrentTerm` then lands on `t`). -/
theorem handleAppendEntries_true_reply_currentTerm (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d : raft_data (P := P)} {t' : term}
    {es' : List (entry (P := P))}
    (h : handleAppendEntries me st t lid pli plt es ci
      = (d, .AppendEntriesReply t' es' true)) :
    d.currentTerm = t := by
  unfold handleAppendEntries at h
  split at h
  · injection h with h1 h2
    injection h2 with h2a h2b h2c
    cases h2c
  · rename_i hng
    have hle : st.currentTerm ≤ t :=
      Nat.not_lt.mp (fun hlt => hng (by simpa [Nat.blt_eq] using hlt))
    repeat' split at h
    all_goals injection h with h1 h2
    all_goals injection h2 with h2a h2b h2c
    all_goals try cases h2c
    all_goals rw [← h1]
    all_goals exact advanceCurrentTerm_le_eq hle

/-- `RefinementSpecLemmas.v:404-441`
(`update_elections_data_appendEntries_log_allEntries`), in the lane's
compact form: either nothing moved, or the responder sits at term `t`,
the request's entries are recorded at `t`, and the log took one of its
three accept shapes. -/
theorem update_elections_data_appendEntries_log_allEntries
    (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) (t : term)
    (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {d m}
    (h : handleAppendEntries me st.2 t lid pli plt es ci = (d, m)) :
    (d.log = st.2.log ∧
     (update_elections_data_appendEntries me st t lid pli plt es
        ci).allEntries = st.1.allEntries) ∨
    (d.currentTerm = t ∧
     (update_elections_data_appendEntries me st t lid pli plt es
        ci).allEntries = (es.map fun e => (t, e)) ++ st.1.allEntries ∧
     (d.log = st.2.log ∨ d.log = es ∨
      d.log = es ++ removeAfterIndex st.2.log pli)) := by
  obtain ⟨t'', r'', hm⟩ :=
    handleAppendEntries_reply_entries me st.2 t lid pli plt es ci h
  subst hm
  cases r''
  · unfold update_elections_data_appendEntries
    rw [h]
    left
    refine ⟨?_, rfl⟩
    rw [handleAppendEntries_false_reply_state me st.2 t lid pli plt es
      ci h]
  · obtain ⟨heqt, -⟩ :=
      handleAppendEntries_reply_true me st.2 t lid pli plt es ci h
    have heqt' : t = t'' := heqt.symm
    subst heqt'
    unfold update_elections_data_appendEntries
    rw [h]
    right
    refine ⟨handleAppendEntries_true_reply_currentTerm me st.2 t lid
      pli plt es ci h, rfl, ?_⟩
    rcases handleAppendEntries_log_cases me st.2 t lid pli plt es ci h
      with hd | ⟨-, hd⟩ | ⟨e2, -, -, -, hd⟩
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr hd)

/-- `RefinementSpecLemmas.v:312-360`
(`update_elections_data_client_request_log_allEntries`): the record and
the append happen together, on the same entry, at the handler's (=
unchanged) current term. -/
theorem update_elections_data_client_request_log_allEntries
    (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out d l}
    (hcr : handleClientRequest me st.2 client id c = (out, d, l)) :
    ((update_elections_data_client_request me st client id
        c).allEntries = st.1.allEntries ∧ d.log = st.2.log) ∨
    (∃ e : entry (P := P), e.eTerm = d.currentTerm ∧
      (update_elections_data_client_request me st client id
        c).allEntries = (d.currentTerm, e) :: st.1.allEntries ∧
      d.log = e :: st.2.log) := by
  unfold update_elections_data_client_request
  rw [hcr]
  simp only []
  rcases handleClientRequest_log_full me st.2 client id c hcr with
    ⟨hty, hlog⟩ | ⟨-, heq⟩
  · rw [hlog, if_pos (by
      simp only [Nat.blt_eq, List.length_cons]
      exact Nat.lt_succ_self _)]
    exact Or.inr ⟨_,
      ((handleClientRequest_spec me st.2 client id c hcr).2.1).symm, rfl,
      rfl⟩
  · rw [heq, if_neg (by
      simp only [Nat.blt_eq]
      exact Nat.lt_irrefl _)]
    exact Or.inl ⟨rfl, rfl⟩

/-! ## transitive_commit (`Raft/TransitiveCommitInterface.v` /
`RaftProofs/TransitiveCommitProof.v`) -/

/-- `TransitiveCommitInterface.v:9-15` (`transitive_commit`). -/
def transitive_commit (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e e' : entry (P := P)) (t : term),
    e ∈ (net.nwState h).2.log →
    e' ∈ (net.nwState h).2.log →
    e.eIndex ≤ e'.eIndex →
    committed net e' t →
    committed net e t

/-- `TransitiveCommitProof.v:15-27` (`transitive_commit_invariant`):
`committed` is downward closed — the witness pair transfers along
`entries_match`. -/
theorem transitive_commit_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      transitive_commit net := by
  intro net hreach h e e' t he he' hidx hcom
  obtain ⟨x, e'', hle, hdc, hidx', he'x, he''x⟩ := hcom
  refine ⟨x, e'', hle, hdc, Nat.le_trans hidx hidx', ?_, he''x⟩
  exact (entries_match_invariant net hreach h x e' e' e rfl rfl he' he'x
    hidx).mp he

/-! ## all_entries_leader_logs (`Raft/AllEntriesLeaderLogsInterface.v` /
`RaftProofs/AllEntriesLeaderLogsProof.v` — the assembly interface) -/

/-- `AllEntriesLeaderLogsInterface.v` (`leader_without_missing_entry`). -/
def leader_without_missing_entry (net : RefinedNet) : Prop :=
  ∀ (t : term) (e : entry (P := P)) (h : name (P := P)),
    (t, e) ∈ (net.nwState h).1.allEntries →
    e ∈ (net.nwState h).2.log ∨
    ∃ (t' : term) (log' : List (entry (P := P)))
      (leader : name (P := P)),
      t' > t ∧ (t', log') ∈ (net.nwState leader).1.leaderLogs ∧
      e ∉ log'

/-- `AllEntriesLeaderLogsInterface.v`
(`appendEntriesRequest_exists_leaderLog`). -/
def appendEntriesRequest_exists_leaderLog (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    ∃ log, (t, log) ∈ (net.nwState p.pSrc).1.leaderLogs

/-- `AllEntriesLeaderLogsInterface.v`
(`appendEntriesRequest_leaderLog_not_in`). -/
def appendEntriesRequest_leaderLog_not_in (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) (log : List (entry (P := P))) (e : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    e.eIndex > pli → e ∉ es →
    (t, log) ∈ (net.nwState p.pSrc).1.leaderLogs →
    e ∉ log

/-- `AllEntriesLeaderLogsInterface.v` (`leaderLogs_leader`). -/
def leaderLogs_leader (net : RefinedNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).2.type = .Leader →
    ∃ log' es,
      ((net.nwState h).2.currentTerm, log')
        ∈ (net.nwState h).1.leaderLogs ∧
      (net.nwState h).2.log = es ++ log'

/-- `AllEntriesLeaderLogsInterface.v` (`all_entries_leader_logs`). -/
def all_entries_leader_logs (net : RefinedNet) : Prop :=
  leader_without_missing_entry net ∧
  appendEntriesRequest_exists_leaderLog net ∧
  appendEntriesRequest_leaderLog_not_in net ∧
  leaderLogs_leader net

/-- `AllEntriesLeaderLogsProof.v:28-38`
(`leader_without_missing_entry_invariant`): a projection of unit 8's
`allEntries_log`. -/
theorem leader_without_missing_entry_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leader_without_missing_entry net := by
  intro net hreach t e h hin
  rcases allEntries_log_invariant net hreach t e h hin with hlog |
    ⟨t', leader, ll, hll, hlt, -, hnot, -⟩
  · exact Or.inl hlog
  · exact Or.inr ⟨t', ll, leader, hlt, hll, hnot⟩

/-- `AllEntriesLeaderLogsProof.v:40-47`
(`appendEntriesRequest_exists_leaderLog_invariant` = unit 7's
came-from-leaders). -/
theorem appendEntriesRequest_exists_leaderLog_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      appendEntriesRequest_exists_leaderLog net :=
  fun net hreach p t lid pli plt es ci hp hbody =>
    append_entries_came_from_leaders_invariant net hreach p t lid pli
      plt es ci hp hbody

/-- `AllEntriesLeaderLogsProof.v:49-84`
(`appendEntriesRequest_leaderLog_not_in_invariant`): an entry above the
prevLog cut that is not in the packet cannot be in the sender's
snapshot — the packet's `es' ++ ll'` decomposition (unit 8's
AERLeaderLogs) would have carried it. -/
theorem appendEntriesRequest_leaderLog_not_in_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      appendEntriesRequest_leaderLog_not_in net := by
  intro net hreach p t lid pli plt es ci log0 e hp hbody hgt hnotes hll0
    helog
  obtain ⟨h, ll, es', ll', hsplit, -, hll, hpre, hdisj⟩ :=
    append_entries_leaderLogs_invariant net hreach p t lid pli plt es ci
      hp hbody
  have hlleq : log0 = ll :=
    one_leaderLog_per_term_log_invariant net hreach p.pSrc h t log0 ll
      hll0 hll
  subst hlleq
  have hsll : sorted log0 := leaderLogs_sorted_invariant net hreach h t
    log0 hll
  have hmax : e.eIndex ≤ maxIndex log0 := maxIndex_is_max hsll helog
  apply hnotes
  rw [hsplit]
  refine List.mem_append.mpr (Or.inr ?_)
  rcases hdisj with ⟨-, hpligt⟩ | ⟨e2, -, -, -, hsane⟩ | ⟨-, -, hlleq'⟩
  · exact absurd (Nat.lt_trans hgt (Nat.lt_of_le_of_lt hmax hpligt))
      (Nat.lt_irrefl _)
  · rcases hsane with hne | hplieq
    · have hs_es : sorted es :=
        entries_sorted_nw_invariant net hreach p t lid pli plt es ci hp
          hbody
      have hc_es : contiguous_range_exact_lo es pli :=
        entries_contiguous_nw_invariant net hreach p t lid pli plt es ci
          hp hbody
      rw [hsplit] at hs_es hc_es
      exact prefix_contiguous hne hpre hsll helog hgt
        (contiguous_app hs_es hc_es)
    · rw [hplieq] at hgt
      exact absurd (Nat.lt_of_le_of_lt hmax hgt) (Nat.lt_irrefl _)
  · rw [hlleq']
    exact helog

/-- `AllEntriesLeaderLogsProof.v:87-96` (`leaderLogs_leader_invariant`
= the weak face of unit 7's strong form). -/
theorem leaderLogs_leader_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_leader net := by
  intro net hreach h hty
  obtain ⟨ll, es, hll, hlog, -⟩ :=
    leaders_have_leaderLogs_strong_invariant net hreach h hty
  exact ⟨ll, es, hll, hlog⟩

/-- `AllEntriesLeaderLogsProof.v:98-106` (the interface conjunction). -/
theorem all_entries_leader_logs_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      all_entries_leader_logs net :=
  fun net hreach =>
    ⟨leader_without_missing_entry_invariant net hreach,
     appendEntriesRequest_exists_leaderLog_invariant net hreach,
     appendEntriesRequest_leaderLog_not_in_invariant net hreach,
     leaderLogs_leader_invariant net hreach⟩

/-! ## in_log_in_all_entries (`Raft/InLogInAllEntriesInterface.v` /
`RaftProofs/InLogInAllEntriesProof.v`) -/

/-- `InLogInAllEntriesInterface.v` (`in_log_in_all_entries`). -/
def in_log_in_all_entries (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (net.nwState h).2.log →
    ∃ t, (t, e) ∈ (net.nwState h).1.allEntries

/-- Transport for `in_log_in_all_entries` across steps that keep the
log and the records at the updated node. -/
theorem iliae_of_update {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : in_log_in_all_entries net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hlog : d.log = (net.nwState u).2.log)
    (hae : gd.allEntries = (net.nwState u).1.allEntries) :
    in_log_in_all_entries net' := by
  intro h0 e he
  rw [hst h0] at he ⊢
  by_cases heq : u = h0
  · subst heq
    rw [update_same] at he ⊢
    show ∃ t, (t, e) ∈ gd.allEntries
    rw [hae]
    replace he : e ∈ d.log := he
    rw [hlog] at he
    exact hP u e he
  · rw [update_neq _ _ (Ne.symm heq)] at he ⊢
    exact hP h0 e he

/-- `InLogInAllEntriesProof.v` (`in_log_in_all_entries_invariant`):
every log entry is recorded at some term. -/
theorem in_log_in_all_entries_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      in_log_in_all_entries net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h e he
    exact nomatch he
  · -- client_request: the joint movement lemma pays immediately
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    intro h0 e he
    replace he : e ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.log := he
    show ∃ t0, (t0, e) ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).1.allEntries
    rw [hst h0] at he ⊢
    by_cases heq : h = h0
    · subst heq
      rw [update_same] at he ⊢
      replace he : e ∈ d.log := he
      show ∃ t, (t, e) ∈ gd.allEntries
      subst hgd
      rcases update_elections_data_client_request_log_allEntries h
          (net.nwState h) client id c hcr with ⟨hae, hlog⟩ |
        ⟨e0, -, hae, hlog⟩
      · rw [hae]
        rw [hlog] at he
        exact hP h e he
      · rw [hae]
        rw [hlog] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨d.currentTerm, List.mem_cons_self ..⟩
        · obtain ⟨t0, ht0⟩ := hP h e he
          exact ⟨t0, List.mem_cons_of_mem _ ht0⟩
    · rw [update_neq _ _ (Ne.symm heq)] at he ⊢
      exact hP h0 e he
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps
    obtain ⟨hlog, -, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    exact iliae_of_update hP hst hlog
      (by subst hgd
          exact (update_elections_data_timeout_ghost h (net.nwState h)).2)
  · -- append_entries: accepted entries are recorded together
    intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd hbody hP
      _hreach hpkts hst _hps
    intro h0 e he
    replace he : e ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.log := he
    show ∃ t0, (t0, e) ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).1.allEntries
    rw [hst h0] at he ⊢
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at he ⊢
      replace he : e ∈ d.log := he
      show ∃ t0, (t0, e) ∈ gd.allEntries
      subst hgd
      rcases update_elections_data_appendEntries_log_allEntries p.pDst
          (net.nwState p.pDst) t n pli plt es ci hae with ⟨hlog, hane⟩ |
        ⟨-, hane, hlogc⟩
      · rw [hane]
        rw [hlog] at he
        exact hP p.pDst e he
      · rw [hane]
        have hines : ∀ e0 ∈ es, ∃ t0, (t0, e0) ∈
            ((es.map fun e1 => (t, e1)) ++
              (net.nwState p.pDst).1.allEntries) := by
          intro e0 he0
          exact ⟨t, List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨e0, he0, rfl⟩))⟩
        have hold : ∀ e0 ∈ (net.nwState p.pDst).2.log, ∃ t0, (t0, e0) ∈
            ((es.map fun e1 => (t, e1)) ++
              (net.nwState p.pDst).1.allEntries) := by
          intro e0 he0
          obtain ⟨t0, ht0⟩ := hP p.pDst e0 he0
          exact ⟨t0, List.mem_append.mpr (Or.inr ht0)⟩
        rcases hlogc with hd | hd | hd
        · rw [hd] at he
          exact hold e he
        · rw [hd] at he
          exact hines e he
        · rw [hd] at he
          rcases List.mem_append.mp he with he | he
          · exact hines e he
          · exact hold e (removeAfterIndex_in he)
    · rw [update_neq _ _ heq] at he ⊢
      exact hP h0 e he
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst _hps
    exact iliae_of_update hP hst
      (handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2 p.pSrc
        t es res haer)
      (by rw [hgd])
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd hbody hP
      _hreach hpkts hst _hps
    exact iliae_of_update hP hst
      (handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc lli
        llt hrv)
      (by subst hgd
          exact (update_elections_data_requestVote_cronies p.pDst p.pSrc
            t p.pSrc lli llt (net.nwState p.pDst)).2.2)
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd hbody hP _hreach hpkts
      hst _hps
    exact iliae_of_update hP hst
      (by rw [← hrvr]
          exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
            p.pSrc t v)
      (by subst hgd
          exact (update_elections_data_requestVoteReply_votes p.pDst
            p.pSrc t v (net.nwState p.pDst)).2.2)
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨-, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
    refine iliae_of_update hP hst ?_ (by rw [hstate])
    rw [hlog, hstate]
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hdgs hP _hreach hstate hst _hps
    obtain ⟨hlog, -, -, -, -, -⟩ := doGenericServer_spec h d hdgs
    refine iliae_of_update hP hst ?_ (by rw [hstate])
    rw [hlog, hstate]
  · -- state_same_packet_subset
    intro net net' hstate _hpk hP _hreach
    intro h0 e he
    rw [← hstate h0] at he ⊢
    exact hP h0 e he
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    refine iliae_of_update hP hst ?_ (by rw [hstate])
    rw [← hrb, hstate]
    rfl

end SafetyLeaves
end Raft
end VerdiCompat
