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
  (`candidateEntriesTerm`, the term-level twin of unit 3's — relocated
  to CandidateEntries.lean at the unit-16 consolidation, where the
  entry-level preserves set is now DERIVED from it;
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

/-! ## log_all_entries (`Raft/LogAllEntriesInterface.v` /
`RaftProofs/LogAllEntriesProof.v`) -/

/-- `LogAllEntriesInterface.v` (`log_all_entries`): a current-term log
entry is recorded at its own term. -/
def log_all_entries (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (net.nwState h).2.log →
    e.eTerm = (net.nwState h).2.currentTerm →
    (e.eTerm, e) ∈ (net.nwState h).1.allEntries

/-- `LogAllEntriesProof.v:27-39`
(`no_entries_past_current_term_host_lifted_invariant`). -/
theorem nepct_host_lifted :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (h : name (P := P)) (e : entry (P := P)),
        e ∈ (net.nwState h).2.log →
        e.eTerm ≤ (net.nwState h).2.currentTerm :=
  fun net hreach h e he =>
    (lift_prop _ no_entries_past_current_term_invariant net hreach).1 h e he

/-- Transport for `log_all_entries` across steps that keep the log and
records at the updated node and move its term only UP (a strictly
higher term empties the premise via the lifted term-sanity). -/
theorem lae_of_update {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : log_all_entries net)
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hlog : d.log = (net.nwState u).2.log)
    (hae : gd.allEntries = (net.nwState u).1.allEntries)
    (hct : (net.nwState u).2.currentTerm ≤ d.currentTerm) :
    log_all_entries net' := by
  intro h0 e he heterm
  rw [hst h0] at he heterm ⊢
  by_cases heq : u = h0
  · subst heq
    rw [update_same] at he heterm ⊢
    show (e.eTerm, e) ∈ gd.allEntries
    rw [hae]
    replace he : e ∈ d.log := he
    replace heterm : e.eTerm = d.currentTerm := heterm
    rw [hlog] at he
    have hle := nepct_host_lifted net hreach u e he
    exact hP u e he (Nat.le_antisymm hle (heterm ▸ hct))
  · rw [update_neq _ _ (Ne.symm heq)] at he heterm ⊢
    exact hP h0 e he heterm

/-- `LogAllEntriesProof.v:246-266` (`log_all_entries_invariant`). -/
theorem log_all_entries_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      log_all_entries net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h e he
    exact nomatch he
  · -- client_request: the fresh entry's record is at its own term
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst _hps
    intro h0 e he heterm
    replace he : e ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.log := he
    replace heterm : e.eTerm = ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.currentTerm := heterm
    show (e.eTerm, e) ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).1.allEntries
    rw [hst h0] at he heterm ⊢
    by_cases heq : h = h0
    · subst heq
      rw [update_same] at he heterm ⊢
      replace he : e ∈ d.log := he
      replace heterm : e.eTerm = d.currentTerm := heterm
      show (e.eTerm, e) ∈ gd.allEntries
      subst hgd
      obtain ⟨-, hcteq, -, -, -⟩ :=
        handleClientRequest_spec h (net.nwState h).2 client id c hcr
      rcases update_elections_data_client_request_log_allEntries h
          (net.nwState h) client id c hcr with ⟨hane, hlog⟩ |
        ⟨e0, he0t, hane, hlog⟩
      · rw [hane]
        rw [hlog] at he
        exact hP h e he (by rw [heterm, hcteq])
      · rw [hane]
        rw [hlog] at he
        rcases List.mem_cons.mp he with rfl | he
        · rw [heterm]
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _
            (hP h e he (by rw [heterm, hcteq]))
    · rw [update_neq _ _ (Ne.symm heq)] at he heterm ⊢
      exact hP h0 e he heterm
  · -- timeout: log/records unchanged, term only grows
    intro net h st' ps' gd out d l hto hgd hP hreach hst _hps
    obtain ⟨hlog, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine lae_of_update hP hreach hst hlog
      (by subst hgd
          exact (update_elections_data_timeout_ghost h (net.nwState h)).2)
      ?_
    rcases hcases with ⟨hcteq, -⟩ | ⟨hcteq, -⟩
    · exact Nat.le_of_eq hcteq.symm
    · rw [hcteq]
      exact Nat.le_succ _
  · -- append_entries: accepted entries recorded at the (new) term
    intro xs p ys net st' ps' gd d m t n pli plt es ci hae hgd hbody hP
      hreach hpkts hst _hps
    intro h0 e he heterm
    replace he : e ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.log := he
    replace heterm : e.eTerm = ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.currentTerm := heterm
    show (e.eTerm, e) ∈ ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).1.allEntries
    rw [hst h0] at he heterm ⊢
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at he heterm ⊢
      replace he : e ∈ d.log := he
      replace heterm : e.eTerm = d.currentTerm := heterm
      show (e.eTerm, e) ∈ gd.allEntries
      subst hgd
      have hmono : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm :=
        (handleAppendEntries_currentTerm_leaderId p.pDst
          (net.nwState p.pDst).2 t n pli plt es ci hae).1
      have hold : ∀ e0 ∈ (net.nwState p.pDst).2.log,
          e0.eTerm = d.currentTerm →
          (e0.eTerm, e0) ∈ (net.nwState p.pDst).1.allEntries := by
        intro e0 he0 het0
        have hle := nepct_host_lifted net hreach p.pDst e0 he0
        exact hP p.pDst e0 he0 (Nat.le_antisymm hle (het0 ▸ hmono))
      rcases update_elections_data_appendEntries_log_allEntries p.pDst
          (net.nwState p.pDst) t n pli plt es ci hae with ⟨hlog, hane⟩ |
        ⟨hcteq, hane, hlogc⟩
      · rw [hane]
        rw [hlog] at he
        exact hold e he heterm
      · rw [hane]
        have hines : ∀ e0 ∈ es, e0.eTerm = d.currentTerm →
            (e0.eTerm, e0) ∈ ((es.map fun e1 => (t, e1)) ++
              (net.nwState p.pDst).1.allEntries) := by
          intro e0 he0 het0
          refine List.mem_append.mpr (Or.inl
            (List.mem_map.mpr ⟨e0, he0, ?_⟩))
          rw [het0, hcteq]
        rcases hlogc with hd | hd | hd
        · rw [hd] at he
          exact List.mem_append.mpr (Or.inr (hold e he heterm))
        · rw [hd] at he
          exact hines e he heterm
        · rw [hd] at he
          rcases List.mem_append.mp he with he | he
          · exact hines e he heterm
          · exact List.mem_append.mpr (Or.inr
              (hold e (removeAfterIndex_in he) heterm))
    · rw [update_neq _ _ heq] at he heterm ⊢
      exact hP h0 e he heterm
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP hreach
      hpkts hst _hps
    obtain ⟨-, hcases, -⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc
        t es res haer
    refine lae_of_update hP hreach hst
      (handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2 p.pSrc
        t es res haer)
      (by rw [hgd]) ?_
    rcases hcases with ⟨hcteq, -⟩ | ⟨hlt, -⟩
    · exact Nat.le_of_eq hcteq.symm
    · exact Nat.le_of_lt hlt
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      hreach hpkts hst _hps
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t p.pSrc lli
        llt hrv
    exact lae_of_update hP hreach hst
      (handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc lli
        llt hrv)
      (by subst hgd
          exact (update_elections_data_requestVote_cronies p.pDst p.pSrc
            t p.pSrc lli llt (net.nwState p.pDst)).2.2) hle
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts
      hst _hps
    refine lae_of_update hP hreach hst
      (by rw [← hrvr]
          exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
            p.pSrc t v)
      (by subst hgd
          exact (update_elections_data_requestVoteReply_votes p.pDst
            p.pSrc t v (net.nwState p.pDst)).2.2) ?_
    rcases (handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2
        p.pSrc t v hrvr).1 with ⟨hcteq, -⟩ | ⟨hlt, -⟩
    · exact Nat.le_of_eq hcteq.symm
    · exact Nat.le_of_lt hlt
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst _hps
    obtain ⟨hct, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
    refine lae_of_update hP hreach hst (by rw [hlog, hstate])
      (by rw [hstate]) ?_
    rw [hct, hstate]
    exact Nat.le_refl _
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hdgs hP hreach hstate hst _hps
    obtain ⟨hlog, -, hct, -, -, -⟩ := doGenericServer_spec h d hdgs
    refine lae_of_update hP hreach hst (by rw [hlog, hstate])
      (by rw [hstate]) ?_
    rw [hct, hstate]
    exact Nat.le_refl _
  · -- state_same_packet_subset
    intro net net' hstate _hpk hP _hreach
    intro h0 e he heterm
    rw [← hstate h0] at he heterm ⊢
    exact hP h0 e he heterm
  · -- reboot: log, term, and records all survive
    intro net net' gd d h d' hrb hP hreach hstate hst _hpkts
    refine lae_of_update hP hreach hst ?_ (by rw [hstate]) ?_
    · rw [← hrb, hstate]
      rfl
    · rw [← hrb, hstate]
      exact Nat.le_refl _

/-! ## lastApplied_le_commitIndex (`Raft/LastAppliedLeCommitIndexInterface.v`
/ `RaftProofs/LastAppliedLeCommitIndexProof.v`, BASE layer) -/

/-- `LastAppliedLeCommitIndexInterface.v` (`lastApplied_le_commitIndex`). -/
def lastApplied_le_commitIndex (net : RaftNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).lastApplied ≤ (net.nwState h).commitIndex

omit O in
/-- `advanceCurrentTerm` never touches the watermarks. -/
theorem advanceCurrentTerm_la_ci (st : raft_data (P := P)) (t : term) :
    (advanceCurrentTerm st t).lastApplied = st.lastApplied ∧
    (advanceCurrentTerm st t).commitIndex = st.commitIndex := by
  unfold advanceCurrentTerm
  split <;> exact ⟨rfl, rfl⟩

omit O in
/-- `LastAppliedLeCommitIndexProof.v` (the per-message movement, one
pass): every message handler keeps `lastApplied` and never lowers
`commitIndex`. -/
theorem handleAppendEntries_la_ci (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d m}
    (h : handleAppendEntries me st t lid pli plt es ci = (d, m)) :
    d.lastApplied = st.lastApplied ∧ st.commitIndex ≤ d.commitIndex := by
  have hadv := advanceCurrentTerm_la_ci st t
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals injection h with h1 h2
  all_goals rw [← h1]
  all_goals first
    | exact ⟨rfl, Nat.le_refl _⟩
    | exact ⟨hadv.1, Nat.le_of_eq hadv.2.symm⟩
    | exact ⟨hadv.1, Nat.le_max_left ..⟩

omit O in
theorem handleAppendEntriesReply_la_ci (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term)
    (es : List (entry (P := P))) (r : Bool) {d l}
    (h : handleAppendEntriesReply me st src t es r = (d, l)) :
    d.lastApplied = st.lastApplied ∧ d.commitIndex = st.commitIndex := by
  have hadv := advanceCurrentTerm_la_ci st t
  unfold handleAppendEntriesReply at h
  repeat' split at h
  all_goals injection h with h1 h2
  all_goals rw [← h1]
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact hadv

omit O in
theorem handleRequestVote_la_ci (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {d m}
    (h : handleRequestVote me st t cand lli llt = (d, m)) :
    d.lastApplied = st.lastApplied ∧ d.commitIndex = st.commitIndex := by
  have hadv := advanceCurrentTerm_la_ci st t
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals injection h with h1 h2
  all_goals rw [← h1]
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact hadv

omit O in
theorem handleRequestVoteReply_la_ci (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term)
    (v : Bool) :
    (handleRequestVoteReply me st src t v).lastApplied = st.lastApplied ∧
    (handleRequestVoteReply me st src t v).commitIndex = st.commitIndex := by
  have hadv := advanceCurrentTerm_la_ci st t
  unfold handleRequestVoteReply
  simp only []
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact hadv

omit O in
theorem handleTimeout_la_ci (me : name (P := P))
    (st : raft_data (P := P)) {out d l}
    (h : handleTimeout me st = (out, d, l)) :
    d.lastApplied = st.lastApplied ∧ d.commitIndex = st.commitIndex := by
  unfold handleTimeout tryToBecomeLeader at h
  split at h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h)
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

omit O in
theorem handleClientRequest_la_ci (me : name (P := P))
    (st : raft_data (P := P)) (client : R.clientId) (id : Nat)
    (c : P.input) {out d l}
    (h : handleClientRequest me st client id c = (out, d, l)) :
    d.lastApplied = st.lastApplied ∧ d.commitIndex = st.commitIndex := by
  unfold handleClientRequest at h
  split at h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h)
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

omit O R in
/-- `LastAppliedLeCommitIndexProof.v:71-84` (`fold_left_max`),
specialized. -/
theorem le_foldl_max : ∀ (l : List Nat) (z z' : Nat), z ≤ z' →
    z ≤ l.foldl max z' := by
  intro l
  induction l with
  | nil => exact fun z z' h => h
  | cons a l ih =>
    intro z z' h
    exact ih z (max z' a) (Nat.le_trans h (Nat.le_max_left ..))

omit O in
/-- `LastAppliedLeCommitIndexProof.v:60-120` (`doLeader` watermark
movement): `lastApplied` fixed, `commitIndex` only advances
(`advanceCommitIndex` folds `max`). -/
theorem doLeader_la_ci (st : raft_data (P := P)) (me : name (P := P))
    {os d' ms} (h : doLeader st me = (os, d', ms)) :
    d'.lastApplied = st.lastApplied ∧ st.commitIndex ≤ d'.commitIndex := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  all_goals first
    | exact ⟨rfl, Nat.le_refl _⟩
    | exact ⟨rfl, le_foldl_max _ _ _ (Nat.le_refl _)⟩

/-- `LastAppliedLeCommitIndexProof.v:122-137` (`doGenericServer`
watermark movement): `commitIndex` fixed; `lastApplied` either stays or
jumps exactly to `commitIndex`. -/
theorem doGenericServer_la_ci (h : name (P := P))
    (st : raft_data (P := P)) {os d' ms}
    (hdgs : doGenericServer h st = (os, d', ms)) :
    d'.commitIndex = st.commitIndex ∧
    (d'.lastApplied = st.lastApplied ∨ d'.lastApplied = st.commitIndex) := by
  unfold doGenericServer at hdgs
  rcases hae : applyEntries h st
      ((findGtIndex st.log st.lastApplied).filter
        (fun x => (st.lastApplied <? x.eIndex) && (x.eIndex <=? st.commitIndex))).reverse
    with ⟨o1, st1⟩
  rw [hae] at hdgs
  simp only [Prod.mk.injEq] at hdgs
  obtain ⟨-, rfl, -⟩ := hdgs
  obtain ⟨-, -, -, -, -, hci, hla⟩ := applyEntries_spec h _ st hae
  refine ⟨hci, ?_⟩
  split
  · exact Or.inr (by rw [hci])
  · exact Or.inl (by rw [hla])

/-- Per-node transport for `lastApplied_le_commitIndex`. -/
theorem lalci_of_update {net : RaftNet}
    {st' : name (P := P) → raft_data (P := P)} {ps'} {u : name (P := P)}
    {d : raft_data (P := P)}
    (hP : lastApplied_le_commitIndex net)
    (hst : ∀ h', st' h' = update net.nwState u d h')
    (himp : (net.nwState u).lastApplied ≤ (net.nwState u).commitIndex →
      d.lastApplied ≤ d.commitIndex) :
    lastApplied_le_commitIndex ⟨ps', st'⟩ := by
  intro h0
  show (st' h0).lastApplied ≤ (st' h0).commitIndex
  rw [hst h0]
  by_cases heq : u = h0
  · subst heq
    rw [update_same]
    exact himp (hP u)
  · rw [update_neq _ _ (Ne.symm heq)]
    exact hP h0

/-- `LastAppliedLeCommitIndexProof.v:200-223`
(`lastApplied_le_commitIndex_invariant`, BASE). -/
theorem lastApplied_le_commitIndex_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      lastApplied_le_commitIndex net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: both watermarks 0
    intro h
    exact Nat.le_refl _
  · -- client_request
    intro h net st' ps' out d l client id c hcr hP _hreach hst _hps
    obtain ⟨hla, hci⟩ :=
      handleClientRequest_la_ci h (net.nwState h) client id c hcr
    exact lalci_of_update hP hst (fun hle => by rw [hla, hci]; exact hle)
  · -- timeout
    intro net h st' ps' out d l hto hP _hreach hst _hps
    obtain ⟨hla, hci⟩ := handleTimeout_la_ci h (net.nwState h) hto
    exact lalci_of_update hP hst (fun hle => by rw [hla, hci]; exact hle)
  · -- append_entries
    intro xs p ys net st' ps' d m t n pli plt es ci hae hbody hP _hreach
      hpkts hst _hps
    obtain ⟨hla, hci⟩ :=
      handleAppendEntries_la_ci p.pDst (net.nwState p.pDst) t n pli plt
        es ci hae
    exact lalci_of_update hP hst
      (fun hle => by rw [hla]; exact Nat.le_trans hle hci)
  · -- append_entries_reply
    intro xs p ys net st' ps' d m t es res haer hbody hP _hreach hpkts
      hst _hps
    obtain ⟨hla, hci⟩ :=
      handleAppendEntriesReply_la_ci p.pDst (net.nwState p.pDst) p.pSrc
        t es res haer
    exact lalci_of_update hP hst (fun hle => by rw [hla, hci]; exact hle)
  · -- request_vote
    intro xs p ys net st' ps' d m t cid lli llt hrv hbody hP _hreach
      hpkts hst _hps
    obtain ⟨hla, hci⟩ :=
      handleRequestVote_la_ci p.pDst (net.nwState p.pDst) t p.pSrc lli
        llt hrv
    exact lalci_of_update hP hst (fun hle => by rw [hla, hci]; exact hle)
  · -- request_vote_reply
    intro xs p ys net st' ps' d t v hrvr hbody hP _hreach hpkts hst _hps
    obtain ⟨hla, hci⟩ :=
      handleRequestVoteReply_la_ci p.pDst (net.nwState p.pDst) p.pSrc t v
    exact lalci_of_update hP hst
      (fun hle => by rw [← hrvr] at *; rw [hla, hci]; exact hle)
  · -- do_leader
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hla, hci⟩ := doLeader_la_ci d h hdl
    refine lalci_of_update hP hst (fun hle => ?_)
    rw [hstate] at hle
    rw [hla]
    exact Nat.le_trans hle hci
  · -- do_generic_server
    intro net st' ps' d os d' ms h hdgs hP _hreach hstate hst _hps
    obtain ⟨hci, hla⟩ := doGenericServer_la_ci h d hdgs
    refine lalci_of_update hP hst (fun hle => ?_)
    rw [hstate] at hle
    rw [hci]
    rcases hla with hla | hla
    · rw [hla]
      exact hle
    · rw [hla]
      exact Nat.le_refl _
  · -- state_same_packet_subset
    intro net net' hstate _hpk hP _hreach
    intro h0
    rw [← hstate h0]
    exact hP h0
  · -- reboot: watermarks survive
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    intro h0
    rw [hst h0]
    by_cases heq : h = h0
    · subst heq
      rw [update_same, ← hrb]
      show (reboot d).lastApplied ≤ (reboot d).commitIndex
      have hh := hP h
      rw [hstate] at hh
      exact hh
    · rw [update_neq _ _ (Ne.symm heq)]
      exact hP h0

/-! ## no_append_entries_to_self (`Raft/NoAppendEntriesToSelfInterface.v`
/ `RaftProofs/NoAppendEntriesToSelfProof.v`, BASE layer) -/

/-- `NoAppendEntriesToSelfInterface.v` (`no_append_entries_to_self`). -/
def no_append_entries_to_self (net : RaftNet) : Prop :=
  ∀ (p : RaftPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    p.pDst = p.pSrc → False

omit O in
/-- `NoAppendEntriesToSelfProof.v:9-24` (`doLeader_no_messages_to_self`):
the replica fan-out filters the sender out. -/
theorem doLeader_messages_not_self (st : raft_data (P := P))
    (me : name (P := P)) {os d' ms}
    (h : doLeader st me = (os, d', ms)) :
    ∀ q ∈ ms, q.1 ≠ me := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, -, rfl⟩ := h
  all_goals intro q hq
  · obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hq
    obtain ⟨-, hfilter⟩ := List.mem_filter.mp hnode
    intro heq
    replace heq : node = me := heq
    rw [heq] at hfilter
    simp at hfilter
  · exact nomatch hq
  · exact nomatch hq

/-- `NoAppendEntriesToSelfProof.v:124-142`
(`no_append_entries_to_self_invariant`, BASE): only `doLeader` mints
AppendEntries, and its recipients exclude the sender. -/
theorem no_append_entries_to_self_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      no_append_entries_to_self net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro p t n pli plt es ci hp _ _
    exact nomatch hp
  · -- client_request: sends nothing
    intro h net st' ps' out d l client id c hcr hP _hreach hst hps
    intro p t n pli plt es ci hp hbody hdst
    rcases hps p hp with hold | hnew
    · exact hP p t n pli plt es ci hold hbody hdst
    · obtain ⟨-, -, -, -, hl⟩ :=
        handleClientRequest_spec h (net.nwState h) client id c hcr
      rw [hl] at hnew
      simp [send_packets] at hnew
  · -- timeout: RequestVotes only
    intro net h st' ps' out d l hto hP _hreach hst hps
    intro p t n pli plt es ci hp hbody hdst
    rcases hps p hp with hold | hnew
    · exact hP p t n pli plt es ci hold hbody hdst
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t3, c3, l3, l4, hq⟩ :=
        (handleTimeout_spec h (net.nwState h) hto).2.2 m0 hm0
      replace hbody : m0.2 = msg.AppendEntries t n pli plt es ci := hbody
      rw [hq] at hbody
      exact nomatch hbody
  · -- append_entries: the reply is an AppendEntriesReply
    intro xs p ys net st' ps' d m t n pli plt es ci hae hbody hP _hreach
      hpkts hst hps
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | rfl
    · exact hP p0 t0 n0 pli0 plt0 es0 ci0
        (by rw [hpkts]; exact mem_of_mem_remove_middle hold) hbody0 hdst0
    · obtain ⟨t', r, hm⟩ :=
        handleAppendEntries_reply_entries p.pDst (net.nwState p.pDst) t
          n pli plt es ci hae
      replace hbody0 : m = msg.AppendEntries t0 n0 pli0 plt0 es0 ci0 :=
        hbody0
      rw [hm] at hbody0
      exact nomatch hbody0
  · -- append_entries_reply: sends nothing
    intro xs p ys net st' ps' d m t es res haer hbody hP _hreach hpkts
      hst hps
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t0 n0 pli0 plt0 es0 ci0
        (by rw [hpkts]; exact mem_of_mem_remove_middle hold) hbody0 hdst0
    · obtain ⟨-, -, hm⟩ :=
        handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst) p.pSrc
          t es res haer
      rw [hm] at hnew
      simp [send_packets] at hnew
  · -- request_vote: the reply is a RequestVoteReply
    intro xs p ys net st' ps' d m t cid lli llt hrv hbody hP _hreach
      hpkts hst hps
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | rfl
    · exact hP p0 t0 n0 pli0 plt0 es0 ci0
        (by rw [hpkts]; exact mem_of_mem_remove_middle hold) hbody0 hdst0
    · obtain ⟨t', v, hm⟩ :=
        handleRequestVote_reply_shape p.pDst (net.nwState p.pDst) t
          p.pSrc lli llt hrv
      replace hbody0 : m = msg.AppendEntries t0 n0 pli0 plt0 es0 ci0 :=
        hbody0
      rw [hm] at hbody0
      exact nomatch hbody0
  · -- request_vote_reply: sends nothing
    intro xs p ys net st' ps' d t v hrvr hbody hP _hreach hpkts hst hps
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    exact hP p0 t0 n0 pli0 plt0 es0 ci0
      (by rw [hpkts]; exact mem_of_mem_remove_middle (hps p0 hp0))
      hbody0 hdst0
  · -- do_leader: recipients exclude the sender
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t0 n0 pli0 plt0 es0 ci0 hold hbody0 hdst0
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      have hne := doLeader_messages_not_self d h hdl m0 hm0
      replace hdst0 : m0.1 = h := hdst0
      exact hne hdst0
  · -- do_generic_server: sends nothing
    intro net st' ps' d os d' ms h hdgs hP _hreach hstate hst hps
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    rcases hps p0 hp0 with hold | hnew
    · exact hP p0 t0 n0 pli0 plt0 es0 ci0 hold hbody0 hdst0
    · obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hdgs
      rw [hms] at hnew
      simp [send_packets] at hnew
  · -- state_same_packet_subset
    intro net net' _hstate hpk hP _hreach
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    exact hP p0 t0 n0 pli0 plt0 es0 ci0 (hpk p0 hp0) hbody0 hdst0
  · -- reboot: packets unchanged
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    intro p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0
    rw [← hpkts] at hp0
    exact hP p0 t0 n0 pli0 plt0 es0 ci0 hp0 hbody0 hdst0

/-! ## match_index_sanity (`Raft/MatchIndexSanityInterface.v` /
`RaftProofs/MatchIndexSanityProof.v`, BASE layer) — a leader's
matchIndex estimates never point past its own log. The proof mirrors
the lane's `nextIndex_safety` (AppendEntriesChain.lean): the
append-entries-reply case rides `append_entries_reply_sublog` +
`maxIndex_is_max`, exactly upstream's argument. -/

/-- `MatchIndexSanityInterface.v:9-13` (`match_index_sanity`). -/
def match_index_sanity (net : RaftNet) : Prop :=
  ∀ leader h : name (P := P),
    (net.nwState leader).type = .Leader →
    assoc_default (net.nwState leader).matchIndex h 0 ≤
      maxIndex (net.nwState leader).log

/-- `cacheApplyEntry` never touches `matchIndex` (the `_nextIndex`
sibling's shape). -/
theorem cacheApplyEntry_matchIndex (st : raft_data (P := P))
    (e : entry (P := P)) {o st'} (h : cacheApplyEntry st e = (o, st')) :
    st'.matchIndex = st.matchIndex := by
  unfold cacheApplyEntry applyEntry at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl⟩ := h
  all_goals rfl

theorem applyEntries_matchIndex (me : name (P := P)) :
    ∀ (es : List (entry (P := P))) (st : raft_data (P := P)) {o st'},
    applyEntries me st es = (o, st') → st'.matchIndex = st.matchIndex := by
  intro es
  induction es with
  | nil =>
    intro st o st' h
    unfold applyEntries at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | cons e es ih =>
    intro st o st' h
    unfold applyEntries at h
    rcases hce : cacheApplyEntry st e with ⟨o1, st1⟩
    rw [hce] at h
    simp only [] at h
    rcases hae : applyEntries me st1 es with ⟨o2, st2⟩
    rw [hae] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact (ih st1 hae).trans (cacheApplyEntry_matchIndex st e hce)

/-- `SpecLemmas.v:970-980` (`doGenericServer_matchIndex_preserved`'s
matchIndex face). -/
theorem doGenericServer_matchIndex (me : name (P := P))
    (st : raft_data (P := P)) {os st' ms}
    (h : doGenericServer me st = (os, st', ms)) :
    st'.matchIndex = st.matchIndex := by
  unfold doGenericServer at h
  rcases hae : applyEntries me st
      ((findGtIndex st.log st.lastApplied).filter
        (fun x => (st.lastApplied <? x.eIndex) && (x.eIndex <=? st.commitIndex))).reverse
    with ⟨o1, st1⟩
  rw [hae] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  show st1.matchIndex = st.matchIndex
  exact applyEntries_matchIndex me _ st hae

omit O in
/-- `SpecLemmas.v:996-1004` (`doLeader_matchIndex_preserved`'s
matchIndex face). -/
theorem doLeader_matchIndex (st : raft_data (P := P)) (me : name (P := P))
    {os st' ms} (h : doLeader st me = (os, st', ms)) :
    st'.matchIndex = st.matchIndex := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  all_goals rfl

omit O in
/-- `SpecLemmas.v:916-924` (`handleTimeout_matchIndex_preserved`'s
matchIndex face — unconditional in our port: neither arm touches it). -/
theorem handleTimeout_matchIndex (me : name (P := P))
    (st : raft_data (P := P)) {out st' l}
    (h : handleTimeout me st = (out, st', l)) :
    st'.matchIndex = st.matchIndex := by
  unfold handleTimeout tryToBecomeLeader at h
  split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  all_goals rfl

omit O in
/-- `SpecLemmas.v:962-969` (`handleRequestVote_matchIndex_preserved`'s
matchIndex face). -/
theorem handleRequestVote_matchIndex (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m)) :
    st'.matchIndex = st.matchIndex := by
  have hadv : (advanceCurrentTerm st t).matchIndex = st.matchIndex := by
    unfold advanceCurrentTerm
    split
    · rfl
    · rfl
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | rfl
    | exact hadv

omit O in
/-- `SpecLemmas.v:938-951` (`handleClientRequest_matchIndex`): the log
and matchIndex both unchanged, or the leader records its own fresh
maxIndex. -/
theorem handleClientRequest_matchIndex (me : name (P := P))
    (st : raft_data (P := P)) (client : R.clientId) (id : Nat)
    (c : P.input) {out st' l}
    (h : handleClientRequest me st client id c = (out, st', l)) :
    (maxIndex st'.log = maxIndex st.log ∧ st'.matchIndex = st.matchIndex) ∨
    (st'.matchIndex = assoc_set st.matchIndex me (maxIndex st'.log) ∧
     maxIndex st'.log = maxIndex st.log + 1) := by
  unfold handleClientRequest at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact Or.inr ⟨rfl, rfl⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩

omit O in
/-- `MatchIndexSanityProof.v:88-105` (`handleAppendEntriesReply_matchIndex`):
a leader after an AppendEntriesReply keeps its matchIndex, or a true
same-term reply bumps the sender's slot to
`max (old slot) (maxIndex es)`. The log never moves. -/
theorem handleAppendEntriesReply_matchIndex (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term)
    (es : List (entry (P := P))) (res : Bool) {st' l}
    (h : handleAppendEntriesReply me st src t es res = (st', l))
    (hty : st'.type = .Leader) :
    st.type = st'.type ∧ st'.log = st.log ∧
    (st'.matchIndex = st.matchIndex ∨
     (res = true ∧ st.currentTerm = t ∧
      st'.matchIndex = assoc_set st.matchIndex src
        (max (assoc_default st.matchIndex src 0) (maxIndex es)))) := by
  unfold handleAppendEntriesReply advanceCurrentTerm at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  · rename_i heq hres
    simp only [beq_iff_eq] at heq
    exact ⟨rfl, rfl, Or.inr ⟨hres, heq, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl rfl⟩
  all_goals first
    | (rename_i hc1 hc2
       exact absurd hc1 hc2)
    | exact serverType.noConfusion hty
    | exact ⟨rfl, rfl, Or.inl rfl⟩

omit O in
/-- `MatchIndexSanityProof.v:148-161` (`handleRequestVoteReply_matchIndex`):
a leader after a RequestVoteReply keeps its matchIndex, or has just
won and reset it to its own maxIndex slot. -/
theorem handleRequestVoteReply_matchIndex (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term) (v : Bool)
    {st'} (h : handleRequestVoteReply me st src t v = st')
    (hty : st'.type = .Leader) :
    (st.type = .Leader ∧ st'.matchIndex = st.matchIndex) ∨
    st'.matchIndex = assoc_set [] me (maxIndex st.log) := by
  unfold handleRequestVoteReply advanceCurrentTerm at h
  simp only [] at h
  repeat' split at h
  all_goals subst h
  all_goals first
    | (rename_i hc1 hc2
       exact absurd hc1 hc2)
    | exact Or.inr rfl
    | exact Or.inl ⟨hty, rfl⟩
    | exact serverType.noConfusion hty

/-- `MatchIndexSanityProof.v:46-62` (`match_index_sanity_preserved`),
in the lane's `_of_update` transport shape. -/
theorem match_index_sanity_of_update {net : RaftNet}
    {ps' : List (Packet (raft_base_params (P := P)) raft_multi_params)}
    {st' : name (P := P) → raft_data (P := P)} {u : name (P := P)}
    {d : raft_data (P := P)}
    (hP : match_index_sanity net)
    (hst : ∀ h', st' h' = update net.nwState u d h')
    (hd : d.type = .Leader →
      (net.nwState u).type = .Leader ∧
      d.matchIndex = (net.nwState u).matchIndex ∧
      d.log = (net.nwState u).log) :
    match_index_sanity (⟨ps', st'⟩ : RaftNet) := by
  intro leader h hty
  replace hty : (st' leader).type = .Leader := hty
  show assoc_default (st' leader).matchIndex h 0 ≤ maxIndex (st' leader).log
  rw [hst leader] at hty ⊢
  by_cases heq : leader = u
  · rw [heq, update_same] at hty ⊢
    obtain ⟨hty0, hmi, hlog⟩ := hd hty
    rw [hmi, hlog]
    exact hP u h hty0
  · rw [update_neq _ _ heq] at hty ⊢
    exact hP leader h hty

/-- `MatchIndexSanityProof.v:232-253` (`match_index_sanity_invariant`),
BASE: a leader's matchIndex estimates never exceed its own maxIndex.
The append-entries-reply case rides `append_entries_reply_sublog`: a
true reply's entries are in the leader's own log. -/
theorem match_index_sanity_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      match_index_sanity net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: everyone starts a follower
    intro leader h hty
    exact nomatch hty
  · -- client_request: the leader records its own fresh maxIndex
    intro h net st' ps' out d l client id c hcr hP _hreach hst _hps
    obtain ⟨htyd, -, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h) client id c hcr
    intro leader h0 hty
    replace hty : (st' leader).type = .Leader := hty
    show assoc_default (st' leader).matchIndex h0 0 ≤
      maxIndex (st' leader).log
    rw [hst leader] at hty ⊢
    by_cases heq : leader = h
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      have hty0 : (net.nwState h).type = .Leader := by
        rw [← htyd]
        exact hty
      rcases handleClientRequest_matchIndex h (net.nwState h) client id c
        hcr with ⟨hmax, hmi⟩ | ⟨hmi, hmax⟩
      · rw [hmi, hmax]
        exact hP h h0 hty0
      · rw [hmi]
        by_cases hsrc : h0 = h
        · rw [hsrc, assoc_set_same_default]
          exact Nat.le_refl _
        · rw [assoc_set_diff_default _ _ _ _ _ hsrc, hmax]
          exact Nat.le_trans (hP h h0 hty0) (Nat.le_succ _)
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP leader h0 hty
  · -- timeout
    intro net h st' ps' out d l hto hP _hreach hst _hps
    obtain ⟨hlog, hbr, -⟩ := handleTimeout_spec h (net.nwState h) hto
    refine match_index_sanity_of_update hP hst ?_
    intro htyl
    rcases hbr with ⟨-, hty, -, -⟩ | ⟨-, hty, -, -, -⟩
    · rw [hty] at htyl
      exact ⟨htyl, handleTimeout_matchIndex h (net.nwState h) hto, hlog⟩
    · rw [hty] at htyl
      exact nomatch htyl
  · -- append_entries: a standing leader rejected
    intro xs p ys net st' ps' d m t n0 pli plt es ci hae _hbody hP _hreach
      _hpkts hst _hps
    refine match_index_sanity_of_update hP hst ?_
    intro htyl
    have hd : d = net.nwState p.pDst :=
      handleAppendEntries_reject_of_not_follower p.pDst (net.nwState p.pDst)
        t n0 pli plt es ci hae (by rw [htyl]; exact fun heq => nomatch heq)
    rw [hd]
    exact ⟨by rw [← hd]; exact htyl, rfl, rfl⟩
  · -- append_entries_reply: THE case
    intro xs p ys net st' ps' d m t es res haer hbody hP hreach hpkts hst
      _hps
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hsorted := (logs_sorted_invariant net hreach).1
    intro leader h0 hty
    replace hty : (st' leader).type = .Leader := hty
    show assoc_default (st' leader).matchIndex h0 0 ≤
      maxIndex (st' leader).log
    rw [hst leader] at hty ⊢
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      obtain ⟨htyeq, hlogd, hcases⟩ := handleAppendEntriesReply_matchIndex
        p.pDst (net.nwState p.pDst) p.pSrc t es res haer hty
      have hty0 : (net.nwState p.pDst).type = .Leader := by
        rw [htyeq]
        exact hty
      rw [hlogd]
      rcases hcases with hsame | ⟨hres, hct, hset⟩
      · rw [hsame]
        exact hP p.pDst h0 hty0
      · rw [hset]
        by_cases hsrc : h0 = p.pSrc
        · rw [hsrc, assoc_set_same_default]
          refine Nat.max_le.mpr ⟨hP p.pDst p.pSrc hty0, ?_⟩
          cases hes : es with
          | nil => exact Nat.zero_le _
          | cons e0 es' =>
            have he0 : e0 ∈ (net.nwState p.pDst).log :=
              append_entries_reply_sublog_invariant net hreach p t es
                p.pDst e0 hp_in (by rw [hbody, hres]) hct hty0
                (by rw [hes]; exact List.mem_cons_self ..)
            show e0.eIndex ≤ maxIndex (net.nwState p.pDst).log
            exact maxIndex_is_max (hsorted p.pDst) he0
        · rw [assoc_set_diff_default _ _ _ _ _ hsrc]
          exact hP p.pDst h0 hty0
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP leader h0 hty
  · -- request_vote
    intro xs p ys net st' ps' d m t cid lli llt hrv _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, -, hbr, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst) t p.pSrc lli llt
        hrv
    refine match_index_sanity_of_update hP hst ?_
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
  · -- request_vote_reply: a fresh win resets matchIndex to its own slot
    intro xs p ys net st' ps' d t v hrvr _hbody hP _hreach _hpkts hst _hps
    have hlogd : d.log = (net.nwState p.pDst).log := by
      rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst) p.pSrc
        t v
    intro leader h0 hty
    replace hty : (st' leader).type = .Leader := hty
    show assoc_default (st' leader).matchIndex h0 0 ≤
      maxIndex (st' leader).log
    rw [hst leader] at hty ⊢
    by_cases heq : leader = p.pDst
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      rcases handleRequestVoteReply_matchIndex p.pDst (net.nwState p.pDst)
        p.pSrc t v hrvr hty with ⟨hty0, hmi⟩ | hmi
      · rw [hmi, hlogd]
        exact hP p.pDst h0 hty0
      · rw [hmi, hlogd]
        by_cases hsrc : h0 = p.pDst
        · rw [hsrc, assoc_set_same_default]
          exact Nat.le_refl _
        · rw [assoc_set_diff_default _ _ _ _ _ hsrc]
          exact Nat.zero_le _
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP leader h0 hty
  · -- do_leader
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨-, -, hty, -, hlog, -⟩ := doLeader_spec d h hdl
    refine match_index_sanity_of_update hP hst ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨by rw [hstate]; exact htyl, ?_, ?_⟩
    · rw [doLeader_matchIndex d h hdl, hstate]
    · rw [hlog, hstate]
  · -- do_generic_server
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨hlog, hty, -, -, -, -⟩ := doGenericServer_spec h d hgs
    refine match_index_sanity_of_update hP hst ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨by rw [hstate]; exact htyl, ?_, ?_⟩
    · rw [doGenericServer_matchIndex h d hgs, hstate]
    · rw [hlog, hstate]
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach
    intro leader h0 hty
    replace hty : (net'.nwState leader).type = .Leader := hty
    show assoc_default (net'.nwState leader).matchIndex h0 0 ≤
      maxIndex (net'.nwState leader).log
    rw [← hstates leader] at hty ⊢
    exact hP leader h0 hty
  · -- reboot: a rebooted node is a follower
    intro net net' d h d' hrb hP _hreach hstate hst _hpkts
    refine match_index_sanity_of_update hP hst ?_
    intro htyl
    rw [← hrb] at htyl
    exact nomatch htyl

/-- `PrevLogCandidateEntriesTermInterface.v:10-16`
(`prevLog_candidateEntriesTerm`): every in-flight AppendEntries with a
positive prevLogTerm has an election-winner witness for that term. -/
def prevLog_candidateEntriesTerm (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (lid : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    0 < plt → candidateEntriesTerm plt net.nwState

/-- `PrevLogCandidateEntriesTermProof.v:428-449`
(`prevLog_candidateEntriesTerm_invariant`): old packets transport
through the per-handler preserves lemmas; the ONLY creation case is
`doLeader`, where the positive prevLogTerm is the term of the
`findAtIndex` pivot entry in the sender's own log, certified by
`candidate_entries_invariant` (host) through the definitional
`candidateEntries_term` bridge — exactly upstream's route. -/
theorem prevLog_candidateEntriesTerm_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      prevLog_candidateEntriesTerm net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro p t lid pli plt es ci hp _ _
    exact nomatch hp
  · -- client_request: no packets sent
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
    obtain ⟨hty, hct, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hgc : gd.cronies = (net.nwState h).1.cronies := by
      rw [hgd]
      exact (update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.1
    intro p0 t0 lid pli plt es ci hp0 hbody0 hplt
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hl] at h1
        simp [send_packets] at h1
    exact candidateEntriesTerm_ext hst
      (candidateEntriesTerm_update_same hgc hct hty
        (hP p0 t0 lid pli plt es ci hold hbody0 hplt))
  · -- timeout: only RequestVotes sent
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    obtain ⟨-, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
    intro p0 t0 lid pli plt es ci hp0 hbody0 hplt
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
        obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
        replace hbody0 : m0.2 = msg.AppendEntries t0 lid pli plt es ci :=
          hbody0
        rw [hq2] at hbody0
        exact nomatch hbody0
    subst hgd
    exact candidateEntriesTerm_ext hst
      (handleTimeout_preserves_candidateEntriesTerm hreach hto
        (hP p0 t0 lid pli plt es ci hold hbody0 hplt))
  · -- append_entries: the reply is an AppendEntriesReply
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt
        es ci hae
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
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
    subst hgd
    exact candidateEntriesTerm_ext hst
      (handleAppendEntries_preserves_candidateEntriesTerm hae
        (hP p0 t0 lid pli2 plt2 es2 ci2 hold hbody0 hplt))
  · -- append_entries_reply: no messages
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · rw [hl] at h1
        simp [send_packets] at h1
    subst hgd
    exact candidateEntriesTerm_ext hst
      (handleAppendEntriesReply_preserves_candidateEntriesTerm haer
        (hP p0 t0 lid pli2 plt2 es2 ci2 hold hbody0 hplt))
  · -- request_vote: the reply is a RequestVoteReply
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
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
    subst hgd
    exact candidateEntriesTerm_ext hst
      (handleRequestVote_preserves_candidateEntriesTerm hrv
        (hP p0 t0 lid pli2 plt2 es2 ci2 hold hbody0 hplt))
  · -- request_vote_reply: no sends
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts
      hst hps
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    subst hgd
    subst hrvr
    exact candidateEntriesTerm_ext hst
      (handleRequestVoteReply_preserves_candidateEntriesTerm hreach
        (hP p0 t0 lid pli2 plt2 es2 ci2 hold hbody0 hplt))
  · -- do_leader: THE creation case
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
    obtain ⟨hctd, -, htyd, -, -, -⟩ := doLeader_spec d h hdl
    have hgc : gd.cronies = (net.nwState h).1.cronies := by rw [hstate]
    have hctn : d'.currentTerm = (net.nwState h).2.currentTerm := by
      rw [hctd, hstate]
    have htyn : d'.type = (net.nwState h).2.type := by
      rw [htyd, hstate]
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · exact candidateEntriesTerm_ext hst
        (candidateEntriesTerm_update_same hgc hctn htyn
          (hP p0 t0 lid pli2 plt2 es2 ci2 hold hbody0 hplt))
    · -- fresh AE: plt2 is the findAtIndex pivot's term in the sender's log
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨pli3, ci3, hq2⟩ := doLeader_messages_full d h hdl m0 hm0
      replace hbody0 : m0.2 = msg.AppendEntries t0 lid pli2 plt2 es2 ci2 :=
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
        obtain ⟨he_in, -⟩ := findAtIndex_elim hfind
        have he' : e ∈ (net.nwState h).2.log := by
          rw [hstate]
          exact he_in
        have hcet : candidateEntriesTerm plt2 net.nwState := by
          rw [← f4]
          exact candidateEntries_term
            ((candidate_entries_invariant net hreach).1 h e he')
        exact candidateEntriesTerm_ext hst
          (candidateEntriesTerm_update_same hgc hctn htyn hcet)
  · -- do_generic_server: no messages
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨-, hty, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hgc : gd.cronies = (net.nwState h).1.cronies := by rw [hstate]
    have hctn : d'.currentTerm = (net.nwState h).2.currentTerm := by
      rw [hct, hstate]
    have htyn : d'.type = (net.nwState h).2.type := by
      rw [hty, hstate]
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hms] at h1
        simp [send_packets] at h1
    exact candidateEntriesTerm_ext hst
      (candidateEntriesTerm_update_same hgc hctn htyn
        (hP p0 t0 lid pli2 plt2 es2 ci2 hold hbody0 hplt))
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    exact candidateEntriesTerm_ext (fun h => (hstates h).symm)
      (hP p0 t0 lid pli2 plt2 es2 ci2 (hpkts p0 hp0) hbody0 hplt)
  · -- reboot: a rebooted node is a follower with its ghost intact
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    subst hrb
    intro p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    rw [← hpkts] at hp0
    refine candidateEntriesTerm_ext hst ?_
    obtain ⟨x, hw, himp⟩ := hP p0 t0 lid pli2 plt2 es2 ci2 hp0 hbody0 hplt
    by_cases hxh : x = h
    · subst hxh
      refine ⟨x, ?_, ?_⟩
      · rw [update_same]
        show wonElection (dedup (gd.cronies plt2)) = true
        rw [show gd.cronies = (net.nwState x).1.cronies from by rw [hstate]]
        exact hw
      · rw [update_same]
        show (reboot d).currentTerm = plt2 →
          (reboot d).type ≠ serverType.Candidate
        exact fun _ hcand => nomatch hcand
    · refine ⟨x, ?_, ?_⟩
      · rw [update_neq _ _ hxh]
        exact hw
      · rw [update_neq _ _ hxh]
        exact himp

end SafetyLeaves
end Raft
end VerdiCompat
