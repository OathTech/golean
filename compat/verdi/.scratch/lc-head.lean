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
        ⟨enew, hterm, hcons, hleader, -, -⟩
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

/-! ## allEntries_leader_sublog -/

/-- `AllEntriesLeaderSublogInterface.v:8-13` (`allEntries_leader_sublog`). -/
def allEntries_leader_sublog (net : RefinedNet) : Prop :=
  ∀ (leader : name (P := P)) (e : entry (P := P)) (h : name (P := P)),
    (net.nwState leader).2.type = .Leader →
    e ∈ (net.nwState h).1.allEntries.map Prod.snd →
    e.eTerm = (net.nwState leader).2.currentTerm →
    e ∈ (net.nwState leader).2.log

/-- `AllEntriesLeaderSublogProof.v:28-44` (`lifted_leader_sublog_nw`). -/
theorem lifted_leader_sublog_nw :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (p : RefinedPacket) (t : term) (n : name (P := P))
        (pli : logIndex) (plt : term) (es : List (entry (P := P)))
        (ci : logIndex) (leader : name (P := P)) (e : entry (P := P)),
        p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
        (net.nwState leader).2.type = .Leader → e ∈ es →
        e.eTerm = (net.nwState leader).2.currentTerm →
        e ∈ (net.nwState leader).2.log := by
  intro net hreach p t n pli plt es ci leader e hp hbody hty he hterm
  exact (lift_prop _ leader_sublog_invariant_invariant net hreach).2
    leader (deghost_packet p) t n pli plt es ci e hty
    (List.mem_map_of_mem hp) hbody he hterm

omit O in
/-- A TRUE AppendEntries reply leaves a follower behind. -/
theorem handleAppendEntries_true_reply_type (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d : raft_data (P := P)} {t' : term}
    {es' : List (entry (P := P))}
    (h : handleAppendEntries me st t lid pli plt es ci
      = (d, .AppendEntriesReply t' es' true)) :
    d.type = .Follower := by
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, hm⟩ := h
  all_goals first
    | rfl
    | (injection hm with f1 f2 f3
       exact nomatch f3)

omit O in
/-- A FALSE AppendEntries reply is a rejection: the state is untouched. -/
theorem handleAppendEntries_false_reply_state (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {d : raft_data (P := P)} {t' : term}
    {es' : List (entry (P := P))}
    (h : handleAppendEntries me st t lid pli plt es ci
      = (d, .AppendEntriesReply t' es' false)) :
    d = st := by
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, hm⟩ := h
  all_goals first
    | rfl
    | (injection hm with f1 f2 f3
       exact nomatch f3)

omit O in
/-- `AllEntriesLeaderSublogProof.v:99-118`
(`update_elections_data_appendEntries_log_allEntries_leader`): an
AppendEntries that leaves you a leader was a rejection — nothing moved. -/
theorem update_elections_data_appendEntries_log_allEntries_leader
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {d m}
    (hae : handleAppendEntries me st.2 t lid pli plt es ci = (d, m))
    (hty : d.type = .Leader) :
    d = st.2 ∧
    (update_elections_data_appendEntries me st t lid pli plt es
      ci).allEntries = st.1.allEntries := by
  obtain ⟨t'', r'', rfl⟩ :=
    handleAppendEntries_reply_entries me st.2 t lid pli plt es ci hae
  cases r''
  · have hds : d = st.2 :=
      handleAppendEntries_false_reply_state me st.2 t lid pli plt es ci
        hae
    refine ⟨hds, ?_⟩
    show (update_elections_data_appendEntries me st t lid pli plt es
      ci).allEntries = st.1.allEntries
    unfold update_elections_data_appendEntries
    rw [hae]
  · exfalso
    have hf := handleAppendEntries_true_reply_type me st.2 t lid pli plt
      es ci hae
    rw [hf] at hty
    exact nomatch hty

/-- `AllEntriesLeaderSublogProof.v` (`allEntries_leader_sublog_invariant`):
a leader's current-term record is in its log — fresh CR records are the
leader's own head (or `one_leader_per_term` kills a second leader);
fresh AE records ride the lifted nw `leader_sublog`; an RVR that mints
a leader dies on `wonElection_candidateEntries_rvr` against
`allEntries_candidateEntries` (W1's payoff). -/
theorem allEntries_leader_sublog_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_leader_sublog net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro leader e h _ he _
    exact nomatch he
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    obtain ⟨htyeq, hcteq, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    -- the leader's post-state ct/type project to the pre-state
    have htyL : (net.nwState leader).2.type = .Leader := by
      rw [hst leader] at hty
      by_cases heql : leader = h
      · subst heql
        rw [update_same] at hty
        rw [← htyeq]
        exact hty
      · rw [update_neq _ _ heql] at hty
        exact hty
    have hctL : (st' leader).2.currentTerm
        = (net.nwState leader).2.currentTerm := by
      rw [hst leader]
      by_cases heql : leader = h
      · subst heql
        rw [update_same]
        exact hcteq
      · rw [update_neq _ _ heql]
    -- membership: old record, or the fresh head
    have hmem : e ∈ (net.nwState h0).1.allEntries.map Prod.snd ∨
        (h0 = h ∧ ∃ enew : entry (P := P),
          e = enew ∧ enew.eTerm = d.currentTerm ∧
          (net.nwState h).2.type = .Leader ∧ enew ∈ d.log) := by
      rw [hst h0] at he
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        subst hgd
        rcases update_elections_data_client_request_allEntries_head_term
          h0 (net.nwState h0) client id c hcr with hsame |
          ⟨enew, henterm, hcons, hleader, hend, -⟩
        · rw [hsame] at he
          exact Or.inl he
        · rw [hcons] at he
          rcases List.mem_map.mp he with ⟨⟨tp, ep⟩, hpmem, hpe⟩
          rcases List.mem_cons.mp hpmem with heqp | hold
          · injection heqp with h1 h2
            refine Or.inr ⟨rfl, enew, ?_, henterm, hleader, hend⟩
            rw [← hpe, h2]
          · exact Or.inl (List.mem_map.mpr ⟨(tp, ep), hold, hpe⟩)
      · rw [update_neq _ _ heq0] at he
        exact Or.inl he
    rcases hmem with hold | ⟨heq0h, enew, heenew, henterm, hleaderu, hend⟩
    · -- old record: the pre-state invariant, log only grows at h
      have hin := hP leader e h0 htyL hold (by rw [← hctL, ← hterm])
      rw [hst leader]
      by_cases heql : leader = h
      · subst heql
        rw [update_same]
        show e ∈ d.log
        rcases handleClientRequest_log_full leader
          (net.nwState leader).2 client id c hcr with ⟨-, hlogd⟩ |
          ⟨-, heqd⟩
        · rw [hlogd]
          exact List.mem_cons_of_mem _ hin
        · rw [heqd]
          exact hin
      · rw [update_neq _ _ heql]
        exact hin
    · -- the fresh record: its recorder is a leader at the same term —
      -- one leader per term makes it THE leader
      have hcteq2 : (net.nwState h).2.currentTerm
          = (net.nwState leader).2.currentTerm := by
        rw [← hcteq, ← henterm, ← heenew, hterm, hctL]
      have heq : h = leader :=
        lifted_one_leader_per_term net hreach h leader hcteq2 hleaderu
          htyL
      rw [← heq, hst h, update_same]
      show e ∈ d.log
      rw [heenew]
      exact hend
  · -- timeout: nothing moves (or the leader stopped being one)
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    obtain ⟨hlog, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hgd,
          (update_elections_data_timeout_ghost h0 (net.nwState h0)).2]
          at he
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = h
    · subst heql
      rw [update_same] at hty hterm ⊢
      replace hty : d.type = .Leader := hty
      rcases hcases with ⟨hct2, hty2, -, -⟩ | ⟨-, hty2, -, -, -⟩
      · show e ∈ d.log
        rw [hlog]
        refine hP leader e h0 ?_ he' ?_
        · rw [← hty2]
          exact hty
        · rw [← hct2]
          exact hterm
      · rw [hty2] at hty
        exact nomatch hty
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm
  · -- append_entries
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd hbody hP
      hreach hpkts hst hps
    have hpin : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    by_cases heql : leader = p.pDst
    · -- the updated node stayed leader: the AE was a rejection
      subst heql
      rw [hst p.pDst, update_same] at hty hterm ⊢
      replace hty : d.type = .Leader := hty
      obtain ⟨hds, hghost⟩ :=
        update_elections_data_appendEntries_log_allEntries_leader p.pDst
          (net.nwState p.pDst) t n0 pli plt es ci hae hty
      subst hds
      show e ∈ (net.nwState p.pDst).2.log
      have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
        rw [hst h0] at he
        by_cases heq0 : h0 = p.pDst
        · subst heq0
          rw [update_same] at he
          replace he : e ∈ gd.allEntries.map Prod.snd := he
          rw [hgd, hghost] at he
          exact he
        · rw [update_neq _ _ heq0] at he
          exact he
      exact hP p.pDst e h0 hty he' hterm
    · rw [hst leader, update_neq _ _ heql] at hty hterm ⊢
      have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd ∨
          e ∈ es := by
        rw [hst h0] at he
        by_cases heq0 : h0 = p.pDst
        · subst heq0
          rw [update_same] at he
          replace he : e ∈ gd.allEntries.map Prod.snd := he
          rw [hgd] at he
          rcases update_elections_data_appendEntries_allEntries_term_cases
            p.pDst (net.nwState p.pDst) t n0 pli plt es ci hae with
            hsame | ⟨t', -, hcons⟩
          · rw [hsame] at he
            exact Or.inl he
          · rw [hcons] at he
            rcases List.mem_map.mp he with ⟨⟨tp, ep⟩, hpmem, hpe⟩
            rcases List.mem_append.mp hpmem with hmap | hold
            · obtain ⟨e2, he2, heq2⟩ := List.mem_map.mp hmap
              injection heq2 with h1 h2
              right
              rw [← hpe, ← h2]
              exact he2
            · exact Or.inl (List.mem_map.mpr ⟨(tp, ep), hold, hpe⟩)
        · rw [update_neq _ _ heq0] at he
          exact Or.inl he
      rcases he' with hold | hees
      · exact hP leader e h0 hty hold hterm
      · exact lifted_leader_sublog_nw net hreach p t n0 pli plt es ci
          leader e hpin hbody hty hees hterm
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, hcases, -⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    have hlog := handleAppendEntriesReply_log p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hgd] at he
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = p.pDst
    · subst heql
      rw [update_same] at hty hterm ⊢
      replace hty : d.type = .Leader := hty
      rcases hcases with ⟨hct2, -, hty2⟩ | ⟨-, -, hty2⟩
      · show e ∈ d.log
        rw [hlog]
        refine hP p.pDst e h0 ?_ he' ?_
        · rw [← hty2]
          exact hty
        · rw [← hct2]
          exact hterm
      · rw [hty2] at hty
        exact nomatch hty
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨-, -, hcases, -⟩ := handleRequestVote_spec p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t
      p.pSrc lli llt hrv
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hgd, (update_elections_data_requestVote_cronies p.pDst
          p.pSrc t p.pSrc lli llt (net.nwState p.pDst)).2.2] at he
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = p.pDst
    · subst heql
      rw [update_same] at hty hterm ⊢
      replace hty : d.type = .Leader := hty
      rcases hcases with ⟨hct2, hty2⟩ | hty2
      · show e ∈ d.log
        rw [hlog]
        refine hP p.pDst e h0 ?_ he' ?_
        · rw [← hty2]
          exact hty
        · rw [← hct2]
          exact hterm
      · rw [hty2] at hty
        exact nomatch hty
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm
  · -- request_vote_reply: a freshly minted leader dies on
    -- candidate-entries; otherwise nothing moved
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts
      hst hps
    have hpin : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = p.pDst
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hgd, (update_elections_data_requestVoteReply_votes p.pDst
          p.pSrc t v (net.nwState p.pDst)).2.2] at he
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = p.pDst
    · subst heql
      rw [update_same] at hty hterm ⊢
      replace hty : d.type = .Leader := hty
      rcases handleRequestVoteReply_RVR_spec p.pDst
        (net.nwState p.pDst).2 p.pSrc t v hrvr with heqd |
        ⟨htyf, -, -⟩ | ⟨hct2, hlog2, hwin | hty2⟩
      · -- unchanged
        subst heqd
        exact hP p.pDst e h0 hty he' hterm
      · rw [htyf] at hty
        exact nomatch hty
      · -- fresh win: the record at the winner's term contradicts
        -- candidate entries
        exfalso
        obtain ⟨hcand, -, hv, hctt, hwon⟩ := hwin
        obtain ⟨⟨tp, ep⟩, hpmem, hpe⟩ := List.mem_map.mp he'
        have hce : candidateEntries e net.nwState := by
          have := allEntries_candidateEntries_invariant net hreach h0 tp
            ep hpmem
          rw [← hpe]
          exact this
        have hteq : e.eTerm = t := by
          rw [hterm, hct2, hctt]
        have hbody' : p.pBody = .RequestVoteReply e.eTerm true := by
          rw [_hbody, hteq, hv]
        have hct3 : (net.nwState p.pDst).2.currentTerm = e.eTerm := by
          rw [hteq]
          exact hctt
        exact wonElection_candidateEntries_rvr
          (votes_correct_invariant net hreach)
          (cronies_correct_invariant net hreach) hce hpin hbody' hct3
          hwon hcand
      · -- type carried: it was already the leader
        show e ∈ d.log
        rw [hlog2]
        refine hP p.pDst e h0 ?_ he' ?_
        · rw [← hty2]
          exact hty
        · rw [← hct2]
          exact hterm
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hct2, -, hty2, -, hlog2, -⟩ := doLeader_spec d h hdl
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hstate]
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = h
    · subst heql
      rw [update_same] at hty hterm ⊢
      replace hty : d'.type = .Leader := hty
      show e ∈ d'.log
      rw [hlog2]
      have hd : e ∈ (net.nwState leader).2.log := by
        refine hP leader e h0 ?_ he' ?_
        · rw [hstate]
          show d.type = .Leader
          rw [← hty2]
          exact hty
        · rw [hstate]
          show e.eTerm = d.currentTerm
          rw [← hct2]
          exact hterm
      rw [hstate] at hd
      exact hd
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hlog2, hty2, hct2, -, -, -⟩ := doGenericServer_spec h d hgs
    intro leader e h0 hty he hterm
    replace hty : (st' leader).2.type = .Leader := hty
    replace he : e ∈ (st' h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (st' leader).2.currentTerm := hterm
    show e ∈ (st' leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hstate]
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = h
    · subst heql
      rw [update_same] at hty hterm ⊢
      replace hty : d'.type = .Leader := hty
      show e ∈ d'.log
      rw [hlog2]
      have hd : e ∈ (net.nwState leader).2.log := by
        refine hP leader e h0 ?_ he' ?_
        · rw [hstate]
          show d.type = .Leader
          rw [← hty2]
          exact hty
        · rw [hstate]
          show e.eTerm = d.currentTerm
          rw [← hct2]
          exact hterm
      rw [hstate] at hd
      exact hd
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach leader e h0 hty he hterm
    replace hty : (net'.nwState leader).2.type = .Leader := hty
    replace he : e ∈ (net'.nwState h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (net'.nwState leader).2.currentTerm := hterm
    show e ∈ (net'.nwState leader).2.log
    rw [← hstates leader] at hty hterm ⊢
    rw [← hstates h0] at he
    exact hP leader e h0 hty he hterm
  · -- reboot: the leader survives only away from the reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    intro leader e h0 hty he hterm
    replace hty : (net'.nwState leader).2.type = .Leader := hty
    replace he : e ∈ (net'.nwState h0).1.allEntries.map Prod.snd := he
    replace hterm : e.eTerm = (net'.nwState leader).2.currentTerm := hterm
    show e ∈ (net'.nwState leader).2.log
    have he' : e ∈ (net.nwState h0).1.allEntries.map Prod.snd := by
      rw [hst h0] at he
      by_cases heq0 : h0 = h
      · subst heq0
        rw [update_same] at he
        replace he : e ∈ gd.allEntries.map Prod.snd := he
        rw [hstate]
        exact he
      · rw [update_neq _ _ heq0] at he
        exact he
    rw [hst leader] at hty hterm ⊢
    by_cases heql : leader = h
    · subst heql
      rw [update_same] at hty
      replace hty : d'.type = .Leader := hty
      rw [← hrb] at hty
      exact nomatch hty
    · rw [update_neq _ _ heql] at hty hterm ⊢
      exact hP leader e h0 hty he' hterm

/-! ## allEntries_log_matching -/

/-- `AllEntriesLogMatchingInterface.v:8-14` (`allEntries_log_matching`). -/
def allEntries_log_matching (net : RefinedNet) : Prop :=
  ∀ (e e' : entry (P := P)) (h h' : name (P := P)),
    e ∈ (net.nwState h).2.log →
    e' ∈ (net.nwState h').1.allEntries.map Prod.snd →
    e.eTerm = e'.eTerm → e.eIndex = e'.eIndex → e = e'

/-- `AllEntriesLogMatchingProof.v:20-27` (`allEntries_log_matching_nw`). -/
def allEntries_log_matching_nw (net : RefinedNet) : Prop :=
  ∀ (e e' : entry (P := P)) (h : name (P := P)) (p : RefinedPacket)
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets →
    p.pBody = .AppendEntries t lid pli plt es ci →
    e ∈ es →
    e' ∈ (net.nwState h).1.allEntries.map Prod.snd →
    e.eTerm = e'.eTerm → e.eIndex = e'.eIndex → e = e'

/-- `AllEntriesLogMatchingProof.v:29-30`
(`allEntries_log_matching_inductive`). -/
def allEntries_log_matching_inductive (net : RefinedNet) : Prop :=
  allEntries_log_matching net ∧ allEntries_log_matching_nw net

/-- `AllEntriesLogMatchingProof.v:124-139` (`packets_entries_eq`):
matched entries across two in-flight packets coincide, by
`entries_match_nw_1` + contiguity + unique indices. -/
theorem almi_packets_entries_eq {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {p p0 : RefinedPacket} {t0 : term} {lid0 : name (P := P)}
    {pli0 : logIndex} {plt0 : term} {es0 : List (entry (P := P))}
    {ci0 : logIndex} {t : term} {lid : name (P := P)} {pli : logIndex}
    {plt : term} {es : List (entry (P := P))} {ci : logIndex}
    {e e' : entry (P := P)}
    (hp0 : p0 ∈ net.nwPackets) (hp : p ∈ net.nwPackets)
    (hbody0 : p0.pBody = .AppendEntries t0 lid0 pli0 plt0 es0 ci0)
    (hbody : p.pBody = .AppendEntries t lid pli plt es ci)
    (he : e ∈ es0) (he' : e' ∈ es)
    (hterm : e.eTerm = e'.eTerm) (hidx : e.eIndex = e'.eIndex) :
    e = e' := by
  have hgt : pli < e'.eIndex :=
    (entries_contiguous_nw_invariant net hreach p t lid pli plt es ci hp
      hbody).2 e' he'
  have hees : e ∈ es :=
    entries_match_nw_1_invariant net hreach p0 t0 lid0 pli0 plt0 es0 ci0
      p t lid pli plt es ci e e' e hp0 hp hbody0 hbody he he' hidx hterm
      he ⟨hidx ▸ hgt, Nat.le_refl _⟩
  exact uniqueIndices_elim_eq
    (sorted_uniqueIndices
      (entries_sorted_nw_invariant net hreach p t lid pli plt es ci hp
        hbody))
    hees he' hidx

/-- Transport for `allEntries_log_matching_inductive` across steps that
keep the updated node's log and allEntries and send no AppendEntries. -/
theorem almi_of_update {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : allEntries_log_matching_inductive net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hae : gd.allEntries = (net.nwState u).1.allEntries)
    (hlog : d.log = (net.nwState u).2.log)
    (hpk : ∀ (p' : RefinedPacket) (t : term) (lid : name (P := P))
      (pli : logIndex) (plt : term) (es : List (entry (P := P)))
      (ci : logIndex), p' ∈ net'.nwPackets →
      p'.pBody = .AppendEntries t lid pli plt es ci →
      p' ∈ net.nwPackets) :
    allEntries_log_matching_inductive net' := by
  obtain ⟨hH, hN⟩ := hP
  have hlogred : ∀ h0, (net'.nwState h0).2.log = (net.nwState h0).2.log := by
    intro h0
    rw [hst h0]
    by_cases heq : h0 = u
    · subst heq
      rw [update_same]
      exact hlog
    · rw [update_neq _ _ heq]
  have haered : ∀ h0, (net'.nwState h0).1.allEntries
      = (net.nwState h0).1.allEntries := by
    intro h0
    rw [hst h0]
    by_cases heq : h0 = u
    · subst heq
      rw [update_same]
      exact hae
    · rw [update_neq _ _ heq]
  constructor
  · intro e e' h h' he he'
    rw [hlogred h] at he
    rw [haered h'] at he'
    exact hH e e' h h' he he'
  · intro e e' h p t lid pli plt es ci hp hbody he he'
    rw [haered h] at he'
    exact hN e e' h p t lid pli plt es ci
      (hpk p t lid pli plt es ci hp hbody) hbody he he'

end LeaderCompleteness
end Raft
end VerdiCompat
