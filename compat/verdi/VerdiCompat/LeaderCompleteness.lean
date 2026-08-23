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

/-- `AllEntriesLogMatchingProof.v:330-430`
(`allEntries_log_matching_inductive_invariant`): host logs and
in-flight entries never disagree with the records — the fresh-record
quadrants ride the (host/nw) `leader_sublog` lifts and the RLML
`entries_match` bridge; two packets glue through `packets_entries_eq`. -/
theorem allEntries_log_matching_inductive_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_log_matching_inductive net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    constructor
    · intro e e' h h' he _ _ _
      exact nomatch he
    · intro e e' h p t lid pli plt es ci hp _ _ _ _ _
      exact nomatch hp
  · -- client_request: the fresh head record sits above every index
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    obtain ⟨hH, hN⟩ := hP
    obtain ⟨-, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hpk : ∀ (p' : RefinedPacket) (t : term) (lid : name (P := P))
        (pli : logIndex) (plt : term) (es : List (entry (P := P)))
        (ci : logIndex), p' ∈ ps' →
        p'.pBody = .AppendEntries t lid pli plt es ci →
        p' ∈ net.nwPackets := by
      intro p' t lid pli plt es ci hp' _
      rcases hps p' hp' with h1 | h1
      · exact h1
      · rw [hl] at h1
        simp [send_packets] at h1
    rcases update_elections_data_client_request_allEntries_head_term h
      (net.nwState h) client id c hcr with hsame |
      ⟨enew, henterm, hcons, hleader, henmem, henidx⟩
    · -- allEntries unchanged; the log can still have grown, but a
      -- grown log means a fresh record too — so here the log is
      -- unchanged as well (a leader's append always records)
      rcases handleClientRequest_log_full h (net.nwState h).2 client id
        c hcr with ⟨htyL, hlogd⟩ | ⟨-, heqd⟩
      · -- leader append with no record: impossible — the ghost guard
        -- fires exactly on log growth
        exfalso
        have hlen : ((net.nwState h).2.log.length <?
            d.log.length) = true := by
          rw [hlogd]
          simp only [Nat.blt_eq, List.length_cons]
          exact Nat.lt_succ_self _
        have hbad := hsame
        unfold update_elections_data_client_request at hbad
        rw [hcr] at hbad
        simp only [] at hbad
        rw [if_pos hlen, hlogd] at hbad
        have hlen2 := congrArg List.length hbad
        simp only [List.length_cons] at hlen2
        exact Nat.succ_ne_self _ hlen2
      · refine almi_of_update ⟨hH, hN⟩ hst ?_ ?_ hpk
        · rw [hgd]
          exact hsame
        · rw [heqd]
    · -- the fresh head: above every old index
      obtain ⟨htyL, hlogd⟩ | ⟨htynl, -⟩ :=
        handleClientRequest_log_full h (net.nwState h).2 client id c hcr
      case inr => exact absurd hleader htynl
      have hsortu : sorted (net.nwState h).2.log :=
        sorted_host_lifted net hreach h
      -- eliminations
      have hlogel : ∀ (h0 : name (P := P)) (e : entry (P := P)),
          e ∈ (st' h0).2.log →
          e ∈ (net.nwState h0).2.log ∨ (h0 = h ∧ e = enew) := by
        intro h0 e he
        rw [hst h0] at he
        by_cases heq : h0 = h
        · subst heq
          rw [update_same] at he
          replace he : e ∈ d.log := he
          rw [hlogd] at he
          rcases List.mem_cons.mp he with rfl | hold
          · right
            refine ⟨rfl, ?_⟩
            -- e is the log's head literal; enew is the recorded head:
            -- both are members of d.log at index maxIndex+1
            have henmem' := henmem
            rw [hlogd] at henmem'
            rcases List.mem_cons.mp henmem' with heq2 | hold2
            · exact heq2.symm
            · exfalso
              have := maxIndex_is_max hsortu hold2
              rw [henidx] at this
              exact Nat.not_succ_le_self _ this
          · exact Or.inl hold
        · rw [update_neq _ _ heq] at he
          exact Or.inl he
      have haeel : ∀ (h0 : name (P := P)) (e' : entry (P := P)),
          e' ∈ (st' h0).1.allEntries.map Prod.snd →
          e' ∈ (net.nwState h0).1.allEntries.map Prod.snd ∨
          (h0 = h ∧ e' = enew) := by
        intro h0 e' he'
        rw [hst h0] at he'
        by_cases heq : h0 = h
        · subst heq
          rw [update_same] at he'
          replace he' : e' ∈ gd.allEntries.map Prod.snd := he'
          rw [hgd, hcons] at he'
          rcases List.mem_map.mp he' with ⟨⟨tp, ep⟩, hpmem, hpe⟩
          rcases List.mem_cons.mp hpmem with heqp | hold
          · injection heqp with h1 h2
            right
            refine ⟨rfl, ?_⟩
            rw [← hpe, h2]
          · exact Or.inl (List.mem_map.mpr ⟨(tp, ep), hold, hpe⟩)
        · rw [update_neq _ _ heq] at he'
          exact Or.inl he'
      -- the two lifted-sublog contradictions
      have habsurd_log : ∀ (h0 : name (P := P)) (e : entry (P := P)),
          e ∈ (net.nwState h0).2.log → e.eTerm = enew.eTerm →
          e.eIndex = enew.eIndex → False := by
        intro h0 e he hterm hidx
        have hct : e.eTerm = (net.nwState h).2.currentTerm := by
          rw [hterm, henterm,
            (handleClientRequest_spec h (net.nwState h).2 client id c
              hcr).2.1]
        have hin := lifted_leader_sublog_host net hreach h h0 e htyL he
          hct
        have := maxIndex_is_max hsortu hin
        rw [hidx, henidx] at this
        exact Nat.not_succ_le_self _ this
      have habsurd_ae : ∀ (h0 : name (P := P)) (e' : entry (P := P)),
          e' ∈ (net.nwState h0).1.allEntries.map Prod.snd →
          e'.eTerm = enew.eTerm → e'.eIndex = enew.eIndex → False := by
        intro h0 e' he' hterm hidx
        have hct : e'.eTerm = (net.nwState h).2.currentTerm := by
          rw [hterm, henterm,
            (handleClientRequest_spec h (net.nwState h).2 client id c
              hcr).2.1]
        have hin := allEntries_leader_sublog_invariant net hreach h e'
          h0 htyL he' hct
        have := maxIndex_is_max hsortu hin
        rw [hidx, henidx] at this
        exact Nat.not_succ_le_self _ this
      constructor
      · intro e e' h0 h1 he he' hterm hidx
        rcases hlogel h0 e he with heold | ⟨-, rfl⟩
        · rcases haeel h1 e' he' with he'old | ⟨-, rfl⟩
          · exact hH e e' h0 h1 heold he'old hterm hidx
          · exact (habsurd_log h0 e heold hterm hidx).elim
        · rcases haeel h1 e' he' with he'old | ⟨-, rfl⟩
          · exact (habsurd_ae h1 e' he'old hterm.symm hidx.symm).elim
          · rfl
      · intro e e' h0 p t lid pli plt es ci hp hbody he he' hterm hidx
        have hp' := hpk p t lid pli plt es ci hp hbody
        rcases haeel h0 e' he' with he'old | ⟨-, rfl⟩
        · exact hN e e' h0 p t lid pli plt es ci hp' hbody he he'old
            hterm hidx
        · exfalso
          have hct : e.eTerm = (net.nwState h).2.currentTerm := by
            rw [hterm, henterm,
              (handleClientRequest_spec h (net.nwState h).2 client id c
                hcr).2.1]
          have hin := lifted_leader_sublog_nw net hreach p t lid pli plt
            es ci h e hp' hbody htyL he hct
          have := maxIndex_is_max hsortu hin
          rw [hidx, henidx] at this
          exact Nat.not_succ_le_self _ this
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    obtain ⟨hlog, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine almi_of_update hP hst ?_ hlog ?_
    · rw [hgd]
      exact (update_elections_data_timeout_ghost h (net.nwState h)).2
    · intro p' t lid pli plt es ci hp' hbody'
      rcases hps p' hp' with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
        obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
        replace hbody' : m0.2 = msg.AppendEntries t lid pli plt es ci :=
          hbody'
        rw [hq2] at hbody'
        exact nomatch hbody'
  · -- append_entries: the packet's entries against the records
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd hbody hP
      hreach hpkts hst hps
    obtain ⟨hH, hN⟩ := hP
    have hpin : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt
        es ci hae
    have hpk : ∀ (p' : RefinedPacket) (t2 : term) (lid : name (P := P))
        (pli2 : logIndex) (plt2 : term) (es2 : List (entry (P := P)))
        (ci2 : logIndex), p' ∈ ps' →
        p'.pBody = .AppendEntries t2 lid pli2 plt2 es2 ci2 →
        p' ∈ net.nwPackets := by
      intro p' t2 lid pli2 plt2 es2 ci2 hp' hbody'
      rcases hps p' hp' with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody'
        replace hbody' : m = msg.AppendEntries t2 lid pli2 plt2 es2 ci2 :=
          hbody'
        rw [hmshape] at hbody'
        exact nomatch hbody'
    -- membership eliminations at the updated node
    have hlogel : ∀ (h0 : name (P := P)) (e : entry (P := P)),
        e ∈ (st' h0).2.log →
        e ∈ (net.nwState h0).2.log ∨ e ∈ es := by
      intro h0 e he
      rw [hst h0] at he
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at he
        replace he : e ∈ d.log := he
        rcases handleAppendEntries_log_cases p.pDst (net.nwState p.pDst).2 t n0
          pli plt es ci hae with hsame | ⟨-, hlogd⟩ |
          ⟨e0, -, -, -, hlogd⟩
        · rw [hsame] at he
          exact Or.inl he
        · rw [hlogd] at he
          exact Or.inr he
        · rw [hlogd] at he
          rcases List.mem_append.mp he with hnew | hold
          · exact Or.inr hnew
          · exact Or.inl (removeAfterIndex_in hold)
      · rw [update_neq _ _ heq] at he
        exact Or.inl he
    have haeel : ∀ (h0 : name (P := P)) (e' : entry (P := P)),
        e' ∈ (st' h0).1.allEntries.map Prod.snd →
        e' ∈ (net.nwState h0).1.allEntries.map Prod.snd ∨ e' ∈ es := by
      intro h0 e' he'
      rw [hst h0] at he'
      by_cases heq : h0 = p.pDst
      · subst heq
        rw [update_same] at he'
        replace he' : e' ∈ gd.allEntries.map Prod.snd := he'
        rw [hgd] at he'
        rcases update_elections_data_appendEntries_allEntries_term_cases
          p.pDst (net.nwState p.pDst) t n0 pli plt es ci hae with hsame |
          ⟨t2, -, hcons⟩
        · rw [hsame] at he'
          exact Or.inl he'
        · rw [hcons] at he'
          rcases List.mem_map.mp he' with ⟨⟨tp, ep⟩, hpmem, hpe⟩
          rcases List.mem_append.mp hpmem with hmap | hold
          · obtain ⟨e2, he2, heq2⟩ := List.mem_map.mp hmap
            injection heq2 with h1 h2
            right
            rw [← hpe, ← h2]
            exact he2
          · exact Or.inl (List.mem_map.mpr ⟨(tp, ep), hold, hpe⟩)
      · rw [update_neq _ _ heq] at he'
        exact Or.inl he'
    -- gluing: a packet entry against a host log entry of equal
    -- index/term is that entry
    have hglue_log : ∀ (h0 : name (P := P)) (e e' : entry (P := P)),
        e ∈ (net.nwState h0).2.log → e' ∈ es →
        e.eTerm = e'.eTerm → e.eIndex = e'.eIndex → e = e' := by
      intro h0 e e' he he' hterm hidx
      have hin : e' ∈ (net.nwState h0).2.log :=
        entries_match_nw_host_invariant net hreach p t n0 pli plt es ci
          h0 e' e e' hpin hbody he' he hidx.symm hterm.symm he'
          (Nat.le_refl _)
      exact uniqueIndices_elim_eq
        (sorted_uniqueIndices (sorted_host_lifted net hreach h0)) he hin
        hidx
    constructor
    · intro e e' h0 h1 he he' hterm hidx
      rcases hlogel h0 e he with heold | henew
      · rcases haeel h1 e' he' with he'old | he'new
        · exact hH e e' h0 h1 heold he'old hterm hidx
        · exact hglue_log h0 e e' heold he'new hterm hidx
      · rcases haeel h1 e' he' with he'old | he'new
        · exact hN e e' h1 p t n0 pli plt es ci hpin hbody henew he'old
            hterm hidx
        · exact uniqueIndices_elim_eq
            (sorted_uniqueIndices
              (entries_sorted_nw_invariant net hreach p t n0 pli plt es
                ci hpin hbody)) henew he'new hidx
    · intro e e' h0 p0 t2 lid pli2 plt2 es2 ci2 hp0 hbody0 he he' hterm
        hidx
      have hp0' := hpk p0 t2 lid pli2 plt2 es2 ci2 hp0 hbody0
      rcases haeel h0 e' he' with he'old | he'new
      · exact hN e e' h0 p0 t2 lid pli2 plt2 es2 ci2 hp0' hbody0 he
          he'old hterm hidx
      · exact almi_packets_entries_eq hreach hp0' hpin hbody0 hbody he
          he'new hterm hidx
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    refine almi_of_update hP hst ?_ ?_ ?_
    · rw [hgd]
    · exact handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t es res haer
    · intro p' t2 lid pli2 plt2 es2 ci2 hp' _
      rcases hps p' hp' with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · rw [hl] at h1
        simp [send_packets] at h1
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    refine almi_of_update hP hst ?_ ?_ ?_
    · rw [hgd]
      exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.2
    · exact handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc
        lli llt hrv
    · intro p' t2 lid pli2 plt2 es2 ci2 hp' hbody'
      rcases hps p' hp' with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody'
        replace hbody' : m = msg.AppendEntries t2 lid pli2 plt2 es2 ci2 :=
          hbody'
        rw [hmshape] at hbody'
        exact nomatch hbody'
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    refine almi_of_update hP hst ?_ ?_ ?_
    · rw [hgd]
      exact (update_elections_data_requestVoteReply_votes p.pDst p.pSrc
        t v (net.nwState p.pDst)).2.2
    · rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t v
    · intro p' t2 lid pli2 plt2 es2 ci2 hp' _
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p' hp')
  · -- do_leader: fresh packets carry the leader's own log
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hH, hN⟩ := hP
    obtain ⟨-, -, -, -, hdlog, -⟩ := doLeader_spec d h hdl
    have hlogred : ∀ h0, (st' h0).2.log = (net.nwState h0).2.log := by
      intro h0
      rw [hst h0]
      by_cases heq : h0 = h
      · subst heq
        rw [update_same]
        show d'.log = (net.nwState h0).2.log
        rw [hdlog, hstate]
      · rw [update_neq _ _ heq]
    have haered : ∀ h0, (st' h0).1.allEntries
        = (net.nwState h0).1.allEntries := by
      intro h0
      rw [hst h0]
      by_cases heq : h0 = h
      · subst heq
        rw [update_same]
        show gd.allEntries = (net.nwState h0).1.allEntries
        rw [hstate]
      · rw [update_neq _ _ heq]
    constructor
    · intro e e' h0 h1 he he' hterm hidx
      rw [hlogred h0] at he
      rw [haered h1] at he'
      exact hH e e' h0 h1 he he' hterm hidx
    · intro e e' h0 p0 t2 lid pli2 plt2 es2 ci2 hp0 hbody0 he he' hterm
        hidx
      rw [haered h0] at he'
      rcases hps p0 hp0 with hold | hnew
      · exact hN e e' h0 p0 t2 lid pli2 plt2 es2 ci2 hold hbody0 he he'
          hterm hidx
      · -- a fresh replica packet: its entries are the leader's own
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
        obtain ⟨pi3, pt3, ci3, es3, hq2, hsub⟩ :=
          doLeader_messages d h hdl m0 hm0
        replace hbody0 :
            m0.2 = msg.AppendEntries t2 lid pli2 plt2 es2 ci2 := hbody0
        rw [hq2] at hbody0
        injection hbody0 with f1 f2 f3 f4 f5 f6
        have heL : e ∈ (net.nwState h).2.log := by
          rw [hstate]
          show e ∈ d.log
          exact hsub e (f5 ▸ he)
        exact hH e e' h h0 heL he' hterm hidx
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hlog2, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    refine almi_of_update hP hst ?_ ?_ ?_
    · rw [hstate]
    · rw [hlog2, hstate]
    · intro p' t2 lid pli2 plt2 es2 ci2 hp' _
      rcases hps p' hp' with h1 | h1
      · exact h1
      · rw [hms] at h1
        simp [send_packets] at h1
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach
    obtain ⟨hH, hN⟩ := hP
    constructor
    · intro e e' h0 h1 he he' hterm hidx
      replace he : e ∈ (net'.nwState h0).2.log := he
      replace he' : e' ∈ (net'.nwState h1).1.allEntries.map Prod.snd :=
        he'
      rw [← hstates h0] at he
      rw [← hstates h1] at he'
      exact hH e e' h0 h1 he he' hterm hidx
    · intro e e' h0 p0 t2 lid pli2 plt2 es2 ci2 hp0 hbody0 he he' hterm
        hidx
      replace he' : e' ∈ (net'.nwState h0).1.allEntries.map Prod.snd :=
        he'
      rw [← hstates h0] at he'
      exact hN e e' h0 p0 t2 lid pli2 plt2 es2 ci2 (hsub p0 hp0) hbody0
        he he' hterm hidx
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    refine almi_of_update hP hst ?_ ?_ ?_
    · rw [hstate]
    · rw [← hrb, hstate]
      rfl
    · intro p' t2 lid pli2 plt2 es2 ci2 hp' _
      rw [← hpkts] at hp'
      exact hp'

/-- `AllEntriesLogMatchingProof.v:425-430`
(`allEntries_log_matching_invariant`). -/
theorem allEntries_log_matching_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_log_matching net :=
  fun net hreach =>
    (allEntries_log_matching_inductive_invariant net hreach).1

/-! ## prefix_within_term — interface defs, support layer, and T1
(`Raft/PrefixWithinTermInterface.v` / `RaftProofs/PrefixWithinTermProof.v`
@ a3375e8; the internal lemma DAG is posted in the arc log's unit-10
opening entry) -/

/-- `PrefixWithinTermInterface.v:10-13`
(`allEntries_leaderLogs_prefix_within_term`). -/
def allEntries_leaderLogs_prefix_within_term (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (l : List (entry (P := P)))
    (h' : name (P := P)),
    (t, l) ∈ (net.nwState h').1.leaderLogs →
    prefix_within_term ((net.nwState h).1.allEntries.map Prod.snd) l

/-- `PrefixWithinTermInterface.v:15-17` (`log_log_prefix_within_term`). -/
def log_log_prefix_within_term (net : RefinedNet) : Prop :=
  ∀ h h' : name (P := P),
    prefix_within_term (net.nwState h).2.log (net.nwState h').2.log

omit O in
/-- `CommonTheorems.v:2049-2056` (`sorted_app_1`). -/
theorem sorted_app_1 {l1 l2 : List (entry (P := P))}
    (hs : sorted (l1 ++ l2)) : sorted l1 := by
  induction l1 with
  | nil => trivial
  | cons a l1 ih =>
    exact ⟨fun e' he' => hs.1 e' (List.mem_append.mpr (Or.inl he')), ih hs.2⟩

omit O in
/-- The right-half twin of `sorted_app_1` (upstream reaches it through
`sorted_subseq`; direct induction here). -/
theorem sorted_app_2 {l1 l2 : List (entry (P := P))}
    (hs : sorted (l1 ++ l2)) : sorted l2 := by
  induction l1 with
  | nil => exact hs
  | cons a l1 ih => exact ih hs.2

omit O in
/-- `CommonTheorems.v:2058-2080` (`Prefix_maxIndex`): a member of a
prefix is bounded by the whole (sorted) list's `maxIndex`. -/
theorem Prefix_maxIndex {l l' : List (entry (P := P))}
    {e : entry (P := P)} (hs' : sorted l') (hp : Prefix l l')
    (he : e ∈ l) : e.eIndex ≤ maxIndex l' :=
  maxIndex_is_max hs' (Prefix_In hp e he)

omit O in
/-- `CommonTheorems.v:2032-2047` (`app_contiguous_maxIndex_le_eq`), in
the sharper `l2 = []` form (upstream concludes `l1 ++ l2 = l1`): a
split contiguous above `i` whose tail prefixes a list capped at `i`
has an empty tail. -/
theorem app_contiguous_maxIndex_le_eq {l1 l2 l2' : List (entry (P := P))}
    {i : logIndex} (hp : Prefix l2 l2')
    (hc : contiguous_range_exact_lo (l1 ++ l2) i)
    (hle : maxIndex l2' ≤ i) : l2 = [] := by
  cases l2 with
  | nil => rfl
  | cons b rest =>
    exfalso
    cases l2' with
    | nil => exact absurd hp not_false
    | cons b' rest' =>
      obtain ⟨rfl, -⟩ := hp
      have hble : b.eIndex ≤ i := hle
      have hbin : b ∈ l1 ++ b :: rest :=
        List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      exact absurd (Nat.lt_of_lt_of_le (hc.2 b hbin) hble)
        (Nat.lt_irrefl _)

omit O in
/-- `CommonTheorems.v:2096-2110` (`contiguous_app_prefix_contiguous`):
chopping a contiguous sorted list at a prefix-of-`l2'` tail leaves the
head contiguous down to `maxIndex l2'`. -/
theorem contiguous_app_prefix_contiguous {l1 l2 l2' : List (entry (P := P))}
    {i : logIndex} (hp : Prefix l2 l2') (hs : sorted (l1 ++ l2))
    (hc : contiguous_range_exact_lo (l1 ++ l2) i)
    (hne : l2 ≠ [] ∨ i = maxIndex l2') :
    contiguous_range_exact_lo l1 (maxIndex l2') := by
  cases l2 with
  | nil =>
    rcases hne with hne | rfl
    · exact absurd rfl hne
    · rw [List.append_nil] at hc
      exact hc
  | cons b rest =>
    cases l2' with
    | nil => exact absurd hp not_false
    | cons b' rest' =>
      obtain ⟨rfl, -⟩ := hp
      have hib : i < b.eIndex :=
        hc.2 b (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
      constructor
      · intro j ⟨hjlo, hjhi⟩
        have hjlo' : b.eIndex < j := hjlo
        cases l1 with
        | nil =>
          exfalso
          have hj0 : j ≤ 0 := hjhi
          exact absurd (Nat.lt_of_lt_of_le hjlo' hj0) (Nat.not_lt_zero _)
        | cons a l1' =>
          have hjapp : j ≤ maxIndex ((a :: l1') ++ b :: rest) := hjhi
          obtain ⟨x, hxidx, hxmem⟩ :=
            hc.1 j ⟨Nat.lt_trans hib hjlo', hjapp⟩
          refine ⟨x, hxidx, ?_⟩
          rcases List.mem_append.mp hxmem with hx1 | hx2
          · exact hx1
          · exfalso
            have hxle : x.eIndex ≤ b.eIndex :=
              maxIndex_is_max (sorted_app_2 hs) hx2
            rw [hxidx] at hxle
            exact absurd (Nat.lt_of_lt_of_le hjlo' hxle)
              (Nat.lt_irrefl _)
      · intro x hx
        have hpos : x.eIndex > 0 :=
          Nat.lt_of_le_of_lt (Nat.zero_le i)
            (hc.2 x (List.mem_append.mpr (Or.inl hx)))
        have hgt : x.eIndex > maxIndex (b :: rest) :=
          sorted_app_in_1 hs hpos hx
        exact hgt

omit O in
/-- `CommonTheorems.v:2125-2138` (`contiguous_app_prefix_2`). -/
theorem contiguous_app_prefix_2 {l l' l'' : List (entry (P := P))}
    {i : logIndex} (hs : sorted (l ++ l'))
    (hc : contiguous_range_exact_lo (l ++ l') 0)
    (hp : Prefix l' l'') (hlo : maxIndex l'' < i) (hhi : i ≤ maxIndex l) :
    ∃ e, e.eIndex = i ∧ e ∈ l := by
  cases l' with
  | nil =>
    rw [List.append_nil] at hc
    exact hc.1 i ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hlo, hhi⟩
  | cons b rest =>
    exact (contiguous_app_prefix_contiguous hp hs hc
      (Or.inl (by simp))).1 i ⟨hlo, hhi⟩

omit O in
/-- `PrefixWithinTermProof.v:902-913` (`prefix_within_term_union`). -/
theorem prefix_within_term_union {l1 l1' l1'' l2 : List (entry (P := P))}
    (h' : prefix_within_term l1' l2) (h'' : prefix_within_term l1'' l2)
    (hsplit : ∀ e ∈ l1, e ∈ l1' ∨ e ∈ l1'') :
    prefix_within_term l1 l2 := fun e e' ht hi he he' =>
  (hsplit e he).elim (fun h => h' e e' ht hi h he')
    (fun h => h'' e e' ht hi h he')

omit O in
/-- `PrefixWithinTermProof.v:1385-1393` (`prefix_within_term_subset`). -/
theorem prefix_within_term_subset {l1 l1' l2 : List (entry (P := P))}
    (h' : prefix_within_term l1' l2) (hsub : ∀ e ∈ l1, e ∈ l1') :
    prefix_within_term l1 l2 := fun e e' ht hi he he' =>
  h' e e' ht hi (hsub e he) he'

omit O in
/-- `PrefixWithinTermProof.v:788-796` (`findGtIndex_prefix_within_term`). -/
theorem findGtIndex_prefix_within_term {l1 l2 : List (entry (P := P))}
    {i : logIndex} (h : prefix_within_term l1 l2) :
    prefix_within_term (findGtIndex l1 i) l2 :=
  prefix_within_term_subset h (fun _ he => findGtIndex_in he)

/-- `PrefixWithinTermProof.v:107-149`
(`log_log_prefix_within_term_invariant`, standalone — T1 of the posted
DAG): any two host logs are prefixes-within-term of each other. Both
entries resolve through `logs_leaderLogs`; `one_leaderLog_per_term_log`
identifies the snapshots; contiguity produces an index-matched witness
in the second log, which either shares `e`'s term (entries_match
transfers `e`) or IS `e` (uniqueIndices on the first log). -/
theorem log_log_prefix_within_term_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      log_log_prefix_within_term net := by
  intro net hreach h h' e e' hterm hidx he he'
  obtain ⟨leader, ll, es, hll, hsplit, -⟩ :=
    logs_leaderLogs_invariant net hreach h e he
  obtain ⟨leader', ll', es', hll', hsplit', hesterm'⟩ :=
    logs_leaderLogs_invariant net hreach h' e' he'
  rw [hterm] at hll
  have hlleq : ll = ll' :=
    one_leaderLog_per_term_log_invariant net hreach leader leader'
      e'.eTerm ll ll' hll hll'
  subst hlleq
  have hgt0 : 0 < e.eIndex := entries_gt_0_invariant net hreach h e he
  have hmax : e.eIndex ≤ maxIndex (net.nwState h').2.log :=
    Nat.le_trans hidx
      (maxIndex_is_max (entries_sorted_invariant net hreach h') he')
  obtain ⟨x, hxidx, hxmem⟩ :=
    (entries_contiguous_invariant net hreach h').1 e.eIndex ⟨hgt0, hmax⟩
  have hxrem : x ∈ removeAfterIndex (net.nwState h').2.log e'.eIndex :=
    removeAfterIndex_le_In (by rw [hxidx]; exact hidx) hxmem
  rw [hsplit'] at hxrem
  rcases List.mem_append.mp hxrem with hxes | hxll
  · have hxterm : e.eTerm = x.eTerm := by
      rw [hesterm' x hxes, hterm]
    exact (entries_match_invariant net hreach h h' e x e hxidx.symm
      hxterm he hxmem (Nat.le_refl _)).mp he
  · have hxinh : x ∈ (net.nwState h).2.log := by
      refine removeAfterIndex_in (l := (net.nwState h).2.log)
        (i := e.eIndex) ?_
      rw [hsplit]
      exact List.mem_append.mpr (Or.inr hxll)
    have hex : e = x :=
      uniqueIndices_elim_eq
        (sorted_uniqueIndices (entries_sorted_invariant net hreach h))
        he hxinh hxidx.symm
    rw [hex]
    exact hxmem

/-! ## T2 — the AE×AE cross-packet prefix fact
(`PrefixWithinTermProof.v:95-747`) -/

/-- `PrefixWithinTermProof.v:95-105`
(`append_entries_append_entries_prefix_within_term_nw`). -/
def append_entries_append_entries_prefix_within_term_nw
    (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex)
    (p' : RefinedPacket) (t' : term) (n' : name (P := P))
    (pli' : logIndex) (plt' : term) (es' : List (entry (P := P)))
    (ci' : logIndex) (e e' : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    p' ∈ net.nwPackets → p'.pBody = .AppendEntries t' n' pli' plt' es' ci' →
    e.eTerm = e'.eTerm → e.eIndex ≤ e'.eIndex →
    e ∈ es → e' ∈ es' →
    (e ∈ es' ∨ (e.eIndex = pli' ∧ e.eTerm = plt') ∨
      (e.eIndex < pli' ∧ e.eTerm ≤ plt'))

omit O in
/-- The positioning core shared by T2's cases (extracted from the
repeated `Prefix`/`locked_or` battles of
`PrefixWithinTermProof.v:154-747`): under `e`'s
`logs_leaderLogs_nw` decomposition, any witness `y ∈ ll` with
`e.eIndex ≤ y.eIndex` forces `e` itself into the snapshot `ll` — the
own-term block `es₁` sits strictly above `maxIndex ll`, which the
witness caps from below. -/
theorem aeae_e_in_ll {es es₁ ll₁ ll : List (entry (P := P))}
    {e y : entry (P := P)} {pli plt : term}
    (hs_es : sorted es) (hc_es : contiguous_range_exact_lo es pli)
    (hsplit : removeAfterIndex es e.eIndex = es₁ ++ ll₁)
    (hpre : Prefix ll₁ ll) (hsll : sorted ll)
    (hdisj : (plt = e.eTerm ∧ pli > maxIndex ll) ∨
      (∃ e2, e2 ∈ ll ∧ e2.eIndex = pli ∧ e2.eTerm = plt ∧
        (ll₁ ≠ [] ∨ pli = maxIndex ll)) ∨
      (plt = 0 ∧ pli = 0 ∧ ll₁ = ll))
    (he : e ∈ es) (hy : y ∈ ll) (hyge : e.eIndex ≤ y.eIndex) :
    e ∈ ll := by
  have hgt_pli : pli < e.eIndex := hc_es.2 e he
  have hymax : y.eIndex ≤ maxIndex ll := maxIndex_is_max hsll hy
  have hemax : e.eIndex ≤ maxIndex ll := Nat.le_trans hyge hymax
  have herem : e ∈ es₁ ++ ll₁ := by
    rw [← hsplit]
    exact removeAfterIndex_le_In (Nat.le_refl _) he
  rcases List.mem_append.mp herem with hees | hell
  · exfalso
    cases hll₁ : ll₁ with
    | cons b rest =>
      -- nonempty prefix shares ll's head: es₁ sits strictly above it
      subst hll₁
      have hsrem : sorted (es₁ ++ b :: rest) := by
        rw [← hsplit]
        exact removeAfterIndex_sorted hs_es
      have habove : e.eIndex > maxIndex (b :: rest) :=
        sorted_app_in_1 hsrem
          (Nat.lt_of_le_of_lt (Nat.zero_le _) hgt_pli) hees
      rw [Prefix_maxIndex_eq hpre (by simp)] at habove
      exact absurd (Nat.lt_of_le_of_lt hemax habove) (Nat.lt_irrefl _)
    | nil =>
      subst hll₁
      rcases hdisj with ⟨-, hpligt⟩ | ⟨e2, -, -, -, hor⟩ | ⟨-, -, hlleq⟩
      · -- pli > maxIndex ll ≥ e.eIndex, yet pli < e.eIndex
        exact absurd (Nat.lt_trans hgt_pli (Nat.lt_of_le_of_lt hemax hpligt))
          (Nat.lt_irrefl _)
      · rcases hor with hne | hplieq
        · exact hne rfl
        · rw [hplieq] at hgt_pli
          exact absurd (Nat.lt_of_le_of_lt hemax hgt_pli) (Nat.lt_irrefl _)
      · -- ll = ll₁ = [], but y ∈ ll
        rw [← hlleq] at hy
        exact nomatch hy
  · exact Prefix_In hpre e hell

/-- `PrefixWithinTermProof.v:154-747`
(`append_entries_append_entries_prefix_within_term_invariant`,
standalone — T2 of the posted DAG). Route re-derived (logged judgment
call): both entries' `logs_leaderLogs_nw` decompositions share one
snapshot (`one_leaderLog_per_term_log`); above `pli'` the entry
transfers into `es'` through its index-matched contiguity witness
(same-term block ⇒ `entries_match_nw_1`; snapshot block ⇒
`aeae_e_in_ll` + uniqueIndices); at/below `pli'` the packet's prevLog
disjunction answers directly, with `aeae_e_in_ll` + `sorted_index_term`
supplying the term bound in the snapshot case. -/
theorem append_entries_append_entries_prefix_within_term_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      append_entries_append_entries_prefix_within_term_nw net := by
  intro net hreach p t n pli plt es ci p' t' n' pli' plt' es' ci' e e'
    hp hbody hp' hbody' hterm hle he he'
  obtain ⟨leader, ll, es₁, ll₁, hll, hpre₁, hsplit₁, hterm₁, hdisj₁⟩ :=
    logs_leaderLogs_nw_invariant net hreach p t n pli plt es ci e
      hp hbody he
  obtain ⟨leader', ll', es₂, ll₂, hll', hpre₂, hsplit₂, hterm₂, hdisj₂⟩ :=
    logs_leaderLogs_nw_invariant net hreach p' t' n' pli' plt' es' ci' e'
      hp' hbody' he'
  rw [hterm] at hll
  have hlleq : ll = ll' :=
    one_leaderLog_per_term_log_invariant net hreach leader leader'
      e'.eTerm ll ll' hll hll'
  subst hlleq
  have hsll : sorted ll := leaderLogs_sorted_invariant net hreach leader'
    e'.eTerm ll hll'
  have hs_es : sorted es :=
    entries_sorted_nw_invariant net hreach p t n pli plt es ci hp hbody
  have hs_es' : sorted es' :=
    entries_sorted_nw_invariant net hreach p' t' n' pli' plt' es' ci'
      hp' hbody'
  have hc_es : contiguous_range_exact_lo es pli :=
    entries_contiguous_nw_invariant net hreach p t n pli plt es ci
      hp hbody
  have hc_es' : contiguous_range_exact_lo es' pli' :=
    entries_contiguous_nw_invariant net hreach p' t' n' pli' plt' es' ci'
      hp' hbody'
  -- the ll₁-side positioning lemma, partially applied
  have position := fun (y : entry (P := P)) (hy : y ∈ ll)
      (hyge : e.eIndex ≤ y.eIndex) =>
    aeae_e_in_ll hs_es hc_es hsplit₁ hpre₁ hsll hdisj₁ he hy hyge
  by_cases hcmp : pli' < e.eIndex
  · -- transfer side: e ∈ es'
    left
    have hmax : e.eIndex ≤ maxIndex es' :=
      Nat.le_trans hle (maxIndex_is_max hs_es' he')
    obtain ⟨x, hxidx, hxmem⟩ := hc_es'.1 e.eIndex ⟨hcmp, hmax⟩
    have hxrem : x ∈ removeAfterIndex es' e'.eIndex :=
      removeAfterIndex_le_In (by rw [hxidx]; exact hle) hxmem
    rw [hsplit₂] at hxrem
    rcases List.mem_append.mp hxrem with hxes | hxll
    · -- same-term block: entries_match_nw_1 transfers e
      have hxterm : e.eTerm = x.eTerm := by
        rw [hterm₂ x hxes, hterm]
      exact entries_match_nw_1_invariant net hreach p t n pli plt es ci
        p' t' n' pli' plt' es' ci' e x e hp hp' hbody hbody' he hxmem
        hxidx.symm hxterm he ⟨hcmp, Nat.le_refl _⟩
    · -- snapshot block: e is IN the snapshot and equals x
      have hxinll : x ∈ ll := Prefix_In hpre₂ x hxll
      have hell : e ∈ ll := position x hxinll (Nat.le_of_eq hxidx.symm)
      have hex : e = x :=
        uniqueIndices_elim_eq (sorted_uniqueIndices hsll) hell hxinll
          hxidx.symm
      rw [hex]
      exact hxmem
  · -- prevLog side: e.eIndex ≤ pli'
    have hle' : e.eIndex ≤ pli' := Nat.le_of_not_lt hcmp
    rcases hdisj₂ with ⟨hplt', -⟩ | ⟨e2, he2ll, he2idx, he2term, -⟩ |
      ⟨-, hpli'0, -⟩
    · -- plt' = e'.eTerm: answer directly
      rcases Nat.eq_or_lt_of_le hle' with heq | hlt
      · exact Or.inr (Or.inl ⟨heq, hterm.trans hplt'.symm⟩)
      · exact Or.inr (Or.inr ⟨hlt, Nat.le_of_eq (hterm.trans hplt'.symm)⟩)
    · -- prevLog entry e2 ∈ ll at pli'
      have hell : e ∈ ll := position e2 he2ll (by rw [he2idx]; exact hle')
      rcases Nat.eq_or_lt_of_le hle' with heq | hlt
      · -- same index: e = e2, terms coincide
        have hex : e = e2 :=
          uniqueIndices_elim_eq (sorted_uniqueIndices hsll) hell he2ll
            (by rw [he2idx]; exact heq)
        exact Or.inr (Or.inl ⟨heq, by rw [hex, he2term]⟩)
      · -- below: sorted snapshot bounds the term
        have hterm_le : e.eTerm ≤ e2.eTerm :=
          sorted_index_term (by rw [he2idx]; exact Nat.le_of_lt hlt)
            hsll hell he2ll
        exact Or.inr (Or.inr ⟨hlt, by rw [← he2term]; exact hterm_le⟩)
    · -- pli' = 0 yet e.eIndex ≤ pli' and e.eIndex > pli ≥ 0
      exfalso
      rw [hpli'0] at hle'
      exact absurd (Nat.lt_of_le_of_lt (Nat.zero_le pli) (hc_es.2 e he))
        (Nat.not_lt_of_le hle')

/-! ## The pwt inductive invariant — conjunct defs and transports
(`PrefixWithinTermProof.v:748-786`, obligations `:1517-1888`) -/

/-- `PrefixWithinTermProof.v:748-751` (`log_leaderLogs_prefix_within_term`). -/
def log_leaderLogs_prefix_within_term (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (ll : List (entry (P := P)))
    (leader : name (P := P)),
    (t, ll) ∈ (net.nwState leader).1.leaderLogs →
    prefix_within_term (net.nwState h).2.log ll

/-- `PrefixWithinTermProof.v:753-755` (`allEntries_log_prefix_within_term`). -/
def allEntries_log_prefix_within_term (net : RefinedNet) : Prop :=
  ∀ h h' : name (P := P),
    prefix_within_term ((net.nwState h).1.allEntries.map Prod.snd)
      (net.nwState h').2.log

/-- `PrefixWithinTermProof.v:757-765`
(`allEntries_append_entries_prefix_within_term_nw`). -/
def allEntries_append_entries_prefix_within_term_nw (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex)
    (h : name (P := P)) (e e' : entry (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    e.eTerm = e'.eTerm → e.eIndex ≤ e'.eIndex →
    e ∈ (net.nwState h).1.allEntries.map Prod.snd → e' ∈ es →
    (e ∈ es ∨ (e.eIndex = pli ∧ e.eTerm = plt) ∨
      (e.eIndex < pli ∧ e.eTerm ≤ plt))

/-- `PrefixWithinTermProof.v:767-772`
(`append_entries_leaderLogs_prefix_within_term`). -/
def append_entries_leaderLogs_prefix_within_term (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex)
    (h : name (P := P)) (t' : term) (ll : List (entry (P := P))),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    (t', ll) ∈ (net.nwState h).1.leaderLogs →
    prefix_within_term es ll

/-- `PrefixWithinTermProof.v:774-778`
(`append_entries_log_prefix_within_term`). -/
def append_entries_log_prefix_within_term (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex)
    (h : name (P := P)),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    prefix_within_term es (net.nwState h).2.log

/-- `PrefixWithinTermProof.v:780-786` (`prefix_within_term_inductive`). -/
def prefix_within_term_inductive (net : RefinedNet) : Prop :=
  allEntries_leaderLogs_prefix_within_term net ∧
  log_leaderLogs_prefix_within_term net ∧
  allEntries_log_prefix_within_term net ∧
  allEntries_append_entries_prefix_within_term_nw net ∧
  append_entries_leaderLogs_prefix_within_term net ∧
  append_entries_log_prefix_within_term net

/-- Generic transport: a step that changes no log, no leaderLogs, no
allEntries at the updated node and adds no AppendEntries packet
preserves the whole conjunction (the shape behind upstream's
timeout/RV/AER/DGS cases, `PrefixWithinTermProof.v:1588-1843`). -/
theorem pwti_of_update {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : prefix_within_term_inductive net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hlog : d.log = (net.nwState u).2.log)
    (hll : gd.leaderLogs = (net.nwState u).1.leaderLogs)
    (hae : gd.allEntries = (net.nwState u).1.allEntries)
    (hpk : ∀ (p' : RefinedPacket) (t : term) (n : name (P := P))
      (pli : logIndex) (plt : term) (es : List (entry (P := P)))
      (ci : logIndex), p' ∈ net'.nwPackets →
      p'.pBody = .AppendEntries t n pli plt es ci →
      p' ∈ net.nwPackets) :
    prefix_within_term_inductive net' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
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
  have hllred : ∀ h0, (net'.nwState h0).1.leaderLogs
      = (net.nwState h0).1.leaderLogs := by
    intro h0
    rw [hst h0]
    by_cases heq : h0 = u
    · subst heq
      rw [update_same]
      exact hll
    · rw [update_neq _ _ heq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h t l h' hin
    rw [hllred h'] at hin
    rw [haered h]
    exact h1 h t l h' hin
  · intro h t ll leader hin
    rw [hllred leader] at hin
    rw [hlogred h]
    exact h2 h t ll leader hin
  · intro h h'
    rw [haered h, hlogred h']
    exact h3 h h'
  · intro p t n pli plt es ci h e e' hp hbody hterm hidx he he'
    rw [haered h] at he
    exact h4 p t n pli plt es ci h e e'
      (hpk p t n pli plt es ci hp hbody) hbody hterm hidx he he'
  · intro p t n pli plt es ci h t' ll hp hbody hin
    rw [hllred h] at hin
    exact h5 p t n pli plt es ci h t' ll
      (hpk p t n pli plt es ci hp hbody) hbody hin
  · intro p t n pli plt es ci h hp hbody
    rw [hlogred h]
    exact h6 p t n pli plt es ci h
      (hpk p t n pli plt es ci hp hbody) hbody

/-- `PrefixWithinTermProof.v:1844-1852` (`prefix_within_term_inductive_init`). -/
theorem prefix_within_term_inductive_init :
    refined_raft_net_invariant_init (P := P) prefix_within_term_inductive := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h t l h' hin
    exact nomatch hin
  · intro h t ll leader hin
    exact nomatch hin
  · intro h h' e e' _ _ he _
    exact nomatch he
  · intro p _ _ _ _ _ _ _ _ _ hp _
    exact nomatch hp
  · intro p _ _ _ _ _ _ _ _ _ hp _
    exact nomatch hp
  · intro p _ _ _ _ _ _ _ hp _
    exact nomatch hp

/-- `PrefixWithinTermProof.v:1644-1709` (`prefix_within_term_inductive_timeout`). -/
theorem prefix_within_term_inductive_timeout :
    refined_raft_net_invariant_timeout (P := P) prefix_within_term_inductive := by
  intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
  obtain ⟨hlog, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
  refine pwti_of_update (net' := ⟨ps', st'⟩) hP hst hlog ?_ ?_ ?_
  · subst hgd
    exact (update_elections_data_timeout_ghost h (net.nwState h)).1
  · subst hgd
    exact (update_elections_data_timeout_ghost h (net.nwState h)).2
  · intro p' t n pli plt es ci hp' hbody
    rcases hps p' hp' with hold | hnew
    · exact hold
    · exfalso
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
      replace hbody : m0.2 = msg.AppendEntries t n pli plt es ci := hbody
      rw [hq2] at hbody
      exact nomatch hbody

/-- `PrefixWithinTermProof.v:1720-1788`
(`prefix_within_term_inductive_request_vote`). -/
theorem prefix_within_term_inductive_request_vote :
    refined_raft_net_invariant_request_vote (P := P)
      prefix_within_term_inductive := by
  intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP _hreach
    hpkts hst hps
  have hgh := update_elections_data_requestVote_cronies p.pDst p.pSrc t
    p.pSrc lli llt (net.nwState p.pDst)
  refine pwti_of_update (net' := ⟨ps', st'⟩) hP hst
    (handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt hrv)
    ?_ ?_ ?_
  · subst hgd
    exact hgh.2.1
  · subst hgd
    exact hgh.2.2
  · intro p' t2 n pli plt es ci hp' hbody'
    rcases hps p' hp' with hold | hnew
    · rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · exfalso
      obtain ⟨t3, v3, hm⟩ :=
        handleRequestVote_reply_shape p.pDst (net.nwState p.pDst).2 t
          p.pSrc lli llt hrv
      rw [hnew] at hbody'
      replace hbody' : m = msg.AppendEntries t2 n pli plt es ci := hbody'
      rw [hm] at hbody'
      exact nomatch hbody'

/-- `PrefixWithinTermProof.v:1588-1635`
(`prefix_within_term_inductive_append_entries_reply`). -/
theorem prefix_within_term_inductive_append_entries_reply :
    refined_raft_net_invariant_append_entries_reply (P := P)
      prefix_within_term_inductive := by
  intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
    hpkts hst hps
  obtain ⟨-, -, hm⟩ :=
    handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t
      es res haer
  refine pwti_of_update (net' := ⟨ps', st'⟩) hP hst
    (handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2 p.pSrc t
      es res haer)
    (by rw [hgd]) (by rw [hgd]) ?_
  · intro p' t2 n pli plt es2 ci hp' _hbody'
    rcases hps p' hp' with hold | hnew
    · rw [hpkts]
      exact mem_of_mem_remove_middle hold
    · exfalso
      rw [hm] at hnew
      simp [send_packets] at hnew

/-- `PrefixWithinTermProof.v:1539-1587`
(`prefix_within_term_inductive_request_vote_reply`): the one transport
with leaderLogs growth — a fresh snapshot is the winner's own log, so
the three leaderLogs-facing conjuncts close through the IH's
`allEntries_log`/`append_entries_log` and T1. -/
theorem prefix_within_term_inductive_request_vote_reply :
    refined_raft_net_invariant_request_vote_reply (P := P)
      prefix_within_term_inductive := by
  intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts hst hps
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  have hgh := update_elections_data_requestVoteReply_votes p.pDst p.pSrc t
    v (net.nwState p.pDst)
  have hlogeq : d.log = (net.nwState p.pDst).2.log := by
    rw [← hrvr]
    exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2 p.pSrc t v
  have hlogred : ∀ h0, ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).2.log = (net.nwState h0).2.log := by
    intro h0
    rw [hst h0]
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same]
      exact hlogeq
    · rw [update_neq _ _ heq]
  have haered : ∀ h0, ((st' h0 : electionsData (P := P) ×
      raft_data (P := P))).1.allEntries
      = (net.nwState h0).1.allEntries := by
    intro h0
    rw [hst h0]
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same]
      subst hgd
      exact hgh.2.2
    · rw [update_neq _ _ heq]
  -- leaderLogs at any node: old, or the fresh snapshot = pDst's log
  have hllred : ∀ (h0 : name (P := P)) (t2 : term)
      (ll : List (entry (P := P))),
      (t2, ll) ∈ ((st' h0 : electionsData (P := P) ×
        raft_data (P := P))).1.leaderLogs →
      (t2, ll) ∈ (net.nwState h0).1.leaderLogs ∨
        ll = (net.nwState p.pDst).2.log := by
    intro h0 t2 ll hin
    rw [hst h0] at hin
    by_cases heq : h0 = p.pDst
    · subst heq
      rw [update_same] at hin
      subst hgd
      rcases leaderLogs_update_elections_data_RVR hin with hold | hfresh
      · exact Or.inl hold
      · right
        rw [hfresh.2.2.2]
        exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2
          p.pSrc t v
    · rw [update_neq _ _ heq] at hin
      exact Or.inl hin
  have hpk : ∀ p' ∈ ps', p' ∈ net.nwPackets := by
    intro p' hp'
    rw [hpkts]
    exact mem_of_mem_remove_middle (hps p' hp')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h t2 l h' hin
    rw [haered h]
    rcases hllred h' t2 l hin with hold | rfl
    · exact h1 h t2 l h' hold
    · exact h3 h p.pDst
  · intro h t2 ll leader hin
    rw [hlogred h]
    rcases hllred leader t2 ll hin with hold | rfl
    · exact h2 h t2 ll leader hold
    · exact log_log_prefix_within_term_invariant net hreach h p.pDst
  · intro h h'
    rw [haered h, hlogred h']
    exact h3 h h'
  · intro p0 t2 n pli plt es ci h e e' hp0 hbody hterm hidx he he'
    rw [haered h] at he
    exact h4 p0 t2 n pli plt es ci h e e' (hpk p0 hp0) hbody hterm hidx
      he he'
  · intro p0 t2 n pli plt es ci h t' ll hp0 hbody hin
    rcases hllred h t' ll hin with hold | rfl
    · exact h5 p0 t2 n pli plt es ci h t' ll (hpk p0 hp0) hbody hold
    · exact h6 p0 t2 n pli plt es ci p.pDst (hpk p0 hp0) hbody
  · intro p0 t2 n pli plt es ci h hp0 hbody
    rw [hlogred h]
    exact h6 p0 t2 n pli plt es ci h (hpk p0 hp0) hbody

/-- `PrefixWithinTermProof.v:1789-1843`
(`prefix_within_term_inductive_do_generic_server`). -/
theorem prefix_within_term_inductive_do_generic_server :
    refined_raft_net_invariant_do_generic_server (P := P)
      prefix_within_term_inductive := by
  intro net st' ps' gd d os d' ms h hdgs hP _hreach hstate hst hps
  obtain ⟨hlog, -, -, -, -, hms⟩ := doGenericServer_spec h d hdgs
  refine pwti_of_update (net' := ⟨ps', st'⟩) hP hst
    (by rw [hlog, hstate]) (by rw [hstate]) (by rw [hstate]) ?_
  · intro p' t n pli plt es ci hp' _hbody
    rcases hps p' hp' with hold | hnew
    · exact hold
    · exfalso
      rw [hms] at hnew
      simp [send_packets] at hnew

/-- `PrefixWithinTermProof.v:1854-1862`
(`prefix_within_term_inductive_state_same_packet_subset`). -/
theorem prefix_within_term_inductive_state_same_packet_subset :
    refined_raft_net_invariant_state_same_packet_subset (P := P)
      prefix_within_term_inductive := by
  intro net net' hstate hpk hP _hreach
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h t l h' hin
    rw [← hstate h'] at hin
    rw [← hstate h]
    exact h1 h t l h' hin
  · intro h t ll leader hin
    rw [← hstate leader] at hin
    rw [← hstate h]
    exact h2 h t ll leader hin
  · intro h h'
    rw [← hstate h, ← hstate h']
    exact h3 h h'
  · intro p t n pli plt es ci h e e' hp hbody hterm hidx he he'
    rw [← hstate h] at he
    exact h4 p t n pli plt es ci h e e' (hpk p hp) hbody hterm hidx he he'
  · intro p t n pli plt es ci h t' ll hp hbody hin
    rw [← hstate h] at hin
    exact h5 p t n pli plt es ci h t' ll (hpk p hp) hbody hin
  · intro p t n pli plt es ci h hp hbody
    rw [← hstate h]
    exact h6 p t n pli plt es ci h (hpk p hp) hbody

/-- `PrefixWithinTermProof.v:1863-1888`
(`prefix_within_term_inductive_reboot`): `reboot` keeps the log and the
whole ghost. -/
theorem prefix_within_term_inductive_reboot :
    refined_raft_net_invariant_reboot (P := P)
      prefix_within_term_inductive := by
  intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
  refine pwti_of_update hP hst ?_ (by rw [hstate]) (by rw [hstate]) ?_
  · rw [← hrb, hstate]
    rfl
  · intro p' t n pli plt es ci hp' _hbody
    rw [← hpkts] at hp'
    exact hp'

end LeaderCompleteness
end Raft
end VerdiCompat
