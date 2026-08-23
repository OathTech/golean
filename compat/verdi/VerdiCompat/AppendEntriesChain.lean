import VerdiCompat.LogMatching

/-!
# The AppendEntries feeder chain — toward leaderLogs_preserved

Campaign Arc 3 unit 7 (the wave table is in the arc log's unit-7
opening entry), 1:1 against the sources @ a3375e8 —

- `allEntries_term_sanity` (`Raft/AllEntriesTermSanityInterface.v`):
  no recorded (term, entry) pair is from the future;
- `log_properties_hold_on_leader_logs`
  (`Raft/LeaderLogsLogPropertiesInterface.v`): any reachability-closed
  property of host logs holds of every leaderLog snapshot;
- `leaders_have_leaderLogs_strong`
  (`Raft/LeadersHaveLeaderLogsStrongInterface.v`): a leader's log is
  its election snapshot plus own-term entries on top;
- `appendEntries_request_reply_correspondence`
  (`Raft/AppendEntriesRequestReplyCorrespondenceInterface.v`),
  `appendEntries_requests_came_from_leaders`
  (`Raft/AppendEntriesRequestsCameFromLeadersInterface.v`),
  `appendEntries_leader` (`Raft/AppendEntriesLeaderInterface.v`),
  `appendEntriesReply_sublog`
  (`Raft/AppendEntriesReplySublogInterface.v`),
  `nextIndex_safety` (`Raft/NextIndexSafetyInterface.v`);
- `leaderLogs_sublog` (`Raft/LeaderLogsSublogInterface.v`) and
  `leaderLogs_logMatching` (`Raft/LeaderLogsLogMatchingInterface.v`).

Statements 1:1 with the Interface files; proofs re-derived through the
ported principles.
-/

namespace VerdiCompat
namespace Raft

section AppendEntriesChain
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RefinedPacket" =>
  Packet (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-! ## allEntries_term_sanity -/

omit O in
/-- `advanceCurrentTerm` never lands below the incoming term. -/
theorem advanceCurrentTerm_ge (st : raft_data (P := P)) (t : term) :
    t ≤ (advanceCurrentTerm st t).currentTerm := by
  unfold advanceCurrentTerm
  split
  · exact Nat.le_refl _
  · rename_i hnlt
    simp only [Nat.blt_eq] at hnlt
    exact Nat.le_of_not_lt hnlt

omit O in
/-- A `true` AppendEntries reply carries the request's term, and the
responder's new term is at least it. -/
theorem handleAppendEntries_reply_true (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P))
    (pli : logIndex) (plt : term) (es : List (entry (P := P)))
    (ci : logIndex) {st' t' es'}
    (h : handleAppendEntries me st t lid pli plt es ci
      = (st', .AppendEntriesReply t' es' true)) :
    t' = t ∧ t ≤ st'.currentTerm := by
  have hadv := advanceCurrentTerm_ge st t
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals injection h with hst hm
  all_goals injection hm with hmt hmes hmr
  all_goals cases hmr
  all_goals refine ⟨hmt.symm, ?_⟩
  all_goals rw [← hst]
  all_goals exact hadv

omit O in
/-- The term-aware shape of the client-request `allEntries` update: the
fresh record's term is the handler's post-state current term. -/
theorem update_elections_data_client_request_allEntries_term_cases
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out d l}
    (hcr : handleClientRequest me st.2 client id c = (out, d, l)) :
    (update_elections_data_client_request me st client id c).allEntries
      = st.1.allEntries ∨
    ∃ e : entry (P := P),
      (update_elections_data_client_request me st client id c).allEntries
        = (d.currentTerm, e) :: st.1.allEntries := by
  unfold update_elections_data_client_request
  rw [hcr]
  simp only []
  cases hdl : d.log with
  | nil =>
    split
    · exact Or.inl rfl
    · exact Or.inl rfl
  | cons e rest =>
    split
    · exact Or.inr ⟨e, rfl⟩
    · exact Or.inl rfl

omit O in
/-- The term-aware shape of the append-entries `allEntries` update: the
recorded term is the (true) reply's. -/
theorem update_elections_data_appendEntries_allEntries_term_cases
    (me : name (P := P)) (st : electionsData (P := P) × raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {d m}
    (hae : handleAppendEntries me st.2 t lid pli plt es ci = (d, m)) :
    (update_elections_data_appendEntries me st t lid pli plt es ci).allEntries
      = st.1.allEntries ∨
    ∃ t', m = .AppendEntriesReply t' es true ∧
      (update_elections_data_appendEntries me st t lid pli plt es
        ci).allEntries
      = (es.map fun e => (t', e)) ++ st.1.allEntries := by
  obtain ⟨t'', r'', rfl⟩ :=
    handleAppendEntries_reply_entries me st.2 t lid pli plt es ci hae
  unfold update_elections_data_appendEntries
  rw [hae]
  cases r''
  · exact Or.inl rfl
  · exact Or.inr ⟨t'', rfl, rfl⟩

/-- `AllEntriesTermSanityInterface.v:8-12` (`allEntries_term_sanity`). -/
def allEntries_term_sanity (net : RefinedNet) : Prop :=
  ∀ (t : term) (e : entry (P := P)) (h : name (P := P)),
    (t, e) ∈ (net.nwState h).1.allEntries →
    t ≤ (net.nwState h).2.currentTerm

/-- Transport for `allEntries_term_sanity`: allEntries kept, term only
grows. -/
theorem allEntries_term_sanity_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : allEntries_term_sanity net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.allEntries = (net.nwState u).1.allEntries)
    (hct : (net.nwState u).2.currentTerm ≤ d.currentTerm) :
    allEntries_term_sanity net' := by
  intro t e h hin
  rw [hst h] at hin ⊢
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hin ⊢
    replace hin : (t, e) ∈ gd.allEntries := hin
    rw [hgd] at hin
    show t ≤ d.currentTerm
    exact Nat.le_trans (hP t e h hin) hct
  · rw [update_neq _ _ heq] at hin ⊢
    exact hP t e h hin

/-- `AllEntriesTermSanityProof.v` (`allEntries_term_sanity_invariant`):
recorded terms never exceed the recorder's current term. -/
theorem allEntries_term_sanity_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      allEntries_term_sanity net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t e h hin
    exact nomatch hin
  · -- client_request: the fresh record carries the handler's own term
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    obtain ⟨-, hctd, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro t e h0 hin
    replace hin : (t, e) ∈ (st' h0).1.allEntries := hin
    show t ≤ (st' h0).2.currentTerm
    rw [hst h0] at hin ⊢
    by_cases heq : h0 = h
    · rw [heq, update_same] at hin ⊢
      replace hin : (t, e) ∈ gd.allEntries := hin
      subst hgd
      show t ≤ d.currentTerm
      rcases update_elections_data_client_request_allEntries_term_cases h
        (net.nwState h) client id c hcr with hsame | ⟨e0, hcons⟩
      · rw [hsame] at hin
        exact Nat.le_trans (hP t e h hin) (Nat.le_of_eq hctd.symm)
      · rw [hcons] at hin
        rcases List.mem_cons.mp hin with heq1 | hin'
        · injection heq1 with h1 h2
          exact Nat.le_of_eq h1
        · exact Nat.le_trans (hP t e h hin') (Nat.le_of_eq hctd.symm)
    · rw [update_neq _ _ heq] at hin ⊢
      exact hP t e h0 hin
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps
    obtain ⟨-, hbr, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine allEntries_term_sanity_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_timeout_ghost h (net.nwState h)).2
    · rcases hbr with ⟨hc, -, -, -⟩ | ⟨hc, -, -, -, -⟩
      · exact Nat.le_of_eq hc.symm
      · rw [hc]
        exact Nat.le_succ _
  · -- append_entries: recorded at the (true) reply's term = the
    -- request's, which the responder's new term dominates
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps
    obtain ⟨-, hbr, -, -⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt
        es ci hae
    have hctd : (net.nwState p.pDst).2.currentTerm ≤ d.currentTerm := by
      rcases hbr with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact Nat.le_of_eq hc.symm
      · exact Nat.le_of_lt hc
    intro t2 e h0 hin
    replace hin : (t2, e) ∈ (st' h0).1.allEntries := hin
    show t2 ≤ (st' h0).2.currentTerm
    rw [hst h0] at hin ⊢
    by_cases heq : h0 = p.pDst
    · rw [heq, update_same] at hin ⊢
      replace hin : (t2, e) ∈ gd.allEntries := hin
      subst hgd
      show t2 ≤ d.currentTerm
      rcases update_elections_data_appendEntries_allEntries_term_cases
        p.pDst (net.nwState p.pDst) t n0 pli plt es ci hae with
        hsame | ⟨t', hreply, happ⟩
      · rw [hsame] at hin
        exact Nat.le_trans (hP t2 e p.pDst hin) hctd
      · rw [happ] at hin
        rcases List.mem_append.mp hin with hnew | hold
        · rcases List.mem_map.mp hnew with ⟨e2, -, heq2⟩
          injection heq2 with h1 h2
          rw [hreply] at hae
          obtain ⟨rfl, hge⟩ := handleAppendEntries_reply_true p.pDst
            (net.nwState p.pDst).2 t n0 pli plt es ci hae
          rw [h1] at hge
          exact hge
        · exact Nat.le_trans (hP t2 e p.pDst hold) hctd
    · rw [update_neq _ _ heq] at hin ⊢
      exact hP t2 e h0 hin
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, hbr, -⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    refine allEntries_term_sanity_of_update hP hst (by rw [hgd]) ?_
    rcases hbr with ⟨hc, -, -⟩ | ⟨hc, -, -⟩
    · exact Nat.le_of_eq hc.symm
    · exact Nat.le_of_lt hc
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach _hpkts hst _hps
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
        hrv
    refine allEntries_term_sanity_of_update hP hst ?_ hle
    subst hgd
    exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t p.pSrc
      lli llt (net.nwState p.pDst)).2.2
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach _hpkts
      hst _hps
    obtain ⟨hbr, -, -, -⟩ := handleRequestVoteReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t v hrvr
    refine allEntries_term_sanity_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_requestVoteReply_votes p.pDst p.pSrc t v
        (net.nwState p.pDst)).2.2
    · rcases hbr with ⟨hc, -⟩ | ⟨hc, -⟩
      · exact Nat.le_of_eq hc.symm
      · exact Nat.le_of_lt hc
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hct, -, -, -, -, -⟩ := doLeader_spec d h hdl
    refine allEntries_term_sanity_of_update hP hst (by rw [hstate]) ?_
    rw [hct, hstate]
    exact Nat.le_refl _
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨-, -, hct, -, -, -⟩ := doGenericServer_spec h d hgs
    refine allEntries_term_sanity_of_update hP hst (by rw [hstate]) ?_
    rw [hct, hstate]
    exact Nat.le_refl _
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach t e h hin
    rw [← hstates h] at hin ⊢
    exact hP t e h hin
  · -- reboot: term survives
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    refine allEntries_term_sanity_of_update hP hst (by rw [hstate]) ?_
    rw [← hrb]
    show (net.nwState h).2.currentTerm ≤ (reboot d).currentTerm
    rw [hstate]
    exact Nat.le_refl _

/-! ## log_properties_hold_on_leader_logs -/

/-- `LeaderLogsLogPropertiesInterface.v:9-11` (`log_property`). -/
def log_property (Pr : List (entry (P := P)) → Prop) : Prop :=
  ∀ (net : RefinedNet) (h : name (P := P)),
    refined_raft_intermediate_reachable net → Pr (net.nwState h).2.log

/-- `LeaderLogsLogPropertiesInterface.v:13-17`
(`log_properties_hold_on_leader_logs`). -/
def log_properties_hold_on_leader_logs (net : RefinedNet) : Prop :=
  ∀ (Pr : List (entry (P := P)) → Prop) (h : name (P := P)) (t : term)
    (ll : List (entry (P := P))),
    log_property Pr → (t, ll) ∈ (net.nwState h).1.leaderLogs → Pr ll

/-- Ghost-unchanged transport for
`log_properties_hold_on_leader_logs`. -/
theorem log_properties_hold_on_leader_logs_of_update
    {net net' : RefinedNet} {u : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : log_properties_hold_on_leader_logs net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs) :
    log_properties_hold_on_leader_logs net' := by
  intro Pr h t ll hlp hin
  rw [hst h] at hin
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hin
    replace hin : (t, ll) ∈ gd.leaderLogs := hin
    rw [hgd] at hin
    exact hP Pr h t ll hlp hin
  · rw [update_neq _ _ heq] at hin
    exact hP Pr h t ll hlp hin

/-- `LeaderLogsLogPropertiesProof.v`
(`log_properties_hold_on_leader_logs_invariant`): a snapshot is a
reachable host log, so any reachability-closed log property holds of
it. -/
theorem log_properties_hold_on_leader_logs_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      log_properties_hold_on_leader_logs net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Pr h t ll _hlp hin
    exact nomatch hin
  · intro h net st' ps' gd out d l client id c _hcr hgd hP _hreach hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2
  · intro net h st' ps' gd out d l _hto hgd hP _hreach hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_timeout_ghost h (net.nwState h)).1
  · intro xs p ys net st' ps' gd d m t n0 pli plt es ci _hae hgd _hbody hP
      _hreach _hpkts hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci).2.2.2
  · intro xs p ys net st' ps' gd d m t es res _haer hgd _hbody hP _hreach
      _hpkts hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    rw [hgd]
  · intro xs p ys net st' ps' gd d m t cid lli llt _hrv hgd _hbody hP
      _hreach _hpkts hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    subst hgd
    exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t p.pSrc
      lli llt (net.nwState p.pDst)).2.1
  · -- request_vote_reply: the fresh snapshot is the winner's own log,
    -- and the pre-state is reachable
    intro xs p ys net st' ps' gd d t v _hrvr hgd _hbody hP hreach _hpkts
      hst _hps
    intro Pr h t2 ll hlp hin
    replace hin : (t2, ll) ∈ (st' h).1.leaderLogs := hin
    rw [hst h] at hin
    by_cases heq : h = p.pDst
    · subst heq
      rw [update_same] at hin
      replace hin : (t2, ll) ∈ gd.leaderLogs := hin
      subst hgd
      rcases leaderLogs_update_elections_data_RVR hin with hold | ⟨-, -, -, hll⟩
      · exact hP Pr p.pDst t2 ll hlp hold
      · rw [hll, handleRequestVoteReply_log]
        exact hlp net p.pDst hreach
    · rw [update_neq _ _ heq] at hin
      exact hP Pr h t2 ll hlp hin
  · intro net st' ps' gd d h os d' ms _hdl hP _hreach hstate hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    rw [hstate]
  · intro net st' ps' gd d os d' ms h _hgs hP _hreach hstate hst _hps
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    rw [hstate]
  · intro net net' hstates _hpkts hP _hreach Pr h t ll hlp hin
    rw [← hstates h] at hin
    exact hP Pr h t ll hlp hin
  · intro net net' gd d h d' _hrb hP _hreach hstate hst _hpkts
    refine log_properties_hold_on_leader_logs_of_update hP hst ?_
    rw [hstate]

/-! ## leaders_have_leaderLogs_strong -/

/-- `LeadersHaveLeaderLogsStrongInterface.v:8-16`
(`leaders_have_leaderLogs_strong`). -/
def leaders_have_leaderLogs_strong (net : RefinedNet) : Prop :=
  ∀ h : name (P := P),
    (net.nwState h).2.type = .Leader →
    ∃ ll es,
      ((net.nwState h).2.currentTerm, ll) ∈ (net.nwState h).1.leaderLogs ∧
      (net.nwState h).2.log = es ++ ll ∧
      (∀ e ∈ es, e.eTerm = (net.nwState h).2.currentTerm)

/-- Transport for `leaders_have_leaderLogs_strong` across steps that
keep ghost leaderLogs, log, type, and term at the updated node. -/
theorem leaders_have_leaderLogs_strong_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : leaders_have_leaderLogs_strong net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs)
    (hd : d.type = .Leader →
      d.log = (net.nwState u).2.log ∧
      d.currentTerm = (net.nwState u).2.currentTerm ∧
      (net.nwState u).2.type = .Leader) :
    leaders_have_leaderLogs_strong net' := by
  intro h hty
  replace hty : (net'.nwState h).2.type = .Leader := hty
  rw [hst h] at hty ⊢
  by_cases heq : h = u
  · subst heq
    rw [update_same] at hty ⊢
    replace hty : d.type = .Leader := hty
    obtain ⟨hlog, hct, hty0⟩ := hd hty
    obtain ⟨ll, es, hmem, hsplit, hterm⟩ := hP h hty0
    refine ⟨ll, es, ?_, ?_, ?_⟩
    · show (d.currentTerm, ll) ∈ gd.leaderLogs
      rw [hct, hgd]
      exact hmem
    · show d.log = es ++ ll
      rw [hlog]
      exact hsplit
    · intro e he
      show e.eTerm = d.currentTerm
      rw [hct]
      exact hterm e he
  · rw [update_neq _ _ heq] at hty ⊢
    exact hP h hty

/-- `LeadersHaveLeaderLogsStrongProof.v:196-278`
(`leaders_have_leaderLogs_strong_invariant`): a leader's log is its
election snapshot plus own-term entries. The two real cases: a client
request stacks one more own-term entry; a fresh win starts with the
empty stack over the just-recorded snapshot. -/
theorem leaders_have_leaderLogs_strong_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaders_have_leaderLogs_strong net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h hty
    exact nomatch hty
  · -- client_request: the fresh entry rides on top of es
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    obtain ⟨htyd, hctd, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro h0 hty
    replace hty : (st' h0).2.type = .Leader := hty
    show ∃ ll es, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs ∧
      (st' h0).2.log = es ++ ll ∧
      ∀ e ∈ es, e.eTerm = (st' h0).2.currentTerm
    rw [hst h0] at hty ⊢
    by_cases heq : h0 = h
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      have hty0 : (net.nwState h).2.type = .Leader := by
        rw [← htyd]
        exact hty
      obtain ⟨ll, es, hmem, hsplit, hterm⟩ := hP h hty0
      subst hgd
      rcases handleClientRequest_log_full h (net.nwState h).2 client id c
        hcr with ⟨-, hlogd⟩ | ⟨hnl, -⟩
      · refine ⟨ll, (⟨h, client, id, maxIndex (net.nwState h).2.log + 1,
          (net.nwState h).2.currentTerm, c⟩ : entry (P := P)) :: es,
          ?_, ?_, ?_⟩
        · show (d.currentTerm, ll) ∈
            (update_elections_data_client_request h (net.nwState h)
              client id c).leaderLogs
          rw [hctd, (update_elections_data_client_request_ghost h
            (net.nwState h) client id c).2.2.2]
          exact hmem
        · show d.log = _ ++ ll
          rw [hlogd, hsplit]
          rfl
        · intro e he
          show e.eTerm = d.currentTerm
          rcases List.mem_cons.mp he with rfl | he'
          · rw [hctd]
          · rw [hctd]
            exact hterm e he'
      · exact absurd hty0 hnl
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP h0 hty
  · -- timeout: a leader only heartbeats
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps
    obtain ⟨hlog, hbr, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine leaders_have_leaderLogs_strong_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_timeout_ghost h (net.nwState h)).1
    · intro htyl
      rcases hbr with ⟨hct, hty, -, -⟩ | ⟨-, hty, -, -, -⟩
      · rw [hty] at htyl
        exact ⟨hlog, hct, htyl⟩
      · rw [hty] at htyl
        exact nomatch htyl
  · -- append_entries: a standing leader rejected
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps
    refine leaders_have_leaderLogs_strong_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_appendEntries_ghost p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci).2.2.2
    · intro htyl
      have hd : d = (net.nwState p.pDst).2 :=
        handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst).2 t n0 pli plt es ci hae
          (by rw [htyl]; exact fun heq => nomatch heq)
      refine ⟨by rw [hd], by rw [hd], ?_⟩
      rw [← hd]
      exact htyl
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      _hpkts hst _hps
    obtain ⟨-, hbr, -⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    refine leaders_have_leaderLogs_strong_of_update hP hst (by rw [hgd]) ?_
    intro htyl
    rcases hbr with ⟨hct, -, hty⟩ | ⟨-, -, hty⟩
    · rw [hty] at htyl
      exact ⟨handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2
        p.pSrc t es res haer, hct, htyl⟩
    · have : serverType.Follower = .Leader := hty.symm.trans htyl
      exact nomatch this
  · -- request_vote
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach _hpkts hst _hps
    obtain ⟨-, -, hbr, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t p.pSrc lli llt
        hrv
    refine leaders_have_leaderLogs_strong_of_update hP hst ?_ ?_
    · subst hgd
      exact (update_elections_data_requestVote_cronies p.pDst p.pSrc t
        p.pSrc lli llt (net.nwState p.pDst)).2.1
    · intro htyl
      rcases hbr with ⟨hct, hty⟩ | hty
      · rw [hty] at htyl
        exact ⟨handleRequestVote_log p.pDst (net.nwState p.pDst).2 t p.pSrc
          lli llt hrv, hct, htyl⟩
      · have : serverType.Follower = .Leader := hty.symm.trans htyl
        exact nomatch this
  · -- request_vote_reply: standing leader, or a fresh win with an empty
    -- own-term stack over the just-recorded snapshot
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach _hpkts
      hst _hps
    obtain ⟨-, -, -, hlead4⟩ := handleRequestVoteReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t v hrvr
    intro h0 hty
    replace hty : (st' h0).2.type = .Leader := hty
    show ∃ ll es, ((st' h0).2.currentTerm, ll) ∈ (st' h0).1.leaderLogs ∧
      (st' h0).2.log = es ++ ll ∧
      ∀ e ∈ es, e.eTerm = (st' h0).2.currentTerm
    rw [hst h0] at hty ⊢
    by_cases heq : h0 = p.pDst
    · rw [heq, update_same] at hty ⊢
      replace hty : d.type = .Leader := hty
      subst hgd
      rcases hlead4 hty with heqd | ⟨hcand, -, -⟩
      · -- standing leader: state untouched, old leaderLogs preserved
        obtain ⟨ll, es, hmem, hsplit, hterm⟩ := hP p.pDst
          (by rw [heqd] at hty; exact hty)
        refine ⟨ll, es, ?_, ?_, ?_⟩
        · show (d.currentTerm, ll) ∈
            (update_elections_data_requestVoteReply p.pDst p.pSrc t v
              (net.nwState p.pDst)).leaderLogs
          rw [heqd]
          exact update_elections_data_requestVoteReply_leaderLogs_old
            p.pDst p.pSrc t v (net.nwState p.pDst) hmem
        · show d.log = es ++ ll
          rw [heqd]
          exact hsplit
        · intro e he
          show e.eTerm = d.currentTerm
          rw [heqd]
          exact hterm e he
      · -- fresh win: the snapshot IS the log; es = []
        have hintro :=
          update_elections_data_requestVoteReply_leaderLogs_intro p.pDst
            p.pSrc t v (net.nwState p.pDst) hcand (by rw [hrvr]; exact hty)
        rw [hrvr] at hintro
        refine ⟨d.log, [], hintro, rfl, ?_⟩
        intro e he
        exact nomatch he
    · rw [update_neq _ _ heq] at hty ⊢
      exact hP h0 hty
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hct, -, hty, -, hlog, -⟩ := doLeader_spec d h hdl
    refine leaders_have_leaderLogs_strong_of_update hP hst (by rw [hstate])
      ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨?_, ?_, ?_⟩
    · rw [hlog, hstate]
    · rw [hct, hstate]
    · rw [hstate]
      exact htyl
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨hlog, hty, hct, -, -, -⟩ := doGenericServer_spec h d hgs
    refine leaders_have_leaderLogs_strong_of_update hP hst (by rw [hstate])
      ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨?_, ?_, ?_⟩
    · rw [hlog, hstate]
    · rw [hct, hstate]
    · rw [hstate]
      exact htyl
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h hty
    replace hty : (net'.nwState h).2.type = .Leader := hty
    show ∃ ll es, ((net'.nwState h).2.currentTerm, ll) ∈
        (net'.nwState h).1.leaderLogs ∧
      (net'.nwState h).2.log = es ++ ll ∧
      ∀ e ∈ es, e.eTerm = (net'.nwState h).2.currentTerm
    rw [← hstates h] at hty ⊢
    exact hP h hty
  · -- reboot: a rebooted node is a follower
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    refine leaders_have_leaderLogs_strong_of_update hP hst (by rw [hstate])
      ?_
    intro htyl
    rw [← hrb] at htyl
    exact nomatch htyl

end AppendEntriesChain

end Raft
end VerdiCompat
