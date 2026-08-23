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

/-! ## append_entries_request_reply_correspondence (BASE)

`AppendEntriesRequestReplyCorrespondenceProof.v` (429 lines): every
true AppendEntriesReply in flight corresponds to an equivalent
REACHABLE network carrying a matching request — the fault model's dup
step keeps the consumed request alive. The subset machinery is Verdi's
`DupDropReordering.v` `dup_drop_reorder`, re-proved here directly as
`subset_reachable` (dup members in, drop the rest). -/

/-- Duplicate one in-flight packet (a `StepFailure_dup` re-step). -/
theorem reachable_dup {net : RaftNet}
    (hreach : raft_intermediate_reachable (P := P) net)
    {p : Packet (raft_base_params (P := P)) raft_multi_params}
    (hp : p ∈ net.nwPackets) :
    raft_intermediate_reachable (P := P) ⟨p :: net.nwPackets, net.nwState⟩ := by
  obtain ⟨xs, ys, hsplit⟩ := List.append_of_mem hp
  refine raft_intermediate_reachable.RIR_step_failure [] net [] _ [] hreach
    (step_failure.StepFailure_dup net _ [] p xs ys hsplit ?_)
  rw [hsplit]
  rfl

/-- Drop a packet-list suffix, one head-of-suffix at a time. -/
theorem reachable_drop_suffix {S : name (P := P) → raft_data (P := P)}
    (build l : List (Packet (raft_base_params (P := P)) raft_multi_params))
    (hreach : raft_intermediate_reachable (P := P) ⟨build ++ l, S⟩) :
    raft_intermediate_reachable (P := P) ⟨build, S⟩ := by
  induction l with
  | nil =>
    rw [List.append_nil] at hreach
    exact hreach
  | cons q l₂ ih =>
    refine ih ?_
    exact raft_intermediate_reachable.RIR_step_failure [] ⟨build ++ q :: l₂, S⟩
      [] _ [] hreach
      (step_failure.StepFailure_drop _ _ [] q build l₂ rfl rfl)

/-- `AppendEntriesRequestReplyCorrespondenceProof.v:178-195`
(`subset_reachable`, via Verdi's `dup_drop_reorder`): a network with the
same states and any member-subset of the packets is reachable. -/
theorem subset_reachable {net : RaftNet}
    (l' : List (Packet (raft_base_params (P := P)) raft_multi_params))
    (hsub : ∀ p ∈ l', p ∈ net.nwPackets)
    (hreach : raft_intermediate_reachable (P := P) net) :
    raft_intermediate_reachable (P := P) ⟨l', net.nwState⟩ := by
  have hbuild : ∀ (b : List (Packet (raft_base_params (P := P))
      raft_multi_params)), (∀ p ∈ b, p ∈ net.nwPackets) →
      raft_intermediate_reachable (P := P)
        ⟨b ++ net.nwPackets, net.nwState⟩ := by
    intro b hb
    induction b with
    | nil =>
      show raft_intermediate_reachable (⟨net.nwPackets, net.nwState⟩ : RaftNet)
      cases net
      exact hreach
    | cons p rest ih =>
      have hmem : p ∈ (⟨rest ++ net.nwPackets, net.nwState⟩ : RaftNet).nwPackets :=
        List.mem_append.mpr (Or.inr (hb p (List.mem_cons_self ..)))
      exact reachable_dup
        (ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))) hmem
  exact reachable_drop_suffix l' net.nwPackets (hbuild l' hsub)

/-- `AppendEntriesRequestReplyCorrespondenceInterface.v:9-14`
(`exists_equivalent_network_with_aer`). -/
def exists_equivalent_network_with_aer (net : RaftNet)
    (src dst : name (P := P)) (t : term) (es : List (entry (P := P))) :
    Prop :=
  ∃ (net' : RaftNet) (pli : logIndex) (plt : term) (ci : logIndex)
    (n : name (P := P)),
    raft_intermediate_reachable net' ∧
    net'.nwState = net.nwState ∧
    net'.nwPackets = net.nwPackets ++
      [⟨src, dst, .AppendEntries t n pli plt es ci⟩]

/-- `AppendEntriesRequestReplyCorrespondenceInterface.v:16-20`
(`append_entries_request_reply_correspondence`). -/
def append_entries_request_reply_correspondence (net : RaftNet) : Prop :=
  ∀ (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (es : List (entry (P := P))),
    p ∈ net.nwPackets → p.pBody = .AppendEntriesReply t es true →
    exists_equivalent_network_with_aer net p.pDst p.pSrc t es

omit O in
/-- Membership embeds under a snoc on the right list. -/
theorem mem_app_snoc {α : Type _} {q r : α} {xs ys : List α}
    (h : q ∈ xs ++ ys) : q ∈ xs ++ (ys ++ [r]) := by
  rcases List.mem_append.mp h with h1 | h1
  · exact List.mem_append.mpr (Or.inl h1)
  · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h1)))

/-- `AppendEntriesRequestReplyCorrespondenceProof.v:198-443`
(`append_entries_request_reply_correspondence_invariant`): each
obligation re-plays the step from the equivalent network; the creation
case (an accepted AppendEntries) first DUPLICATES the request being
consumed, so one copy survives beside the fresh reply. -/
theorem append_entries_request_reply_correspondence_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      append_entries_request_reply_correspondence net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: no packets
    intro p0 t0 es0 hp0 _
    exact nomatch hp0
  · -- client_request: re-play; sends nothing
    intro h net st' ps' out d l client id c hcr hP _hreach hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 hold hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_handleInput net₀ h
        (.ClientRequest client id c) out d l _ st' hreach₀ ?_ ?_ ?_
      · show handleInput h (.ClientRequest client id c)
          (net₀.nwState h) = (out, d, l)
        rw [hst₀]
        exact hcr
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (by rw [hpk₀]; exact List.mem_append.mpr (Or.inl h1))
          · exact Or.inr h1
        · exact Or.inl (by
            rw [hpk₀]
            exact List.mem_append.mpr (Or.inr hq'))
    · exfalso
      obtain ⟨-, -, -, -, hl⟩ :=
        handleClientRequest_spec h (net.nwState h) client id c hcr
      rw [hl] at hnew
      simp [send_packets] at hnew
  · -- timeout: re-play; sends only RequestVotes
    intro net h st' ps' out d l hto hP _hreach hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 hold hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_handleInput net₀ h
        .Timeout out d l _ st' hreach₀ ?_ ?_ ?_
      · show handleInput h .Timeout (net₀.nwState h) = (out, d, l)
        rw [hst₀]
        exact hto
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (by rw [hpk₀]; exact List.mem_append.mpr (Or.inl h1))
          · exact Or.inr h1
        · exact Or.inl (by
            rw [hpk₀]
            exact List.mem_append.mpr (Or.inr hq'))
    · exfalso
      obtain ⟨-, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h) hto
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
      replace hbody0 : m0.2 = msg.AppendEntriesReply t0 es0 true := hbody0
      rw [hq2] at hbody0
      exact nomatch hbody0
  · -- append_entries: the CREATION case — dup the consumed request
    intro xs p ys net st' ps' d m t n0 pli plt es ci hae hbody hP hreach
      hpkts hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hm2 : ∀ (S : name (P := P) → raft_data (P := P)),
        S p.pDst = net.nwState p.pDst →
        handleMessage p.pSrc p.pDst p.pBody (S p.pDst)
          = (d, [(p.pSrc, m)]) := by
      intro S hS
      rw [hS]
      unfold handleMessage
      rw [hbody]
      simp only []
      rw [hae]
    rcases hps p0 hp0 with hold | hnew
    · -- old reply: re-play the delivery from the equivalent network
      obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 (by rw [hpkts]; exact mem_of_mem_remove_middle hold)
          hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_handleMessage p net₀ xs
        (ys ++ [⟨p0.pDst, p0.pSrc,
          .AppendEntries t0 n' pli' plt' es0 ci'⟩]) st' _ d
        [(p.pSrc, m)] hreach₀ (hm2 net₀.nwState (by rw [hst₀])) ?_ ?_ ?_
      · rw [hpk₀, hpkts, List.append_assoc, List.cons_append]
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (mem_app_snoc h1)
          · right
            show q ∈ [(⟨p.pDst, p.pSrc, m⟩ :
              Packet (raft_base_params (P := P)) raft_multi_params)]
            rw [h1]
            exact List.mem_cons_self ..
        · exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_append.mpr
            (Or.inr hq'))))
    · -- the fresh reply: dup the request, then deliver one copy
      subst hnew
      replace hbody0 : m = msg.AppendEntriesReply t0 es0 true := hbody0
      subst hbody0
      obtain ⟨t'', r'', hml⟩ := handleAppendEntries_reply_entries p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci hae
      injection hml with hml1 hml2 hml3
      obtain ⟨ht0, -⟩ := handleAppendEntries_reply_true p.pDst
        (net.nwState p.pDst) t n0 pli plt es ci hae
      have hdup : raft_intermediate_reachable (P := P)
          ⟨p :: net.nwPackets, net.nwState⟩ := reachable_dup hreach hp_in
      refine ⟨⟨ps' ++ [p], st'⟩, pli, plt, ci, n0, ?_, rfl, ?_⟩
      · refine raft_intermediate_reachable.RIR_handleMessage p
          ⟨p :: net.nwPackets, net.nwState⟩ (p :: xs) ys st' _ d
          [(p.pSrc, msg.AppendEntriesReply t0 es0 true)] hdup
          (hm2 net.nwState rfl) ?_ ?_ ?_
        · show p :: net.nwPackets = (p :: xs) ++ p :: ys
          rw [hpkts]
          rfl
        · intro h'
          exact hst h'
        · intro q hq
          rcases List.mem_append.mp hq with hq' | hq'
          · rcases hps q hq' with h1 | h1
            · left
              rcases List.mem_append.mp h1 with h2 | h2
              · exact List.mem_append.mpr
                  (Or.inl (List.mem_cons_of_mem _ h2))
              · exact List.mem_append.mpr (Or.inr h2)
            · right
              show q ∈ [(⟨p.pDst, p.pSrc,
                msg.AppendEntriesReply t0 es0 true⟩ :
                Packet (raft_base_params (P := P)) raft_multi_params)]
              rw [h1]
              exact List.mem_cons_self ..
          · obtain rfl := List.mem_singleton.mp hq'
            exact Or.inl (List.mem_append.mpr
              (Or.inl (List.mem_cons_self ..)))
      · show ps' ++ [p] = ps' ++ [⟨p.pSrc, p.pDst,
          msg.AppendEntries t0 n0 pli plt es0 ci⟩]
        rw [ht0, hml2, ← hbody]
  · -- append_entries_reply: re-play; replies carry no AppendEntries
    intro xs p ys net st' ps' d m t es res haer hbody hP _hreach hpkts hst
      hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst) p.pSrc t es res haer
    rcases hps p0 hp0 with hold | hnew
    · obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 (by rw [hpkts]; exact mem_of_mem_remove_middle hold)
          hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_handleMessage p net₀ xs
        (ys ++ [⟨p0.pDst, p0.pSrc,
          .AppendEntries t0 n' pli' plt' es0 ci'⟩]) st' _ d m hreach₀
        ?_ ?_ ?_ ?_
      · show handleMessage p.pSrc p.pDst p.pBody (net₀.nwState p.pDst)
          = (d, m)
        rw [hst₀]
        unfold handleMessage
        rw [hbody]
        simp only []
        exact haer
      · rw [hpk₀, hpkts, List.append_assoc, List.cons_append]
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (mem_app_snoc h1)
          · exact Or.inr h1
        · exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_append.mpr
            (Or.inr hq'))))
    · exfalso
      rw [hl] at hnew
      simp [send_packets] at hnew
  · -- request_vote: re-play; the reply is a RequestVoteReply
    intro xs p ys net st' ps' d m t cid lli llt hrv hbody hP _hreach hpkts
      hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 (by rw [hpkts]; exact mem_of_mem_remove_middle hold)
          hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_handleMessage p net₀ xs
        (ys ++ [⟨p0.pDst, p0.pSrc,
          .AppendEntries t0 n' pli' plt' es0 ci'⟩]) st' _ d
        [(p.pSrc, m)] hreach₀ ?_ ?_ ?_ ?_
      · show handleMessage p.pSrc p.pDst p.pBody (net₀.nwState p.pDst)
          = (d, [(p.pSrc, m)])
        rw [hst₀]
        unfold handleMessage
        rw [hbody]
        simp only []
        rw [hrv]
      · rw [hpk₀, hpkts, List.append_assoc, List.cons_append]
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (mem_app_snoc h1)
          · right
            show q ∈ [(⟨p.pDst, p.pSrc, m⟩ :
              Packet (raft_base_params (P := P)) raft_multi_params)]
            rw [h1]
            exact List.mem_cons_self ..
        · exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_append.mpr
            (Or.inr hq'))))
    · exfalso
      obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
        (net.nwState p.pDst) t p.pSrc lli llt hrv
      rw [hnew] at hbody0
      replace hbody0 : m = msg.AppendEntriesReply t0 es0 true := hbody0
      rw [hmshape] at hbody0
      exact nomatch hbody0
  · -- request_vote_reply: re-play; nothing is sent
    intro xs p ys net st' ps' d t v hrvr hbody hP _hreach hpkts hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
      hP p0 t0 es0
        (by rw [hpkts]; exact mem_of_mem_remove_middle (hps p0 hp0)) hbody0
    refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
      .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
      pli', plt', ci', n', ?_, rfl, rfl⟩
    refine raft_intermediate_reachable.RIR_handleMessage p net₀ xs
      (ys ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩]) st' _ d [] hreach₀
      ?_ ?_ ?_ ?_
    · show handleMessage p.pSrc p.pDst p.pBody (net₀.nwState p.pDst)
        = (d, [])
      rw [hst₀]
      unfold handleMessage
      rw [hbody]
      simp only []
      rw [hrvr]
    · rw [hpk₀, hpkts, List.append_assoc, List.cons_append]
    · intro h'
      rw [hst₀]
      exact hst h'
    · intro q hq
      rcases List.mem_append.mp hq with hq' | hq'
      · exact Or.inl (mem_app_snoc (hps q hq'))
      · exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_append.mpr
          (Or.inr hq'))))
  · -- do_leader: re-play; fresh messages are AppendEntries, not replies
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 hold hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_doLeader net₀ st' _ h os d' ms
        hreach₀ ?_ ?_ ?_
      · show doLeader (net₀.nwState h) h = (os, d', ms)
        rw [hst₀, hstate]
        exact hdl
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (by rw [hpk₀]; exact List.mem_append.mpr (Or.inl h1))
          · exact Or.inr h1
        · exact Or.inl (by
            rw [hpk₀]
            exact List.mem_append.mpr (Or.inr hq'))
    · exfalso
      obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨t3, l3, p3, p4, e3, c3, hq2⟩ := (doLeader_spec d h hdl).2.2.2.2.2
        m0 hm0
      replace hbody0 : m0.2 = msg.AppendEntriesReply t0 es0 true := hbody0
      rw [hq2] at hbody0
      exact nomatch hbody0
  · -- do_generic_server: re-play; nothing is sent
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    intro p0 t0 es0 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    rcases hps p0 hp0 with hold | hnew
    · obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
        hP p0 t0 es0 hold hbody0
      refine ⟨⟨ps' ++ [⟨p0.pDst, p0.pSrc,
        .AppendEntries t0 n' pli' plt' es0 ci'⟩], st'⟩,
        pli', plt', ci', n', ?_, rfl, rfl⟩
      refine raft_intermediate_reachable.RIR_doGenericServer net₀ st' _ os
        d' ms h hreach₀ ?_ ?_ ?_
      · show doGenericServer h (net₀.nwState h) = (os, d', ms)
        rw [hst₀, hstate]
        exact hgs
      · intro h'
        rw [hst₀]
        exact hst h'
      · intro q hq
        rcases List.mem_append.mp hq with hq' | hq'
        · rcases hps q hq' with h1 | h1
          · exact Or.inl (by rw [hpk₀]; exact List.mem_append.mpr (Or.inl h1))
          · exact Or.inr h1
        · exact Or.inl (by
            rw [hpk₀]
            exact List.mem_append.mpr (Or.inr hq'))
    · exfalso
      rw [hms] at hnew
      simp [send_packets] at hnew
  · -- state_same_packet_subset: dup/drop to the survivor set
    intro net net'' hstates hsub hP _hreach
    intro p0 t0 es0 hp0 hbody0
    obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
      hP p0 t0 es0 (hsub p0 hp0) hbody0
    refine ⟨⟨net''.nwPackets ++ [⟨p0.pDst, p0.pSrc,
      .AppendEntries t0 n' pli' plt' es0 ci'⟩], net₀.nwState⟩,
      pli', plt', ci', n', ?_, ?_, rfl⟩
    · refine subset_reachable _ ?_ hreach₀
      intro q hq
      rw [hpk₀]
      rcases List.mem_append.mp hq with h1 | h1
      · exact List.mem_append.mpr (Or.inl (hsub q h1))
      · exact List.mem_append.mpr (Or.inr h1)
    · rw [hst₀]
      exact funext hstates
  · -- reboot: the crash-and-return re-step
    intro net net'' d h d' hrb hP _hreach hstate hst hpkts
    intro p0 t0 es0 hp0 hbody0
    obtain ⟨net₀, pli', plt', ci', n', hreach₀, hst₀, hpk₀⟩ :=
      hP p0 t0 es0 (by rw [hpkts]; exact hp0) hbody0
    refine ⟨⟨net₀.nwPackets,
      update net₀.nwState h (reboot (net₀.nwState h))⟩,
      pli', plt', ci', n', ?_, ?_, ?_⟩
    · exact raft_intermediate_reachable.RIR_step_failure [h] net₀
        (removeAll h [h]) _ [] hreach₀
        (step_failure.StepFailure_reboot h net₀ _ [h] _
          (List.mem_cons_self ..) rfl rfl)
    · show update net₀.nwState h (reboot (net₀.nwState h)) = net''.nwState
      rw [hst₀, hstate, hrb]
      exact (funext hst).symm
    · show net₀.nwPackets = net''.nwPackets ++ _
      rw [hpk₀, hpkts]

/-! ## appendEntries_requests_came_from_leaders -/

omit O in
/-- Only a leader's `doLeader` sends anything. -/
theorem doLeader_messages_leader (st : raft_data (P := P))
    (me : name (P := P)) {os st' ms} {q : name (P := P) × msg (P := P)}
    (h : doLeader st me = (os, st', ms)) (hq : q ∈ ms) :
    st.type = .Leader := by
  unfold doLeader at h
  split at h
  · rename_i htype
    exact htype
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact nomatch hq

/-- `AppendEntriesRequestsCameFromLeadersInterface.v:8-15`
(`append_entries_came_from_leaders`). -/
def append_entries_came_from_leaders (net : RefinedNet) : Prop :=
  ∀ (p : RefinedPacket) (t : term) (n : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t n pli plt es ci →
    ∃ ll, (t, ll) ∈ (net.nwState p.pSrc).1.leaderLogs

/-- Sender-side transport: leaderLogs only grow at the updated node. -/
theorem came_from_leaders_transport {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgrow : ∀ (t : term) (ll : List (entry (P := P))),
      (t, ll) ∈ (net.nwState u).1.leaderLogs → (t, ll) ∈ gd.leaderLogs)
    {src : name (P := P)} {t : term}
    (hex : ∃ ll, (t, ll) ∈ (net.nwState src).1.leaderLogs) :
    ∃ ll, (t, ll) ∈ (net'.nwState src).1.leaderLogs := by
  obtain ⟨ll, hll⟩ := hex
  rw [hst src]
  by_cases heq : src = u
  · rw [heq, update_same]
    rw [heq] at hll
    exact ⟨ll, hgrow t ll hll⟩
  · rw [update_neq _ _ heq]
    exact ⟨ll, hll⟩

/-- `AppendEntriesRequestsCameFromLeadersProof.v:24-160`
(`append_entries_came_from_leaders_invariant`): a fresh AppendEntries
is sent by `doLeader` at the sender's own term, and
`leaders_have_leaderLogs` supplies the snapshot; leaderLogs only
grow. -/
theorem append_entries_came_from_leaders_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      append_entries_came_from_leaders net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro p0 t0 n1 pli plt es ci hp0 _
    exact nomatch hp0
  · -- client_request: no packets sent
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst hps
    obtain ⟨-, -, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro p0 t0 n1 pli plt es ci hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hl] at h1
        simp [send_packets] at h1
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli plt es ci hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_client_request_ghost h (net.nwState h)
      client id c).2.2.2]
    exact hll
  · -- timeout: only RequestVotes
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    obtain ⟨-, -, hmsgs⟩ := handleTimeout_spec h (net.nwState h).2 hto
    intro p0 t0 n1 pli plt es ci hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp h1
        obtain ⟨t3, c3, l3, l4, hq2⟩ := hmsgs m0 hm0
        replace hbody0 : m0.2 = msg.AppendEntries t0 n1 pli plt es ci :=
          hbody0
        rw [hq2] at hbody0
        exact nomatch hbody0
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli plt es ci hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_timeout_ghost h (net.nwState h)).1]
    exact hll
  · -- append_entries: the reply is an AppendEntriesReply
    intro xs p ys net st' ps' gd d m t n0 pli plt es ci hae hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨-, -, -, t', es', r', hmshape⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t n0 pli plt
        es ci hae
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_appendEntries_ghost p.pDst
      (net.nwState p.pDst) t n0 pli plt es ci).2.2.2]
    exact hll
  · -- append_entries_reply: no messages
    intro xs p ys net st' ps' gd d m t es res haer hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨-, -, hl⟩ := handleAppendEntriesReply_spec p.pDst
      (net.nwState p.pDst).2 p.pSrc t es res haer
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · rw [hl] at h1
        simp [send_packets] at h1
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    rw [hgd]
    exact hll
  · -- request_vote: the reply is a RequestVoteReply
    intro xs p ys net st' ps' gd d m t cid lli llt hrv hgd _hbody hP
      _hreach hpkts hst hps
    obtain ⟨t'', v'', hmshape⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t p.pSrc lli llt hrv
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · rw [hpkts]
        exact mem_of_mem_remove_middle h1
      · exfalso
        rw [h1] at hbody0
        replace hbody0 : m = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
          hbody0
        rw [hmshape] at hbody0
        exact nomatch hbody0
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t p.pSrc
      lli llt (net.nwState p.pDst)).2.1]
    exact hll
  · -- request_vote_reply: no sends; old snapshots survive the cons
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP _hreach hpkts
      hst hps
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rw [hpkts]
      exact mem_of_mem_remove_middle (hps p0 hp0)
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    subst hgd
    exact update_elections_data_requestVoteReply_leaderLogs_old p.pDst
      p.pSrc t v (net.nwState p.pDst) hll
  · -- do_leader: THE creation case — the sender is a leader, and
    -- leaders_have_leaderLogs supplies the snapshot at its own term
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst hps
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    rcases hps p0 hp0 with hold | hnew
    · refine came_from_leaders_transport hst ?_
        (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
      intro t2 ll hll
      rw [hstate] at hll
      exact hll
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hnew
      obtain ⟨pi3, pt3, ci3, es3, hq2, -⟩ := doLeader_messages d h hdl m0 hm0
      replace hbody0 : m0.2 = msg.AppendEntries t0 n1 pli2 plt2 es2 ci2 :=
        hbody0
      rw [hq2] at hbody0
      injection hbody0 with f1 f2 f3 f4 f5 f6
      have htype : d.type = .Leader := doLeader_messages_leader d h hdl hm0
      obtain ⟨ll, hll⟩ := leaders_have_leaderLogs_invariant net hreach h
        (by rw [hstate]; exact htype)
      refine ⟨ll, ?_⟩
      show (t0, ll) ∈ (st' h).1.leaderLogs
      rw [hst h, update_same]
      show (t0, ll) ∈ gd.leaderLogs
      have hgd : gd = (net.nwState h).1 := by
        rw [hstate]
      rw [hgd]
      rw [hstate] at hll
      show (t0, ll) ∈ (net.nwState h).1.leaderLogs
      have hteq : (net.nwState h).2.currentTerm = t0 := by
        rw [hstate]
        exact f1
      rw [← hteq]
      rw [hstate]
      exact hll
  · -- do_generic_server: no messages
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨-, -, -, -, -, hms⟩ := doGenericServer_spec h d hgs
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    replace hp0 : p0 ∈ ps' := hp0
    have hold : p0 ∈ net.nwPackets := by
      rcases hps p0 hp0 with h1 | h1
      · exact h1
      · rw [hms] at h1
        simp [send_packets] at h1
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hold hbody0)
    intro t2 ll hll
    rw [hstate] at hll
    exact hll
  · -- state_same_packet_subset
    intro net net' hstates hsub hP _hreach p0 t0 n1 pli2 plt2 es2 ci2 hp0
      hbody0
    obtain ⟨ll, hll⟩ := hP p0 t0 n1 pli2 plt2 es2 ci2 (hsub p0 hp0) hbody0
    rw [hstates p0.pSrc] at hll
    exact ⟨ll, hll⟩
  · -- reboot: ghost and packets survive
    intro net net' gd d h d' _hrb hP _hreach hstate hst hpkts
    intro p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0
    rw [← hpkts] at hp0
    refine came_from_leaders_transport hst ?_
      (hP p0 t0 n1 pli2 plt2 es2 ci2 hp0 hbody0)
    intro t2 ll hll
    rw [hstate] at hll
    exact hll

/-! ## leaderLogs_sublog -/

omit O in
/-- `LeaderLogsSublogProof.v:181-197` (`handleRequestVoteReply_RVR_spec`):
the three-way outcome of a RequestVoteReply — untouched, stepped down to
a follower at the reply term, or same-term with an optional
candidate→leader transition. -/
theorem handleRequestVoteReply_RVR_spec (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term) (v : Bool)
    {st'} (h : handleRequestVoteReply me st src t v = st') :
    st' = st ∨
    (st'.type = .Follower ∧ st'.currentTerm = t ∧ st'.log = st.log) ∨
    (st'.currentTerm = st.currentTerm ∧ st'.log = st.log ∧
     ((st.type = .Candidate ∧ st'.type = .Leader ∧ v = true ∧
       st.currentTerm = t ∧
       wonElection (dedup (src :: st.votesReceived)) = true) ∨
      st'.type = st.type)) := by
  unfold handleRequestVoteReply advanceCurrentTerm at h
  simp only [] at h
  repeat' split at h
  all_goals subst h
  · -- t > currentTerm: the advance fired — follower at t
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · -- stale reply: unchanged
    exact Or.inl rfl
  · -- candidate, granted, won: the transition
    rename_i hnge hnlt _x hcand hv hwon
    simp only [Nat.blt_eq] at hnge hnlt
    simp only [Bool.and_eq_true] at hwon
    exact Or.inr (Or.inr ⟨rfl, rfl, Or.inl ⟨hcand, rfl, hv,
      Nat.le_antisymm (Nat.le_of_not_lt hnlt) (Nat.le_of_not_lt hnge),
      hwon.2⟩⟩)
  · -- candidate, granted, tally short
    exact Or.inr (Or.inr ⟨rfl, rfl, Or.inr rfl⟩)
  · -- candidate, not granted, "won": v must be true — impossible
    rename_i hv hwon
    simp only [Bool.and_eq_true] at hwon
    exact absurd hwon.1 hv
  · -- candidate, not granted, tally short
    exact Or.inr (Or.inr ⟨rfl, rfl, Or.inr rfl⟩)
  · -- non-candidate: unchanged
    exact Or.inl rfl

/-- `LeaderLogsSublogProof.v:162-179` (`lifted_leader_sublog_host`) — a
`lift_prop` consumer. -/
theorem lifted_leader_sublog_host :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      ∀ (leader h : name (P := P)) (e : entry (P := P)),
        (net.nwState leader).2.type = .Leader →
        e ∈ (net.nwState h).2.log →
        e.eTerm = (net.nwState leader).2.currentTerm →
        e ∈ (net.nwState leader).2.log := by
  intro net hreach leader h e hty hin hterm
  exact (lift_prop _ leader_sublog_invariant_invariant net hreach).1
    leader e h hty hin hterm

/-- `LeaderLogsSublogInterface.v:8-14` (`leaderLogs_sublog`). -/
def leaderLogs_sublog (net : RefinedNet) : Prop :=
  ∀ (leader : name (P := P)) (t : term) (ll : List (entry (P := P)))
    (e : entry (P := P)) (h : name (P := P)),
    (net.nwState leader).2.type = .Leader →
    (t, ll) ∈ (net.nwState h).1.leaderLogs →
    e ∈ ll →
    e.eTerm = (net.nwState leader).2.currentTerm →
    e ∈ (net.nwState leader).2.log

/-- Transport for `leaderLogs_sublog` across ghost-leaderLogs-preserving
steps whose real update only demotes (leader ⇒ log/term kept). -/
theorem leaderLogs_sublog_of_update {net net' : RefinedNet}
    {u : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hP : leaderLogs_sublog net)
    (hst : ∀ h', net'.nwState h' = update net.nwState u (gd, d) h')
    (hgd : gd.leaderLogs = (net.nwState u).1.leaderLogs)
    (hd : d.type = .Leader →
      d.log = (net.nwState u).2.log ∧
      d.currentTerm = (net.nwState u).2.currentTerm ∧
      (net.nwState u).2.type = .Leader) :
    leaderLogs_sublog net' := by
  intro L t ll e h htyL hin he hterm
  replace htyL : (net'.nwState L).2.type = .Leader := htyL
  replace hin : (t, ll) ∈ (net'.nwState h).1.leaderLogs := hin
  replace hterm : e.eTerm = (net'.nwState L).2.currentTerm := hterm
  show e ∈ (net'.nwState L).2.log
  rw [hst L] at htyL hterm ⊢
  rw [hst h] at hin
  have hin' : (t, ll) ∈ (net.nwState h).1.leaderLogs := by
    by_cases hhu : h = u
    · rw [hhu, update_same] at hin
      replace hin : (t, ll) ∈ gd.leaderLogs := hin
      rw [hgd] at hin
      rw [hhu]
      exact hin
    · rw [update_neq _ _ hhu] at hin
      exact hin
  by_cases hLu : L = u
  · rw [hLu, update_same] at htyL hterm ⊢
    replace htyL : d.type = .Leader := htyL
    obtain ⟨hlog, hct, hty0⟩ := hd htyL
    replace hterm : e.eTerm = d.currentTerm := hterm
    rw [hct] at hterm
    show e ∈ d.log
    rw [hlog]
    exact hP u t ll e h hty0 hin' he hterm
  · rw [update_neq _ _ hLu] at htyL hterm ⊢
    exact hP L t ll e h htyL hin' he hterm

/-- `LeaderLogsSublogProof.v:29-380` (`leaderLogs_sublog_invariant`):
any snapshot entry bearing a leader's current term is in that leader's
log. The RequestVoteReply win case is the crux: a same-term old
snapshot entry contradicts term sanity (own snapshot) or
CandidateEntries via the consumed grant (someone else's). -/
theorem leaderLogs_sublog_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      leaderLogs_sublog net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro L t ll e h _ hin
    exact nomatch hin
  · -- client_request: the leader stacks a fresh own-term entry
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
    obtain ⟨htyd, hctd, -, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    intro L t ll e h0 htyL hin he hterm
    replace htyL : (st' L).2.type = .Leader := htyL
    replace hin : (t, ll) ∈ (st' h0).1.leaderLogs := hin
    replace hterm : e.eTerm = (st' L).2.currentTerm := hterm
    show e ∈ (st' L).2.log
    rw [hst L] at htyL hterm ⊢
    rw [hst h0] at hin
    have hin' : (t, ll) ∈ (net.nwState h0).1.leaderLogs := by
      by_cases hhu : h0 = h
      · rw [hhu, update_same] at hin
        replace hin : (t, ll) ∈ gd.leaderLogs := hin
        subst hgd
        rw [(update_elections_data_client_request_ghost h (net.nwState h)
          client id c).2.2.2] at hin
        rw [hhu]
        exact hin
      · rw [update_neq _ _ hhu] at hin
        exact hin
    by_cases hLu : L = h
    · rw [hLu, update_same] at htyL hterm ⊢
      replace htyL : d.type = .Leader := htyL
      replace hterm : e.eTerm = d.currentTerm := hterm
      have hty0 : (net.nwState h).2.type = .Leader := by
        rw [← htyd]
        exact htyL
      rw [hctd] at hterm
      have hmem : e ∈ (net.nwState h).2.log :=
        hP h t ll e h0 hty0 hin' he hterm
      show e ∈ d.log
      rcases handleClientRequest_log_full h (net.nwState h).2 client id c
        hcr with ⟨-, hlogd⟩ | ⟨hnl, -⟩
      · rw [hlogd]
        exact List.mem_cons_of_mem _ hmem
      · exact absurd hty0 hnl
    · rw [update_neq _ _ hLu] at htyL hterm ⊢
      exact hP L t ll e h0 htyL hin' he hterm
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps
    obtain ⟨hlog, hbr, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    refine leaderLogs_sublog_of_update hP hst ?_ ?_
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
    refine leaderLogs_sublog_of_update hP hst ?_ ?_
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
    refine leaderLogs_sublog_of_update hP hst (by rw [hgd]) ?_
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
    refine leaderLogs_sublog_of_update hP hst ?_ ?_
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
  · -- request_vote_reply: the crux
    intro xs p ys net st' ps' gd d t v hrvr hgd _hbody hP hreach hpkts hst
      _hps
    have hp_in : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hlogd : d.log = (net.nwState p.pDst).2.log := by
      rw [← hrvr]
      exact handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2 p.pSrc
        t v
    intro L t2 ll e h0 htyL hin he hterm
    replace htyL : (st' L).2.type = .Leader := htyL
    replace hin : (t2, ll) ∈ (st' h0).1.leaderLogs := hin
    replace hterm : e.eTerm = (st' L).2.currentTerm := hterm
    show e ∈ (st' L).2.log
    rw [hst L] at htyL hterm ⊢
    rw [hst h0] at hin
    rcases handleRequestVoteReply_RVR_spec p.pDst (net.nwState p.pDst).2
      p.pSrc t v hrvr with heqd | ⟨htyF, -, hlogF⟩ |
      ⟨hctC, hlogC, htrans | htys⟩
    · -- state untouched: only the ghost may have consed — but a cons
      -- requires a candidate that is now a leader, impossible when d = st
      have hin' : (t2, ll) ∈ (net.nwState h0).1.leaderLogs := by
        by_cases hhu : h0 = p.pDst
        · rw [hhu, update_same] at hin
          replace hin : (t2, ll) ∈ gd.leaderLogs := hin
          subst hgd
          rcases leaderLogs_update_elections_data_RVR hin with hold |
            ⟨hLd, hcand, -, -⟩
          · rw [hhu]
            exact hold
          · rw [hrvr, heqd] at hLd
            rw [hLd] at hcand
            exact nomatch hcand
        · rw [update_neq _ _ hhu] at hin
          exact hin
      by_cases hLu : L = p.pDst
      · rw [hLu, update_same] at htyL hterm ⊢
        replace htyL : d.type = .Leader := htyL
        replace hterm : e.eTerm = d.currentTerm := hterm
        rw [heqd] at htyL hterm ⊢
        exact hP p.pDst t2 ll e h0 htyL hin' he hterm
      · rw [update_neq _ _ hLu] at htyL hterm ⊢
        exact hP L t2 ll e h0 htyL hin' he hterm
    · -- stepped down to follower
      have hin' : (t2, ll) ∈ (net.nwState h0).1.leaderLogs := by
        by_cases hhu : h0 = p.pDst
        · rw [hhu, update_same] at hin
          replace hin : (t2, ll) ∈ gd.leaderLogs := hin
          subst hgd
          rcases leaderLogs_update_elections_data_RVR hin with hold |
            ⟨hLd, -, -, -⟩
          · rw [hhu]
            exact hold
          · rw [hrvr] at hLd
            rw [hLd] at htyF
            exact nomatch htyF
        · rw [update_neq _ _ hhu] at hin
          exact hin
      by_cases hLu : L = p.pDst
      · rw [hLu, update_same] at htyL
        replace htyL : d.type = .Leader := htyL
        rw [htyF] at htyL
        exact nomatch htyL
      · rw [update_neq _ _ hLu] at htyL hterm ⊢
        exact hP L t2 ll e h0 htyL hin' he hterm
    · -- the WIN: fresh leader at an unchanged term
      obtain ⟨hcand, htyLd, hv, hteq, hwon⟩ := htrans
      by_cases hLu : L = p.pDst
      · rw [hLu, update_same] at htyL hterm ⊢
        replace hterm : e.eTerm = d.currentTerm := hterm
        show e ∈ d.log
        by_cases hhu : h0 = p.pDst
        · -- own ghost: fresh snapshot is the log itself; an OLD snapshot
          -- at the current term contradicts term sanity
          rw [hhu, update_same] at hin
          replace hin : (t2, ll) ∈ gd.leaderLogs := hin
          subst hgd
          rcases leaderLogs_update_elections_data_RVR hin with hold |
            ⟨-, -, -, hll⟩
          · exfalso
            have hlt := leaderLogs_term_sanity_invariant net hreach p.pDst
              t2 ll e hold he
            have hle := leaderLogs_currentTerm_sanity_invariant net hreach
              p.pDst t2 ll hold
            rw [hctC] at hterm
            rw [hterm] at hlt
            exact absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl _)
          · rw [hll, hrvr] at he
            exact he
        · -- someone else's snapshot at the fresh leader's term: the
          -- consumed grant contradicts CandidateEntries
          rw [update_neq _ _ hhu] at hin
          exfalso
          have hce := leaderLogs_candidateEntries_invariant net hreach h0 e
            t2 ll hin he
          have het : e.eTerm = t := hterm.trans (hctC.trans hteq)
          refine absurd hcand (wonElection_candidateEntries_rvr
            (votes_correct_invariant net hreach)
            (cronies_correct_invariant net hreach) hce (q := p) hp_in
            ?_ ?_ hwon)
          · rw [_hbody, hv, het]
          · exact hteq.trans het.symm
      · -- another standing leader beside the fresh one
        rw [update_neq _ _ hLu] at htyL hterm ⊢
        by_cases hhu : h0 = p.pDst
        · rw [hhu, update_same] at hin
          replace hin : (t2, ll) ∈ gd.leaderLogs := hin
          subst hgd
          rcases leaderLogs_update_elections_data_RVR hin with hold |
            ⟨-, -, -, hll⟩
          · exact hP L t2 ll e h0 htyL (hhu ▸ hold) he hterm
          · rw [hll, hrvr, hlogd] at he
            exact lifted_leader_sublog_host net hreach L p.pDst e htyL he
              hterm
        · rw [update_neq _ _ hhu] at hin
          exact hP L t2 ll e h0 htyL hin he hterm
    · -- same term, type unchanged
      have hin' : (t2, ll) ∈ (net.nwState h0).1.leaderLogs := by
        by_cases hhu : h0 = p.pDst
        · rw [hhu, update_same] at hin
          replace hin : (t2, ll) ∈ gd.leaderLogs := hin
          subst hgd
          rcases leaderLogs_update_elections_data_RVR hin with hold |
            ⟨hLd, hcand, -, -⟩
          · rw [hhu]
            exact hold
          · rw [hrvr] at hLd
            rw [htys] at hLd
            rw [hLd] at hcand
            exact nomatch hcand
        · rw [update_neq _ _ hhu] at hin
          exact hin
      by_cases hLu : L = p.pDst
      · rw [hLu, update_same] at htyL hterm ⊢
        replace htyL : d.type = .Leader := htyL
        replace hterm : e.eTerm = d.currentTerm := hterm
        rw [htys] at htyL
        rw [hctC] at hterm
        show e ∈ d.log
        rw [hlogC]
        exact hP p.pDst t2 ll e h0 htyL hin' he hterm
      · rw [update_neq _ _ hLu] at htyL hterm ⊢
        exact hP L t2 ll e h0 htyL hin' he hterm
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨hct, -, hty, -, hlog, -⟩ := doLeader_spec d h hdl
    refine leaderLogs_sublog_of_update hP hst (by rw [hstate]) ?_
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
    refine leaderLogs_sublog_of_update hP hst (by rw [hstate]) ?_
    intro htyl
    rw [hty] at htyl
    refine ⟨?_, ?_, ?_⟩
    · rw [hlog, hstate]
    · rw [hct, hstate]
    · rw [hstate]
      exact htyl
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach L t ll e h htyL hin he hterm
    replace htyL : (net'.nwState L).2.type = .Leader := htyL
    replace hin : (t, ll) ∈ (net'.nwState h).1.leaderLogs := hin
    replace hterm : e.eTerm = (net'.nwState L).2.currentTerm := hterm
    show e ∈ (net'.nwState L).2.log
    rw [← hstates L] at htyL hterm ⊢
    rw [← hstates h] at hin
    exact hP L t ll e h htyL hin he hterm
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts
    refine leaderLogs_sublog_of_update hP hst (by rw [hstate]) ?_
    intro htyl
    rw [← hrb] at htyl
    exact nomatch htyl

end AppendEntriesChain

end Raft
end VerdiCompat
