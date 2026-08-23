import VerdiCompat.ElectionSafety

/-!
# The candidate_entries ring — entry to the leader-completeness lattice

Campaign Arc 3 unit 3 (design doc §3's "beyond" paragraph): the ring of
invariants `CandidateEntriesProof.v` rides —

- `cronies_term` (`Raft/CroniesTermInterface.v` /
  `RaftProofs/CroniesTermProof.v`): no crony list reaches past its
  node's current term (ghost layer);
- `no_entries_past_current_term` (`Raft/TermSanityInterface.v` /
  `RaftProofs/TermSanityProof.v`): no log entry or in-flight
  AppendEntries entry is from the future (BASE layer);
- `candidateEntries` (`Raft/RefinementCommonDefinitions.v:8-12`) and
  `CandidateEntries` (`Raft/CandidateEntriesInterface.v` /
  `RaftProofs/CandidateEntriesProof.v`): every entry — in a log or in
  flight — was created by a term's election winner.

Statements 1:1 against the cited sources @ a3375e8; proofs re-derived
through the ported principles.
-/

namespace VerdiCompat
namespace Raft

section CandidateEntriesRing
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params
local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-! ## cronies_term -/

/-- `CroniesTermInterface.v:9-12` (`cronies_term`). -/
def cronies_term (net : RefinedNet) : Prop :=
  ∀ (h h' : name (P := P)) (t : term),
    h ∈ (net.nwState h').1.cronies t → t ≤ (net.nwState h').2.currentTerm

/-- `CroniesTermProof.v:271-291` (`cronies_term_invariant`): no crony
list reaches past its node's current term. -/
theorem cronies_term_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      cronies_term net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    intro h h' t hin
    exact nomatch hin
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps
      h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hgd
      rw [(update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.1] at hin
      rw [(handleClientRequest_spec h (net.nwState h).2 client id c hcr).2.1]
      exact hP h0 h t hin
    · exact hP h0 h1 t
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hgd
      obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
      rcases update_elections_data_timeout_cronies_elim hto hin
        with hold | ⟨rfl, -, -⟩
      · have hle := hP h0 h t hold
        rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
        · rw [hct]
          exact hle
        · rw [hct]
          exact Nat.le_succ_of_le hle
      · exact Nat.le_refl _
    · exact hP h0 h1 t
  · -- append_entries
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      _hreach _hpkts hst _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hgd
      rw [(update_elections_data_appendEntries_ghost p.pDst (net.nwState p.pDst)
        t0 n0 pli plt es ci).2.2.1] at hin
      have hle := hP h0 p.pDst t hin
      obtain ⟨-, hcases, -, -⟩ :=
        handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
      rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
      · rw [hct]
        exact hle
      · exact Nat.le_trans hle (Nat.le_of_lt hct)
    · exact hP h0 h1 t
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach
      _hpkts hst _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hgd
      have hle := hP h0 p.pDst t hin
      obtain ⟨-, hcases, -⟩ :=
        handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es res haer
      rcases hcases with ⟨hct, -, -⟩ | ⟨hct, -, -⟩
      · rw [hct]
        exact hle
      · exact Nat.le_trans hle (Nat.le_of_lt hct)
    · exact hP h0 h1 t
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP _hreach
      _hpkts hst _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hgd
      rw [(update_elections_data_requestVote_cronies p.pDst p.pSrc t0 p.pSrc
        lli llt (net.nwState p.pDst)).1] at hin
      obtain ⟨-, hle, -, -⟩ :=
        handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
      exact Nat.le_trans (hP h0 p.pDst t hin) hle
    · exact hP h0 h1 t
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP _hreach _hpkts hst
      _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hgd
      subst hrvr
      obtain ⟨hcases, -, -, -⟩ :=
        handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v rfl
      rcases update_elections_data_requestVoteReply_cronies_elim hin
        with hold | ⟨rfl, -, -⟩
      · have hle := hP h0 p.pDst t hold
        rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
        · rw [hct]
          exact hle
        · exact Nat.le_trans hle (Nat.le_of_lt hct)
      · exact Nat.le_refl _
    · exact hP h0 h1 t
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      rw [(doLeader_spec d h hdl).1]
      have := hP h0 h t
      rw [hstate] at this
      exact this hin
    · exact hP h0 h1 t
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps h0 h1 t
    show h0 ∈ (st' h1).1.cronies t → t ≤ (st' h1).2.currentTerm
    rw [hst h1]
    unfold update
    split
    · intro hin
      obtain ⟨-, -, hct, -, -, -⟩ := doGenericServer_spec h d hgs
      rw [hct]
      have := hP h0 h t
      rw [hstate] at this
      exact this hin
    · exact hP h0 h1 t
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h0 h1 t
    rw [← hstates h1]
    exact hP h0 h1 t
  · -- reboot
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts h0 h1 t
    rw [hst h1]
    unfold update
    split
    · intro hin
      subst hrb
      show t ≤ (reboot d).currentTerm
      have := hP h0 h t
      rw [hstate] at this
      exact this hin
    · exact hP h0 h1 t

/-! ## term_sanity (BASE layer) -/

/-- `TermSanityInterface.v:9-12` (`no_entries_past_current_term_host`). -/
def no_entries_past_current_term_host (net : RaftNet) : Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (net.nwState h).log → e.eTerm ≤ (net.nwState h).currentTerm

/-- `TermSanityInterface.v:14-18` (`no_entries_past_current_term_nw`). -/
def no_entries_past_current_term_nw (net : RaftNet) : Prop :=
  ∀ (e : entry (P := P))
    (p : Packet (raft_base_params (P := P)) raft_multi_params)
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    e ∈ es → e.eTerm ≤ t

/-- `TermSanityInterface.v:20-22` (`no_entries_past_current_term`). -/
def no_entries_past_current_term (net : RaftNet) : Prop :=
  no_entries_past_current_term_host net ∧ no_entries_past_current_term_nw net

/-- `TermSanityProof.v:373-395` (`no_entries_past_current_term_invariant`):
no log entry or in-flight entry is from the future — proved through the
BASE `raft_net_invariant`. -/
theorem no_entries_past_current_term_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      no_entries_past_current_term net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_⟩
    · intro h e he
      exact nomatch he
    · intro e p t lid pli plt es ci hp hbody he
      exact nomatch hp
  · -- client_request: a new entry carries the current term; no packets
    intro h net st' ps' out d l client id c hcr hP _hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, hct, -, -, hl⟩ := handleClientRequest_spec h (net.nwState h) client id c hcr
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hct]
        rcases handleClientRequest_log h (net.nwState h) client id c hcr e he
          with hold | ⟨heq, -⟩
        · exact hhost h e hold
        · exact Nat.le_of_eq heq
      · exact hhost h0 e
    · intro e p t lid pli plt es ci hp hbody he
      show e.eTerm ≤ t
      rcases hps p hp with hold | hnew
      · exact hnw e p t lid pli plt es ci hold hbody he
      · rw [hl] at hnew
        exact nomatch hnew
  · -- timeout: log unchanged, term grows; only RequestVote sent
    intro net h st' ps' out d l hto hP _hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, hcases, hmsg⟩ := handleTimeout_spec h (net.nwState h) hto
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        have hle := hhost h e he
        rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
        · rw [hct]
          exact hle
        · rw [hct]
          exact Nat.le_succ_of_le hle
      · exact hhost h0 e
    · intro e p t lid pli plt es ci hp hbody he
      show e.eTerm ≤ t
      rcases hps p hp with hold | hnew
      · exact hnw e p t lid pli plt es ci hold hbody he
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', cid, lli, llt, heqm⟩ := hmsg q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = q.2 from rfl, heqm] at hbody
        exact nomatch hbody
  · -- append_entries: accepted entries are bounded by the message term,
    -- which the nw invariant already bounds
    intro xs p ys net st' ps' d m t0 n0 pli plt es ci hae _hbody hP _hreach
      hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, hcases, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst) t0 n0 pli plt es ci hae
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rcases handleAppendEntries_log p.pDst (net.nwState p.pDst) t0 n0 pli plt
          es ci hae e he with hold | ⟨hes, hct⟩
        · have hle := hhost p.pDst e hold
          rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
          · rw [hct]
            exact hle
          · exact Nat.le_trans hle (Nat.le_of_lt hct)
        · rw [hct]
          exact hnw e p t0 n0 pli plt es ci hpmem _hbody hes
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      show e.eTerm ≤ t
      rcases hps p' hp' with hold | hnew
      · exact hnw e p' t lid pli' plt' es0 ci' (hpkts ▸ mem_of_mem_remove_middle hold)
          hbody' he
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
  · -- append_entries_reply: log unchanged, term grows, nothing sent
    intro xs p ys net st' ps' d m t0 es res haer _hbody hP _hreach hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, hcases, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst) p.pSrc t0 es res haer
    have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst) p.pSrc
      t0 es res haer
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        have hle := hhost p.pDst e he
        rcases hcases with ⟨hct, -, -⟩ | ⟨hct, -, -⟩
        · rw [hct]
          exact hle
        · exact Nat.le_trans hle (Nat.le_of_lt hct)
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      show e.eTerm ≤ t
      rcases hps p' hp' with hold | hnew
      · exact hnw e p' t lid pli' plt' es0 ci' (hpkts ▸ mem_of_mem_remove_middle hold)
          hbody' he
      · rw [hl] at hnew
        exact nomatch hnew
  · -- request_vote: log unchanged, term grows; reply is a RequestVoteReply
    intro xs p ys net st' ps' d m t0 cid lli llt hrv _hbody hP _hreach hpkts
      hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, hle, -, -⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst) t0 p.pSrc lli llt hrv
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst) t0 p.pSrc
      lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst (net.nwState p.pDst)
      t0 p.pSrc lli llt hrv
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        exact Nat.le_trans (hhost p.pDst e he) hle
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      show e.eTerm ≤ t
      rcases hps p' hp' with hold | hnew
      · exact hnw e p' t lid pli' plt' es0 ci' (hpkts ▸ mem_of_mem_remove_middle hold)
          hbody' he
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
  · -- request_vote_reply: log unchanged, term grows, packets shrink
    intro xs p ys net st' ps' d t0 v hrvr _hbody hP _hreach hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    subst hrvr
    obtain ⟨hcases, -, -, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst) p.pSrc t0 v rfl
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst) p.pSrc t0 v
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        have hle := hhost p.pDst e he
        rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
        · rw [hct]
          exact hle
        · exact Nat.le_trans hle (Nat.le_of_lt hct)
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      exact hnw e p' t lid pli' plt' es0 ci'
        (hpkts ▸ mem_of_mem_remove_middle (hps p' hp')) hbody' he
  · -- do_leader: sent entries come from the sender's own bounded log
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hct, -, -, -, hlog, -⟩ := doLeader_spec d h hdl
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        rw [hct]
        have := hhost h e
        rw [hstate] at this
        exact this he
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      show e.eTerm ≤ t
      rcases hps p' hp' with hold | hnew
      · exact hnw e p' t lid pli' plt' es0 ci' hold hbody' he
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨pi, pt, ci0, es1, heqm, hes⟩ := doLeader_messages d h hdl q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_base_params (P := P)) raft_multi_params).pBody
          = q.2 from rfl, heqm] at hbody'
        injection hbody' with h1 h2 h3 h4 h5 h6
        subst h1
        subst h5
        have := hhost h e
        rw [hstate] at this
        exact this (hes e he)
  · -- do_generic_server: log/term unchanged, nothing sent
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, -, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).log → e.eTerm ≤ (st' h0).currentTerm
      rw [hst h0]
      unfold update
      split
      · intro he
        rw [hlog] at he
        rw [hct]
        have := hhost h e
        rw [hstate] at this
        exact this he
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      show e.eTerm ≤ t
      rcases hps p' hp' with hold | hnew
      · exact hnw e p' t lid pli' plt' es0 ci' hold hbody' he
      · rw [hms] at hnew
        exact nomatch hnew
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    obtain ⟨hhost, hnw⟩ := hP
    refine ⟨?_, ?_⟩
    · intro h0 e
      rw [← hstates h0]
      exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      exact hnw e p' t lid pli' plt' es0 ci' (hpkts p' hp') hbody' he
  · -- reboot: log and term survive; packets unchanged
    intro net net' d h d' hrb hP _hreach hstate hst hpkts
    obtain ⟨hhost, hnw⟩ := hP
    subst hrb
    refine ⟨?_, ?_⟩
    · intro h0 e
      rw [hst h0]
      unfold update
      split
      · intro he
        show e.eTerm ≤ (reboot d).currentTerm
        have := hhost h e
        rw [hstate] at this
        exact this he
      · exact hhost h0 e
    · intro e p' t lid pli' plt' es0 ci' hp' hbody' he
      rw [← hpkts] at hp'
      exact hnw e p' t lid pli' plt' es0 ci' hp' hbody' he

/-! ## candidateEntries (`RefinementCommonDefinitions.v` /
`RefinementCommonTheorems.v` / `CandidateEntriesProof.v`) -/

omit O R in
theorem serverType_cases {s : serverType} (hf : s ≠ .Follower)
    (hc : s ≠ .Candidate) : s = .Leader := by
  cases s
  · exact absurd rfl hf
  · exact absurd rfl hc
  · rfl

/-- `RefinementCommonDefinitions.v:8-12` (`candidateEntries`): the
entry's term had an election winner who is no longer campaigning at that
term. -/
def candidateEntries (e : entry (P := P))
    (sigma : name (P := P) → electionsData (P := P) × raft_data (P := P)) :
    Prop :=
  ∃ h : name (P := P),
    wonElection (dedup ((sigma h).1.cronies e.eTerm)) = true ∧
    ((sigma h).2.currentTerm = e.eTerm → (sigma h).2.type ≠ .Candidate)

omit O in
/-- `RefinementCommonTheorems.v:97-108` (`candidateEntries_ext`). -/
theorem candidateEntries_ext {e : entry (P := P)}
    {sigma sigma' : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    (hext : ∀ h, sigma' h = sigma h) (hce : candidateEntries e sigma) :
    candidateEntries e sigma' := by
  obtain ⟨x, hw, himp⟩ := hce
  refine ⟨x, ?_, ?_⟩
  · rw [hext x]
    exact hw
  · rw [hext x]
    exact himp

omit O in
/-- `RefinementCommonTheorems.v:110-123` (`candidateEntries_same`),
specialized to the one-node updates every obligation performs. -/
theorem candidateEntries_update_same {e : entry (P := P)}
    {sigma : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    {h : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hcr : gd.cronies = (sigma h).1.cronies)
    (hct : d.currentTerm = (sigma h).2.currentTerm)
    (hty : d.type = (sigma h).2.type)
    (hce : candidateEntries e sigma) :
    candidateEntries e (update sigma h (gd, d)) := by
  obtain ⟨x, hw, himp⟩ := hce
  by_cases hxh : x = h
  · subst hxh
    refine ⟨x, ?_, ?_⟩
    · rw [update_same]
      show wonElection (dedup (gd.cronies e.eTerm)) = true
      rw [hcr]
      exact hw
    · rw [update_same]
      show d.currentTerm = e.eTerm → d.type ≠ serverType.Candidate
      rw [hct, hty]
      exact himp
  · refine ⟨x, ?_, ?_⟩
    · rw [update_neq _ _ hxh]
      exact hw
    · rw [update_neq _ _ hxh]
      exact himp

omit O in
/-- `wonElection_no_dup_in` (`CommonTheorems.v:841-846`). -/
theorem wonElection_no_dup_in {l1 l2 : List (name (P := P))}
    (hw : wonElection l1 = true) (hnd : l1.Nodup)
    (hsub : ∀ x ∈ l1, x ∈ l2) : wonElection l2 = true := by
  unfold wonElection at *
  simp at hw ⊢
  exact Nat.le_trans hw (nodup_subset_length hnd hsub)

omit O in
/-- `wonElection_exists_voter` (`CommonTheorems.v:853-857`). -/
theorem wonElection_exists_voter {l : List (name (P := P))}
    (hw : wonElection l = true) : ∃ x, x ∈ l := by
  unfold wonElection at hw
  simp at hw
  cases l with
  | nil => simp at hw
  | cons a l => exact ⟨a, List.mem_cons_self ..⟩

/-- `won_election_cronies` (`RefinementCommonTheorems.v:125-136`): a
leader's cronies at its current term form a winning set. -/
theorem won_election_cronies {net : RefinedNet} (hcc : cronies_correct net)
    {h : name (P := P)} (hty : (net.nwState h).2.type = .Leader) :
    wonElection (dedup
      ((net.nwState h).1.cronies (net.nwState h).2.currentTerm)) = true := by
  obtain ⟨hvrc, -, -, hvrl⟩ := hcc
  refine wonElection_no_dup_in (hvrl h hty) (nodup_dedup _) ?_
  intro x hx
  exact mem_dedup_of_mem (hvrc h x (mem_of_mem_dedup hx) (Or.inl hty))

/-- `CandidateEntriesInterface.v:10-12` (`candidateEntries_host_invariant`). -/
def candidateEntries_host_invariant
    (sigma : name (P := P) → electionsData (P := P) × raft_data (P := P)) :
    Prop :=
  ∀ (h : name (P := P)) (e : entry (P := P)),
    e ∈ (sigma h).2.log → candidateEntries e sigma

/-- `CandidateEntriesInterface.v:14-22` (`candidateEntries_nw_invariant`). -/
def candidateEntries_nw_invariant (net : RefinedNet) : Prop :=
  ∀ (p : Packet (raft_refined_base_params (P := P)) raft_refined_multi_params)
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex),
    p ∈ net.nwPackets → p.pBody = .AppendEntries t lid pli plt es ci →
    ∀ e ∈ es, candidateEntries e net.nwState

/-- `CandidateEntriesInterface.v:24` (`CandidateEntries`). -/
def CandidateEntries (net : RefinedNet) : Prop :=
  candidateEntries_host_invariant net.nwState ∧ candidateEntries_nw_invariant net

/-! ## candidateEntriesTerm — the term-level twin of `candidateEntries`
(`RefinementCommonDefinitions.v:14-18`), and its preserves set
(`RaftProofs/PrevLogCandidateEntriesTermProof.v`). Proofs mirror unit
3's entry-level `*_preserves_candidateEntries` (CandidateEntries.lean)
with `t'` in place of `e.eTerm`; `candidateEntries e σ` is
definitionally `candidateEntriesTerm e.eTerm σ` (the `candidateEntries_term`
bridge). Relocated here from SafetyLeaves.lean at the unit-16 consolidation:
the entry-level `*_preserves_candidateEntries` set below is DERIVED
from these (the `candidateEntries_term` bridge is definitional). -/

/-- `RefinementCommonDefinitions.v:14-18` (`candidateEntriesTerm`):
the TERM had an election winner who is no longer campaigning at it. -/
def candidateEntriesTerm (t : term)
    (sigma : name (P := P) → electionsData (P := P) × raft_data (P := P)) :
    Prop :=
  ∃ h : name (P := P),
    wonElection (dedup ((sigma h).1.cronies t)) = true ∧
    ((sigma h).2.currentTerm = t → (sigma h).2.type ≠ .Candidate)

omit O in
/-- The definitional bridge: an entry's `candidateEntries` witness IS a
`candidateEntriesTerm` witness for its term. -/
theorem candidateEntries_term {e : entry (P := P)}
    {sigma : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    (h : candidateEntries e sigma) : candidateEntriesTerm e.eTerm sigma := h

omit O in
/-- `PrevLogCandidateEntriesTermProof.v:29-37` (`candidateEntriesTerm_ext`). -/
theorem candidateEntriesTerm_ext {t' : term}
    {sigma sigma' : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    (hext : ∀ h, sigma' h = sigma h) (hce : candidateEntriesTerm t' sigma) :
    candidateEntriesTerm t' sigma' := by
  obtain ⟨x, hw, himp⟩ := hce
  refine ⟨x, ?_, ?_⟩
  · rw [hext x]
    exact hw
  · rw [hext x]
    exact himp

omit O in
/-- `PrevLogCandidateEntriesTermProof.v:39-51` (`candidateEntriesTerm_same`),
specialized to the one-node updates (unit 3's `_update_same` shape). -/
theorem candidateEntriesTerm_update_same {t' : term}
    {sigma : name (P := P) → electionsData (P := P) × raft_data (P := P)}
    {h : name (P := P)} {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hcr : gd.cronies = (sigma h).1.cronies)
    (hct : d.currentTerm = (sigma h).2.currentTerm)
    (hty : d.type = (sigma h).2.type)
    (hce : candidateEntriesTerm t' sigma) :
    candidateEntriesTerm t' (update sigma h (gd, d)) := by
  obtain ⟨x, hw, himp⟩ := hce
  by_cases hxh : x = h
  · subst hxh
    refine ⟨x, ?_, ?_⟩
    · rw [update_same]
      show wonElection (dedup (gd.cronies t')) = true
      rw [hcr]
      exact hw
    · rw [update_same]
      show d.currentTerm = t' → d.type ≠ serverType.Candidate
      rw [hct, hty]
      exact himp
  · refine ⟨x, ?_, ?_⟩
    · rw [update_neq _ _ hxh]
      exact hw
    · rw [update_neq _ _ hxh]
      exact himp

/-- `PrevLogCandidateEntriesTermProof.v:83-118` (upstream's misnamed
`handleClientRequest_preserves_candidateEntriesTerm` — it is the
TIMEOUT preservation): a heartbeat changes nothing; a fresh candidacy
only touches the NEW term, where `cronies_term` says no winner can yet
exist. -/
theorem handleTimeout_preserves_candidateEntriesTerm {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {h : name (P := P)} {out d l} {t' : term}
    (hto : handleTimeout h (net.nwState h).2 = (out, d, l))
    (hce : candidateEntriesTerm t' net.nwState) :
    candidateEntriesTerm t' (update net.nwState h
      (update_elections_data_timeout h (net.nwState h), d)) := by
  by_cases hL : (net.nwState h).2.type = .Leader
  · obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
    rcases hcases with ⟨hct, hty, -, -⟩ | ⟨-, -, -, -, hnl⟩
    · exact candidateEntriesTerm_update_same
        (update_elections_data_timeout_cronies_leader h (net.nwState h) hL)
        hct hty hce
    · exact absurd hL hnl
  · obtain ⟨hct, hty, -, -⟩ := handleTimeout_not_leader h (net.nwState h).2
      hto hL
    obtain ⟨x, hw, himp⟩ := hce
    by_cases hxh : x = h
    · subst hxh
      have hnonew : t' ≠ d.currentTerm := by
        intro heq
        obtain ⟨voter, hv⟩ := wonElection_exists_voter hw
        have hb := cronies_term_invariant net hreach voter x t'
          (mem_of_mem_dedup hv)
        rw [heq, hct] at hb
        exact Nat.not_succ_le_self _ hb
      refine ⟨x, ?_, ?_⟩
      · rw [update_same]
        show wonElection (dedup
          ((update_elections_data_timeout x (net.nwState x)).cronies t'))
          = true
        rcases update_elections_data_timeout_cronies_cases hto t'
          with hsame | ⟨heq, -⟩
        · rw [hsame]
          exact hw
        · exact absurd heq hnonew
      · rw [update_same]
        show d.currentTerm = t' → d.type ≠ serverType.Candidate
        intro hprem
        exact absurd hprem.symm hnonew
    · refine ⟨x, ?_, ?_⟩
      · rw [update_neq _ _ hxh]
        exact hw
      · rw [update_neq _ _ hxh]
        exact himp

/-- `PrevLogCandidateEntriesTermProof.v:134-155`
(`handleAppendEntries_preserves_candidateEntriesTerm`). -/
theorem handleAppendEntries_preserves_candidateEntriesTerm {net : RefinedNet}
    {h : name (P := P)} {t0 : term} {n0 : name (P := P)} {pli : logIndex}
    {plt : term} {es : List (entry (P := P))} {ci : logIndex} {d m}
    {t' : term}
    (hae : handleAppendEntries h (net.nwState h).2 t0 n0 pli plt es ci
      = (d, m))
    (hce : candidateEntriesTerm t' net.nwState) :
    candidateEntriesTerm t' (update net.nwState h
      (update_elections_data_appendEntries h (net.nwState h) t0 n0 pli plt
        es ci, d)) := by
  obtain ⟨x, hw, himp⟩ := hce
  have hgc := (update_elections_data_appendEntries_ghost h (net.nwState h)
    t0 n0 pli plt es ci).2.2.1
  by_cases hxh : x = h
  · subst hxh
    refine ⟨x, ?_, ?_⟩
    · rw [update_same]
      show wonElection (dedup
        ((update_elections_data_appendEntries x (net.nwState x) t0 n0 pli
          plt es ci).cronies t')) = true
      rw [hgc]
      exact hw
    · rw [update_same]
      show d.currentTerm = t' → d.type ≠ serverType.Candidate
      by_cases hf : d.type = .Follower
      · intro _ hcand
        rw [hf] at hcand
        exact nomatch hcand
      · have hrej := handleAppendEntries_reject_of_not_follower x
          (net.nwState x).2 t0 n0 pli plt es ci hae hf
        rw [hrej]
        exact himp
  · refine ⟨x, ?_, ?_⟩
    · rw [update_neq _ _ hxh]
      exact hw
    · rw [update_neq _ _ hxh]
      exact himp

/-- `PrevLogCandidateEntriesTermProof.v:165-180`
(`handleAppendEntriesReply_preserves_candidateEntriesTerm`). -/
theorem handleAppendEntriesReply_preserves_candidateEntriesTerm
    {net : RefinedNet}
    {h src : name (P := P)} {t0 : term} {es : List (entry (P := P))}
    {r : Bool} {d ms} {t' : term}
    (haer : handleAppendEntriesReply h (net.nwState h).2 src t0 es r
      = (d, ms))
    (hce : candidateEntriesTerm t' net.nwState) :
    candidateEntriesTerm t' (update net.nwState h ((net.nwState h).1, d)) := by
  obtain ⟨x, hw, himp⟩ := hce
  obtain ⟨-, hcases, -⟩ := handleAppendEntriesReply_spec h (net.nwState h).2
    src t0 es r haer
  by_cases hxh : x = h
  · subst hxh
    refine ⟨x, ?_, ?_⟩
    · rw [update_same]
      exact hw
    · rw [update_same]
      show d.currentTerm = t' → d.type ≠ serverType.Candidate
      rcases hcases with ⟨hct, -, hty⟩ | ⟨-, -, hty⟩
      · rw [hct, hty]
        exact himp
      · rw [hty]
        exact fun _ hcand => nomatch hcand
  · refine ⟨x, ?_, ?_⟩
    · rw [update_neq _ _ hxh]
      exact hw
    · rw [update_neq _ _ hxh]
      exact himp

/-- `PrevLogCandidateEntriesTermProof.v:210-255`
(`handleRequestVote_preserves_candidateEntriesTerm`, via the
`advanceCurrentTerm_same_or_type_follower` argument folded into the
lane's `handleRequestVote_spec`). -/
theorem handleRequestVote_preserves_candidateEntriesTerm {net : RefinedNet}
    {h src : name (P := P)} {t0 : term} {lli : logIndex} {llt : term} {d m}
    {t' : term}
    (hrv : handleRequestVote h (net.nwState h).2 t0 src lli llt = (d, m))
    (hce : candidateEntriesTerm t' net.nwState) :
    candidateEntriesTerm t' (update net.nwState h
      (update_elections_data_requestVote h src t0 src lli llt
        (net.nwState h), d)) := by
  obtain ⟨x, hw, himp⟩ := hce
  obtain ⟨-, -, htycase, -⟩ := handleRequestVote_spec h (net.nwState h).2
    t0 src lli llt hrv
  have hgc := (update_elections_data_requestVote_cronies h src t0 src lli
    llt (net.nwState h)).1
  by_cases hxh : x = h
  · subst hxh
    refine ⟨x, ?_, ?_⟩
    · rw [update_same]
      show wonElection (dedup
        ((update_elections_data_requestVote x src t0 src lli llt
          (net.nwState x)).cronies t')) = true
      rw [hgc]
      exact hw
    · rw [update_same]
      show d.currentTerm = t' → d.type ≠ serverType.Candidate
      rcases htycase with ⟨hct, hty⟩ | hty
      · rw [hct, hty]
        exact himp
      · rw [hty]
        exact fun _ hcand => nomatch hcand
  · refine ⟨x, ?_, ?_⟩
    · rw [update_neq _ _ hxh]
      exact hw
    · rw [update_neq _ _ hxh]
      exact himp

/-- `PrevLogCandidateEntriesTermProof.v:257-296`
(`handleRequestVoteReply_preserves_candidateEntriesTerm`) — the one
case that leans on `cronies_correct`, exactly unit 3's entry-level
argument. -/
theorem handleRequestVoteReply_preserves_candidateEntriesTerm
    {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {h src : name (P := P)} {t0 : term} {v : Bool} {t' : term}
    (hce : candidateEntriesTerm t' net.nwState) :
    candidateEntriesTerm t' (update net.nwState h
      (update_elections_data_requestVoteReply h src t0 v (net.nwState h),
       handleRequestVoteReply h (net.nwState h).2 src t0 v)) := by
  obtain ⟨x, hw, himp⟩ := hce
  obtain ⟨-, -, htycand, htylead⟩ :=
    handleRequestVoteReply_spec h (net.nwState h).2 src t0 v rfl
  by_cases hxh : x = h
  · subst hxh
    refine ⟨x, ?_, ?_⟩
    · rw [update_same]
      show wonElection (dedup
        ((update_elections_data_requestVoteReply x src t0 v
          (net.nwState x)).cronies t')) = true
      rcases update_elections_data_requestVoteReply_cronies_cases x src t0 v
        (net.nwState x) t' with hsame | ⟨heqt, hnewc, htynf⟩
      · rw [hsame]
        exact hw
      · rw [hnewc]
        by_cases hc : (handleRequestVoteReply x (net.nwState x).2 src t0
            v).type = .Candidate
        · obtain ⟨hstc, hcteq⟩ := htycand hc
          exact absurd hstc (himp (hcteq.symm.trans heqt.symm))
        · have hl := serverType_cases htynf hc
          rcases htylead hl with heqst | ⟨-, hwon, -⟩
          · have hvrl := (cronies_correct_invariant net hreach).2.2.2 x
              (by rw [← heqst]; exact hl)
            rw [heqst]
            exact hvrl
          · exact hwon
    · rw [update_same]
      show (handleRequestVoteReply x (net.nwState x).2 src t0 v).currentTerm
          = t' →
        (handleRequestVoteReply x (net.nwState x).2 src t0 v).type
          ≠ serverType.Candidate
      intro hprem hcand
      obtain ⟨hstc, hcteq⟩ := htycand hcand
      exact absurd hstc (himp (hcteq.symm.trans hprem))
  · refine ⟨x, ?_, ?_⟩
    · rw [update_neq _ _ hxh]
      exact hw
    · rw [update_neq _ _ hxh]
      exact himp


/-- `CandidateEntriesProof.v:117-163`
(`handleTimeout_preserves_candidateEntries`): a timeout preserves the
witness — a heartbeat changes nothing; a fresh candidacy only touches
the NEW term, where `cronies_term` says no winner can yet exist. -/
theorem handleTimeout_preserves_candidateEntries {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {h : name (P := P)} {out d l} {e : entry (P := P)}
    (hto : handleTimeout h (net.nwState h).2 = (out, d, l))
    (hce : candidateEntries e net.nwState) :
    candidateEntries e (update net.nwState h
      (update_elections_data_timeout h (net.nwState h), d)) :=
  handleTimeout_preserves_candidateEntriesTerm hreach hto hce

/-- `CandidateEntriesProof.v:199-224`
(`handleAppendEntries_preserves_candidate_entries`). -/
theorem handleAppendEntries_preserves_candidateEntries {net : RefinedNet}
    {h : name (P := P)} {t0 : term} {n0 : name (P := P)} {pli : logIndex}
    {plt : term} {es : List (entry (P := P))} {ci : logIndex} {d m}
    {e : entry (P := P)}
    (hae : handleAppendEntries h (net.nwState h).2 t0 n0 pli plt es ci = (d, m))
    (hce : candidateEntries e net.nwState) :
    candidateEntries e (update net.nwState h
      (update_elections_data_appendEntries h (net.nwState h) t0 n0 pli plt es ci,
       d)) :=
  handleAppendEntries_preserves_candidateEntriesTerm hae hce

/-- `CandidateEntriesProof.v:284-300`
(`handleAppendEntriesReply_preserves_candidate_entries`). -/
theorem handleAppendEntriesReply_preserves_candidateEntries {net : RefinedNet}
    {h src : name (P := P)} {t0 : term} {es : List (entry (P := P))} {r : Bool}
    {d ms} {e : entry (P := P)}
    (haer : handleAppendEntriesReply h (net.nwState h).2 src t0 es r = (d, ms))
    (hce : candidateEntries e net.nwState) :
    candidateEntries e (update net.nwState h ((net.nwState h).1, d)) :=
  handleAppendEntriesReply_preserves_candidateEntriesTerm haer hce

/-- `CandidateEntriesProof.v:377-410`
(`handleRequestVote_preserves_candidateEntries`). -/
theorem handleRequestVote_preserves_candidateEntries {net : RefinedNet}
    {h src : name (P := P)} {t0 : term} {lli : logIndex} {llt : term} {d m}
    {e : entry (P := P)}
    (hrv : handleRequestVote h (net.nwState h).2 t0 src lli llt = (d, m))
    (hce : candidateEntries e net.nwState) :
    candidateEntries e (update net.nwState h
      (update_elections_data_requestVote h src t0 src lli llt (net.nwState h),
       d)) :=
  handleRequestVote_preserves_candidateEntriesTerm hrv hce

/-- `RefinementCommonTheorems.v:138-176`
(`handleRequestVoteReply_preserves_candidate_entries`) — the one case
that leans on `cronies_correct`: an election win snapshots a winning
crony set. -/
theorem handleRequestVoteReply_preserves_candidateEntries {net : RefinedNet}
    (hreach : refined_raft_intermediate_reachable (P := P) net)
    {h src : name (P := P)} {t0 : term} {v : Bool} {e : entry (P := P)}
    (hce : candidateEntries e net.nwState) :
    candidateEntries e (update net.nwState h
      (update_elections_data_requestVoteReply h src t0 v (net.nwState h),
       handleRequestVoteReply h (net.nwState h).2 src t0 v)) :=
  handleRequestVoteReply_preserves_candidateEntriesTerm hreach hce

/-- `CandidateEntriesProof.v:642-663` (`candidate_entries_invariant`):
every entry — in a log or in flight — was created under an election
winner of its term. -/
theorem candidate_entries_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      CandidateEntries net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_⟩
    · intro h e he
      exact nomatch he
    · intro p t lid pli plt es ci hp hbody e he
      exact nomatch hp
  · -- client_request: the new entry's witness is the leader itself
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hty, hct, -, -, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    have hgc : gd.cronies = (net.nwState h).1.cronies := by
      rw [hgd]
      exact (update_elections_data_client_request_ghost h (net.nwState h)
        client id c).2.2.1
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState h (gd, d)) :=
      fun e hce => candidateEntries_update_same hgc hct hty hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rcases handleClientRequest_log h (net.nwState h).2 client id c hcr e he
          with hold | ⟨heTerm, hLeader⟩
        · exact candidateEntries_ext hst (hpres e (hhost h e hold))
        · refine candidateEntries_ext hst ⟨h, ?_, ?_⟩
          · rw [update_same]
            show wonElection (dedup (gd.cronies e.eTerm)) = true
            rw [hgc, heTerm]
            exact won_election_cronies (cronies_correct_invariant net hreach)
              hLeader
          · rw [update_same]
            show d.currentTerm = e.eTerm → d.type ≠ serverType.Candidate
            intro _ hcand
            rw [hty, hLeader] at hcand
            exact nomatch hcand
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli plt es ci hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli plt es ci hold hbody' e he))
      · rw [hl] at hnew
        exact nomatch hnew
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP hreach hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, -, hmsg⟩ := handleTimeout_spec h (net.nwState h).2 hto
    subst hgd
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState h
          (update_elections_data_timeout h (net.nwState h), d)) :=
      fun e hce => handleTimeout_preserves_candidateEntries hreach hto hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rw [show ((update_elections_data_timeout h (net.nwState h), d) :
            electionsData (P := P) × raft_data (P := P)).2.log = d.log from rfl,
          hlog] at he
        exact candidateEntries_ext hst (hpres e (hhost h e he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli plt es ci hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli plt es ci hold hbody' e he))
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', cid, lli, llt, heqm⟩ := hmsg q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = q.2 from rfl, heqm] at hbody'
        exact nomatch hbody'
  · -- append_entries: incoming entries were already covered in flight
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP
      hreach hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
    subst hgd
    have hpmem : p ∈ net.nwPackets := by
      rw [hpkts]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState p.pDst
          (update_elections_data_appendEntries p.pDst (net.nwState p.pDst)
            t0 n0 pli plt es ci, d)) :=
      fun e hce => handleAppendEntries_preserves_candidateEntries hae hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rcases handleAppendEntries_log p.pDst (net.nwState p.pDst).2 t0 n0 pli
          plt es ci hae e he with hold | ⟨hes, -⟩
        · exact candidateEntries_ext hst (hpres e (hhost p.pDst e hold))
        · exact candidateEntries_ext hst
            (hpres e (hnw p t0 n0 pli plt es ci hpmem _hbody e hes))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli' plt' es0 ci'
            (hpkts ▸ mem_of_mem_remove_middle hold) hbody' e he))
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach hpkts
      hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨-, -, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es res haer
    have hlog := handleAppendEntriesReply_log p.pDst (net.nwState p.pDst).2 p.pSrc
      t0 es res haer
    subst hgd
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState p.pDst ((net.nwState p.pDst).1, d)) :=
      fun e hce => handleAppendEntriesReply_preserves_candidateEntries haer hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rw [show (((net.nwState p.pDst).1, d) :
            electionsData (P := P) × raft_data (P := P)).2.log = d.log from rfl,
          hlog] at he
        exact candidateEntries_ext hst (hpres e (hhost p.pDst e he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli' plt' es0 ci'
            (hpkts ▸ mem_of_mem_remove_middle hold) hbody' e he))
      · rw [hl] at hnew
        exact nomatch hnew
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    have hlog := handleRequestVote_log p.pDst (net.nwState p.pDst).2 t0 p.pSrc
      lli llt hrv
    obtain ⟨t', v, hm⟩ := handleRequestVote_reply_shape p.pDst
      (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
    subst hgd
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState p.pDst
          (update_elections_data_requestVote p.pDst p.pSrc t0 p.pSrc lli llt
            (net.nwState p.pDst), d)) :=
      fun e hce => handleRequestVote_preserves_candidateEntries hrv hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rw [show ((update_elections_data_requestVote p.pDst p.pSrc t0 p.pSrc lli
              llt (net.nwState p.pDst), d) :
            electionsData (P := P) × raft_data (P := P)).2.log = d.log from rfl,
          hlog] at he
        exact candidateEntries_ext hst (hpres e (hhost p.pDst e he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli' plt' es0 ci'
            (hpkts ▸ mem_of_mem_remove_middle hold) hbody' e he))
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP hreach hpkts hst hps
    obtain ⟨hhost, hnw⟩ := hP
    subst hgd
    subst hrvr
    have hlog := handleRequestVoteReply_log p.pDst (net.nwState p.pDst).2 p.pSrc t0 v
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState p.pDst
          (update_elections_data_requestVoteReply p.pDst p.pSrc t0 v
            (net.nwState p.pDst),
           handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0 v)) :=
      fun e hce => handleRequestVoteReply_preserves_candidateEntries hreach hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rw [show ((update_elections_data_requestVoteReply p.pDst p.pSrc t0 v
              (net.nwState p.pDst),
             handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0 v) :
            electionsData (P := P) × raft_data (P := P)).2.log
          = (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0
              v).log from rfl,
          hlog] at he
        exact candidateEntries_ext hst (hpres e (hhost p.pDst e he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      show candidateEntries e st'
      exact candidateEntries_ext hst
        (hpres e (hnw p' t lid pli' plt' es0 ci'
          (hpkts ▸ mem_of_mem_remove_middle (hps p' hp')) hbody' e he))
  · -- do_leader: sent entries come from the leader's own covered log
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hct, -, hty, -, hlog, -⟩ := doLeader_spec d h hdl
    have hgc : gd.cronies = (net.nwState h).1.cronies := by rw [hstate]
    have hctn : d'.currentTerm = (net.nwState h).2.currentTerm := by
      rw [hct, hstate]
    have htyn : d'.type = (net.nwState h).2.type := by
      rw [hty, hstate]
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState h (gd, d')) :=
      fun e hce => candidateEntries_update_same hgc hctn htyn hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rw [show ((gd, d') :
            electionsData (P := P) × raft_data (P := P)).2.log = d'.log from rfl,
          hlog] at he
        have hh := hhost h e
        rw [hstate] at hh
        exact candidateEntries_ext hst (hpres e (hh he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli' plt' es0 ci' hold hbody' e he))
      · rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨pi, pt, ci0, es1, heqm, hes⟩ := doLeader_messages d h hdl q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = q.2 from rfl, heqm] at hbody'
        injection hbody' with h1 h2 h3 h4 h5 h6
        subst h5
        have hh := hhost h e
        rw [hstate] at hh
        exact candidateEntries_ext hst (hpres e (hh (hes e he)))
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hhost, hnw⟩ := hP
    obtain ⟨hlog, hty, hct, -, -, hms⟩ := doGenericServer_spec h d hgs
    have hgc : gd.cronies = (net.nwState h).1.cronies := by rw [hstate]
    have hctn : d'.currentTerm = (net.nwState h).2.currentTerm := by
      rw [hct, hstate]
    have htyn : d'.type = (net.nwState h).2.type := by
      rw [hty, hstate]
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState h (gd, d')) :=
      fun e hce => candidateEntries_update_same hgc hctn htyn hce
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (st' h0).2.log → candidateEntries e st'
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        rw [show ((gd, d') :
            electionsData (P := P) × raft_data (P := P)).2.log = d'.log from rfl,
          hlog] at he
        have hh := hhost h e
        rw [hstate] at hh
        exact candidateEntries_ext hst (hpres e (hh he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      show candidateEntries e st'
      rcases hps p' hp' with hold | hnew
      · exact candidateEntries_ext hst
          (hpres e (hnw p' t lid pli' plt' es0 ci' hold hbody' e he))
      · rw [hms] at hnew
        exact nomatch hnew
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    obtain ⟨hhost, hnw⟩ := hP
    refine ⟨?_, ?_⟩
    · intro h0 e he
      rw [← hstates h0] at he
      exact candidateEntries_ext (fun h => (hstates h).symm) (hhost h0 e he)
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      exact candidateEntries_ext (fun h => (hstates h).symm)
        (hnw p' t lid pli' plt' es0 ci' (hpkts p' hp') hbody' e he)
  · -- reboot: a rebooted node is a follower with its ghost intact
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    obtain ⟨hhost, hnw⟩ := hP
    subst hrb
    have hpres : ∀ e : entry (P := P), candidateEntries e net.nwState →
        candidateEntries e (update net.nwState h (gd, reboot d)) := by
      intro e hce
      obtain ⟨x, hw, himp⟩ := hce
      by_cases hxh : x = h
      · subst hxh
        refine ⟨x, ?_, ?_⟩
        · rw [update_same]
          show wonElection (dedup (gd.cronies e.eTerm)) = true
          rw [show gd.cronies = (net.nwState x).1.cronies from by rw [hstate]]
          exact hw
        · rw [update_same]
          show (reboot d).currentTerm = e.eTerm → (reboot d).type ≠ serverType.Candidate
          exact fun _ hcand => nomatch hcand
      · refine ⟨x, ?_, ?_⟩
        · rw [update_neq _ _ hxh]
          exact hw
        · rw [update_neq _ _ hxh]
          exact himp
    refine ⟨?_, ?_⟩
    · intro h0 e
      show e ∈ (net'.nwState h0).2.log → candidateEntries e net'.nwState
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he'' := he'.symm
        subst he''
        intro he
        replace he : e ∈ d.log := he
        have hh := hhost h e
        rw [hstate] at hh
        exact candidateEntries_ext hst (hpres e (hh he))
      · intro he
        exact candidateEntries_ext hst (hpres e (hhost h0 e he))
    · intro p' t lid pli' plt' es0 ci' hp' hbody' e he
      rw [← hpkts] at hp'
      exact candidateEntries_ext hst
        (hpres e (hnw p' t lid pli' plt' es0 ci' hp' hbody' e he))

end CandidateEntriesRing

end Raft
end VerdiCompat
