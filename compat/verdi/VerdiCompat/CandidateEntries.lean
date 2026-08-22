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

end CandidateEntriesRing

end Raft
end VerdiCompat
