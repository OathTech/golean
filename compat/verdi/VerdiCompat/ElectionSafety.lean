import VerdiCompat.ElectionSpecLemmas
import VerdiCompat.ProofStructure

/-!
# The election-safety invariant chain

Port of verdi-raft's election-safety chain (campaign Arc 3 unit 2;
design doc §3): `votes_le_currentTerm` → `votes_correct` →
`candidates_vote_for_selves` → `cronies_correct` →
`one_leader_per_term`, each invariant STATEMENT 1:1 with its
`deps/verdi-raft/theories/Raft/*Interface.v` file (@ a3375e8), each
proof re-derived through the ported induction principles
(`refined_raft_net_invariant` for the ghost layer, `raft_net_invariant`
for the base layer) and delivered at base level through `lower_prop`.
Ghost state is proof-side only (constitution §3.2): the chain's exit
theorem `one_leader_per_term_invariant` mentions no ghost.
-/

namespace VerdiCompat
namespace Raft

section ElectionSafety
variable {P : BaseParams} [O : OneNodeParams P] [R : RaftParams P]

local notation "RefinedNet" =>
  Network (raft_refined_base_params (P := P)) raft_refined_multi_params

/-- `VotesLeCurrentTermInterface.v:9-13` (`votes_le_currentTerm`). -/
def votes_le_currentTerm (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (n : name (P := P)),
    (t, n) ∈ (net.nwState h).1.votes → t ≤ (net.nwState h).2.currentTerm

/-- `VotesLeCurrentTermProof.v:135-155` (`votes_le_current_term_invariant`):
no recorded vote is from the future. -/
theorem votes_le_currentTerm_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votes_le_currentTerm net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: no votes
    intro h t n hin
    exact nomatch hin
  · -- client_request: ghost votes and term both unchanged
    intro h net st' ps' gd out d l client id c hcr hgd hP _hreach hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hgd
      rw [(update_elections_data_client_request_ghost h (net.nwState h)
        client id c).1] at hin
      rw [(handleClientRequest_spec h (net.nwState h).2 client id c hcr).2.1]
      exact hP h t n hin
    · exact hP h0 t n
  · -- timeout: term only grows; a new vote is at the new term
    intro net h st' ps' gd out d l hto hgd hP _hreach hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hgd
      obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h).2 hto
      rcases update_elections_data_timeout_votes_elim hto hin with hold | ⟨rfl, -, -⟩
      · have hle := hP h t n hold
        rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
        · rw [hct]
          exact hle
        · rw [hct]
          exact Nat.le_succ_of_le hle
      · exact Nat.le_refl _
    · exact hP h0 t n
  · -- append_entries: ghost votes unchanged, term only grows
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP _hreach
      _hpkts hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hgd
      rw [(update_elections_data_appendEntries_ghost p.pDst (net.nwState p.pDst)
        t0 n0 pli plt es ci).1] at hin
      have hle := hP p.pDst t n hin
      obtain ⟨-, hcases, -, -⟩ :=
        handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
      rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
      · rw [hct]
        exact hle
      · exact Nat.le_trans hle (Nat.le_of_lt hct)
    · exact hP h0 t n
  · -- append_entries_reply: ghost untouched, term only grows
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach _hpkts
      hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hgd
      have hle := hP p.pDst t n hin
      obtain ⟨-, hcases, -⟩ :=
        handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es res haer
      rcases hcases with ⟨hct, -, -⟩ | ⟨hct, -, -⟩
      · rw [hct]
        exact hle
      · exact Nat.le_trans hle (Nat.le_of_lt hct)
    · exact hP h0 t n
  · -- request_vote: term only grows; a new vote is at the new term
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP _hreach
      _hpkts hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hgd
      obtain ⟨-, hle, -, -⟩ :=
        handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
      rcases update_elections_data_requestVote_votes_elim (src := p.pSrc) hrv hin with hold | ⟨rfl, -⟩
      · exact Nat.le_trans (hP p.pDst t n hold) hle
      · exact Nat.le_refl _
    · exact hP h0 t n
  · -- request_vote_reply: ghost votes unchanged, term only grows
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP _hreach _hpkts hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hgd
      rw [(update_elections_data_requestVoteReply_votes p.pDst p.pSrc t0 v
        (net.nwState p.pDst)).1] at hin
      have hle := hP p.pDst t n hin
      obtain ⟨hcases, -, -, -⟩ :=
        handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v hrvr
      rcases hcases with ⟨hct, -⟩ | ⟨hct, -⟩
      · rw [hct]
        exact hle
      · exact Nat.le_trans hle (Nat.le_of_lt hct)
    · exact hP h0 t n
  · -- do_leader: both components effectively unchanged
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      rw [(doLeader_spec d h hdl).1]
      have := hP h t n
      rw [hstate] at this
      exact this hin
    · exact hP h0 t n
  · -- do_generic_server: both components effectively unchanged
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst _hps h0 t n
    show (t, n) ∈ (st' h0).1.votes → t ≤ (st' h0).2.currentTerm
    rw [hst h0]
    unfold update
    split
    · intro hin
      obtain ⟨-, -, hct, -, -, -⟩ := doGenericServer_spec h d hgs
      rw [hct]
      have := hP h t n
      rw [hstate] at this
      exact this hin
    · exact hP h0 t n
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h0 t n
    rw [← hstates h0]
    exact hP h0 t n
  · -- reboot: ghost and term both survive
    intro net net' gd d h d' hrb hP _hreach hstate hst _hpkts h0 t n
    rw [hst h0]
    unfold update
    split
    · intro hin
      subst hrb
      show t ≤ (reboot d).currentTerm
      have := hP h t n
      rw [hstate] at this
      exact this hin
    · exact hP h0 t n

/-! ## votes_correct (`VotesCorrectInterface.v` / `VotesCorrectProof.v`) -/

/-- `VotesCorrectInterface.v:8-12` (`one_vote_per_term`). -/
def one_vote_per_term (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (n n' : name (P := P)),
    (t, n) ∈ (net.nwState h).1.votes → (t, n') ∈ (net.nwState h).1.votes →
    n = n'

/-- `VotesCorrectInterface.v:14-18` (`votes_currentTerm_votedFor_correct`). -/
def votes_currentTerm_votedFor_correct (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (n : name (P := P)),
    (t, n) ∈ (net.nwState h).1.votes → (net.nwState h).2.currentTerm = t →
    (net.nwState h).2.votedFor = some n

/-- `VotesCorrectInterface.v:20-24` (`currentTerm_votedFor_votes_correct`). -/
def currentTerm_votedFor_votes_correct (net : RefinedNet) : Prop :=
  ∀ (h : name (P := P)) (t : term) (n : name (P := P)),
    (net.nwState h).2.currentTerm = t → (net.nwState h).2.votedFor = some n →
    (t, n) ∈ (net.nwState h).1.votes

/-- `VotesCorrectInterface.v:26-28` (`votes_correct`). -/
def votes_correct (net : RefinedNet) : Prop :=
  one_vote_per_term net ∧ votes_currentTerm_votedFor_correct net ∧
  currentTerm_votedFor_votes_correct net

/-- Node-level bundle of `votes_correct` (proof plumbing; the interface
statements above are 1:1 with upstream). All three conjuncts are
pointwise over nodes, so obligations reduce to one node-state fact. -/
def votes_state_ok (x : electionsData (P := P) × raft_data (P := P)) : Prop :=
  (∀ (t : term) (n n' : name (P := P)),
    (t, n) ∈ x.1.votes → (t, n') ∈ x.1.votes → n = n') ∧
  (∀ (t : term) (n : name (P := P)),
    (t, n) ∈ x.1.votes → x.2.currentTerm = t → x.2.votedFor = some n) ∧
  (∀ (t : term) (n : name (P := P)),
    x.2.currentTerm = t → x.2.votedFor = some n → (t, n) ∈ x.1.votes)

/-- One-node update step for `votes_correct` (the shape every handler
obligation shares). -/
theorem votes_correct_of_update {net net' : RefinedNet} {h : name (P := P)}
    {gd : electionsData (P := P)} {d : raft_data (P := P)}
    (hst : ∀ h0, net'.nwState h0 = update net.nwState h (gd, d) h0)
    (hP : votes_correct net) (hvle : votes_le_currentTerm net)
    (hnode : votes_state_ok (net.nwState h) →
      (∀ (t : term) (n : name (P := P)), (t, n) ∈ (net.nwState h).1.votes →
        t ≤ (net.nwState h).2.currentTerm) →
      votes_state_ok (gd, d)) :
    votes_correct net' := by
  obtain ⟨h1, h2, h3⟩ := hP
  have hok : ∀ h0, votes_state_ok (net.nwState h0) :=
    fun h0 => ⟨fun t n n' => h1 h0 t n n', fun t n => h2 h0 t n,
      fun t n => h3 h0 t n⟩
  have hall : ∀ h0, votes_state_ok (net'.nwState h0) := by
    intro h0
    rw [hst h0]
    unfold update
    split
    · exact hnode (hok h) (fun t n => hvle h t n)
    · exact hok h0
  exact ⟨fun h0 t n n' => (hall h0).1 t n n',
    fun h0 t n => (hall h0).2.1 t n,
    fun h0 t n => (hall h0).2.2 t n⟩

omit O in
/-- Node facts transport along an unchanged ghost `votes` list. -/
private theorem votes_ok_ghost_eq {g gd : electionsData (P := P)}
    {d : raft_data (P := P)} (hgv : gd.votes = g.votes)
    (hok : votes_state_ok (g, d)) : votes_state_ok (gd, d) := by
  obtain ⟨h1, h2, h3⟩ := hok
  refine ⟨fun t n n' hin hin' => h1 t n n' ?_ ?_,
    fun t n hin hc => h2 t n ?_ hc,
    fun t n hc hv => ?_⟩
  · rw [← hgv]; exact hin
  · rw [← hgv]; exact hin'
  · rw [← hgv]; exact hin
  · show (t, n) ∈ gd.votes
    rw [hgv]
    exact h3 t n hc hv

omit O in
/-- Node facts transport along a state change preserving term and vote. -/
private theorem votes_ok_preserved {g : electionsData (P := P)}
    {s d : raft_data (P := P)} (hct : d.currentTerm = s.currentTerm)
    (hvf : d.votedFor = s.votedFor) (hok : votes_state_ok (g, s)) :
    votes_state_ok (g, d) := by
  obtain ⟨h1, h2, h3⟩ := hok
  refine ⟨h1, fun t n hin hc => ?_, fun t n hc hv => ?_⟩
  · rw [hvf]
    exact h2 t n hin (hct.symm.trans hc)
  · exact h3 t n (hct.symm.trans hc) (hvf.symm.trans hv)

omit O in
/-- `votes_correct_timeout`'s node core (`VotesCorrectProof.v:46-67`). -/
private theorem votes_ok_timeout {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l))
    (hok : votes_state_ok st)
    (hvle : ∀ (t : term) (n : name (P := P)),
      (t, n) ∈ st.1.votes → t ≤ st.2.currentTerm) :
    votes_state_ok (update_elections_data_timeout me st, st') := by
  obtain ⟨hovpt, hvctvf, hctvf⟩ := hok
  obtain ⟨-, hcases, -⟩ := handleTimeout_spec me st.2 h
  refine ⟨?_, ?_, ?_⟩
  · intro t n n' hin hin'
    rcases update_elections_data_timeout_votes_elim h hin with ho | ⟨heqt, hplus, hvf⟩
    · rcases update_elections_data_timeout_votes_elim h hin' with ho' | ⟨-, hplus', -⟩
      · exact hovpt t n n' ho ho'
      · exfalso
        have hb := hvle t n ho
        rw [hplus'] at hb
        exact absurd hb (Nat.not_succ_le_self _)
    · rcases update_elections_data_timeout_votes_elim h hin' with ho' | ⟨-, -, hvf'⟩
      · exfalso
        have hb := hvle t n' ho'
        rw [hplus] at hb
        exact absurd hb (Nat.not_succ_le_self _)
      · exact Option.some.inj (hvf.symm.trans hvf')
  · intro t n hin hct
    rcases update_elections_data_timeout_votes_elim h hin with ho | ⟨-, -, hvf⟩
    · rcases hcases with ⟨hct', -, hvf', -⟩ | ⟨hct', -, -, -, -⟩
      · rw [hvf']
        exact hvctvf t n ho (hct'.symm.trans hct)
      · exfalso
        have hb := hvle t n ho
        rw [← hct, hct'] at hb
        exact absurd hb (Nat.not_succ_le_self _)
    · exact hvf
  · intro t n hct hvf
    exact hct ▸ update_elections_data_timeout_votes_intro h
      (fun tt hh htt hvv => hctvf tt hh htt.symm hvv) hvf

omit O in
/-- `votes_correct_append_entries`'s node core
(`VotesCorrectProof.v:69-84`). -/
private theorem votes_ok_appendEntries {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {t0 : term}
    {lid : name (P := P)} {pli : logIndex} {plt : term}
    {es : List (entry (P := P))} {ci : logIndex} {st' m}
    (h : handleAppendEntries me st.2 t0 lid pli plt es ci = (st', m))
    (hok : votes_state_ok st)
    (hvle : ∀ (t : term) (n : name (P := P)),
      (t, n) ∈ st.1.votes → t ≤ st.2.currentTerm) :
    votes_state_ok
      (update_elections_data_appendEntries me st t0 lid pli plt es ci, st') := by
  obtain ⟨hovpt, hvctvf, hctvf⟩ := hok
  obtain ⟨-, hcases, -, -⟩ := handleAppendEntries_spec me st.2 t0 lid pli plt es ci h
  refine votes_ok_ghost_eq
    (update_elections_data_appendEntries_ghost me st t0 lid pli plt es ci).1 ?_
  refine ⟨hovpt, fun t n hin hct => ?_, fun t n hct hvf => ?_⟩
  · rcases hcases with ⟨hct', hvf'⟩ | ⟨hlt, -⟩
    · rw [hvf']
      exact hvctvf t n hin (hct'.symm.trans hct)
    · exfalso
      have hb := Nat.lt_of_lt_of_le (hct ▸ hlt) (hvle t n hin)
      exact absurd hb (Nat.lt_irrefl _)
  · rcases hcases with ⟨hct', hvf'⟩ | ⟨-, hnone⟩
    · exact hctvf t n (hct'.symm.trans hct) (hvf'.symm.trans hvf)
    · rw [hnone] at hvf
      cases hvf

omit O in
/-- `votes_correct_append_entries_reply`'s node core
(`VotesCorrectProof.v:86-101`). -/
private theorem votes_ok_appendEntriesReply {me src : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {t0 : term}
    {es : List (entry (P := P))} {r : Bool} {st' l}
    (h : handleAppendEntriesReply me st.2 src t0 es r = (st', l))
    (hok : votes_state_ok st)
    (hvle : ∀ (t : term) (n : name (P := P)),
      (t, n) ∈ st.1.votes → t ≤ st.2.currentTerm) :
    votes_state_ok (st.1, st') := by
  obtain ⟨hovpt, hvctvf, hctvf⟩ := hok
  obtain ⟨-, hcases, -⟩ := handleAppendEntriesReply_spec me st.2 src t0 es r h
  refine ⟨hovpt, fun t n hin hct => ?_, fun t n hct hvf => ?_⟩
  · rcases hcases with ⟨hct', hvf', -⟩ | ⟨hlt, -, -⟩
    · rw [hvf']
      exact hvctvf t n hin (hct'.symm.trans hct)
    · exfalso
      have hb := Nat.lt_of_lt_of_le (hct ▸ hlt) (hvle t n hin)
      exact absurd hb (Nat.lt_irrefl _)
  · rcases hcases with ⟨hct', hvf', -⟩ | ⟨-, hnone, -⟩
    · exact hctvf t n (hct'.symm.trans hct) (hvf'.symm.trans hvf)
    · rw [hnone] at hvf
      cases hvf

omit O in
/-- `votes_correct_request_vote_reply`'s node core
(`VotesCorrectProof.v:139-165`). -/
private theorem votes_ok_requestVoteReply {me src : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {t0 : term} {v : Bool}
    (hok : votes_state_ok st)
    (hvle : ∀ (t : term) (n : name (P := P)),
      (t, n) ∈ st.1.votes → t ≤ st.2.currentTerm) :
    votes_state_ok (update_elections_data_requestVoteReply me src t0 v st,
      handleRequestVoteReply me st.2 src t0 v) := by
  obtain ⟨hovpt, hvctvf, hctvf⟩ := hok
  obtain ⟨hcases, -, -, -⟩ :=
    handleRequestVoteReply_spec me st.2 src t0 v rfl
  refine votes_ok_ghost_eq
    (update_elections_data_requestVoteReply_votes me src t0 v st).1 ?_
  refine ⟨hovpt, fun t n hin hct => ?_, fun t n hct hvf => ?_⟩
  · rcases hcases with ⟨hct', hvf'⟩ | ⟨hlt, -⟩
    · rw [hvf']
      exact hvctvf t n hin (hct'.symm.trans hct)
    · exfalso
      have hb := Nat.lt_of_lt_of_le (hct ▸ hlt) (hvle t n hin)
      exact absurd hb (Nat.lt_irrefl _)
  · rcases hcases with ⟨hct', hvf'⟩ | ⟨-, hnone⟩
    · exact hctvf t n (hct'.symm.trans hct) (hvf'.symm.trans hvf)
    · rw [hnone] at hvf
      cases hvf

omit O in
/-- `votes_correct_request_vote`'s node core
(`VotesCorrectProof.v:103-137`). -/
private theorem votes_ok_requestVote {me src : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {t0 : term}
    {lli : logIndex} {llt : term} {st' m}
    (h : handleRequestVote me st.2 t0 src lli llt = (st', m))
    (hok : votes_state_ok st)
    (hvle : ∀ (t : term) (n : name (P := P)),
      (t, n) ∈ st.1.votes → t ≤ st.2.currentTerm) :
    votes_state_ok (update_elections_data_requestVote me src t0 src lli llt st,
      st') := by
  obtain ⟨hovpt, hvctvf, hctvf⟩ := hok
  obtain ⟨-, hle, -, hvfcase⟩ := handleRequestVote_spec me st.2 t0 src lli llt h
  have hnovote : ∀ (t : term) (n : name (P := P)),
      st.2.votedFor = none → ¬ st.2.votedFor = some n := by
    intro _ _ hnone hh
    rw [hnone] at hh
    cases hh
  refine ⟨?_, ?_, ?_⟩
  · intro t n n' hin hin'
    rcases update_elections_data_requestVote_votes_elim (src := src) h hin
      with ho | ⟨heqt, hvf⟩
    · rcases update_elections_data_requestVote_votes_elim (src := src) h hin'
        with ho' | ⟨heqt', hvf'⟩
      · exact hovpt t n n' ho ho'
      · -- old (t, n) beside a new grant at the same t
        have heq2 : st'.currentTerm = st.2.currentTerm :=
          Nat.le_antisymm (heqt' ▸ hvle t n ho) hle
        have hst2t : st.2.currentTerm = t := (heqt'.trans heq2).symm
        rcases hvfcase heq2 with hpres | ⟨hnone, -⟩
        · exact Option.some.inj
            ((hvctvf t n ho hst2t).symm.trans (hpres.symm.trans hvf'))
        · exact absurd (hvctvf t n ho hst2t) (hnovote t n hnone)
    · rcases update_elections_data_requestVote_votes_elim (src := src) h hin'
        with ho' | ⟨-, hvf'⟩
      · -- new (t, n) beside an old (t, n')
        have heq2 : st'.currentTerm = st.2.currentTerm :=
          Nat.le_antisymm (heqt ▸ hvle t n' ho') hle
        have hst2t : st.2.currentTerm = t := (heqt.trans heq2).symm
        rcases hvfcase heq2 with hpres | ⟨hnone, -⟩
        · exact Option.some.inj
            ((hpres.symm.trans hvf).symm.trans (hvctvf t n' ho' hst2t))
        · exact absurd (hvctvf t n' ho' hst2t) (hnovote t n' hnone)
      · exact Option.some.inj (hvf.symm.trans hvf')
  · intro t n hin hct
    rcases update_elections_data_requestVote_votes_elim (src := src) h hin
      with ho | ⟨-, hvf⟩
    · have heq2 : st'.currentTerm = st.2.currentTerm :=
        Nat.le_antisymm (hct.symm ▸ hvle t n ho) hle
      have hst2t : st.2.currentTerm = t := heq2.symm.trans hct
      rcases hvfcase heq2 with hpres | ⟨hnone, -⟩
      · rw [hpres]
        exact hvctvf t n ho hst2t
      · exact absurd (hvctvf t n ho hst2t) (hnovote t n hnone)
    · exact hvf
  · intro t n hct hvf
    rcases Nat.lt_or_ge st.2.currentTerm st'.currentTerm with hlt | hge
    · exact hct ▸ update_elections_data_requestVote_votes_intro (src := src) h
        hvf (Or.inl hlt)
    · have heq2 : st'.currentTerm = st.2.currentTerm := Nat.le_antisymm hge hle
      rcases hvfcase heq2 with hpres | ⟨hnone, -⟩
      · exact update_elections_data_requestVote_votes_old me src t0 src lli llt st
          (hctvf t n (heq2.symm.trans hct) (hpres.symm.trans hvf))
      · exact hct ▸ update_elections_data_requestVote_votes_intro (src := src) h
          hvf (Or.inr hnone)

/-- `VotesCorrectProof.v:222-243` (`votes_correct_invariant`): the ghost
`votes` list is a faithful, per-term-unique record of every vote. -/
theorem votes_correct_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      votes_correct net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_, ?_⟩
    · intro h t n n' hin hin'
      exact nomatch hin
    · intro h t n hin hct
      exact nomatch hin
    · intro h t n hct hvf
      exact nomatch hvf
  · -- client_request
    intro h net st' ps' gd out d l client id c hcr hgd hP hreach hst _hps
    subst hgd
    obtain ⟨-, hct, hvf, -, -⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr
    exact votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach)
      (fun hok _ => votes_ok_ghost_eq
        (update_elections_data_client_request_ghost h (net.nwState h) client id c).1
        (votes_ok_preserved hct hvf hok))
  · -- timeout
    intro net h st' ps' gd out d l hto hgd hP hreach hst _hps
    subst hgd
    exact votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach)
      (fun hok hvle => votes_ok_timeout hto hok hvle)
  · -- append_entries
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP hreach
      _hpkts hst _hps
    subst hgd
    exact votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach)
      (fun hok hvle => votes_ok_appendEntries hae hok hvle)
  · -- append_entries_reply
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP hreach _hpkts
      hst _hps
    subst hgd
    exact votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach)
      (fun hok hvle => votes_ok_appendEntriesReply haer hok hvle)
  · -- request_vote
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP hreach
      _hpkts hst _hps
    subst hgd
    exact votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach)
      (fun hok hvle => votes_ok_requestVote hrv hok hvle)
  · -- request_vote_reply
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP hreach _hpkts hst _hps
    subst hgd
    subst hrvr
    exact votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach)
      (fun hok hvle => votes_ok_requestVoteReply hok hvle)
  · -- do_leader
    intro net st' ps' gd d h os d' ms hdl hP hreach hstate hst _hps
    obtain ⟨hct, hvf, -, -, -, -⟩ := doLeader_spec d h hdl
    refine votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach) (fun hok _ => ?_)
    rw [hstate] at hok
    exact votes_ok_preserved hct hvf hok
  · -- do_generic_server
    intro net st' ps' gd d os d' ms h hgs hP hreach hstate hst _hps
    obtain ⟨-, -, hct, -, hvf, -⟩ := doGenericServer_spec h d hgs
    refine votes_correct_of_update (net' := ⟨ps', st'⟩) hst hP
      (votes_le_currentTerm_invariant net hreach) (fun hok _ => ?_)
    rw [hstate] at hok
    exact votes_ok_preserved hct hvf hok
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨fun h0 t n n' hin hin' => h1 h0 t n n' ?_ ?_,
      fun h0 t n hin hc => ?_, fun h0 t n hc hv => ?_⟩
    · rw [hstates h0]; exact hin
    · rw [hstates h0]; exact hin'
    · rw [← hstates h0] at hin hc ⊢
      exact h2 h0 t n hin hc
    · rw [← hstates h0] at hc hv ⊢
      exact h3 h0 t n hc hv
  · -- reboot
    intro net net' gd d h d' hrb hP hreach hstate hst _hpkts
    subst hrb
    refine votes_correct_of_update (net' := net') hst hP
      (votes_le_currentTerm_invariant net hreach) (fun hok _ => ?_)
    rw [hstate] at hok
    exact votes_ok_preserved rfl rfl hok

/-! ## candidates_vote_for_selves (BASE layer —
`CandidatesVoteForSelvesInterface.v` / `CandidatesVoteForSelvesProof.v`,
through the already-ported base `raft_net_invariant`) -/

local notation "RaftNet" => Network (raft_base_params (P := P)) raft_multi_params

/-- `CandidatesVoteForSelvesInterface.v:8-11` (`candidates_vote_for_selves`). -/
def candidates_vote_for_selves (net : RaftNet) : Prop :=
  ∀ h : name (P := P), (net.nwState h).type = .Candidate →
    (net.nwState h).votedFor = some h

/-- One-node update step for `candidates_vote_for_selves` (pointwise
plumbing, mirroring `votes_correct_of_update` at the base layer). -/
theorem cvfs_of_update {net net' : RaftNet} {h : name (P := P)}
    {d : raft_data (P := P)}
    (hst : ∀ h0, net'.nwState h0 = update net.nwState h d h0)
    (hP : candidates_vote_for_selves net)
    (hnode : ((net.nwState h).type = .Candidate →
        (net.nwState h).votedFor = some h) →
      (d.type = .Candidate → d.votedFor = some h)) :
    candidates_vote_for_selves net' := by
  intro h0
  rw [hst h0]
  unfold update
  split
  · rename_i heq
    subst heq
    exact hnode (hP h0)
  · exact hP h0

/-- `CandidatesVoteForSelvesProof.v:110-129`
(`candidates_vote_for_selves_invariant`) — proved through the BASE
`raft_net_invariant`: a candidate has always voted for itself. -/
theorem candidates_vote_for_selves_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      candidates_vote_for_selves net := by
  refine raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init: type Follower
    intro h hty
    exact nomatch hty
  · -- client_request
    intro h net st' ps' out d l client id c hcr hP _hreach hst _hps
    obtain ⟨hty, -, hvf, -, -⟩ := handleClientRequest_spec h (net.nwState h) client id c hcr
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    rw [hvf]
    exact hn (hty.symm.trans hcand)
  · -- timeout
    intro net h st' ps' out d l hto hP _hreach hst _hps
    obtain ⟨-, hcases, -⟩ := handleTimeout_spec h (net.nwState h) hto
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    rcases hcases with ⟨-, hty, hvf, -⟩ | ⟨-, -, hvf, -, -⟩
    · rw [hvf]
      exact hn (hty.symm.trans hcand)
    · exact hvf
  · -- append_entries: candidate ⇒ rejected ⇒ untouched
    intro xs p ys net st' ps' d m t n pli plt es ci hae _hbody hP _hreach _hpkts
      hst _hps
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    have heq := handleAppendEntries_reject_of_not_follower p.pDst
      (net.nwState p.pDst) t n pli plt es ci hae
      (fun hf => nomatch hcand.symm.trans hf)
    rw [heq] at hcand ⊢
    exact hn hcand
  · -- append_entries_reply
    intro xs p ys net st' ps' d m t es res haer _hbody hP _hreach _hpkts hst _hps
    obtain ⟨-, hcases, -⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst) p.pSrc t es res haer
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    rcases hcases with ⟨-, hvf, hty⟩ | ⟨-, -, hty⟩
    · rw [hvf]
      exact hn (hty.symm.trans hcand)
    · exact absurd (hty.symm.trans hcand) (fun hh => nomatch hh)
  · -- request_vote
    intro xs p ys net st' ps' d m t cid lli llt hrv _hbody hP _hreach _hpkts
      hst _hps
    obtain ⟨-, -, htycase, hvfcase⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst) t p.pSrc lli llt hrv
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    rcases htycase with ⟨hcteq, hty⟩ | hty
    · rcases hvfcase hcteq with hpres | ⟨hnone, -⟩
      · rw [hpres]
        exact hn (hty.symm.trans hcand)
      · exact absurd (hn (hty.symm.trans hcand))
          (by rw [hnone]; exact fun hh => nomatch hh)
    · exact absurd (hty.symm.trans hcand) (fun hh => nomatch hh)
  · -- request_vote_reply
    intro xs p ys net st' ps' d t v hrvr _hbody hP _hreach _hpkts hst _hps
    obtain ⟨hvfcase, -, htycand, -⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst) p.pSrc t v hrvr
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    obtain ⟨hty, hcteq⟩ := htycand hcand
    rcases hvfcase with ⟨-, hvf⟩ | ⟨hlt, -⟩
    · rw [hvf]
      exact hn hty
    · exact absurd hcteq (Nat.ne_of_gt hlt)
  · -- do_leader
    intro net st' ps' d h os d' ms hdl hP _hreach hstate hst _hps
    obtain ⟨-, hvf, hty, -, -, -⟩ := doLeader_spec d h hdl
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    rw [hstate] at hn
    rw [hvf]
    exact hn (hty.symm.trans hcand)
  · -- do_generic_server
    intro net st' ps' d os d' ms h hgs hP _hreach hstate hst _hps
    obtain ⟨-, hty, -, -, hvf, -⟩ := doGenericServer_spec h d hgs
    refine cvfs_of_update hst hP (fun hn hcand => ?_)
    rw [hstate] at hn
    rw [hvf]
    exact hn (hty.symm.trans hcand)
  · -- state_same_packet_subset
    intro net net' hstates _hpkts hP _hreach h0
    rw [← hstates h0]
    exact hP h0
  · -- reboot: a rebooted node is a follower
    intro net net' d h d' hrb hP _hreach hstate hst _hpkts h0
    rw [hst h0]
    unfold update
    split
    · subst hrb
      intro hcand
      exact nomatch hcand
    · exact hP h0

end ElectionSafety

end Raft
end VerdiCompat
