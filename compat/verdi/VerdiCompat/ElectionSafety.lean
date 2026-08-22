import VerdiCompat.ElectionSpecLemmas
import VerdiCompat.ProofStructure
import VerdiCompat.Properties

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

/-! ## cronies_correct (`CroniesCorrectInterface.v` /
`CroniesCorrectProof.v`) -/

/-- `CroniesCorrectInterface.v:9-14` (`votes_received_cronies`). -/
def votes_received_cronies (net : RefinedNet) : Prop :=
  ∀ (h crony : name (P := P)),
    crony ∈ (net.nwState h).2.votesReceived →
    ((net.nwState h).2.type = .Leader ∨ (net.nwState h).2.type = .Candidate) →
    crony ∈ (net.nwState h).1.cronies ((net.nwState h).2.currentTerm)

/-- `CroniesCorrectInterface.v:16-19` (`cronies_votes`). -/
def cronies_votes (net : RefinedNet) : Prop :=
  ∀ (t : term) (cand crony : name (P := P)),
    crony ∈ (net.nwState cand).1.cronies t →
    (t, cand) ∈ (net.nwState crony).1.votes

/-- `CroniesCorrectInterface.v:21-25` (`votes_nw`). -/
def votes_nw (net : RefinedNet) : Prop :=
  ∀ (p : Packet (raft_refined_base_params (P := P)) raft_refined_multi_params)
    (t : term),
    p.pBody = .RequestVoteReply t true →
    p ∈ net.nwPackets →
    (t, p.pDst) ∈ (net.nwState p.pSrc).1.votes

/-- `CroniesCorrectInterface.v:27-30` (`votes_received_leaders`). -/
def votes_received_leaders (net : RefinedNet) : Prop :=
  ∀ h : name (P := P), (net.nwState h).2.type = .Leader →
    wonElection (dedup (net.nwState h).2.votesReceived) = true

/-- `CroniesCorrectInterface.v:32-33` (`cronies_correct`). -/
def cronies_correct (net : RefinedNet) : Prop :=
  votes_received_cronies net ∧ cronies_votes net ∧ votes_nw net ∧
  votes_received_leaders net

theorem mem_of_mem_remove_middle {α : Type _} {p' p : α}
    {xs ys : List α} (h : p' ∈ xs ++ ys) : p' ∈ xs ++ p :: ys := by
  rcases List.mem_append.mp h with h1 | h1
  · exact List.mem_append.mpr (Or.inl h1)
  · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h1))

/-- `CroniesCorrectProof.v:686-703` (`cronies_correct_invariant`): the
ghost `cronies` are honest supporter lists — backed by recorded votes,
covering `votesReceived`, and full for every leader. -/
theorem cronies_correct_invariant :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      cronies_correct net := by
  refine refined_raft_net_invariant ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- init
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h crony hcr _
      exact nomatch hcr
    · intro t cand crony hcr
      exact nomatch hcr
    · intro p t _ hp
      exact nomatch hp
    · intro h hty
      exact nomatch hty
  · -- client_request: state and ghost cronies untouched; no packets sent
    intro h net st' ps' gd out d l client id c hcr0 hgd hP _hreach hst hps
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨hty, hct, -, hvr, hl⟩ :=
      handleClientRequest_spec h (net.nwState h).2 client id c hcr0
    have hgv : gd.votes = (net.nwState h).1.votes := by
      rw [hgd]
      exact (update_elections_data_client_request_ghost h (net.nwState h) client id c).1
    have hgc : gd.cronies = (net.nwState h).1.cronies := by
      rw [hgd]
      exact (update_elections_data_client_request_ghost h (net.nwState h) client id c).2.2.1
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState h (gd, d) h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        show (t, n) ∈ gd.votes
        rw [hgv]
        exact hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        show crony ∈ gd.cronies d.currentTerm
        rw [hgc, hct]
        refine hvrc h crony ?_ ?_
        · rw [← hvr]; exact hc
        · rw [← hty]; exact hty'
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin
        rw [← hgc]
        exact hcin
      · exact fun x => x
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst (hnw p' t hbody' hold)
      · rw [hl] at hnew
        exact nomatch hnew
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rw [hvr]
        exact hvrl h (hty.symm.trans hld)
      · exact hvrl h0
  · -- timeout: a fresh candidacy snapshots itself; only RequestVote sent
    intro net h st' ps' gd out d l hto hgd hP _hreach hst hps
    subst hgd
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨-, hcases, hmsg⟩ := handleTimeout_spec h (net.nwState h).2 hto
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState h
          (update_elections_data_timeout h (net.nwState h), d) h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        exact update_elections_data_timeout_votes_old h (net.nwState h) hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        by_cases hL : (net.nwState h).2.type = .Leader
        · show crony ∈ (update_elections_data_timeout h (net.nwState h)).cronies
            d.currentTerm
          rw [update_elections_data_timeout_cronies_leader h (net.nwState h) hL]
          rcases hcases with ⟨hct, hty, -, hvr⟩ | ⟨-, -, -, -, hnl⟩
          · rw [hct]
            refine hvrc h crony ?_ ?_
            · rw [← hvr]; exact hc
            · rw [← hty]; exact hty'
          · exact absurd hL hnl
        · obtain ⟨-, -, -, hvr⟩ := handleTimeout_not_leader h (net.nwState h).2 hto hL
          show crony ∈ (update_elections_data_timeout h (net.nwState h)).cronies
            d.currentTerm
          rw [update_elections_data_timeout_cronies_intro hto hL]
          exact hc
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      have hcin' : crony ∈ (update net.nwState h
          (update_elections_data_timeout h (net.nwState h), d) cand).1.cronies t :=
        hcin
      revert hcin'
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin'
        rcases update_elections_data_timeout_cronies_elim hto hcin'
          with hold | ⟨heqt, hcr, hnl⟩
        · exact hmono crony t h (hcv t h crony hold)
        · obtain ⟨-, -, hvf, hvr⟩ := handleTimeout_not_leader h (net.nwState h).2 hto hnl
          rw [hvr] at hcr
          have hch : crony = h := List.mem_singleton.mp hcr
          subst hch
          show (t, crony) ∈ (update net.nwState crony
            (update_elections_data_timeout crony (net.nwState crony), d) crony).1.votes
          rw [update_same]
          exact heqt ▸ update_elections_data_timeout_votes_intro hto
            (fun tt hh _ hvv =>
              (votes_correct_invariant net (by assumption)).2.2 crony tt hh
                (by simp_all) hvv) hvf
      · intro hcin'
        exact hmono crony t cand (hcv t cand crony hcin')
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst (hnw p' t hbody' hold)
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', cid, lli, llt, heqm⟩ := hmsg q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = q.2 from rfl, heqm] at hbody'
        exact nomatch hbody'
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rcases hcases with ⟨hct, hty, -, hvr⟩ | ⟨-, hty, -, -, -⟩
        · rw [hvr]
          exact hvrl h (hty.symm.trans hld)
        · rw [hty] at hld
          exact nomatch hld
      · exact hvrl h0
  · -- append_entries: candidate/leader ⇒ rejected ⇒ untouched
    intro xs p ys net st' ps' gd d m t0 n0 pli plt es ci hae hgd _hbody hP _hreach
      hpkts hst hps
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    have hgv : gd.votes = (net.nwState p.pDst).1.votes := by
      rw [hgd]
      exact (update_elections_data_appendEntries_ghost p.pDst (net.nwState p.pDst)
        t0 n0 pli plt es ci).1
    have hgc : gd.cronies = (net.nwState p.pDst).1.cronies := by
      rw [hgd]
      exact (update_elections_data_appendEntries_ghost p.pDst (net.nwState p.pDst)
        t0 n0 pli plt es ci).2.2.1
    obtain ⟨-, -, -, t', es', r', hm⟩ :=
      handleAppendEntries_spec p.pDst (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState p.pDst (gd, d) h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        show (t, n) ∈ gd.votes
        rw [hgv]
        exact hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        have hrej := handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
          (by rcases hty' with hh | hh <;> (rw [hh]; exact fun he => nomatch he))
        rw [hrej] at hc hty' ⊢
        show crony ∈ gd.cronies (net.nwState p.pDst).2.currentTerm
        rw [hgc]
        exact hvrc p.pDst crony hc hty'
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin
        rw [← hgc]
        exact hcin
      · exact fun x => x
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst
          (hnw p' t hbody' (hpkts ▸ mem_of_mem_remove_middle hold))
      · exfalso
        subst hnew
        rw [show (⟨p.pDst, p.pSrc, m⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = m from rfl, hm] at hbody'
        exact nomatch hbody'
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        have hrej := handleAppendEntries_reject_of_not_follower p.pDst
          (net.nwState p.pDst).2 t0 n0 pli plt es ci hae
          (by rw [hld]; exact fun he => nomatch he)
        rw [hrej] at hld ⊢
        exact hvrl p.pDst hld
      · exact hvrl h0
  · -- append_entries_reply: ghost untouched, no packets sent
    intro xs p ys net st' ps' gd d m t0 es res haer hgd _hbody hP _hreach hpkts
      hst hps
    subst hgd
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨hvr, hcases, hl⟩ :=
      handleAppendEntriesReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 es res haer
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState p.pDst ((net.nwState p.pDst).1, d) h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        exact hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        rcases hcases with ⟨hct, -, hty⟩ | ⟨-, -, hty⟩
        · show crony ∈ (net.nwState p.pDst).1.cronies d.currentTerm
          rw [hct]
          refine hvrc p.pDst crony ?_ ?_
          · rw [← hvr]; exact hc
          · rw [← hty]; exact hty'
        · rcases hty' with hh | hh <;> (rw [hty] at hh; exact nomatch hh)
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        exact fun x => x
      · exact fun x => x
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst
          (hnw p' t hbody' (hpkts ▸ mem_of_mem_remove_middle hold))
      · rw [hl] at hnew
        exact nomatch hnew
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rcases hcases with ⟨-, -, hty⟩ | ⟨-, -, hty⟩
        · rw [hvr]
          exact hvrl p.pDst (hty.symm.trans hld)
        · rw [hty] at hld
          exact nomatch hld
      · exact hvrl h0
  · -- request_vote: the vote-granting reply is backed by the fresh ghost record
    intro xs p ys net st' ps' gd d m t0 cid lli llt hrv hgd _hbody hP hreach
      hpkts hst hps
    subst hgd
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨hvr, hle, htycase, hvfcase⟩ :=
      handleRequestVote_spec p.pDst (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
    obtain ⟨hgc, -, -⟩ := update_elections_data_requestVote_cronies p.pDst p.pSrc
      t0 p.pSrc lli llt (net.nwState p.pDst)
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState p.pDst
          (update_elections_data_requestVote p.pDst p.pSrc t0 p.pSrc lli llt
            (net.nwState p.pDst), d) h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        exact update_elections_data_requestVote_votes_old p.pDst p.pSrc t0 p.pSrc
          lli llt (net.nwState p.pDst) hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        rcases htycase with ⟨hct, hty⟩ | hty
        · show crony ∈ (update_elections_data_requestVote p.pDst p.pSrc t0 p.pSrc
            lli llt (net.nwState p.pDst)).cronies d.currentTerm
          rw [hgc, hct]
          refine hvrc p.pDst crony ?_ ?_
          · rw [← hvr]; exact hc
          · rw [← hty]; exact hty'
        · rcases hty' with hh | hh <;> (rw [hty] at hh; exact nomatch hh)
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin
        rw [← hgc]
        exact hcin
      · exact fun x => x
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst
          (hnw p' t hbody' (hpkts ▸ mem_of_mem_remove_middle hold))
      · subst hnew
        replace hbody' : m = msg.RequestVoteReply (P := P) t true := hbody'
        subst hbody'
        obtain ⟨hctt, hvft⟩ := handleRequestVote_reply_true p.pDst
          (net.nwState p.pDst).2 t0 p.pSrc lli llt hrv
        show (t, p.pSrc) ∈ (update net.nwState p.pDst
          (update_elections_data_requestVote p.pDst p.pSrc t0 p.pSrc lli llt
            (net.nwState p.pDst), d) p.pDst).1.votes
        rw [update_same]
        show (t, p.pSrc) ∈ (update_elections_data_requestVote p.pDst p.pSrc t0
          p.pSrc lli llt (net.nwState p.pDst)).votes
        rcases Nat.lt_or_ge (net.nwState p.pDst).2.currentTerm d.currentTerm
          with hlt | hge
        · exact hctt ▸ update_elections_data_requestVote_votes_intro
            (src := p.pSrc) hrv hvft (Or.inl hlt)
        · have heq2 : d.currentTerm = (net.nwState p.pDst).2.currentTerm :=
            Nat.le_antisymm hge hle
          rcases hvfcase heq2 with hpres | ⟨hnone, -⟩
          · have hold : ((net.nwState p.pDst).2.currentTerm, p.pSrc) ∈
                (net.nwState p.pDst).1.votes :=
              (votes_correct_invariant net hreach).2.2 p.pDst _ p.pSrc rfl
                (hpres.symm.trans hvft)
            have := update_elections_data_requestVote_votes_old p.pDst p.pSrc t0
              p.pSrc lli llt (net.nwState p.pDst) hold
            rw [show t = (net.nwState p.pDst).2.currentTerm from
              (hctt.symm.trans heq2)] at *
            exact this
          · exact hctt ▸ update_elections_data_requestVote_votes_intro
              (src := p.pSrc) hrv hvft (Or.inr hnone)
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rcases htycase with ⟨-, hty⟩ | hty
        · rw [hvr]
          exact hvrl p.pDst (hty.symm.trans hld)
        · rw [hty] at hld
          exact nomatch hld
      · exact hvrl h0
  · -- request_vote_reply: the tally is backed by old votes and the consumed reply
    intro xs p ys net st' ps' gd d t0 v hrvr hgd _hbody hP hreach hpkts hst hps
    subst hgd
    subst hrvr
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨hcases, hcrony, htycand, htylead⟩ :=
      handleRequestVoteReply_spec p.pDst (net.nwState p.pDst).2 p.pSrc t0 v rfl
    obtain ⟨hgv, -, -⟩ := update_elections_data_requestVoteReply_votes p.pDst p.pSrc
      t0 v (net.nwState p.pDst)
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState p.pDst
          (update_elections_data_requestVoteReply p.pDst p.pSrc t0 v
            (net.nwState p.pDst),
           handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0 v)
          h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        show (t, n) ∈ (update_elections_data_requestVoteReply p.pDst p.pSrc t0 v
          (net.nwState p.pDst)).votes
        rw [hgv]
        exact hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        show crony ∈ (update_elections_data_requestVoteReply p.pDst p.pSrc t0 v
          (net.nwState p.pDst)).cronies
          (handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0 v).currentTerm
        rw [update_elections_data_requestVoteReply_cronies_intro
          (by rcases hty' with hh | hh <;> (rw [hh]; exact fun he => nomatch he))]
        exact hc
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      have hcin' : crony ∈ (update net.nwState p.pDst
          (update_elections_data_requestVoteReply p.pDst p.pSrc t0 v
            (net.nwState p.pDst),
           handleRequestVoteReply p.pDst (net.nwState p.pDst).2 p.pSrc t0 v)
          cand).1.cronies t := hcin
      revert hcin'
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin'
        rcases update_elections_data_requestVoteReply_cronies_elim hcin'
          with hold | ⟨heqt, hcr, htynf⟩
        · exact hmono crony t p.pDst (hcv t p.pDst crony hold)
        · -- the tally: crony is the fresh voter or an old supporter
          rcases hcrony crony hcr with ⟨rfl, hv, hct⟩ | holdvr
          · -- fresh voter: the consumed RequestVoteReply packet backs it
            refine hmono p.pSrc t p.pDst ?_
            rw [heqt, hct]
            refine hnw p t0 ?_ ?_
            · rw [_hbody, hv]
            · rw [hpkts]
              exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
          · -- old supporter: the node was already campaigning at this term
            have htyold : (net.nwState p.pDst).2.type = .Leader ∨
                (net.nwState p.pDst).2.type = .Candidate := by
              rcases hcase : (handleRequestVoteReply p.pDst (net.nwState p.pDst).2
                  p.pSrc t0 v).type with h1 | h1 | h1
              · exact absurd hcase htynf
              · exact Or.inr (htycand hcase).1
              · rcases htylead hcase with heqst | ⟨hcand, -, -⟩
                · rw [← heqst, hcase]
                  exact Or.inl rfl
                · exact Or.inr hcand
            have hcteq : (handleRequestVoteReply p.pDst (net.nwState p.pDst).2
                p.pSrc t0 v).currentTerm = (net.nwState p.pDst).2.currentTerm := by
              rcases hcase : (handleRequestVoteReply p.pDst (net.nwState p.pDst).2
                  p.pSrc t0 v).type with h1 | h1 | h1
              · exact absurd hcase htynf
              · exact (htycand hcase).2
              · rcases htylead hcase with heqst | ⟨-, -, hct⟩
                · rw [heqst]
                · exact hct
            refine hmono crony t p.pDst
              (hcv t p.pDst crony ?_)
            rw [heqt, hcteq]
            exact hvrc p.pDst crony holdvr htyold
      · intro hcin'
        exact hmono crony t cand (hcv t cand crony hcin')
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      exact hmono p'.pSrc t p'.pDst
        (hnw p' t hbody' (hpkts ▸ mem_of_mem_remove_middle (hps p' hp')))
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rcases htylead hld with heqst | ⟨-, hwon, -⟩
        · rw [heqst]
          exact hvrl p.pDst (heqst ▸ hld)
        · exact hwon
      · exact hvrl h0
  · -- do_leader: state facts preserved; only AppendEntries sent
    intro net st' ps' gd d h os d' ms hdl hP _hreach hstate hst hps
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨hct, -, hty, hvr, -, hmsg⟩ := doLeader_spec d h hdl
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState h (gd, d') h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        show (t, n) ∈ gd.votes
        have : (net.nwState h).1 = gd := by rw [hstate]
        rw [← this]
        exact hin
      · exact hin
    have hgnode : (net.nwState h).1 = gd := by rw [hstate]
    have hdnode : (net.nwState h).2 = d := by rw [hstate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        show crony ∈ gd.cronies d'.currentTerm
        rw [← hgnode, hct, ← hdnode]
        refine hvrc h crony ?_ ?_
        · rw [hdnode, ← hvr]; exact hc
        · rw [hdnode, ← hty]; exact hty'
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin
        rw [hgnode]
        exact hcin
      · exact fun x => x
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst (hnw p' t hbody' hold)
      · exfalso
        rcases List.mem_map.mp hnew with ⟨q, hq, rfl⟩
        obtain ⟨t', lid, pli, plt, es, ci, heqm⟩ := hmsg q hq
        rw [show (⟨h, q.1, q.2⟩ :
            Packet (raft_refined_base_params (P := P)) raft_refined_multi_params).pBody
          = q.2 from rfl, heqm] at hbody'
        exact nomatch hbody'
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rw [hvr, ← hdnode]
        exact hvrl h (hdnode.symm ▸ (hty.symm.trans hld))
      · exact hvrl h0
  · -- do_generic_server: state facts preserved; nothing sent
    intro net st' ps' gd d os d' ms h hgs hP _hreach hstate hst hps
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    obtain ⟨-, hty, hct, hvr, -, hms⟩ := doGenericServer_spec h d hgs
    have hgnode : (net.nwState h).1 = gd := by rw [hstate]
    have hdnode : (net.nwState h).2 = d := by rw [hstate]
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (update net.nwState h (gd, d') h0).1.votes := by
      intro h0 t n hin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        show (t, n) ∈ gd.votes
        rw [← hgnode]
        exact hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      show crony ∈ (st' h0).2.votesReceived →
        ((st' h0).2.type = .Leader ∨ (st' h0).2.type = .Candidate) →
        crony ∈ (st' h0).1.cronies ((st' h0).2.currentTerm)
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hc hty'
        show crony ∈ gd.cronies d'.currentTerm
        rw [← hgnode, hct, ← hdnode]
        refine hvrc h crony ?_ ?_
        · rw [hdnode, ← hvr]; exact hc
        · rw [hdnode, ← hty]; exact hty'
      · exact hvrc h0 crony
    · intro t cand crony
      show crony ∈ (st' cand).1.cronies t → (t, cand) ∈ (st' crony).1.votes
      rw [hst cand, hst crony]
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin
        rw [hgnode]
        exact hcin
      · exact fun x => x
    · intro p' t hbody' hp'
      show (t, p'.pDst) ∈ (st' p'.pSrc).1.votes
      rw [hst p'.pSrc]
      rcases hps p' hp' with hold | hnew
      · exact hmono p'.pSrc t p'.pDst (hnw p' t hbody' hold)
      · rw [hms] at hnew
        exact nomatch hnew
    · intro h0
      show (st' h0).2.type = .Leader → wonElection (dedup (st' h0).2.votesReceived) = true
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hld
        rw [hvr, ← hdnode]
        exact hvrl h (hdnode.symm ▸ (hty.symm.trans hld))
      · exact hvrl h0
  · -- state_same_packet_subset
    intro net net' hstates hpkts hP _hreach
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      rw [← hstates h0]
      exact hvrc h0 crony
    · intro t cand crony
      rw [← hstates cand, ← hstates crony]
      exact hcv t cand crony
    · intro p' t hbody' hp'
      rw [← hstates p'.pSrc]
      exact hnw p' t hbody' (hpkts p' hp')
    · intro h0
      rw [← hstates h0]
      exact hvrl h0
  · -- reboot: a rebooted node is a follower with no votesReceived; ghost intact
    intro net net' gd d h d' hrb hP _hreach hstate hst hpkts
    subst hrb
    obtain ⟨hvrc, hcv, hnw, hvrl⟩ := hP
    have hgnode : (net.nwState h).1 = gd := by rw [hstate]
    have hmono : ∀ (h0 : name (P := P)) (t : term) (n : name (P := P)),
        (t, n) ∈ (net.nwState h0).1.votes →
        (t, n) ∈ (net'.nwState h0).1.votes := by
      intro h0 t n hin
      rw [hst h0]
      unfold update
      split
      · rename_i he'
        have he := he'.symm
        subst he
        show (t, n) ∈ gd.votes
        rw [← hgnode]
        exact hin
      · exact hin
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 crony
      rw [hst h0]
      unfold update
      split
      · intro _ hty'
        rcases hty' with hh | hh <;> exact nomatch hh
      · exact hvrc h0 crony
    · intro t cand crony
      rw [hst cand]
      unfold update
      intro hcin
      refine hmono crony t cand (hcv t cand crony ?_)
      revert hcin
      split
      · rename_i he'
        have he := he'.symm
        subst he
        intro hcin
        rw [hgnode]
        exact hcin
      · exact fun x => x
    · intro p' t hbody' hp'
      rw [← hpkts] at hp'
      exact hmono p'.pSrc t p'.pDst (hnw p' t hbody' hp')
    · intro h0
      rw [hst h0]
      unfold update
      split
      · intro hty'
        exact nomatch hty'
      · exact hvrl h0

/-! ## Quorum counting (`CommonTheorems.v:1376-1404`, StructTact `pigeon`)

Proved constructively — the lane's axiom set is [propext, Quot.sound],
so no `by_contra`/`Classical`; the pigeonhole argument is a structural
induction with decidable membership. -/

omit O R in
/-- Membership survives `dedup` (StructTact `in_dedup_was_in`). -/
theorem mem_of_mem_dedup {A : Type _} [DecidableEq A] {x : A} :
    ∀ {l : List A}, x ∈ dedup l → x ∈ l := by
  intro l
  induction l with
  | nil => exact fun h => nomatch h
  | cons a as ih =>
    intro h
    unfold dedup at h
    simp only [] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

omit O R in
/-- `dedup` loses no members (StructTact `dedup_In`). -/
theorem mem_dedup_of_mem {A : Type _} [DecidableEq A] {x : A} :
    ∀ {l : List A}, x ∈ l → x ∈ dedup l := by
  intro l
  induction l with
  | nil => exact fun h => nomatch h
  | cons a as ih =>
    intro h
    unfold dedup
    simp only []
    split
    · rename_i hmem
      rcases List.mem_cons.mp h with rfl | h
      · exact ih hmem
      · exact ih h
    · rename_i hmem
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

omit O R in
/-- `dedup` produces no duplicates (StructTact `NoDup_dedup`). -/
theorem nodup_dedup {A : Type _} [DecidableEq A] :
    ∀ (l : List A), (dedup l).Nodup := by
  intro l
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    unfold dedup
    simp only []
    split
    · exact ih
    · rename_i hmem
      rw [List.nodup_cons]
      exact ⟨fun hd => hmem (mem_of_mem_dedup hd), ih⟩

omit O R in
/-- Constructive one-occurrence erasure (core's `List.erase` lemmas pull
in `Classical.choice`, outside the lane's axiom set — the AxCheck sweep
rejected them; this replacement keeps the counting argument inside
[propext, Quot.sound]). -/
def eraseOne {A : Type _} [DecidableEq A] : List A → A → List A
  | [], _ => []
  | b :: bs, a => if a = b then bs else b :: eraseOne bs a

omit O R in
theorem eraseOne_length {A : Type _} [DecidableEq A] {a : A} :
    ∀ {l : List A}, a ∈ l → (eraseOne l a).length + 1 = l.length := by
  intro l
  induction l with
  | nil => exact fun h => nomatch h
  | cons b bs ih =>
    intro h
    unfold eraseOne
    split
    · simp
    · rename_i hne
      have hab : a ∈ bs := by
        rcases List.mem_cons.mp h with rfl | h
        · exact absurd rfl hne
        · exact h
      simp only [List.length_cons]
      rw [← ih hab]

omit O R in
theorem mem_eraseOne_of_ne {A : Type _} [DecidableEq A] {x a : A} :
    ∀ {l : List A}, x ≠ a → x ∈ l → x ∈ eraseOne l a := by
  intro l
  induction l with
  | nil => exact fun _ h => nomatch h
  | cons b bs ih =>
    intro hne h
    unfold eraseOne
    split
    · rename_i hab
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd hab.symm hne
      · exact h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hne h)

omit O R in
/-- A duplicate-free list is no longer than any list containing it. -/
theorem nodup_subset_length {A : Type _} [DecidableEq A] :
    ∀ {sub l : List A}, sub.Nodup → (∀ a ∈ sub, a ∈ l) →
      sub.length ≤ l.length := by
  intro sub
  induction sub with
  | nil => exact fun _ _ => Nat.zero_le _
  | cons a rest ih =>
    intro l hnd hsub
    rw [List.nodup_cons] at hnd
    have hal : a ∈ l := hsub a (List.mem_cons_self ..)
    have hrest : ∀ b ∈ rest, b ∈ eraseOne l a := by
      intro b hb
      exact mem_eraseOne_of_ne (fun he => hnd.1 (by rw [← he]; exact hb))
        (hsub b (List.mem_cons_of_mem _ hb))
    have hlen := ih hnd.2 hrest
    have herase := eraseOne_length hal
    simp only [List.length_cons]
    omega

omit O R in
/-- StructTact `pigeon` (`ListUtil.v:641-649`), constructive form: two
duplicate-free sublists of `l` jointly longer than `l` intersect. -/
theorem pigeon {A : Type _} [DecidableEq A] :
    ∀ (sub1 : List A) (l sub2 : List A),
      (∀ a ∈ sub1, a ∈ l) → (∀ a ∈ sub2, a ∈ l) →
      sub1.Nodup → sub2.Nodup →
      l.length < sub1.length + sub2.length →
      ∃ a, a ∈ sub1 ∧ a ∈ sub2 := by
  intro sub1
  induction sub1 with
  | nil =>
    intro l sub2 _ hs2 _ hn2 hlen
    have := nodup_subset_length hn2 hs2
    simp only [List.length_nil] at hlen
    omega
  | cons a rest ih =>
    intro l sub2 hs1 hs2 hn1 hn2 hlen
    by_cases ha2 : a ∈ sub2
    · exact ⟨a, List.mem_cons_self .., ha2⟩
    · rw [List.nodup_cons] at hn1
      have hal : a ∈ l := hs1 a (List.mem_cons_self ..)
      have hrest : ∀ b ∈ rest, b ∈ eraseOne l a := fun b hb =>
        mem_eraseOne_of_ne (fun he => hn1.1 (by rw [← he]; exact hb))
          (hs1 b (List.mem_cons_of_mem _ hb))
      have hsub2 : ∀ b ∈ sub2, b ∈ eraseOne l a := fun b hb =>
        mem_eraseOne_of_ne (fun he => ha2 (by rw [← he]; exact hb)) (hs2 b hb)
      have herase := eraseOne_length hal
      have hlen' : (eraseOne l a).length < rest.length + sub2.length := by
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨x, hx1, hx2⟩ := ih (eraseOne l a) sub2 hrest hsub2 hn1.2 hn2 hlen'
      exact ⟨x, List.mem_cons_of_mem _ hx1, hx2⟩

/-- `div2_correct'` (`CommonTheorems.v:1376-1381`). -/
theorem div2_le' : ∀ n : Nat, n ≤ div2 n + (div2 n + 1)
  | 0 => by simp [div2]
  | 1 => by simp [div2]
  | n + 2 => by
    have := div2_le' n
    show n + 2 ≤ div2 n + 1 + (div2 n + 1 + 1)
    omega

/-- `div2_correct` (`CommonTheorems.v:1383-1392`). -/
theorem div2_correct {c a b : Nat} (ha : div2 c < a)
    (hb : div2 c < b) : c < a + b := by
  have := div2_le' c
  omega

omit O in
/-- `wonElection_one_in_common` (`CommonTheorems.v:1394-1404`): two
election winners share a voter. -/
theorem wonElection_one_in_common (l l' : List (name (P := P)))
    (hw : wonElection (dedup l) = true) (hw' : wonElection (dedup l') = true) :
    ∃ h, h ∈ l ∧ h ∈ l' := by
  unfold wonElection at hw hw'
  simp at hw hw'
  obtain ⟨a, ha1, ha2⟩ := pigeon (dedup l) (nodes (P := P)) (dedup l')
    (fun a _ => allFin_all a) (fun a _ => allFin_all a)
    (nodup_dedup l) (nodup_dedup l')
    (div2_correct (c := (nodes (P := P)).length)
      (Nat.lt_of_succ_le hw) (Nat.lt_of_succ_le hw'))
  exact ⟨a, mem_of_mem_dedup ha1, mem_of_mem_dedup ha2⟩

/-! ## The chain's exit: one_leader_per_term
(`OneLeaderPerTermInterface.v` / `OneLeaderPerTermProof.v`) -/

/- `one_leader_per_term` itself (`OneLeaderPerTermInterface.v:8-13`) was
already ported by the P1 statement arc — `Properties.lean:27` — together
with the named transfer target `OneLeaderPerTermStatement`. This chain
PROVES that statement natively (design note §9's translate-don't-certify
route). -/

/-- `OneLeaderPerTermProof.v:25-54` (`one_leader_per_term_invariant'`):
the ghost-level core — two same-term leaders share a voter, who voted
once per term. -/
theorem one_leader_per_term_ghost :
    ∀ net, refined_raft_intermediate_reachable (P := P) net →
      one_leader_per_term (deghost net) := by
  intro net hreach
  obtain ⟨hovpt, -, -⟩ := votes_correct_invariant net hreach
  obtain ⟨hvrc, hcv, -, hvrl⟩ := cronies_correct_invariant net hreach
  intro h h' hct hty hty'
  have hw : wonElection (dedup (net.nwState h).2.votesReceived) = true :=
    hvrl h hty
  have hw' : wonElection (dedup (net.nwState h').2.votesReceived) = true :=
    hvrl h' hty'
  obtain ⟨crony, hc1, hc2⟩ := wonElection_one_in_common _ _ hw hw'
  have hcr1 : crony ∈ (net.nwState h).1.cronies (net.nwState h).2.currentTerm :=
    hvrc h crony hc1 (Or.inl hty)
  have hcr2 : crony ∈ (net.nwState h').1.cronies (net.nwState h').2.currentTerm :=
    hvrc h' crony hc2 (Or.inl hty')
  have hv1 : ((net.nwState h).2.currentTerm, h) ∈ (net.nwState crony).1.votes :=
    hcv _ h crony hcr1
  have hv2 : ((net.nwState h').2.currentTerm, h') ∈ (net.nwState crony).1.votes :=
    hcv _ h' crony hcr2
  have hcteq : (net.nwState h).2.currentTerm = (net.nwState h').2.currentTerm := hct
  rw [← hcteq] at hv2
  exact hovpt crony _ h h' hv1 hv2

/-- `OneLeaderPerTermProof.v:56-67` (`one_leader_per_term_invariant`) —
ELECTION SAFETY, delivered at the BASE layer through `lower_prop`: in
every reachable network, at most one leader per term. The statement
mentions no ghost state (constitution §3.2). -/
theorem one_leader_per_term_invariant :
    ∀ net, raft_intermediate_reachable (P := P) net →
      one_leader_per_term net :=
  lower_prop one_leader_per_term one_leader_per_term_ghost

/-- The P1 arc's declared transfer target for election safety
(`Properties.lean`, `OneLeaderPerTermStatement`) — discharged NATIVELY,
as the §9 ruling directs: what Verdi proved, re-proved in Lean over the
ported spec. -/
theorem oneLeaderPerTermStatement_holds :
    OneLeaderPerTermStatement P :=
  one_leader_per_term_invariant

end ElectionSafety

end Raft
end VerdiCompat
