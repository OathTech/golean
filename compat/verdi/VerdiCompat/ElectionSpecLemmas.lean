import VerdiCompat.RefinedProofStructure

/-!
# Handler and ghost-update spec lemmas for the election-safety chain

Ports of the slices of `deps/verdi-raft/theories/Raft/SpecLemmas.v` and
`Raft/RefinementSpecLemmas.v` (@ a3375e8) that the election-safety chain
actually uses (campaign Arc 3 unit 2; design doc
`docs/2026-08-22_campaign-arc3-refined-port-design.md` §3-§4 — helpers
ported on demand only). Style note (recorded in the arc log): where
upstream proves many single-fact lemmas per handler, we prove ONE
comprehensive cases lemma per handler capturing every fact the chain
needs, each docstring citing the upstream lemmas it subsumes. The
upstream statements are recoverable as one-line corollaries; the case
analysis is done once per handler instead of once per fact.
-/

namespace VerdiCompat
namespace Raft

section ElectionSpecLemmas
variable {P : BaseParams} [R : RaftParams P]

/-! ## Base handler facts (`SpecLemmas.v`) -/

/-- `advanceCurrentTerm` either leaves term/vote/type alone or strictly
advances the term, clearing the vote and demoting to follower. Log and
votesReceived are never touched. -/
theorem advanceCurrentTerm_spec (st : raft_data (P := P)) (t : term) :
    (advanceCurrentTerm st t).votesReceived = st.votesReceived ∧
    (advanceCurrentTerm st t).log = st.log ∧
    (((advanceCurrentTerm st t).currentTerm = st.currentTerm ∧
      (advanceCurrentTerm st t).votedFor = st.votedFor ∧
      (advanceCurrentTerm st t).type = st.type) ∨
     (st.currentTerm < (advanceCurrentTerm st t).currentTerm ∧
      (advanceCurrentTerm st t).votedFor = none ∧
      (advanceCurrentTerm st t).type = .Follower)) := by
  unfold advanceCurrentTerm
  split
  · rename_i hlt
    simp at hlt
    exact ⟨rfl, rfl, Or.inr ⟨hlt, rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- Subsumes `handleClientRequest_type` / `_currentTerm` (`SpecLemmas.v:577`)
/ `_term_votedFor` (`:1235`) and the packet fact behind
`handleClientRequest_rvr` (`CroniesCorrectProof.v:27`): a client request
never changes type/term/vote/votesReceived and sends NO packets. -/
theorem handleClientRequest_spec (me : name (P := P)) (st : raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out st' l}
    (h : handleClientRequest me st client id c = (out, st', l)) :
    st'.type = st.type ∧ st'.currentTerm = st.currentTerm ∧
    st'.votedFor = st.votedFor ∧ st'.votesReceived = st.votesReceived ∧
    l = [] := by
  unfold handleClientRequest at h
  split at h <;>
    (simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h; simp_all)

/-- Subsumes `handleTimeout_currentTerm` (`SpecLemmas.v:120`),
`handleTimeout_same_term_votedFor_preserved`
(`RefinementSpecLemmas.v:58`), and the packet fact behind
`handleTimeout_rvr`: a timeout either heartbeats (state unchanged except
`shouldSend`) or starts a candidacy at term+1 voting for self; only
RequestVote messages are sent. -/
theorem handleTimeout_spec (me : name (P := P)) (st : raft_data (P := P))
    {out st' l} (h : handleTimeout me st = (out, st', l)) :
    st'.log = st.log ∧
    ((st'.currentTerm = st.currentTerm ∧ st'.type = st.type ∧
      st'.votedFor = st.votedFor ∧ st'.votesReceived = st.votesReceived) ∨
     (st'.currentTerm = st.currentTerm + 1 ∧ st'.type = .Candidate ∧
      st'.votedFor = some me ∧ st'.votesReceived = [me] ∧
      st.type ≠ .Leader)) ∧
    (∀ q ∈ l, ∃ t' cid lli llt, q.2 = msg.RequestVote (P := P) t' cid lli llt) := by
  unfold handleTimeout tryToBecomeLeader at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h
  · exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl, rfl⟩, by simp⟩
  · rename_i hnotLeader
    refine ⟨rfl, Or.inr ⟨rfl, rfl, rfl, rfl, fun heq => hnotLeader heq⟩, ?_⟩
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨node, -, rfl⟩ := hq
    exact ⟨_, _, _, _, rfl⟩

/-- Subsumes `handleAppendEntries_currentTerm` (`SpecLemmas.v:100`),
`handleAppendEntries_same_term_votedFor_preserved` (`:48`),
`handleAppendEntries_term_votedFor` (`:1248`), the type/votesReceived
facts used by `cronies_correct_append_entries`, and the reply shape
behind `handleAppendEntries_rvr`. -/
theorem handleAppendEntries_spec (me : name (P := P)) (st : raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m)) :
    st'.votesReceived = st.votesReceived ∧
    ((st'.currentTerm = st.currentTerm ∧ st'.votedFor = st.votedFor) ∨
     (st.currentTerm < st'.currentTerm ∧ st'.votedFor = none)) ∧
    (st'.type = st.type ∨ st'.type = .Follower) ∧
    ∃ t' es' r, m = msg.AppendEntriesReply (P := P) t' es' r := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals
    simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals
    first
    | exact ⟨rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl, _, _, _, rfl⟩
    | · obtain ⟨hvr, -, hcases⟩ := hadv
        refine ⟨hvr, ?_, Or.inr rfl, _, _, _, rfl⟩
        rcases hcases with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩

/-- Subsumes `handleAppendEntriesReply_currentTerm` (`SpecLemmas.v:91`),
`handleAppendEntriesReply_same_term_votedFor_preserved` (`:60`),
`handleAppendEntriesReply_term_votedFor` (`:1258`), and the packet fact
behind `handleAppendEntriesReply_rvr`: no messages at all are sent. -/
theorem handleAppendEntriesReply_spec (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term)
    (es : List (entry (P := P))) (r : Bool) {st' l}
    (h : handleAppendEntriesReply me st src t es r = (st', l)) :
    st'.votesReceived = st.votesReceived ∧
    ((st'.currentTerm = st.currentTerm ∧ st'.votedFor = st.votedFor ∧
      st'.type = st.type) ∨
     (st.currentTerm < st'.currentTerm ∧ st'.votedFor = none ∧
      st'.type = .Follower)) ∧
    l = [] := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntriesReply at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals first
    | exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩
    | (obtain ⟨hvr, -, hcases⟩ := hadv
       exact ⟨hvr, hcases.imp id id, rfl⟩)

/-- Subsumes `handleRequestVote_currentTerm` (`SpecLemmas.v:336`),
`handleRequestVote_votesReceived` (`CroniesCorrectProof.v:219`),
`handleRequestVote_currentTerm_same_or_follower`
(`CroniesCorrectProof.v:228`), `handleRequestVote_votedFor`
(`SpecLemmas.v:8`) and `handleRequestVote_currentTerm_votedFor`
(`:312`). -/
theorem handleRequestVote_spec (me : name (P := P)) (st : raft_data (P := P))
    (t : term) (cand : name (P := P)) (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m)) :
    st'.votesReceived = st.votesReceived ∧
    st.currentTerm ≤ st'.currentTerm ∧
    ((st'.currentTerm = st.currentTerm ∧ st'.type = st.type) ∨
     st'.type = .Follower) ∧
    (st'.currentTerm = st.currentTerm →
      st'.votedFor = st.votedFor ∨
      (st.votedFor = none ∧ st'.votedFor = some cand)) := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals obtain ⟨hvr, -, hcases⟩ := hadv
  all_goals
    rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  all_goals simp_all
  all_goals exact ⟨Nat.le_of_lt h1, fun heq => absurd heq (Ne.symm (Nat.ne_of_lt h1))⟩

/-- `handleRequestVote_reply_true` (`SpecLemmas.v:1281`) +
`handleRequestVote_true_votedFor` (`CroniesCorrectProof.v:199`): a `true`
grant reports the voter's (new) current term and records the vote. -/
theorem handleRequestVote_reply_true (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' t'}
    (h : handleRequestVote me st t cand lli llt
          = (st', .RequestVoteReply t' true)) :
    st'.currentTerm = t' ∧ st'.votedFor = some cand := by
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  -- reject: reply false — contradiction
  · simp at h
  -- grant (no prior vote): votedFor := cand, reply true at the new term
  · simp only [Prod.mk.injEq, msg.RequestVoteReply.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  -- repeat grant: reply (decide (cand = c')) = true forces cand = c'
  · rename_i heq
    simp at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, heq⟩
  -- refuse: reply false — contradiction
  · simp at h

/-- Subsumes `handleRequestVoteReply_currentTerm'` (`SpecLemmas.v:325`),
`handleRequestVoteReply_term_votedFor_cases` (`:35`),
`handleRequestVoteReply_term_votedFor` (`:1268`),
`handleRequestVoteReply_candidate` (`CroniesCorrectProof.v:313`),
`handleRequestVoteReply_votesReceived` (`:324`), and
`handleRequestVoteReply_leader` (`:335`). -/
theorem handleRequestVoteReply_spec (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term) (v : Bool) {st'}
    (h : handleRequestVoteReply me st src t v = st') :
    ((st'.currentTerm = st.currentTerm ∧ st'.votedFor = st.votedFor) ∨
     (st.currentTerm < st'.currentTerm ∧ st'.votedFor = none)) ∧
    (∀ crony ∈ st'.votesReceived,
      (crony = src ∧ v = true ∧ st'.currentTerm = t) ∨
      crony ∈ st.votesReceived) ∧
    (st'.type = .Candidate → st.type = .Candidate ∧
      st'.currentTerm = st.currentTerm) ∧
    (st'.type = .Leader →
      st' = st ∨
      (st.type = .Candidate ∧
       wonElection (dedup st'.votesReceived) = true ∧
       st'.currentTerm = st.currentTerm)) := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleRequestVoteReply at h
  simp only [] at h
  split at h
  -- branch: t > currentTerm — step down to follower at the advanced term
  · subst h
    obtain ⟨hvr, -, hcases⟩ := hadv
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hcases with ⟨a, b, -⟩ | ⟨a, b, -⟩
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr ⟨a, b⟩
    · intro crony hc
      right
      rw [← hvr]
      exact hc
    · intro hty
      exact nomatch hty
    · intro hty
      exact nomatch hty
  · split at h
    -- branch: t < currentTerm — stale reply ignored
    · subst h
      exact ⟨Or.inl ⟨rfl, rfl⟩, fun _ hc => Or.inr hc, fun hty => ⟨hty, rfl⟩,
        fun _ => Or.inl rfl⟩
    · split at h
      -- branch: t = currentTerm, candidate — tally the vote
      · rename_i hgt hlt _sv hty
        subst h
        have hteq : st.currentTerm = t := by
          simp at hgt hlt
          exact Nat.le_antisymm hlt hgt
        refine ⟨Or.inl ⟨rfl, rfl⟩, ?_, fun _ => ⟨hty, rfl⟩, ?_⟩
        · intro crony hc
          replace hc : crony ∈ (if v then [src] else []) ++ st.votesReceived := hc
          rcases List.mem_append.mp hc with hc | hc
          · split at hc
            · rename_i hv
              simp at hc
              exact Or.inl ⟨hc, hv, hteq⟩
            · simp at hc
          · exact Or.inr hc
        · intro hld
          replace hld : (if v && wonElection (dedup (src :: st.votesReceived)) then
              serverType.Leader else st.type) = serverType.Leader := hld
          split at hld
          · rename_i hwon
            simp only [Bool.and_eq_true] at hwon
            right
            refine ⟨hty, ?_, rfl⟩
            show wonElection (dedup ((if v then [src] else []) ++ st.votesReceived)) = true
            rw [hwon.1]
            exact hwon.2
          · rw [hty] at hld
            exact nomatch hld
      -- branch: t = currentTerm, non-candidate — ignored
      · subst h
        exact ⟨Or.inl ⟨rfl, rfl⟩, fun _ hc => Or.inr hc, fun hty => ⟨hty, rfl⟩,
          fun _ => Or.inl rfl⟩

/-- Subsumes `doLeader_currentTerm` (`SpecLemmas.v:82`),
`doLeader_term_votedFor` (`:1208`), `doLeader_st`
(`CroniesCorrectProof.v:497`), and the packet fact behind `do_leader_rvr`
(`:510`): `doLeader` touches only commit/replication bookkeeping, and
sends only AppendEntries messages. -/
theorem doLeader_spec (st : raft_data (P := P)) (me : name (P := P)) {os st' ms}
    (h : doLeader st me = (os, st', ms)) :
    st'.currentTerm = st.currentTerm ∧ st'.votedFor = st.votedFor ∧
    st'.type = st.type ∧ st'.votesReceived = st.votesReceived ∧
    st'.log = st.log ∧
    (∀ q ∈ ms, ∃ t' lid pli plt es ci,
      q.2 = msg.AppendEntries (P := P) t' lid pli plt es ci) := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, rfl⟩ := h
  all_goals refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  all_goals intro q hq
  all_goals first
    | (simp only [List.mem_map] at hq
       obtain ⟨node, -, rfl⟩ := hq
       exact ⟨_, _, _, _, _, _, rfl⟩)
    | simp at hq

section WithO
variable [O : OneNodeParams P]

/-- `cacheApplyEntry` touches only the client cache and the state
machine. -/
theorem cacheApplyEntry_spec (st : raft_data (P := P)) (e : entry (P := P))
    {o st'} (h : cacheApplyEntry st e = (o, st')) :
    st'.log = st.log ∧ st'.type = st.type ∧
    st'.currentTerm = st.currentTerm ∧
    st'.votesReceived = st.votesReceived ∧ st'.votedFor = st.votedFor ∧
    st'.commitIndex = st.commitIndex ∧ st'.lastApplied = st.lastApplied := by
  unfold cacheApplyEntry applyEntry at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl⟩ := h
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `use_applyEntries_spec`'s content (`SpecLemmas.v` applyEntries_spec):
`applyEntries` only applies commands and fills the client cache. -/
theorem applyEntries_spec (me : name (P := P)) :
    ∀ (es : List (entry (P := P))) (st : raft_data (P := P)) {o st'},
    applyEntries me st es = (o, st') →
    st'.log = st.log ∧ st'.type = st.type ∧
    st'.currentTerm = st.currentTerm ∧
    st'.votesReceived = st.votesReceived ∧ st'.votedFor = st.votedFor ∧
    st'.commitIndex = st.commitIndex ∧ st'.lastApplied = st.lastApplied := by
  intro es
  induction es with
  | nil =>
    intro st o st' h
    unfold applyEntries at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
    obtain ⟨a1, b1, c1, d1, e1, f1, g1⟩ := cacheApplyEntry_spec st e hce
    obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := ih st1 hae
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1,
      f2.trans f1, g2.trans g1⟩

/-- Subsumes `doGenericServer_currentTerm` (`SpecLemmas.v:70`),
`doGenericServer_log_type_term_votesReceived` (`:1219`), and the packet
fact behind `do_generic_server_pkts` (`CroniesCorrectProof.v:572`): no
messages at all. -/
theorem doGenericServer_spec (me : name (P := P)) (st : raft_data (P := P))
    {os st' ms} (h : doGenericServer me st = (os, st', ms)) :
    st'.log = st.log ∧ st'.type = st.type ∧
    st'.currentTerm = st.currentTerm ∧
    st'.votesReceived = st.votesReceived ∧ st'.votedFor = st.votedFor ∧
    ms = [] := by
  unfold doGenericServer at h
  rcases hae : applyEntries me st
      ((findGtIndex st.log st.lastApplied).filter
        (fun x => (st.lastApplied <? x.eIndex) && (x.eIndex <=? st.commitIndex))).reverse
    with ⟨o1, st1⟩
  rw [hae] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  obtain ⟨a1, b1, c1, d1, e1, -, -⟩ := applyEntries_spec me _ st hae
  exact ⟨a1, b1, c1, d1, e1, rfl⟩

end WithO

/-! ## Ghost-update facts (`RefinementSpecLemmas.v`), votes-focused -/

/-- `votes_update_elections_data_client_request`
(`RefinementSpecLemmas.v:130`) + `votesWithLog_same_client_request`
(`:139`) + the cronies/leaderLogs analogues used by
`cronies_correct_client_request`: only `allEntries` can change. -/
theorem update_elections_data_client_request_ghost (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) (client : R.clientId)
    (id : Nat) (c : P.input) :
    (update_elections_data_client_request me st client id c).votes = st.1.votes ∧
    (update_elections_data_client_request me st client id c).votesWithLog
      = st.1.votesWithLog ∧
    (update_elections_data_client_request me st client id c).cronies = st.1.cronies ∧
    (update_elections_data_client_request me st client id c).leaderLogs
      = st.1.leaderLogs := by
  unfold update_elections_data_client_request
  simp only []
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- `votes_same_append_entries` (`RefinementSpecLemmas.v:34`) + the
votesWithLog/cronies/leaderLogs analogues: only `allEntries` can
change. -/
theorem update_elections_data_appendEntries_ghost (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) (t : term)
    (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) :
    (update_elections_data_appendEntries me st t lid pli plt es ci).votes
      = st.1.votes ∧
    (update_elections_data_appendEntries me st t lid pli plt es ci).votesWithLog
      = st.1.votesWithLog ∧
    (update_elections_data_appendEntries me st t lid pli plt es ci).cronies
      = st.1.cronies ∧
    (update_elections_data_appendEntries me st t lid pli plt es ci).leaderLogs
      = st.1.leaderLogs := by
  unfold update_elections_data_appendEntries
  simp only []
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- `votes_update_elections_data_request_vote_reply_eq`
(`RefinementSpecLemmas.v:67`) + votesWithLog/allEntries analogues: a
RequestVoteReply never touches `votes`/`votesWithLog`/`allEntries`. -/
theorem update_elections_data_requestVoteReply_votes (me src : name (P := P))
    (t : term) (v : Bool) (st : electionsData (P := P) × raft_data (P := P)) :
    (update_elections_data_requestVoteReply me src t v st).votes = st.1.votes ∧
    (update_elections_data_requestVoteReply me src t v st).votesWithLog
      = st.1.votesWithLog ∧
    (update_elections_data_requestVoteReply me src t v st).allEntries
      = st.1.allEntries := by
  unfold update_elections_data_requestVoteReply
  simp only []
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- `update_elections_data_requestVote_cronies`
(`CroniesCorrectProof.v:209`) + the leaderLogs/allEntries analogues: a
RequestVote touches only `votes`/`votesWithLog`. -/
theorem update_elections_data_requestVote_cronies (me src : name (P := P))
    (t : term) (cand : name (P := P)) (lli : logIndex) (llt : term)
    (st : electionsData (P := P) × raft_data (P := P)) :
    (update_elections_data_requestVote me src t cand lli llt st).cronies
      = st.1.cronies ∧
    (update_elections_data_requestVote me src t cand lli llt st).leaderLogs
      = st.1.leaderLogs ∧
    (update_elections_data_requestVote me src t cand lli llt st).allEntries
      = st.1.allEntries := by
  unfold update_elections_data_requestVote
  simp only []
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- `votes_update_elections_data_request_vote`
(`RefinementSpecLemmas.v:11`): a vote in the updated ghost state is an
old vote or the vote the handler just granted (at the handler's new
term). -/
theorem update_elections_data_requestVote_votes_elim
    {me src : name (P := P)} {t : term} {cand : name (P := P)}
    {lli : logIndex} {llt : term}
    {st : electionsData (P := P) × raft_data (P := P)} {st' m}
    (h : handleRequestVote me st.2 t cand lli llt = (st', m))
    {t' : term} {h' : name (P := P)}
    (hin : (t', h') ∈
      (update_elections_data_requestVote me src t cand lli llt st).votes) :
    (t', h') ∈ st.1.votes ∨ (t' = st'.currentTerm ∧ st'.votedFor = some h') := by
  unfold update_elections_data_requestVote at hin
  rw [h] at hin
  simp only [] at hin
  repeat' split at hin
  all_goals first
    | exact Or.inl hin
    | (rcases List.mem_cons.mp hin with heq | hin
       · injection heq with h1 h2
         subst h1
         subst h2
         exact Or.inr ⟨rfl, by assumption⟩
       · exact Or.inl hin)

/-- `votes_update_elections_data_request_vote_intro_old`
(`RefinementSpecLemmas.v:95`): old votes survive the update. -/
theorem update_elections_data_requestVote_votes_old (me src : name (P := P))
    (t : term) (cand : name (P := P)) (lli : logIndex) (llt : term)
    (st : electionsData (P := P) × raft_data (P := P))
    {t' : term} {h' : name (P := P)} (hin : (t', h') ∈ st.1.votes) :
    (t', h') ∈
      (update_elections_data_requestVote me src t cand lli llt st).votes := by
  unfold update_elections_data_requestVote
  simp only []
  repeat' split
  all_goals first
    | exact hin
    | exact List.mem_cons_of_mem _ hin

/-- `votes_update_elections_data_request_vote_intro`
(`RefinementSpecLemmas.v:78`): a genuinely NEW grant (term advanced, or
no prior vote this term) is recorded in the ghost `votes`. -/
theorem update_elections_data_requestVote_votes_intro
    {me src : name (P := P)} {t : term} {cand : name (P := P)}
    {lli : logIndex} {llt : term}
    {st : electionsData (P := P) × raft_data (P := P)} {st' m}
    (h : handleRequestVote me st.2 t cand lli llt = (st', m))
    {h' : name (P := P)} (hvf : st'.votedFor = some h')
    (hnew : st.2.currentTerm < st'.currentTerm ∨ st.2.votedFor = none) :
    (st'.currentTerm, h') ∈
      (update_elections_data_requestVote me src t cand lli llt st).votes := by
  have hspec := handleRequestVote_spec me st.2 t cand lli llt h
  unfold update_elections_data_requestVote
  rw [h]
  simp only [] at *
  repeat' split
  -- fresh grant (no prior vote): recorded at the head
  · rename_i hnone hsome
    rw [hsome] at hvf
    injection hvf with hvf
    subst hvf
    exact List.mem_cons_self ..
  -- unchanged re-grant (same term, same vote): contradicts hnew
  · rename_i hsome hsome' heqb
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at heqb
    rcases hnew with hlt | hnone
    · exact absurd heqb.1 (Nat.ne_of_lt hlt)
    · rw [hnone] at hsome
      cases hsome
  -- changed vote: recorded at the head
  · rename_i hsome hsome' hneqb
    rw [hsome'] at hvf
    injection hvf with hvf
    subst hvf
    exact List.mem_cons_self ..
  -- no vote in st': contradicts hvf
  · rename_i hfun1 hfun2
    exfalso
    rcases hcase : st.2.votedFor with _ | c
    · exact hfun1 _ hcase hvf
    · exact hfun2 _ _ hcase hvf

/-- `votes_update_elections_data_timeout`
(`RefinementSpecLemmas.v:120`) strengthened with the votedFor fact of
`votes_update_elections_data_timeout_votedFor` (`:43`). -/
theorem update_elections_data_timeout_votes_elim
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l))
    {t' : term} {h' : name (P := P)}
    (hin : (t', h') ∈ (update_elections_data_timeout me st).votes) :
    (t', h') ∈ st.1.votes ∨ (t' = st'.currentTerm ∧ st'.votedFor = some h') := by
  unfold update_elections_data_timeout at hin
  rw [h] at hin
  simp only [] at hin
  repeat' split at hin
  all_goals first
    | exact Or.inl hin
    | (rcases List.mem_cons.mp hin with heq | hin
       · injection heq with h1 h2
         subst h1
         subst h2
         exact Or.inr ⟨rfl, by assumption⟩
       · exact Or.inl hin)

/-- `update_elections_data_timeout_votes_intro_new`
(`RefinementSpecLemmas.v:106`): after a timeout, the (term, votedFor)
pair of the new state is in the ghost `votes` — either it was just
recorded, or the state is unchanged and the old invariant supplies it. -/
theorem update_elections_data_timeout_votes_intro
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l))
    (hold : ∀ (tt : term) (hh : name (P := P)),
      tt = st.2.currentTerm → st.2.votedFor = some hh → (tt, hh) ∈ st.1.votes)
    {h' : name (P := P)} (hvf : st'.votedFor = some h') :
    (st'.currentTerm, h') ∈ (update_elections_data_timeout me st).votes := by
  have hspec := handleTimeout_spec me st.2 h
  unfold update_elections_data_timeout
  rw [h]
  simp only []
  repeat' split
  all_goals first
    | -- ghost unchanged (the node was a leader, the handler a no-op):
      -- the old invariant supplies the vote
      (rename_i hsome hleader
       obtain ⟨-, hcases, -⟩ := hspec
       rcases hcases with ⟨hct, -, hvf', -⟩ | ⟨-, -, -, -, hne⟩
       · rw [hct]
         exact hold _ _ rfl (hvf'.symm.trans hvf)
       · exact absurd hleader hne)
    | -- new candidacy: recorded at the head (or hvf contradicts
      -- st'.votedFor = none) — both closed by congruence
      simp_all

end ElectionSpecLemmas

end Raft
end VerdiCompat
