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

/-- The candidacy branch of `handleTimeout`, forced by the trigger: a
non-leader that times out becomes a candidate at term+1 voting for
itself (the correlation `RefinementSpecLemmas.v`'s Ltac extracts from
the shared scrutinee). -/
theorem handleTimeout_not_leader (me : name (P := P)) (st : raft_data (P := P))
    {out st' l} (h : handleTimeout me st = (out, st', l))
    (hnl : st.type ≠ .Leader) :
    st'.currentTerm = st.currentTerm + 1 ∧ st'.type = .Candidate ∧
    st'.votedFor = some me ∧ st'.votesReceived = [me] := by
  unfold handleTimeout tryToBecomeLeader at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h
  · rename_i heq
    exact absurd heq hnl
  · exact ⟨rfl, rfl, rfl, rfl⟩

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

/-- Branch correlation the blanket spec loses: an AppendEntries that
leaves the receiver a candidate or leader was REJECTED — the state is
untouched (accept branches always demote to follower). -/
theorem handleAppendEntries_reject_of_not_follower (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (lid : name (P := P)) (pli : logIndex)
    (plt : term) (es : List (entry (P := P))) (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m))
    (hty : st'.type ≠ .Follower) : st' = st := by
  unfold handleAppendEntries at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals first
    | rfl
    | exact absurd rfl hty

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
    (t', h') ∈ st.1.votes ∨
    (t' = st'.currentTerm ∧ t' = st.2.currentTerm + 1 ∧
     st'.votedFor = some h') := by
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
         rename_i hnl _ _
         have hcand := handleTimeout_not_leader me st.2 h (fun heq => hnl heq)
         exact Or.inr ⟨rfl, hcand.1 ▸ rfl, by assumption⟩
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

/-! ## Ghost-update facts, cronies-focused (for `CroniesCorrectProof.v`) -/

/-- Old votes survive a timeout's ghost update. -/
theorem update_elections_data_timeout_votes_old (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    {t' : term} {h' : name (P := P)} (hin : (t', h') ∈ st.1.votes) :
    (t', h') ∈ (update_elections_data_timeout me st).votes := by
  unfold update_elections_data_timeout
  simp only []
  repeat' split
  all_goals first
    | exact hin
    | exact List.mem_cons_of_mem _ hin

/-- A crony in the timeout-updated ghost is an old crony, or the snapshot
of the fresh candidacy (which implies the node was not a leader). -/
theorem update_elections_data_timeout_cronies_elim
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l))
    {tm : term} {crony : name (P := P)}
    (hin : crony ∈ (update_elections_data_timeout me st).cronies tm) :
    crony ∈ st.1.cronies tm ∨
    (tm = st'.currentTerm ∧ crony ∈ st'.votesReceived ∧
     st.2.type ≠ .Leader) := by
  unfold update_elections_data_timeout at hin
  rw [h] at hin
  simp only [] at hin
  repeat' split at hin
  all_goals first
    | exact Or.inl hin
    | (simp only [] at hin
       rename_i hnl _
       split at hin
       · rename_i heqtm
         exact Or.inr ⟨heqtm, hin, fun he => hnl he⟩
       · exact Or.inl hin)

/-- A leader's timeout (heartbeat) leaves the ghost cronies unchanged. -/
theorem update_elections_data_timeout_cronies_leader (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    (hl : st.2.type = .Leader) :
    (update_elections_data_timeout me st).cronies = st.1.cronies := by
  unfold update_elections_data_timeout
  simp only []
  repeat' split
  all_goals first
    | rfl
    | (rename_i _ hnl
       exact absurd hl hnl)
    | (rename_i hnl _
       exact absurd hl hnl)

/-- A non-leader's timeout snapshots the fresh candidacy's votesReceived
into cronies at the new term. -/
theorem update_elections_data_timeout_cronies_intro
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l)) (hnl : st.2.type ≠ .Leader) :
    (update_elections_data_timeout me st).cronies st'.currentTerm
      = st'.votesReceived := by
  obtain ⟨-, hty, hvf, -⟩ := handleTimeout_not_leader me st.2 h hnl
  unfold update_elections_data_timeout
  rw [h]
  simp only []
  repeat' split
  all_goals first
    | (rename_i hleader
       exact absurd hleader hnl)
    | (rename_i hnone
       rw [hnone] at hvf
       cases hvf)
    | simp

/-- A crony in the RequestVoteReply-updated ghost is an old crony or a
member of the (possibly updated) votesReceived snapshot at the current
term. -/
theorem update_elections_data_requestVoteReply_cronies_elim
    {me src : name (P := P)} {t0 : term} {v : Bool}
    {st : electionsData (P := P) × raft_data (P := P)}
    {tm : term} {crony : name (P := P)}
    (hin : crony ∈ (update_elections_data_requestVoteReply me src t0 v st).cronies tm) :
    crony ∈ st.1.cronies tm ∨
    (tm = (handleRequestVoteReply me st.2 src t0 v).currentTerm ∧
     crony ∈ (handleRequestVoteReply me st.2 src t0 v).votesReceived ∧
     (handleRequestVoteReply me st.2 src t0 v).type ≠ .Follower) := by
  unfold update_elections_data_requestVoteReply at hin
  simp only [] at hin
  repeat' split at hin
  all_goals first
    | exact Or.inl hin
    | (simp only [] at hin
       split at hin
       · rename_i heqtm
         exact Or.inr ⟨heqtm, hin, by simp_all⟩
       · exact Or.inl hin)

/-- A reply that leaves the node a candidate or leader snapshots its
votesReceived into cronies at its current term. -/
theorem update_elections_data_requestVoteReply_cronies_intro
    {me src : name (P := P)} {t0 : term} {v : Bool}
    {st : electionsData (P := P) × raft_data (P := P)}
    (hty : (handleRequestVoteReply me st.2 src t0 v).type ≠ .Follower) :
    (update_elections_data_requestVoteReply me src t0 v st).cronies
        (handleRequestVoteReply me st.2 src t0 v).currentTerm
      = (handleRequestVoteReply me st.2 src t0 v).votesReceived := by
  unfold update_elections_data_requestVoteReply
  simp only []
  repeat' split
  all_goals first
    | (rename_i hf
       exact absurd hf hty)
    | simp

/-! ## Log- and message-shape facts (for `TermSanityProof.v` and
`CandidateEntriesProof.v`) -/

/-- `findGtIndex_in` (`CommonTheorems.v:326`). -/
theorem findGtIndex_in {e : entry (P := P)} :
    ∀ {l : List (entry (P := P))} {i : logIndex}, e ∈ findGtIndex l i → e ∈ l := by
  intro l
  induction l with
  | nil => exact fun h => nomatch h
  | cons a as ih =>
    intro i h
    unfold findGtIndex at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)
    · exact nomatch h

/-- `removeAfterIndex_in` (`CommonTheorems.v:112`). -/
theorem removeAfterIndex_in {e : entry (P := P)} :
    ∀ {l : List (entry (P := P))} {i : logIndex},
      e ∈ removeAfterIndex l i → e ∈ l := by
  intro l
  induction l with
  | nil => exact fun h => nomatch h
  | cons a as ih =>
    intro i h
    unfold removeAfterIndex at h
    split at h
    · exact h
    · exact List.mem_cons_of_mem _ (ih h)

/-- If the term does not go backwards, `advanceCurrentTerm` lands exactly
on the incoming term. -/
theorem advanceCurrentTerm_le_eq {st : raft_data (P := P)} {t : term}
    (hle : st.currentTerm ≤ t) : (advanceCurrentTerm st t).currentTerm = t := by
  unfold advanceCurrentTerm
  split
  · rfl
  · rename_i hnlt
    simp at hnlt
    exact Nat.le_antisymm hle hnlt

/-- `advanceCurrentTerm_same_or_type_follower`
(`CandidateEntriesProof.v:351`). -/
theorem advanceCurrentTerm_same_or_follower (st : raft_data (P := P)) (t : term) :
    advanceCurrentTerm st t = st ∨ (advanceCurrentTerm st t).type = .Follower := by
  unfold advanceCurrentTerm
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- `handleClientRequest_spec`'s log clause (`CandidateEntriesProof.v:16`,
`TermSanityProof.v` client_request case): a new entry carries the
leader's current term. -/
theorem handleClientRequest_log (me : name (P := P)) (st : raft_data (P := P))
    (client : R.clientId) (id : Nat) (c : P.input) {out st' l}
    (h : handleClientRequest me st client id c = (out, st', l)) :
    ∀ e ∈ st'.log, e ∈ st.log ∨ (e.eTerm = st.currentTerm ∧ st.type = .Leader) := by
  unfold handleClientRequest at h
  split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl, -⟩ := h
  · rename_i hty
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inr ⟨rfl, hty⟩
    · exact Or.inl he
  · exact fun e he => Or.inl he

/-- `handleAppendEntries_spec`'s log clause (`TermSanityProof.v`,
`CandidateEntriesProof.v:197`): every entry of the new log is old or
came in with the (accepted) message's term. -/
theorem handleAppendEntries_log (me : name (P := P)) (st : raft_data (P := P))
    (t : term) (lid : name (P := P)) (pli : logIndex) (plt : term)
    (es : List (entry (P := P))) (ci : logIndex) {st' m}
    (h : handleAppendEntries me st t lid pli plt es ci = (st', m)) :
    ∀ e ∈ st'.log, e ∈ st.log ∨ (e ∈ es ∧ st'.currentTerm = t) := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntries at h
  split at h
  · -- rejected: state unchanged
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun e he => Or.inl he
  · rename_i hnle
    simp at hnle
    have hct : (advanceCurrentTerm st t).currentTerm = t :=
      advanceCurrentTerm_le_eq hnle
    repeat' split at h
    all_goals simp only [Prod.mk.injEq] at h
    all_goals obtain ⟨rfl, rfl⟩ := h
    all_goals intro e he
    all_goals first
      | exact Or.inl he
      | (left
         show e ∈ st.log
         rw [← hadv.2.1]
         exact he)
      | exact Or.inr ⟨he, hct⟩
      | (rcases List.mem_append.mp he with he | he
         · exact Or.inr ⟨he, hct⟩
         · exact Or.inl (removeAfterIndex_in he))

/-- Log preservation for the three handlers that never touch it. -/
theorem handleRequestVote_log (me : name (P := P)) (st : raft_data (P := P))
    (t : term) (cand : name (P := P)) (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m)) :
    st'.log = st.log := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | rfl
    | exact hadv.2.1

theorem handleAppendEntriesReply_log (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term)
    (es : List (entry (P := P))) (r : Bool) {st' l}
    (h : handleAppendEntriesReply me st src t es r = (st', l)) :
    st'.log = st.log := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleAppendEntriesReply at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -⟩ := h
  all_goals first
    | rfl
    | exact hadv.2.1

theorem handleRequestVoteReply_log (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term) (v : Bool) :
    (handleRequestVoteReply me st src t v).log = st.log := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleRequestVoteReply
  simp only []
  repeat' split
  all_goals first
    | rfl
    | exact hadv.2.1

/-- `handleRequestVote` replies only with `RequestVoteReply`. -/
theorem handleRequestVote_reply_shape (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m)) :
    ∃ t' v, m = msg.RequestVoteReply (P := P) t' v := by
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, rfl⟩ := h
  all_goals exact ⟨_, _, rfl⟩

/-- `doLeader_in_entries`'s content (`CandidateEntriesProof.v:465`) plus
the term shape needed by `TermSanityProof.v`'s do_leader case: every sent
AppendEntries carries the sender's current term and entries from its own
log. -/
theorem doLeader_messages (st : raft_data (P := P)) (me : name (P := P))
    {os st' ms} (h : doLeader st me = (os, st', ms)) :
    ∀ q ∈ ms, ∃ pi pt ci es,
      q.2 = msg.AppendEntries (P := P) st.currentTerm me pi pt es ci ∧
      ∀ e ∈ es, e ∈ st.log := by
  unfold doLeader advanceCommitIndex at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨-, -, rfl⟩ := h
  all_goals intro q hq
  · simp only [List.mem_map] at hq
    obtain ⟨node, -, rfl⟩ := hq
    refine ⟨_, _, _, _, rfl, fun e he => findGtIndex_in he⟩
  · exact nomatch hq
  · exact nomatch hq

/-- The cronies function after a timeout, at FUNCTION level: per term,
unchanged or snapshotted to the fresh candidacy's votesReceived. -/
theorem update_elections_data_timeout_cronies_cases
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l)) (tm : term) :
    (update_elections_data_timeout me st).cronies tm = st.1.cronies tm ∨
    (tm = st'.currentTerm ∧
     (update_elections_data_timeout me st).cronies tm = st'.votesReceived) := by
  unfold update_elections_data_timeout
  rw [h]
  simp only []
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | (simp only []
       split
       · rename_i heqtm
         exact Or.inr ⟨heqtm, rfl⟩
       · exact Or.inl rfl)

/-- The cronies function after a RequestVoteReply, at FUNCTION level:
per term, unchanged or snapshotted to the new votesReceived. -/
theorem update_elections_data_requestVoteReply_cronies_cases
    (me src : name (P := P)) (t0 : term) (v : Bool)
    (st : electionsData (P := P) × raft_data (P := P)) (tm : term) :
    (update_elections_data_requestVoteReply me src t0 v st).cronies tm
      = st.1.cronies tm ∨
    (tm = (handleRequestVoteReply me st.2 src t0 v).currentTerm ∧
     (update_elections_data_requestVoteReply me src t0 v st).cronies tm
       = (handleRequestVoteReply me st.2 src t0 v).votesReceived ∧
     (handleRequestVoteReply me st.2 src t0 v).type ≠ .Follower) := by
  unfold update_elections_data_requestVoteReply
  simp only []
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | (simp only []
       split
       · rename_i heqtm
         exact Or.inr ⟨heqtm, rfl, by simp_all⟩
       · exact Or.inl rfl)

/-! ## Unit-4 additions: leaderLogs/votesWithLog ghost facts and the
handler facts the leaderLogs ring needs (`RefinementSpecLemmas.v`,
`SpecLemmas.v` slices; sources cited per lemma). -/

/-- `moreUpToDate_refl` (`CommonTheorems.v:2306`). -/
theorem moreUpToDate_refl (t i : Nat) : moreUpToDate t i t i = true := by
  simp [moreUpToDate]

/-- `handleTimeout_messages` (`SpecLemmas.v`): every message a timeout
sends is a RequestVote at the (new) current term carrying the sender's
own maxIndex/maxTerm — and the sender ends a non-follower. -/
theorem handleTimeout_messages (me : name (P := P)) (st : raft_data (P := P))
    {out st' l} (h : handleTimeout me st = (out, st', l)) :
    ∀ q ∈ l, q.2 = msg.RequestVote (P := P) st'.currentTerm me
      (maxIndex st'.log) (maxTerm st'.log) := by
  unfold handleTimeout tryToBecomeLeader at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h
  · exact fun q hq => nomatch hq
  · intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨node, -, rfl⟩ := hq
    rfl

/-- `handleRequestVote`'s reply always carries the responder's NEW
current term (all four branches reply at the post-handler term). -/
theorem handleRequestVote_reply_term (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' m}
    (h : handleRequestVote me st t cand lli llt = (st', m)) :
    ∃ v, m = msg.RequestVoteReply (P := P) st'.currentTerm v := by
  unfold handleRequestVote at h
  simp only [] at h
  repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals exact ⟨_, rfl⟩

/-- `handleRequestVote_reply_true'` (`SpecLemmas.v`) + the moreUpToDate
guard: a `true` reply is granted AT THE REQUEST'S TERM (the reject branch
kills any request below the responder's term), the responder's log is
untouched, and the grant passed the up-to-date check against it. -/
theorem handleRequestVote_grant (me : name (P := P))
    (st : raft_data (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term) {st' t'}
    (h : handleRequestVote me st t cand lli llt
          = (st', .RequestVoteReply t' true)) :
    t' = t ∧ st'.currentTerm = t ∧ st'.log = st.log ∧
    moreUpToDate llt lli (maxTerm st.log) (maxIndex st.log) = true := by
  have hadv := advanceCurrentTerm_spec st t
  unfold handleRequestVote at h
  split at h
  · simp at h
  · rename_i hnle
    simp only [Nat.blt_eq] at hnle
    replace hnle : st.currentTerm ≤ t := Nat.le_of_not_lt hnle
    have hct : (advanceCurrentTerm st t).currentTerm = t :=
      advanceCurrentTerm_le_eq hnle
    simp only [] at h
    split at h
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      have hmore : moreUpToDate llt lli (maxTerm st.log) (maxIndex st.log)
          = true := by
        rw [← hadv.2.1]
        exact hguard.2
      split at h
      · simp only [Prod.mk.injEq, msg.RequestVoteReply.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨hct.symm ▸ rfl, hct, hadv.2.1, hmore⟩
      · simp only [Prod.mk.injEq, msg.RequestVoteReply.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨hct.symm ▸ rfl, hct, hadv.2.1, hmore⟩
    · simp at h

/-- `handleRequestVoteReply_spec'`'s leader-transition clause
(`SpecLemmas.v:467-478`): a non-leader that emerges from
`handleRequestVoteReply` as leader was a candidate that just won — the
reply was a grant at exactly its current term, and its votesReceived
grew by exactly the replier. -/
theorem handleRequestVoteReply_leader_transition (me : name (P := P))
    (st : raft_data (P := P)) (src : name (P := P)) (t : term) (v : Bool) {st'}
    (h : handleRequestVoteReply me st src t v = st')
    (hnl : st.type ≠ .Leader) (hty' : st'.type = .Leader) :
    st.type = .Candidate ∧ v = true ∧ st.currentTerm = t ∧
    st'.currentTerm = st.currentTerm ∧
    st'.votesReceived = src :: st.votesReceived ∧
    st'.log = st.log ∧
    wonElection (dedup (src :: st.votesReceived)) = true := by
  unfold handleRequestVoteReply at h
  simp only [] at h
  split at h
  · -- t > currentTerm: steps down to follower — not a leader
    subst h
    exact nomatch hty'
  · split at h
    · -- stale reply: state unchanged — still not a leader
      subst h
      exact absurd hty' hnl
    · rename_i hngt hnlt
      simp only [Nat.blt_eq] at hngt hnlt
      have hteq : st.currentTerm = t :=
        Nat.le_antisymm (Nat.le_of_not_lt hnlt) (Nat.le_of_not_lt hngt)
      split at h
      · -- candidate: the tally
        rename_i hcand
        subst h
        replace hty' : (if (v && wonElection (dedup (src :: st.votesReceived)))
            = true then serverType.Leader else st.type) = .Leader := hty'
        split at hty'
        · rename_i hwon
          simp only [Bool.and_eq_true] at hwon
          obtain ⟨rfl, hwon⟩ := hwon
          exact ⟨hcand, rfl, hteq, rfl, by simp, rfl, hwon⟩
        · exact absurd hty' hnl
      · -- non-candidate: unchanged — still not a leader
        subst h
        exact absurd hty' hnl

/-! ### leaderLogs ghost facts -/

/-- `update_elections_data_timeout_leaderLogs`
(`RefinementSpecLemmas.v:234`) + the allEntries analogue: a timeout
touches neither. -/
theorem update_elections_data_timeout_ghost (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    (update_elections_data_timeout me st).leaderLogs = st.1.leaderLogs ∧
    (update_elections_data_timeout me st).allEntries = st.1.allEntries := by
  unfold update_elections_data_timeout
  simp only []
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- `update_elections_data_requestVoteReply_old`
(`RefinementSpecLemmas.v:278`): old leaderLogs survive an RVR update. -/
theorem update_elections_data_requestVoteReply_leaderLogs_old
    (me src : name (P := P)) (t : term) (v : Bool)
    (st : electionsData (P := P) × raft_data (P := P))
    {t2 : term} {ll : List (entry (P := P))}
    (hin : (t2, ll) ∈ st.1.leaderLogs) :
    (t2, ll) ∈ (update_elections_data_requestVoteReply me src t v st).leaderLogs := by
  unfold update_elections_data_requestVoteReply
  simp only []
  repeat' split
  all_goals first
    | exact hin
    | exact List.mem_cons_of_mem _ hin

/-- `leaderLogs_update_elections_data_RVR`
(`RefinementSpecLemmas.v:261-276`): a leaderLog after an RVR update is an
old one, or the snapshot of a candidate→leader transition (new term =
the winner's current term, new log = the winner's log). -/
theorem leaderLogs_update_elections_data_RVR
    {me src : name (P := P)} {t : term} {v : Bool}
    {st : electionsData (P := P) × raft_data (P := P)}
    {t2 : term} {ll : List (entry (P := P))}
    (hin : (t2, ll) ∈
      (update_elections_data_requestVoteReply me src t v st).leaderLogs) :
    (t2, ll) ∈ st.1.leaderLogs ∨
    ((handleRequestVoteReply me st.2 src t v).type = .Leader ∧
     st.2.type = .Candidate ∧
     t2 = (handleRequestVoteReply me st.2 src t v).currentTerm ∧
     ll = (handleRequestVoteReply me st.2 src t v).log) := by
  unfold update_elections_data_requestVoteReply at hin
  simp only [] at hin
  repeat' split at hin
  all_goals first
    | exact Or.inl hin
    | (rename_i hleader hcand
       rcases List.mem_cons.mp hin with heq | hin
       · injection heq with h1 h2
         exact Or.inr ⟨hleader, hcand, h1, h2⟩
       · exact Or.inl hin)

/-! ### votesWithLog ghost facts -/

/-- `update_elections_data_request_vote_votesWithLog_old`
(`LeaderLogsVotesWithLogProof.v:77-90`). -/
theorem update_elections_data_requestVote_votesWithLog_old
    (me src : name (P := P)) (t : term) (cand : name (P := P))
    (lli : logIndex) (llt : term)
    (st : electionsData (P := P) × raft_data (P := P))
    {t' : term} {h' : name (P := P)} {vl : List (entry (P := P))}
    (hin : (t', h', vl) ∈ st.1.votesWithLog) :
    (t', h', vl) ∈
      (update_elections_data_requestVote me src t cand lli llt st).votesWithLog := by
  unfold update_elections_data_requestVote
  simp only []
  repeat' split
  all_goals first
    | exact hin
    | exact List.mem_cons_of_mem _ hin

/-- `update_elections_data_timeout_votesWithLog_old`
(`LeaderLogsVotesWithLogProof.v:175-183`). -/
theorem update_elections_data_timeout_votesWithLog_old (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P))
    {t' : term} {h' : name (P := P)} {vl : List (entry (P := P))}
    (hin : (t', h', vl) ∈ st.1.votesWithLog) :
    (t', h', vl) ∈ (update_elections_data_timeout me st).votesWithLog := by
  unfold update_elections_data_timeout
  simp only []
  repeat' split
  all_goals first
    | exact hin
    | exact List.mem_cons_of_mem _ hin

/-- `update_elections_data_timeout_votesWithLog_votesReceived`
(`RefinementSpecLemmas.v:599-614`): a timeout is a leader heartbeat
(votesReceived and ghost votesWithLog unchanged) or a fresh candidacy
(votesReceived reset to the self-vote and the self-vote-with-log
recorded at the new term). -/
theorem update_elections_data_timeout_votesWithLog_votesReceived
    {me : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l)) :
    (st'.votesReceived = st.2.votesReceived ∧
     (update_elections_data_timeout me st).votesWithLog = st.1.votesWithLog ∧
     st'.type = .Leader) ∨
    (st'.votesReceived = [me] ∧
     (update_elections_data_timeout me st).votesWithLog
       = (st'.currentTerm, me, st'.log) :: st.1.votesWithLog ∧
     st'.currentTerm = st.2.currentTerm + 1) := by
  unfold update_elections_data_timeout
  rw [h]
  simp only []
  unfold handleTimeout tryToBecomeLeader at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h
  · -- leader heartbeat: votedFor may be anything, but the leader branch
    -- leaves the ghost alone
    rename_i hleader
    left
    refine ⟨rfl, ?_, hleader⟩
    split
    · rw [if_pos hleader]
    · rfl
  · -- fresh candidacy: votedFor = some me, records at the new term
    rename_i hnl
    right
    refine ⟨rfl, ?_, rfl⟩
    split
    · rename_i cid' heq
      injection heq with heq
      subst heq
      rw [if_neg hnl]
    · rename_i heq
      exact nomatch heq

/-- `update_elections_data_timeout_votedFor`
(`RefinementSpecLemmas.v:616-635`). -/
theorem update_elections_data_timeout_votedFor
    {me : name (P := P)} {cid : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)} {out st' l}
    (h : handleTimeout me st.2 = (out, st', l))
    (hvf : st'.votedFor = some cid) :
    (st.2.votedFor = some cid ∧ st'.currentTerm = st.2.currentTerm ∧
     st'.type = st.2.type ∧
     (update_elections_data_timeout me st).votesWithLog = st.1.votesWithLog) ∨
    (cid = me ∧ st'.currentTerm = st.2.currentTerm + 1 ∧
     (update_elections_data_timeout me st).votesWithLog
       = (st'.currentTerm, cid, st'.log) :: st.1.votesWithLog) := by
  unfold update_elections_data_timeout
  rw [h]
  simp only []
  unfold handleTimeout tryToBecomeLeader at h
  split at h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h
  · -- heartbeat: st' = {st.2 with shouldSend := true}
    rename_i hleader
    left
    refine ⟨hvf, rfl, rfl, ?_⟩
    split
    · rw [if_pos hleader]
    · rfl
  · -- candidacy: votedFor = some me
    rename_i hnl
    right
    replace hvf : me = cid := by
      simpa using hvf
    subst hvf
    refine ⟨rfl, rfl, ?_⟩
    split
    · rename_i cid' heq
      injection heq with heq
      subst heq
      rw [if_neg hnl]
    · rename_i heq
      exact nomatch heq

/-- `update_elections_data_request_vote_votedFor`
(`RefinementSpecLemmas.v:637-660`): after a RequestVote, a recorded vote
is the untouched old one (same term), or a fresh grant to the candidate
at the request's term — recorded in votesWithLog with the voter's log,
which passed the up-to-date check. Stated with `cand` in both the `src`
and `candidateId` positions, as at the dispatch site. -/
theorem update_elections_data_requestVote_votedFor
    {me : name (P := P)} {cid : name (P := P)}
    {st : electionsData (P := P) × raft_data (P := P)}
    {t : term} {cand : name (P := P)} {lli : logIndex} {llt : term} {st' m}
    (h : handleRequestVote me st.2 t cand lli llt = (st', m))
    (hvf : st'.votedFor = some cid) :
    (st.2.votedFor = some cid ∧ st'.currentTerm = st.2.currentTerm) ∨
    (cid = cand ∧ st'.currentTerm = t ∧
     (update_elections_data_requestVote me cand t cand lli llt st).votesWithLog
       = (st'.currentTerm, cid, st'.log) :: st.1.votesWithLog ∧
     moreUpToDate llt lli (maxTerm st'.log) (maxIndex st'.log) = true) := by
  have hadv := advanceCurrentTerm_spec st.2 t
  unfold update_elections_data_requestVote
  rw [h]
  simp only []
  unfold handleRequestVote at h
  split at h
  · -- reject: state unchanged
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    left
    exact ⟨hvf, rfl⟩
  · rename_i hnle
    simp only [Nat.blt_eq] at hnle
    replace hnle : st.2.currentTerm ≤ t := Nat.le_of_not_lt hnle
    have hct : (advanceCurrentTerm st.2 t).currentTerm = t :=
      advanceCurrentTerm_le_eq hnle
    simp only [] at h
    split at h
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      split at h
      · -- fresh grant (advanced votedFor = none)
        rename_i hnone
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        replace hvf : cid = cand := by
          simpa using hvf.symm
        subst hvf
        right
        have hmore : moreUpToDate llt lli
            (maxTerm (advanceCurrentTerm st.2 t).log)
            (maxIndex (advanceCurrentTerm st.2 t).log) = true := hguard.2
        refine ⟨rfl, hct, ?_, hmore⟩
        -- the ghost's match: st.2.votedFor vs (some cid)
        rcases hcase : st.2.votedFor with _ | c
        · simp only []
        · -- old vote existed but the advance cleared it: terms differ
          have hne : ((st.2.currentTerm == (advanceCurrentTerm st.2 t).currentTerm)
              && decide (c = cid)) = false := by
            rcases hadv.2.2 with ⟨-, hvfeq, -⟩ | ⟨hlt, -, -⟩
            · rw [hcase] at hvfeq
              rw [hvfeq] at hnone
              cases hnone
            · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
              exact Or.inl (Nat.ne_of_lt hlt)
          simp only [hne]
          simp
      · -- repeat grant: votedFor untouched by the handler
        rename_i c' hsome
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [hsome] at hvf
        left
        rcases hadv.2.2 with ⟨hcteq, hvfeq, -⟩ | ⟨-, hvfeq, -⟩
        · rw [hvfeq] at hsome
          exact ⟨hsome.symm ▸ hvf, hcteq⟩
        · rw [hvfeq] at hsome
          cases hsome
    · -- refuse: advanced state only
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      left
      rcases hadv.2.2 with ⟨hcteq, hvfeq, -⟩ | ⟨-, hvfeq, -⟩
      · exact ⟨hvfeq ▸ hvf, hcteq⟩
      · rw [hvfeq] at hvf
        cases hvf

/-- The votes/votesWithLog lockstep shape of a RequestVote ghost update
(for `VotesVotesWithLogCorrespondProof.v`): both unchanged, or both
extended with matching heads. -/
theorem update_elections_data_requestVote_lockstep (me src : name (P := P))
    (t : term) (cand : name (P := P)) (lli : logIndex) (llt : term)
    (st : electionsData (P := P) × raft_data (P := P)) :
    ((update_elections_data_requestVote me src t cand lli llt st).votes
        = st.1.votes ∧
     (update_elections_data_requestVote me src t cand lli llt st).votesWithLog
        = st.1.votesWithLog) ∨
    (∃ t' n vl,
     (update_elections_data_requestVote me src t cand lli llt st).votes
        = (t', n) :: st.1.votes ∧
     (update_elections_data_requestVote me src t cand lli llt st).votesWithLog
        = (t', n, vl) :: st.1.votesWithLog) := by
  unfold update_elections_data_requestVote
  simp only []
  repeat' split
  all_goals first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨_, _, _, rfl, rfl⟩

/-- The votes/votesWithLog lockstep shape of a timeout ghost update. -/
theorem update_elections_data_timeout_lockstep (me : name (P := P))
    (st : electionsData (P := P) × raft_data (P := P)) :
    ((update_elections_data_timeout me st).votes = st.1.votes ∧
     (update_elections_data_timeout me st).votesWithLog = st.1.votesWithLog) ∨
    (∃ t' n vl,
     (update_elections_data_timeout me st).votes = (t', n) :: st.1.votes ∧
     (update_elections_data_timeout me st).votesWithLog
        = (t', n, vl) :: st.1.votesWithLog) := by
  unfold update_elections_data_timeout
  simp only []
  repeat' split
  all_goals first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨_, _, _, rfl, rfl⟩

end ElectionSpecLemmas

end Raft
end VerdiCompat
