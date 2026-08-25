import GoLeanProofs.Specs.Raft.NativeS1Chain

/-! # C3 — the etcd discharge layer (S1 fragment, complete)
(scoping lane `campaign-arc4b`, unit C3, 2026-08-27.)

## What this module is

Charter part 3: the etcd dialect discharges EVERY S1 signature member
— `ElectObligations voters (EStep voters)` is constructed
(`etcd_discharges`), completing the set SC1's PROVED LINK 3 specimen
started (O1/O2 at the `specRecvVote` node level). The headline
corollary `etcd_one_leader_per_term` then instantiates the native
chain at this dialect.

## The step relation and its two modeling premises (both recorded)

`EStep` is the election-fragment step over `SNet`: one node runs one
specRound function (`specBecomeCandidate` / `specRecvVote` /
`specRecvVoteResp`, each line-cited in `NativeObligations.lean`), the
rest of the net is framed, and the GHOST RULES attach exactly where
the signature's docstrings say (a grant pushes the vote entry; a
victory pushes the victory record). Two premises on the
`recvVoteResp` constructor stand for dialect-side facts outside the
S1 fragment's node vocabulary, per the `SNet` docstring's stated
design ("in-flight packets stay dialect-side; the ghost obligations
absorb T3's `votes_nw`"):

- **`hgen` (response genuineness)** — a counted grant corresponds to
  a ghost vote for this candidate at its current term. This is the
  vote-record/network correspondence (T3's `votes_nw`,
  `ElectionSpecLemmas.lean`) absorbed as a receive-step premise:
  etcd's `poll` counts a response only at `m.Term == r.Term` (the
  Step preamble drops stale, raises on newer — raft.go:1120-1146),
  and the responder recorded the grant before replying
  (raft.go:1278).
- **`htally` (tally well-formedness, `TallyOK`)** — the candidate's
  tally has nodup keys drawn from `voters`, and its granted entries
  are ghost-faithful at the current term. This premise is REDUNDANT
  ON THE REACHABLE SET — proved below (`tallyOK_reachable`): it is
  an inductive invariant of `EStep` itself from empty-tally starts,
  so guarding with it prunes no reachable behavior. It is stated as
  a premise (rather than proved inline at the victory step) because
  obligation members quantify over ALL nets, where an arbitrary
  tally is garbage.

The other preconditions: `hfrom : from_ ∈ voters` (responses come
from configured voters — the twin's fixed `MajorityConfig`,
twin-lib.go:207-215) and `hc : c ≠ 0` / `hi : i ≠ 0` (etcd node ids
are nonzero; 0 is the `None` sentinel).

**The self-vote ghost rule** (a modeling-fidelity point found while
constructing the witness, recorded): `campaign` pushes the ghost
vote `(term+1, i)` for the candidate ITSELF — exactly where
verdi-raft's `electionsData` records the own-vote at the candidate
transition. Without it a genuine self-directed `MsgVoteResp`
(etcd's `msgsAfterAppend` self-response, raft.go:1066-1075) could
never satisfy `hgen`, so real twin traces — a 3-node leader via
self-vote + one grant — would be UNSIMULABLE and the safety theorem
would not cover them. The abstract dialect must over-approximate
the subject; this rule is what keeps the simulation direction
honest. -/

namespace GoLean.RaftSeam.NativeSpec

/-! ## Net/ghost update helpers and their lemmas -/

/-- One-node net update with an explicit ghost. -/
def updNode (N : SNet) (i : Nat) (r : ENode) (g : Ghost) : SNet :=
  { node := fun j => if j = i then r else N.node j, ghost := g }

theorem updNode_self (N : SNet) (i : Nat) (r : ENode) (g : Ghost) :
    (updNode N i r g).node i = r := by simp [updNode]

theorem updNode_other (N : SNet) {i j : Nat} (r : ENode) (g : Ghost)
    (h : j ≠ i) : (updNode N i r g).node j = N.node j := by
  simp [updNode, h]

theorem updNode_ghost (N : SNet) (i : Nat) (r : ENode) (g : Ghost) :
    (updNode N i r g).ghost = g := rfl

/-- Ghost-vote push (the grant rule's ghost delta). -/
def pushVote (g : Ghost) (v t c : Nat) : Ghost :=
  { g with votes := fun w => if w = v then (t, c) :: g.votes w
                             else g.votes w }

theorem pushVote_self (g : Ghost) (v t c : Nat) :
    (pushVote g v t c).votes v = (t, c) :: g.votes v := by simp [pushVote]

theorem pushVote_other (g : Ghost) {v w : Nat} (t c : Nat) (h : w ≠ v) :
    (pushVote g v t c).votes w = g.votes w := by simp [pushVote, h]

theorem pushVote_victories (g : Ghost) (v t c : Nat) :
    (pushVote g v t c).victories = g.victories := rfl

/-- Victory push (the leader-entry rule's ghost delta). -/
def pushVictory (g : Ghost) (t l : Nat) (q : List Nat) : Ghost :=
  { g with victories := (t, l, q) :: g.victories }

theorem pushVictory_votes (g : Ghost) (t l : Nat) (q : List Nat) :
    (pushVictory g t l q).votes = g.votes := rfl

theorem pushVictory_victories (g : Ghost) (t l : Nat) (q : List Nat) :
    (pushVictory g t l q).victories = (t, l, q) :: g.victories := rfl

/-! ## Tally lemmas (`recordVote` / `grantedOf`) -/

theorem mem_recordVote {l : List (Nat × Bool)} {v : Nat} {g : Bool}
    {p : Nat × Bool} (h : p ∈ recordVote l v g) :
    p ∈ l ∨ p = (v, g) := by
  unfold recordVote at h
  split at h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem recordVote_keys_nodup {l : List (Nat × Bool)} {v : Nat}
    {g : Bool} (h : (l.map Prod.fst).Nodup) :
    ((recordVote l v g).map Prod.fst).Nodup := by
  unfold recordVote
  split
  · exact h
  · rename_i hany
    simp only [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, h⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨p, hp, hpv⟩
    exact hany (List.any_eq_true.mpr
      ⟨p, hp, by rw [hpv]; exact beq_self_eq_true' v⟩)

theorem mem_grantedOf {l : List (Nat × Bool)} {v : Nat}
    (h : v ∈ grantedOf l) : (v, true) ∈ l := by
  unfold grantedOf at h
  rcases List.mem_map.mp h with ⟨p, hp, hpv⟩
  rcases List.mem_filter.mp hp with ⟨hpl, hp2⟩
  obtain ⟨a, b⟩ := p
  cases hpv
  cases b
  · exact absurd hp2 (by simp)
  · exact hpl

theorem grantedOf_nodup {l : List (Nat × Bool)}
    (h : (l.map Prod.fst).Nodup) : (grantedOf l).Nodup := by
  have hsub : List.Sublist ((l.filter (·.2)).map (·.1))
      (l.map Prod.fst) := List.Sublist.map _ List.filter_sublist
  exact List.Nodup.sublist hsub h

/-! ## specRound branch lemmas (the pair-form facts the discharge
consumes; SC1's link-3 lemmas cover O1/O2 at this level already) -/

theorem specBecomeCandidate_state (r : ENode) (i : Nat) :
    (specBecomeCandidate r i).state = 1 := rfl

theorem specBecomeCandidate_term (r : ENode) (i : Nat) :
    (specBecomeCandidate r i).term = r.term + 1 := rfl

/-- `specRecvVote` never manufactures a leader: a post-state leader
was one already, at an unchanged term (the preamble demotes; the
grant branch touches only `vote`). -/
theorem specRecvVote_state (r : ENode) (f mT mLT mI : Nat) :
    (specRecvVote r f mT mLT mI).1.state = 2 →
    r.state = 2 ∧ (specRecvVote r f mT mLT mI).1.term = r.term := by
  unfold specRecvVote
  by_cases hpre : r.term < mT
  · simp only [hpre, if_true]
    split
    · intro h2; exact absurd h2 (by simp)
    · intro h2; exact absurd h2 (by simp)
  · simp only [hpre, if_false]
    split
    · intro h2; exact ⟨h2, rfl⟩
    · intro h2; exact ⟨h2, rfl⟩

/-- The grant branch records the requester as the vote. -/
theorem specRecvVote_grant_vote (r : ENode) (f mT mLT mI : Nat) :
    (specRecvVote r f mT mLT mI).2 = true →
    (specRecvVote r f mT mLT mI).1.vote = f := by
  unfold specRecvVote
  by_cases hpre : r.term < mT
  · simp only [hpre, if_true]
    split
    · intro _; rfl
    · intro hg; cases hg
  · simp only [hpre, if_false]
    split
    · intro _; rfl
    · intro hg; cases hg

/-- `specRecvVoteResp` keeps term and vote in every branch. -/
theorem specRecvVoteResp_term_vote (r : ENode) (s : Nat)
    (voters : List Nat) (f : Nat) (rej : Bool) :
    (specRecvVoteResp r s voters f rej).1.term = r.term ∧
    (specRecvVoteResp r s voters f rej).1.vote = r.vote := by
  simp only [specRecvVoteResp]
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- The winning branch: a candidate, the quorum guard over the
post-record tally, leader post-state, unchanged term. -/
theorem specRecvVoteResp_won {r r' : ENode} {s : Nat}
    {voters : List Nat} {f : Nat} {rej : Bool}
    (h : specRecvVoteResp r s voters f rej = (r', true)) :
    r.state = 1 ∧ r'.state = 2 ∧ r'.term = r.term ∧
    voters.length <
      2 * (grantedOf (recordVote r.votesRec f (!rej))).length := by
  simp only [specRecvVoteResp] at h
  split at h
  · injection h with h1 h2
    cases h2
  · rename_i hstate
    have hs1 : r.state = 1 := by
      by_cases h1 : r.state = 1
      · exact h1
      · exact absurd (by simp [h1]) hstate
    split at h
    · rename_i hguard
      injection h with h1 h2
      exact ⟨hs1, by rw [← h1], by rw [← h1], hguard⟩
    · injection h with h1 h2
      cases h2

/-- The non-winning branches keep the state. -/
theorem specRecvVoteResp_notWon {r r' : ENode} {s : Nat}
    {voters : List Nat} {f : Nat} {rej : Bool}
    (h : specRecvVoteResp r s voters f rej = (r', false)) :
    r'.state = r.state := by
  simp only [specRecvVoteResp] at h
  split at h
  · injection h with h1 h2
    rw [← h1]
  · split at h
    · injection h with h1 h2
      cases h2
    · injection h with h1 h2
      rw [← h1]

/-! ## The tally well-formedness premise -/

/-- Tally well-formedness at node `i` (the `recvVoteResp` premise):
nodup keys drawn from the configuration, granted entries
ghost-faithful at the node's current term. Redundant on the
reachable set — `tallyOK_reachable` below. -/
structure TallyOK (voters : List Nat) (N : SNet) (i : Nat) : Prop where
  keysNodup : (((N.node i).votesRec).map Prod.fst).Nodup
  keysSub : ∀ p ∈ (N.node i).votesRec, p.1 ∈ voters
  faithful : ∀ p ∈ (N.node i).votesRec, p.2 = true →
    ((N.node i).term, i) ∈ N.ghost.votes p.1

/-! ## The etcd election-fragment step relation -/

/-- The etcd dialect's abstract step (election fragment): each
constructor runs one specRound function at one node, frames the
rest, and applies the ghost rule the signature names. The
intermediate spec results are constructor indices pinned by
defining equations (`hspec`) so discharge proofs are case analyses
over the branch lemmas above. -/
inductive EStep (voters : List Nat) : SNet → SNet → Prop where
  | campaign (N : SNet) (i : Nat) (hi : i ≠ 0) :
      EStep voters N
        (updNode N i (specBecomeCandidate (N.node i) i)
          (pushVote N.ghost i ((N.node i).term + 1) i))
  | recvVote (N : SNet) (v c mT mLT mI : Nat) (r' : ENode) (g : Bool)
      (hc : c ≠ 0)
      (hspec : specRecvVote (N.node v) c mT mLT mI = (r', g)) :
      EStep voters N
        (updNode N v r'
          (if g then pushVote N.ghost v r'.term c else N.ghost))
  | recvVoteResp (N : SNet) (i from_ : Nat) (reject : Bool)
      (r' : ENode) (won : Bool)
      (hfrom : from_ ∈ voters)
      (htally : TallyOK voters N i)
      (hgen : reject = false →
        ((N.node i).term, i) ∈ N.ghost.votes from_)
      (hspec : specRecvVoteResp (N.node i) i voters from_ reject
        = (r', won)) :
      EStep voters N
        (updNode N i r'
          (if won then
            pushVictory N.ghost (N.node i).term i
              (grantedOf (recordVote (N.node i).votesRec from_ (!reject)))
           else N.ghost))

/-! ## The discharge (charter part 3's deliverable) -/

/-- **The etcd dialect discharges the whole S1 obligation signature.**
Per-member sites (each also cited in the member docstrings,
`NativeObligations.lean`): O1/O2 = the SC1 link-3 lemmas + the
branch lemmas; O3a/O5a = the ghost rules only push; O3b = the grant
rule's shape; O4 = the winning branch's guard + `TallyOK` +
genuineness; O5b = the branch lemmas' term stability. -/
theorem etcd_discharges (voters : List Nat) :
    ElectObligations voters (EStep voters) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- O1 termMono
    intro N N' hs j
    cases hs with
    | campaign i hi =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self, specBecomeCandidate_term]
        exact Nat.le_succ _
      · rw [updNode_other _ _ _ hj]
        exact Nat.le_refl _
    | recvVote v c mT mLT mI r' g hc hspec =>
      by_cases hj : j = v
      · subst hj
        rw [updNode_self]
        have := specRecvVote_termMono (N.node j) c mT mLT mI
        rwa [hspec] at this
      · rw [updNode_other _ _ _ hj]
        exact Nat.le_refl _
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self]
        have := (specRecvVoteResp_term_vote (N.node j) j voters
          from_ reject).1
        rw [hspec] at this
        exact Nat.le_of_eq this.symm
      · rw [updNode_other _ _ _ hj]
        exact Nat.le_refl _
  · -- O2 votePersist
    intro N N' hs j hne
    cases hs with
    | campaign i hi =>
      by_cases hj : j = i
      · subst hj
        right
        rw [updNode_self, specBecomeCandidate_term]
        exact Nat.lt_succ_self _
      · exact absurd (by rw [updNode_other _ _ _ hj]) hne
    | recvVote v c mT mLT mI r' g hc hspec =>
      by_cases hj : j = v
      · subst hj
        rw [updNode_self] at hne ⊢
        have := specRecvVote_votePersist (N.node j) c mT mLT mI
        rw [hspec] at this
        exact this hne
      · exact absurd (by rw [updNode_other _ _ _ hj]) hne
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self] at hne
        have := (specRecvVoteResp_term_vote (N.node j) j voters
          from_ reject).2
        rw [hspec] at this
        exact absurd this hne
      · exact absurd (by rw [updNode_other _ _ _ hj]) hne
  · -- O3a ghostVotesMono
    intro N N' hs v t c hin
    cases hs with
    | campaign i hi =>
      rw [updNode_ghost]
      by_cases hv : v = i
      · subst hv
        rw [pushVote_self]
        exact List.mem_cons_of_mem _ hin
      · rw [pushVote_other _ _ _ hv]
        exact hin
    | recvVote v₀ c₀ mT mLT mI r' g hc hspec =>
      rw [updNode_ghost]
      split
      · by_cases hv : v = v₀
        · subst hv
          rw [pushVote_self]
          exact List.mem_cons_of_mem _ hin
        · rw [pushVote_other _ _ _ hv]
          exact hin
      · exact hin
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      rw [updNode_ghost]
      split
      · rw [pushVictory_votes]; exact hin
      · exact hin
  · -- O3b ghostVotesNew
    intro N N' hs v t c hin hnot
    cases hs with
    | campaign i hi =>
      rw [updNode_ghost] at hin
      by_cases hv : v = i
      · subst hv
        rw [pushVote_self] at hin
        rcases List.mem_cons.mp hin with heq | hold
        · have h1 : t = (N.node v).term + 1 := congrArg Prod.fst heq
          have h2 : c = v := congrArg Prod.snd heq
          subst h1; subst h2
          exact ⟨by rw [updNode_self, specBecomeCandidate_term],
            by rw [updNode_self]; rfl, hi⟩
        · exact absurd hold hnot
      · rw [pushVote_other _ _ _ hv] at hin
        exact absurd hin hnot
    | recvVote v₀ c₀ mT mLT mI r' g hc hspec =>
      rw [updNode_ghost] at hin
      cases g with
      | false =>
        rw [if_neg Bool.false_ne_true] at hin
        exact absurd hin hnot
      | true =>
        rw [if_pos rfl] at hin
        by_cases hv : v = v₀
        · subst hv
          rw [pushVote_self] at hin
          rcases List.mem_cons.mp hin with heq | hold
          · have h1 : t = r'.term := congrArg Prod.fst heq
            have h2 : c = c₀ := congrArg Prod.snd heq
            have hgv := specRecvVote_grant_vote (N.node v) c₀ mT mLT mI
              (by rw [hspec])
            rw [hspec] at hgv
            subst h1; subst h2
            exact ⟨by rw [updNode_self], by rw [updNode_self]; exact hgv,
              hc⟩
          · exact absurd hold hnot
        · rw [pushVote_other _ _ _ hv] at hin
          exact absurd hin hnot
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      rw [updNode_ghost] at hin
      cases won with
      | false =>
        rw [if_neg Bool.false_ne_true] at hin
        exact absurd hin hnot
      | true =>
        rw [if_pos rfl, pushVictory_votes] at hin
        exact absurd hin hnot
  · -- O4 leaderEntry
    intro N N' hs j hpre hpost
    cases hs with
    | campaign i hi =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self, specBecomeCandidate_state] at hpost
        cases hpost
      · rw [updNode_other _ _ _ hj] at hpost
        exact absurd hpost hpre
    | recvVote v c mT mLT mI r' g hc hspec =>
      by_cases hj : j = v
      · subst hj
        rw [updNode_self] at hpost
        have := specRecvVote_state (N.node j) c mT mLT mI
        rw [hspec] at this
        exact absurd (this hpost).1 hpre
      · rw [updNode_other _ _ _ hj] at hpost
        exact absurd hpost hpre
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self] at hpost
        cases won with
        | false =>
          rw [specRecvVoteResp_notWon hspec] at hpost
          exact absurd hpost hpre
        | true =>
          obtain ⟨-, -, hterm, hguard⟩ := specRecvVoteResp_won hspec
          rw [updNode_self, updNode_ghost, if_pos rfl, hterm]
          refine ⟨grantedOf (recordVote (N.node j).votesRec from_
              (!reject)),
            ⟨grantedOf_nodup (recordVote_keys_nodup htally.keysNodup),
             ?_, hguard⟩, ?_, ?_⟩
          · intro w hw'
            rcases mem_recordVote (mem_grantedOf hw') with hp | hp
            · exact htally.keysSub _ hp
            · have hwf : w = from_ := congrArg Prod.fst hp
              rw [hwf]; exact hfrom
          · rw [pushVictory_victories]
            exact List.mem_cons_self ..
          · intro w hw'
            rw [pushVictory_votes]
            rcases mem_recordVote (mem_grantedOf hw') with hp | hp
            · exact htally.faithful _ hp rfl
            · have hwf : w = from_ := congrArg Prod.fst hp
              have h2 : (!reject) = true := by
                have h0 : ((w, true) : Nat × Bool).2 = true := rfl
                rw [hp] at h0
                exact h0
              have hrej : reject = false := by
                cases reject
                · rfl
                · cases h2
              rw [hwf]
              exact hgen hrej
      · rw [updNode_other _ _ _ hj] at hpost
        exact absurd hpost hpre
  · -- O5a victoriesMono
    intro N N' hs e hin
    cases hs with
    | campaign i hi => exact hin
    | recvVote v c mT mLT mI r' g hc hspec =>
      rw [updNode_ghost]
      split
      · rw [pushVote_victories]; exact hin
      · exact hin
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      rw [updNode_ghost]
      split
      · rw [pushVictory_victories]
        exact List.mem_cons_of_mem _ hin
      · exact hin
  · -- O5b leaderStable
    intro N N' hs j hpre hpost
    cases hs with
    | campaign i hi =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self, specBecomeCandidate_state] at hpost
        cases hpost
      · rw [updNode_other _ _ _ hj]
    | recvVote v c mT mLT mI r' g hc hspec =>
      by_cases hj : j = v
      · subst hj
        rw [updNode_self] at hpost ⊢
        have := specRecvVote_state (N.node j) c mT mLT mI
        rw [hspec] at this
        exact (this hpost).2
      · rw [updNode_other _ _ _ hj]
    | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
      by_cases hj : j = i
      · subst hj
        rw [updNode_self]
        have := (specRecvVoteResp_term_vote (N.node j) j voters
          from_ reject).1
        rw [hspec] at this
        exact this
      · rw [updNode_other _ _ _ hj]

/-! ## The headline corollary -/

/-- **THE NATIVE `one_leader_per_term`, etcd dialect**: over every
net reachable by the etcd election-fragment steps from any start
with empty ghost votes and no leaders, two same-term leaders
coincide. (The twin's boot state — followers over the seeded
snapshot, twin-lib.go:198-215, at any party count — satisfies the
premises trivially.) -/
theorem etcd_one_leader_per_term (voters : List Nat) {N₀ N : SNet}
    (hv : ∀ v t c, (t, c) ∉ N₀.ghost.votes v)
    (hnl : ∀ i, (N₀.node i).state ≠ 2)
    (hreach : ReachRel (EStep voters) N₀ N) :
    oneLeaderPerTerm N :=
  native_one_leader_per_term (etcd_discharges voters) ⟨hv, hnl⟩ hreach

/-! ## The `TallyOK` premise is redundant on the reachable set -/

/-- `TallyOK` at every node is itself an inductive invariant of
`EStep` from empty-tally starts — so the `recvVoteResp` premise
prunes NO reachable behavior: on any reachable net the premise is
derivable, and the guarded relation coincides with the unguarded
one there. (The honesty capstone for the guard-shaped absorption of
T3's tally correspondence.) -/
theorem tallyOK_step {voters : List Nat} {N N' : SNet}
    (hI : ∀ i, TallyOK voters N i) (hs : EStep voters N N') :
    ∀ i, TallyOK voters N' i := by
  -- ghost votes never shrink along any EStep
  have hmono : ∀ w t c, (t, c) ∈ N.ghost.votes w →
      (t, c) ∈ N'.ghost.votes w :=
    fun w t c => (etcd_discharges voters).ghostVotesMono hs w t c
  -- node terms never move without the tally's fate being decided,
  -- so case on the constructor
  intro j
  cases hs with
  | campaign i hi =>
    by_cases hj : j = i
    · subst hj
      refine ⟨?_, ?_, ?_⟩ <;> simp [updNode_self, specBecomeCandidate]
    · refine ⟨?_, ?_, ?_⟩
      · rw [updNode_other _ _ _ hj]; exact (hI j).keysNodup
      · rw [updNode_other _ _ _ hj]; exact (hI j).keysSub
      · rw [updNode_other _ _ _ hj]
        intro p hp h2
        exact hmono _ _ _ ((hI j).faithful p hp h2)
  | recvVote v c mT mLT mI r' g hc hspec =>
    by_cases hj : j = v
    · subst hj
      -- the receive step either clears the tally (preamble) or keeps
      -- it with the term unchanged
      have hcase : (r'.votesRec = []) ∨
          (r'.votesRec = (N.node j).votesRec ∧
            r'.term = (N.node j).term) := by
        unfold specRecvVote at hspec
        by_cases hpre : (N.node j).term < mT
        · simp only [hpre, if_true] at hspec
          split at hspec <;>
            (injection hspec with h1 h2; exact Or.inl (by rw [← h1]))
        · simp only [hpre, if_false] at hspec
          split at hspec <;>
            (injection hspec with h1 h2;
             exact Or.inr ⟨by rw [← h1], by rw [← h1]⟩)
      rcases hcase with hclr | ⟨hkeep, hterm⟩
      · refine ⟨?_, ?_, ?_⟩ <;> simp [updNode_self, hclr]
      · refine ⟨?_, ?_, ?_⟩
        · rw [updNode_self, hkeep]; exact (hI j).keysNodup
        · rw [updNode_self, hkeep]; exact (hI j).keysSub
        · rw [updNode_self, hkeep]
          intro p hp h2
          have hm := hmono _ _ _ ((hI j).faithful p hp h2)
          rw [← hterm] at hm
          exact hm
    · refine ⟨?_, ?_, ?_⟩
      · rw [updNode_other _ _ _ hj]; exact (hI j).keysNodup
      · rw [updNode_other _ _ _ hj]; exact (hI j).keysSub
      · rw [updNode_other _ _ _ hj]
        intro p hp h2
        exact hmono _ _ _ ((hI j).faithful p hp h2)
  | recvVoteResp i from_ reject r' won hfrom htally hgen hspec =>
    by_cases hj : j = i
    · subst hj
      have hcase : (r'.votesRec = []) ∨
          (r'.term = (N.node j).term ∧ won = false ∧
            (r'.votesRec = (N.node j).votesRec ∨
             r'.votesRec =
               recordVote (N.node j).votesRec from_ (!reject))) := by
        simp only [specRecvVoteResp] at hspec
        split at hspec
        · injection hspec with h1 h2
          exact Or.inr ⟨by rw [← h1], h2.symm, Or.inl (by rw [← h1])⟩
        · split at hspec
          · injection hspec with h1 h2
            exact Or.inl (by rw [← h1])
          · injection hspec with h1 h2
            exact Or.inr ⟨by rw [← h1], h2.symm,
              Or.inr (by rw [← h1])⟩
      rcases hcase with hclr | ⟨hterm, hw, hkeep | hkeep⟩
      · refine ⟨?_, ?_, ?_⟩ <;> simp [updNode_self, hclr]
      · refine ⟨?_, ?_, ?_⟩
        · rw [updNode_self, hkeep]; exact (hI j).keysNodup
        · rw [updNode_self, hkeep]; exact (hI j).keysSub
        · rw [updNode_self, hkeep, hterm, updNode_ghost, hw,
            if_neg Bool.false_ne_true]
          exact (hI j).faithful
      · refine ⟨?_, ?_, ?_⟩
        · rw [updNode_self, hkeep]
          exact recordVote_keys_nodup (hI j).keysNodup
        · rw [updNode_self, hkeep]
          intro p hp
          rcases mem_recordVote hp with h | h
          · exact (hI j).keysSub _ h
          · have : p.1 = from_ := congrArg Prod.fst h
            rw [this]; exact hfrom
        · rw [updNode_self, hkeep, hterm, updNode_ghost, hw,
            if_neg Bool.false_ne_true]
          intro p hp h2
          rcases mem_recordVote hp with h | h
          · exact (hI j).faithful _ h h2
          · have hp1 : p.1 = from_ := congrArg Prod.fst h
            have hb : (!reject) = true := by
              have h0 := h2
              rw [h] at h0
              exact h0
            have hrej : reject = false := by
              cases reject
              · rfl
              · cases hb
            rw [hp1]
            exact hgen hrej
    · refine ⟨?_, ?_, ?_⟩
      · rw [updNode_other _ _ _ hj]; exact (hI j).keysNodup
      · rw [updNode_other _ _ _ hj]; exact (hI j).keysSub
      · rw [updNode_other _ _ _ hj]
        intro p hp h2
        exact hmono _ _ _ ((hI j).faithful p hp h2)

/-- The redundancy corollary: from empty-tally starts, `TallyOK`
holds at every reachable net. -/
theorem tallyOK_reachable {voters : List Nat} {N₀ N : SNet}
    (h0 : ∀ i, (N₀.node i).votesRec = [])
    (hr : ReachRel (EStep voters) N₀ N) :
    ∀ i, TallyOK voters N i := by
  refine invariance (P := fun N => ∀ i, TallyOK voters N i)
    (fun hP hs => tallyOK_step hP hs) ?_ hr
  intro i
  refine ⟨?_, ?_, ?_⟩ <;> simp [h0 i]

end GoLean.RaftSeam.NativeSpec
