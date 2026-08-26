/-! # SC1 — the obligation-signature probe: the native S1 fragment
(scoping lane `campaign-arc4b`, 2026-08-26; design of record: the
campaign worktree's `docs/2026-08-25_campaign-layerc-design.md` §8 D2
REVISED — the family route b′; empirical gate "SC1, running" named
there).

## What this module is

MEASUREMENT AND DECISION INPUT, not machinery (the SC1 charter): the
b′ route's obligation signature drafted at probe scale, the native
`one_leader_per_term` statement over the etcd-abstract vocabulary,
the superstructure skeleton organized around the signature, and the
2–3 cheapest chain links proved end-to-end as the per-lemma cost
calibration. Nothing here is consumed by any landed proof; the
statement chain that is NOT yet proved ships as named `Prop`
definitions (never as unproven theorem stubs), each docstring-classified
PORTS / ADAPTS / NEW against the T3 lattice
(`compat/verdi/VerdiCompat/`, read-only, cited by file:line at branch
tip 3bbb0f10).

## The b′ frame (design §8 D2 revised)

The per-transition obligations implicit in T3's proof structure
become the family interface (`ElectObligations` below): the invariant
superstructure is proved FROM the signature; each dialect (the Verdi
mirror, etcd's specRound) discharges the obligations. The empirical
census grounding this shape (SC1 slice 1, derivation in
`docs/campaign-arc4b-log.md`):

- The three T3 chain files (ElectionSafety / CandidateEntries /
  LeaderLogs, 5,005 lines) contain **ZERO direct handler unfolds** —
  every `unfold`/`simp` target is `update` (net plumbing) or
  `wonElection/dedup/eraseOne/div2` (dialect-free quorum math).
  All concrete-handler consumption is quarantined in
  `ElectionSpecLemmas.lean` (~50 spec lemmas) — which under b′ IS the
  Verdi-dialect discharge file.
- The measured ADAPTS driver: etcd's `becomeLeader` calls
  `reset(r.Term)` → `r.trk.ResetVotes()` (raftsubject/raft/raft.go:
  952→800→813), so an etcd LEADER retains NO tally — T3's
  `votes_received_leaders` (leader state carries `wonElection
  votesReceived`, ElectionSafety.lean:702) cannot port statement-
  intact. The signature therefore states the leader-quorum fact at
  the TRANSITION (obligation `leaderEntry` below) and carries it in a
  victory GHOST — exactly verdi-raft's `electoralVictories` device,
  now promoted to the family interface. The INTENT: Verdi would
  discharge from state or ghost; etcd only from ghost — visibly
  different implementations, the vacuity discipline's requirement.
  STATUS (corrected at the landing fix round, 2026-08-26): that
  requirement is NOT YET MET by landed artifacts — `ElectObligations`
  has exactly ONE construction site in the whole tree
  (`etcd_discharges`, NativeEtcdDischarge.lean); the Verdi instance
  was deliberately not built (arc4b log, on the record) and is an
  open vacuity debt, census item I1-V of the T1 open-obligation
  census (landing fix-round log entry). The per-member "Verdi: …"
  notes below are design CITATIONS to T3's proofs, not landed
  discharges.

LINEAGE (per the doctrine): parametric invariance over an abstract
transition-system signature — the TLA+/IOA refinement-family classic
(Abadi–Lamport auxiliary/ghost variables for the victory record);
quorum-system axiomatization (Malkhi–Reiter shape) for `quorumInter`.
No new mechanism class.

## Vocabulary

The shared abstract axes are the C1 adapter probe's (`ENode`:
state/term/vote/lead numbering as in the arm fixtures — 0=F/1=C/2=L,
0 = None for vote/lead; the probe's `πNode` showed these are exactly
the Verdi-shared axes). `votesRec` mirrors etcd `trk.Votes`
(raft.go:1094 `poll` → `RecordVote`/`TallyVotes`). Logs newest-first
(the adapter-probe convention), `(index, term)` pairs. -/

namespace GoLean.RaftSeam.NativeSpec

/-! ## The etcd-abstract node and the election-fragment step functions
(the specRound vocabulary, S1 fragment — each cited to the subject) -/

/-- The etcd-abstract node record — the adapter probe's `ENode`
extended with the poll record (`trk.Votes`, an assoc list; etcd's
`RecordVote` keeps the first record for a voter — raftsubject/
tracker/tracker.go `RecordVote`). -/
structure ENode where
  state : Nat                      -- 0=F, 1=C, 2=L (StateType)
  term : Nat
  vote : Nat                       -- 0 = None
  lead : Nat                       -- 0 = None
  log : List (Nat × Nat)           -- (index, term), newest-first
  committed : Nat
  votesRec : List (Nat × Bool)     -- trk.Votes (voter, granted)
  deriving Repr, DecidableEq

def lastIndex (r : ENode) : Nat := (r.log.head?.map Prod.fst).getD 0
def lastTerm  (r : ENode) : Nat := (r.log.head?.map Prod.snd).getD 0

/-- `raftLog.isUpToDate` (raftsubject/raft/log.go): candidate's last
entry id (t, i) is up to date vs the local log. -/
def upToDate (r : ENode) (candLastTerm candLastIndex : Nat) : Bool :=
  (lastTerm r < candLastTerm) ||
    (candLastTerm == lastTerm r && lastIndex r ≤ candLastIndex)

/-- `RecordVote` (tracker.go): first record wins. -/
def recordVote (l : List (Nat × Bool)) (v : Nat) (g : Bool) :
    List (Nat × Bool) :=
  if l.any (fun p => p.1 == v) then l else (v, g) :: l

/-- Granted-voter set of the poll record. -/
def grantedOf (l : List (Nat × Bool)) : List Nat :=
  (l.filter (·.2)).map (·.1)

/-- `becomeCandidate` (raft.go:921-935): `reset(Term+1)` (vote
cleared, lead cleared, tally cleared — raft.go:800-829) then
`Vote := id`, `state := C`. The campaign event's node delta; the
self-vote MsgVoteResp rides `msgsAfterAppend` (raft.go:1066-1075
comment) and is polled at harvest, so the record stays empty here. -/
def specBecomeCandidate (r : ENode) (selfId : Nat) : ENode :=
  { r with state := 1, term := r.term + 1, vote := selfId, lead := 0,
           votesRec := [] }

/-- The MsgVote receive step (raft.go:1108-1146 term preamble +
1231-1284 vote case), same-or-higher-term, PreVote off (the twin
config): on `m.Term > r.Term`, `becomeFollower(m.Term, None)` first
(vote and lead reset via `reset`); then
`canVote := Vote == from ∨ (Vote == None ∧ lead == None)` and the
up-to-date check; a grant records `Vote := from`. Returns
(node', granted). Ignores `m.Term < r.Term` upstream (the stale
branch replies reject at the caller's level; stale handling is a
dispatch-arm concern, not this fragment's). -/
def specRecvVote (r : ENode) (from_ mTerm mLogTerm mIndex : Nat) :
    ENode × Bool :=
  -- term preamble (raft.go:1120-1146; lease check off: checkQuorum unset)
  let r₀ := if r.term < mTerm then
              { r with state := 0, term := mTerm, vote := 0, lead := 0,
                       votesRec := [] }
            else r
  let canVote := r₀.vote == from_ || (r₀.vote == 0 && r₀.lead == 0)
  if canVote && upToDate r₀ mLogTerm mIndex then
    ({ r₀ with vote := from_ }, true)
  else (r₀, false)

/-- Majority quorum over voter ids (the twin's `MajorityConfig` at
its voter set; raftsubject/quorum/majority.go `VoteResult`). -/
def isQuorum (voters : List Nat) (q : List Nat) : Prop :=
  q.Nodup ∧ (∀ v ∈ q, v ∈ voters) ∧ voters.length < 2 * q.length

/-- The MsgVoteResp receive step at a candidate (raft.go stepCandidate
→ `poll` (1094) → on `VoteWon`, `becomeLeader` (952): `reset(Term)` —
which CLEARS the tally (raft.go:813) — `lead := id`, `state := L`,
noop append (`appendEntry(emptyEnt)`, raft.go:980-81)). Returns
(node', wonNow). The quorum test is over the POST-record tally. -/
def specRecvVoteResp (r : ENode) (selfId : Nat) (voters : List Nat)
    (from_ : Nat) (reject : Bool) : ENode × Bool :=
  if r.state != 1 then (r, false)   -- non-candidates drop (fragment scope)
  else
    let rec' := recordVote r.votesRec from_ (!reject)
    if 2 * (grantedOf rec').length > voters.length then
      -- becomeLeader: reset(Term) clears the tally, keeps term+vote;
      -- lead := id; the noop entry appended (raft.go:952-990).
      ({ r with state := 2, lead := selfId, votesRec := [],
                log := (lastIndex r + 1, r.term) :: r.log }, true)
    else ({ r with votesRec := rec' }, false)

/-! ## The abstract net, ghost, and the family step relation -/

/-- Ghost elections data (proof-side only, constitution §3.2): the
all-history vote record per voter and the victory record — verdi-raft's
`electionsData` promoted to the family interface (the ADAPTS driver
above: etcd's leader retains no tally, so the victory GHOST is the
only dialect-neutral carrier of the quorum evidence). -/
structure Ghost where
  votes : Nat → List (Nat × Nat)          -- voter ↦ (term, candidate)
  victories : List (Nat × Nat × List Nat) -- (term, leader, quorum)

/-- The abstract net a dialect projects into: node states by id plus
the ghost. In-flight packets stay dialect-side; the obligations
quantify over the projected axes only (the S1 chain provably never
consumes packets beyond the vote-record correspondence — T3's
`votes_nw` — which the ghost obligations absorb; see the log's
classification table). -/
structure SNet where
  node : Nat → ENode
  ghost : Ghost

/-! ## The obligation signature (the b′ family interface, S1 fragment)

Each member is a per-transition fact. The measured origin of each:
what T3's chain proofs actually consume from `ElectionSpecLemmas`
(the census in `docs/campaign-arc4b-log.md`, SC1 slice 1). The
vacuity discipline (design §8 D2) REQUIRES each obligation
dischargeable by BOTH dialects with visibly different
implementations; the per-member dialect notes record the intended
routes. LANDED STATUS: only the etcd instance exists
(`etcd_discharges`) — the second-dialect discharge is the open
I1-V debt (see the module-header status note; corrected at the
landing fix round from text that asserted the two-dialect property
as fact). -/

structure ElectObligations (voters : List Nat)
    (step : SNet → SNet → Prop) : Prop where
  /-- O1 — terms monotone. Verdi: `advanceCurrentTerm_spec`
  (ElectionSpecLemmas.lean:29) + per-handler term facts; etcd: the
  Step preamble only raises (raft.go:1120-1146), `becomeCandidate`
  raises (921), `reset` keeps-or-raises (800). -/
  termMono : ∀ {N N'}, step N N' → ∀ i, (N.node i).term ≤ (N'.node i).term
  /-- O2 — vote persistence within a term: a cast vote changes only
  with a term rise. Verdi: handler specs (votedFor unchanged /
  advanceCurrentTerm resets); etcd: `reset` clears vote ONLY on term
  change (raft.go:801-804); the grant path sets it at the (possibly
  just-raised) current term (raft.go:1278). -/
  votePersist : ∀ {N N'}, step N N' → ∀ i,
    (N'.node i).vote ≠ (N.node i).vote →
    (N.node i).vote = 0 ∨ (N.node i).term < (N'.node i).term
  /-- O3a — ghost votes grow monotonically. -/
  ghostVotesMono : ∀ {N N'}, step N N' → ∀ v t c,
    (t, c) ∈ N.ghost.votes v → (t, c) ∈ N'.ghost.votes v
  /-- O3b — ghost-vote intro/elim faithfulness: a NEW ghost entry for
  voter v is exactly a grant landed in v's post-state. Verdi:
  `update_elections_data_requestVote_votes_intro/_elim`
  (ElectionSpecLemmas.lean:515/475); etcd: the specRound ghost rule
  attaches the entry at `specRecvVote`'s grant. -/
  ghostVotesNew : ∀ {N N'}, step N N' → ∀ v t c,
    (t, c) ∈ N'.ghost.votes v → (t, c) ∉ N.ghost.votes v →
    (N'.node v).term = t ∧ (N'.node v).vote = c ∧ c ≠ 0
  /-- O4 — leader entry carries a quorum victory: a node ENTERING the
  leader state records a victory whose quorum all ghost-voted for it
  at its term. Verdi: `handleRequestVoteReply_leader_transition`
  (ElectionSpecLemmas.lean:1050) + `wonElection` at `votesReceived`;
  etcd: `specRecvVoteResp`'s quorum test over the post tally, ghost
  rule seeds the victory (the tally is then CLEARED — raft.go:813 —
  which is exactly why this is transition-scoped). -/
  leaderEntry : ∀ {N N'}, step N N' → ∀ i,
    (N.node i).state ≠ 2 → (N'.node i).state = 2 →
    ∃ q, isQuorum voters q ∧
      ((N'.node i).term, i, q) ∈ N'.ghost.victories ∧
      ∀ v ∈ q, ((N'.node i).term, i) ∈ N'.ghost.votes v
  /-- O5a — victories grow monotonically. -/
  victoriesMono : ∀ {N N'}, step N N' → ∀ e,
    e ∈ N.ghost.victories → e ∈ N'.ghost.victories
  /-- O5b — leader stability: a node that IS a leader stays a leader
  at the same term or leaves the leader state; its term cannot move
  while it remains leader. Verdi: leaders step down only through
  `advanceCurrentTerm` (type := Follower with the term rise); etcd: a
  leader's term rises only through the Step preamble's
  `becomeFollower` (raft.go:1140-1149), which leaves the leader
  state, and `stepLeader` never raises its own term. -/
  leaderStable : ∀ {N N'}, step N N' → ∀ i,
    (N.node i).state = 2 → (N'.node i).state = 2 →
    (N'.node i).term = (N.node i).term

/-! ## The superstructure (proved FROM the signature)

The reachability closure a dialect supplies (its own seeded start +
step star). Stated trace-free: `Reach` is any predicate closed under
`step` containing the seed, with the seed's ghost/leader emptiness. -/

/-- The invariant bundle the exit theorem consumes — T3's chain
compacted to the ghost-victory form (the ADAPTS reshape). I1 =
`one_vote_per_term` on the ghost (ElectionSafety.lean:188); I2 = the
victory-backed leader fact (replacing `votes_received_leaders`,
ElectionSafety.lean:702, per the ResetVotes finding). -/
structure ChainInv (voters : List Nat) (N : SNet) : Prop where
  oneVotePerTerm : ∀ v t c c',
    (t, c) ∈ N.ghost.votes v → (t, c') ∈ N.ghost.votes v → c = c'
  leaderVictory : ∀ i, (N.node i).state = 2 →
    ∃ q, isQuorum voters q ∧
      ((N.node i).term, i, q) ∈ N.ghost.victories ∧
      ∀ v ∈ q, ((N.node i).term, i) ∈ N.ghost.votes v

/-- The native S1 statement — `one_leader_per_term` at the
etcd-abstract level (T3's `Properties.lean:27` reshaped onto `SNet`;
the checker-implication leaf's premise, design §4). -/
def oneLeaderPerTerm (N : SNet) : Prop :=
  ∀ i j, (N.node i).state = 2 → (N.node j).state = 2 →
    (N.node i).term = (N.node j).term → i = j

/-! ### PROVED LINK 1 (calibration): quorum intersection for majority
quorums — the O6 discharge, dialect-free. T3 proves this via
dedup/pigeon (ElectionSafety.lean:1527-1698); here the two-quorum
counting core is restated over `isQuorum` and proved from a pigeonhole
argument on filtered lists. -/

theorem length_filter_add_length_filter_not (l : List Nat) (p : Nat → Bool) :
    (l.filter p).length + (l.filter (fun a => !(p a))).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hpa : p a with
    | true =>
      simp only [List.filter, hpa, Bool.not_true, List.length_cons]
      omega
    | false =>
      simp only [List.filter, hpa, Bool.not_false, List.length_cons]
      omega

theorem nodup_subset_length' {q l : List Nat} (hq : q.Nodup)
    (hsub : ∀ v ∈ q, v ∈ l) : q.length ≤ l.length := by
  induction q generalizing l with
  | nil => exact Nat.zero_le _
  | cons a q ih =>
    have ha : a ∈ l := hsub a (List.mem_cons_self ..)
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
    have hnd := List.nodup_cons.mp hq
    have hsub' : ∀ v ∈ q, v ∈ s ++ t := by
      intro v hv
      have hvl := hsub v (List.mem_cons_of_mem _ hv)
      rcases List.mem_append.mp hvl with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd hv hnd.1
        · exact List.mem_append.mpr (Or.inr h)
    have := ih hnd.2 hsub'
    simp only [List.length_append, List.length_cons] at *
    omega

/-- **PROVED LINK 1** — two majority quorums of the same voter list
intersect. (The O6/`quorumInter` discharge for the majority dialect —
what T3 gets from `pigeon`+`div2_correct`, re-derived here in the
`isQuorum` counting form to price the math layer: this file's proof
is ~40 lines against T3's ~170-line dedup/pigeon ring, because the
quorum-set form skips the dedup normalization the `votesReceived`
list route needs — a b′ dividend, the tally lists stay dialect-side.) -/
theorem majority_quorums_intersect {voters q q' : List Nat}
    (h : isQuorum voters q) (h' : isQuorum voters q') :
    ∃ v, v ∈ q ∧ v ∈ q' := by
  by_cases hex : ∃ v, v ∈ q ∧ v ∈ q'
  · exact hex
  exfalso
  have hno : ∀ v, v ∈ q → v ∉ q' := fun v hv hv' => hex ⟨v, hv, hv'⟩
  -- q ⊆ voters.filter (∈ q), q' ⊆ voters.filter (∉ q); count.
  obtain ⟨hnd, hsub, hmaj⟩ := h
  obtain ⟨hnd', hsub', hmaj'⟩ := h'
  have hq : q.length ≤ (voters.filter (fun v => q.contains v)).length := by
    refine nodup_subset_length' hnd ?_
    intro v hv
    exact List.mem_filter.mpr ⟨hsub v hv, by
      simpa [List.contains_iff_mem] using hv⟩
  have hq' : q'.length ≤
      (voters.filter (fun v => !(q.contains v))).length := by
    refine nodup_subset_length' hnd' ?_
    intro v hv
    refine List.mem_filter.mpr ⟨hsub' v hv, ?_⟩
    have : v ∉ q := fun hvq => hno v hvq hv
    simpa [List.contains_iff_mem] using this
  have hsum := length_filter_add_length_filter_not voters
    (fun v => q.contains v)
  omega

/-! ### PROVED LINK 2 (calibration): the exit assembly — the T3
`one_leader_per_term_ghost` 25-liner (ElectionSafety.lean:1722-1748)
re-derived over the signature's invariant bundle. -/

/-- **PROVED LINK 2** — ELECTION SAFETY from the chain invariants:
two same-term leaders' victory quorums intersect; the common voter's
ghost votes name both leaders at that term; one vote per term forces
equality. Statement-shape-identical to T3's ghost core; the proof is
12 lines against T3's 27 (the victory bundle pre-packages what T3
reassembles from `cronies_correct`'s four conjuncts). -/
theorem oneLeaderPerTerm_of_chainInv {voters : List Nat} {N : SNet}
    (hI : ChainInv voters N) : oneLeaderPerTerm N := by
  intro i j hi hj hterm
  obtain ⟨q, hq, -, hvotes⟩ := hI.leaderVictory i hi
  obtain ⟨q', hq', -, hvotes'⟩ := hI.leaderVictory j hj
  obtain ⟨v, hvq, hvq'⟩ := majority_quorums_intersect hq hq'
  have h1 := hvotes v hvq
  have h2 := hvotes' v hvq'
  rw [← hterm] at h2
  exact hI.oneVotePerTerm v _ i j h1 h2

/-! ### PROVED LINK 3 (calibration): an etcd-side obligation
discharge — `specRecvVote` discharges O1 (termMono) and O2
(votePersist) at the node level. This is the discharge layer's
per-lemma cost specimen: pure case analysis on the spec function. -/

/-- **PROVED LINK 3a** — the MsgVote receive step never lowers the
term (O1's per-arm discharge shape). -/
theorem specRecvVote_termMono (r : ENode) (f mT mLT mI : Nat) :
    r.term ≤ (specRecvVote r f mT mLT mI).1.term := by
  unfold specRecvVote
  by_cases h : r.term < mT
  · simp only [h, if_true]
    split <;> exact Nat.le_of_lt h
  · simp only [h, if_false]
    split <;> exact Nat.le_refl _

/-- **PROVED LINK 3b** — the MsgVote receive step changes a cast vote
only from None or across a term rise (O2's per-arm discharge shape:
the preamble's reset is a term rise; the grant path requires
`vote ∈ {0, from}`). -/
theorem specRecvVote_votePersist (r : ENode) (f mT mLT mI : Nat) :
    (specRecvVote r f mT mLT mI).1.vote ≠ r.vote →
    r.vote = 0 ∨ r.term < (specRecvVote r f mT mLT mI).1.term := by
  unfold specRecvVote
  by_cases hpre : r.term < mT
  · simp only [hpre, if_true]
    intro _
    right
    split <;> exact hpre
  · simp only [hpre, if_false]
    by_cases hgrant :
        ((r.vote == f || (r.vote == 0 && r.lead == 0)) &&
          upToDate r mLT mI) = true
    · simp only [hgrant, if_true]
      intro hne
      rcases Bool.and_eq_true .. |>.mp hgrant with ⟨hcv, -⟩
      rcases Bool.or_eq_true .. |>.mp hcv with h | h
      · exact absurd (Nat.beq_eq ▸ (by simpa using h) : r.vote = f).symm hne
      · left; exact by simpa using (Bool.and_eq_true .. |>.mp h).1
    · simp only [hgrant]
      intro hne
      exact absurd rfl hne

/-! ## The UNPROVED superstructure skeleton (statements only —
named Props, the b′ port ledger; classifications against T3)

Each is the b′ image of a T3 chain theorem. None is a theorem here —
proving them is the C3-native-S1 unit's work; SC1 prices them. -/

/-- SKELETON (PORTS — T3 `votes_le_currentTerm_invariant`,
ElectionSafety.lean:36; consumes O1 + O3b only): no ghost vote is
from the future. -/
def Skel_votesLeCurrentTerm (_voters : List Nat)
    (_step Reach : SNet → SNet → Prop) : Prop :=
  ∀ N₀ N, Reach N₀ N →
    ∀ v t c, (t, c) ∈ N.ghost.votes v → t ≤ (N.node v).term

/-- SKELETON (PORTS — T3 `votes_correct_invariant`,
ElectionSafety.lean:465; consumes O1 + O2 + O3a/b + votesLe): the
ghost history is one-vote-per-term and current-term-coherent. The
per-step obligations reshape from `votes_ok_*` (ElectionSafety.lean:
265-463, six step kinds) to one obligation-parametric preservation
lemma — the plumbing rewrite is the port's whole cost. -/
def Skel_votesCorrect (_voters : List Nat)
    (_step Reach : SNet → SNet → Prop) : Prop :=
  ∀ N₀ N, Reach N₀ N →
    (∀ v t c c', (t, c) ∈ N.ghost.votes v → (t, c') ∈ N.ghost.votes v →
      c = c') ∧
    (∀ v t c, (t, c) ∈ N.ghost.votes v → (N.node v).term = t →
      (N.node v).vote = c)

/-- SKELETON (ADAPTS — T3 `cronies_correct_invariant`,
ElectionSafety.lean:720, RESHAPED to the victory-ghost form: the
`votes_received_leaders` conjunct cannot port statement-intact
because etcd's `becomeLeader` clears the tally (raft.go:813); the
victory record carries the quorum evidence instead — consumes O4 +
O5a/b + O3a): every leader's victory is on record with its quorum's
ghost votes. -/
def Skel_leaderVictory (voters : List Nat)
    (_step Reach : SNet → SNet → Prop) : Prop :=
  ∀ N₀ N, Reach N₀ N →
    ∀ i, (N.node i).state = 2 →
      ∃ q, isQuorum voters q ∧
        ((N.node i).term, i, q) ∈ N.ghost.victories ∧
        ∀ v ∈ q, ((N.node i).term, i) ∈ N.ghost.votes v

/-- SKELETON (PORTS — the exit, T3 `one_leader_per_term_invariant`,
ElectionSafety.lean:1750; PROVED LINK 2 already discharges the
assembly given the two skeletons above, so this Prop's proof is
exactly `oneLeaderPerTerm_of_chainInv` + the two preservation
inductions): election safety over every reachable abstract net. -/
def Skel_oneLeaderPerTerm (_voters : List Nat)
    (_step Reach : SNet → SNet → Prop) : Prop :=
  ∀ N₀ N, Reach N₀ N → oneLeaderPerTerm N

/-! ## The T1-scoped alternative (decision input, not a route pick)

Under the twin driver the campaign event is issued ONCE, pre-loop
(tools/raftsubject/twin-chdriver.go:44), and no other event can make
a node candidate (`becomeCandidate` is reachable only from
`hup`/`campaign`; ticks are never driven). So under EVERY stream only
node 1 ever leaves the follower state, and S1's disagreement branch
(twin-lib.go:272-278) is unreachable by a one-invariant argument
("only node 1 ever claims") that needs NONE of the chain above. That
fact is driver-shaped (legitimate for T1 — the statement quantifies
over THIS driver's streams — and survives T2's num_parties, which
keeps the single pre-loop campaign) but buys nothing for the family.
Priced in the log as the ~0.5-unit floor; the signature route above
is the ~2.5–3-unit family investment. The coordinator's re-sequencing
call.

DELETED at the arc-4 landing fix round (2026-08-26):
`Skel_onlyNodeOneClaims`, the statement-only sketch of that floor
route — zero consumers anywhere in the tree, superseded by the
signature route (flagged for deletion at the arc4b landing, skipped
twice; the deletion test — whole-tree identifier scan + build — was
run at the fix round). The prose above remains as the decision
record. -/

end GoLean.RaftSeam.NativeSpec
