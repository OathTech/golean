import GoLeanProofs.Specs.Raft.NativeObligations

/-! # C3 — the native S1 chain over the obligation signature
(scoping lane `campaign-arc4b`, unit C3, 2026-08-27; design of
record: the campaign worktree's
`docs/2026-08-26_campaign-flexibility-redesign.md` §3 I1 — the
obligation signature as the spec⟷dialect interface; SC1's sized plan
in `docs/campaign-arc4b-log.md`.)

## What this module is

Charter parts 1+2: the obligation-parametric INDUCTION PRINCIPLE
(the `RefinedProofStructure.refined_raft_net_invariant` analog — one
signature-parametric principle replacing the concrete-handler-equation
plumbing, exactly as SC1's zero-residue census predicted) and the S1
SUPERSTRUCTURE re-plumbed over `ElectObligations` up through the
native `one_leader_per_term`. Per SC1's per-lemma classification this
is "re-plumbing, not re-reasoning": every preservation argument below
is T3's (`compat/verdi/VerdiCompat/ElectionSafety.lean`, cited per
theorem at branch base 740c719e), with the ONE measured ADAPTS
reshape — `cronies_correct` → the victory-ghost form (`leaderVictory`
below), because etcd's `becomeLeader` clears the tally
(raftsubject/raft/raft.go:952→800→813) so the leader-quorum fact is
transition-scoped (obligation O4) and ghost-carried.

n-GENERIC throughout (I3's demand): `voters : List Nat` is the one
configuration parameter; no literal party count appears anywhere in
this file.

A deliberate b′ simplification, recorded: T3's `votes_correct` has a
THIRD conjunct (`currentTerm_votedFor_votes_correct`,
ElectionSafety.lean:201 — the converse direction, current vote ∈
ghost) consumed by its `votes_nw`/cronies plumbing. The victory ghost
absorbs that consumer (O4 hands the quorum's votes directly), so the
native chain carries only the two conjuncts `Skel_votesCorrect`
states, plus the two auxiliaries (`votesLe`, `nonzero`) the
preservation induction itself needs.

LINEAGE: parametric invariance over an abstract transition-system
signature (Abadi–Lamport auxiliary/ghost variables; the TLA+/IOA
refinement-family classic). The induction principle is the standard
reflexive-transitive-closure invariance rule — no new mechanism
class.

## The reachability closure

SC1's skeleton Props take an abstract binary `Reach`; the intended
instantiation ("any predicate closed under step containing the seed,
with the seed's ghost/leader emptiness" — NativeObligations.lean's
superstructure header) is `GoodReach step N₀ N := Seed N₀ ∧
ReachRel step N₀ N` below, and every skeleton is discharged at
exactly that instantiation, for EVERY obligation-discharging dialect
at once. -/

namespace GoLean.RaftSeam.NativeSpec

/-- Reflexive-transitive closure of a dialect's abstract step. -/
inductive ReachRel (step : SNet → SNet → Prop) : SNet → SNet → Prop where
  | refl (N : SNet) : ReachRel step N N
  | tail {N₀ N N' : SNet} :
      ReachRel step N₀ N → step N N' → ReachRel step N₀ N'

theorem ReachRel.trans {step : SNet → SNet → Prop} {A B C : SNet}
    (hab : ReachRel step A B) (hbc : ReachRel step B C) :
    ReachRel step A C := by
  induction hbc with
  | refl => exact hab
  | tail _ hs ih => exact .tail ih hs

/-- **The obligation-parametric induction principle** (charter part
1): any predicate preserved by the dialect's step holds on the whole
reachable set from any state satisfying it. This is the b′
replacement for T3's `refined_raft_net_invariant`
(`RefinedProofStructure.lean`): where T3's principle hands each
obligation a concrete handler equation, this one hands the
preservation premise whatever the OBLIGATION SIGNATURE provides —
the invariant proofs below consume `ElectObligations` members only,
never a dialect's handlers. -/
theorem invariance {step : SNet → SNet → Prop} {P : SNet → Prop}
    (hstep : ∀ {N N'}, P N → step N N' → P N')
    {N₀ N : SNet} (h0 : P N₀) (hr : ReachRel step N₀ N) : P N := by
  induction hr with
  | refl => exact h0
  | tail _ hs ih => exact hstep ih hs

/-- Ghost votes persist along the closure (O3a starred) — the
carrier of the cross-time argument below. -/
theorem ghostVotes_mono_star {voters : List Nat}
    {step : SNet → SNet → Prop} (ob : ElectObligations voters step)
    {N N' : SNet} (hr : ReachRel step N N') {v t c : Nat}
    (hin : (t, c) ∈ N.ghost.votes v) : (t, c) ∈ N'.ghost.votes v := by
  induction hr with
  | refl => exact hin
  | tail _ hs ih => exact ob.ghostVotesMono hs v t c ih

/-! ## The seed and the invariant bundle -/

/-- The dialect-neutral seed conditions: no ghost votes, no leaders.
(Deliberately MINIMAL — victory-record emptiness is not needed:
`leaderVictory` at the seed is vacuous through `noLeaders`. Both
dialects' inits satisfy this trivially: the twin boots three
followers over the seeded snapshot, twin-lib.go:198-215; Verdi's
`init_handlers` starts all followers with empty `electionsData`.) -/
structure Seed (N : SNet) : Prop where
  votesEmpty : ∀ v t c, (t, c) ∉ N.ghost.votes v
  noLeaders : ∀ i, (N.node i).state ≠ 2

/-- The seeded reachability closure — the `Reach` instantiation of
every SC1 skeleton Prop. -/
def GoodReach (step : SNet → SNet → Prop) (N₀ N : SNet) : Prop :=
  Seed N₀ ∧ ReachRel step N₀ N

/-- The full inductive invariant bundle (the S1 chain compacted):

- `votesLe` — PORTS (T3 `votes_le_currentTerm_invariant`,
  ElectionSafety.lean:36; consumes O1 + O3b);
- `oneVote` + `coherent` — PORTS (T3 `votes_correct_invariant`'s
  first two conjuncts, ElectionSafety.lean:465/187/194; consumes
  O1 + O2 + O3a/b + votesLe; T3's six `votes_ok_*` step obligations
  are here ONE obligation-parametric preservation lemma — the
  plumbing rewrite SC1 priced);
- `nonzero` — plumbing auxiliary (T3 gets this from `votedFor :
  Option name`'s `some`; the Nat-encoded vocabulary carries it as an
  invariant; consumes O3b);
- `leaderVictory` — ADAPTS (T3 `cronies_correct_invariant`,
  ElectionSafety.lean:720, reshaped to the victory-ghost form per the
  ResetVotes finding; consumes O4 + O5a/b + O3a).

`ChainInv` (the exit's premise, NativeObligations.lean) is a face of
this bundle — `toChainInv` below. -/
structure FullInv (voters : List Nat) (N : SNet) : Prop where
  votesLe : ∀ v t c, (t, c) ∈ N.ghost.votes v → t ≤ (N.node v).term
  oneVote : ∀ v t c c', (t, c) ∈ N.ghost.votes v →
    (t, c') ∈ N.ghost.votes v → c = c'
  coherent : ∀ v t c, (t, c) ∈ N.ghost.votes v →
    (N.node v).term = t → (N.node v).vote = c
  nonzero : ∀ v t c, (t, c) ∈ N.ghost.votes v → c ≠ 0
  leaderVictory : ∀ i, (N.node i).state = 2 →
    ∃ q, isQuorum voters q ∧
      ((N.node i).term, i, q) ∈ N.ghost.victories ∧
      ∀ v ∈ q, ((N.node i).term, i) ∈ N.ghost.votes v

theorem FullInv.toChainInv {voters : List Nat} {N : SNet}
    (h : FullInv voters N) : ChainInv voters N :=
  ⟨h.oneVote, h.leaderVictory⟩

/-! ## The preservation induction (the port's substance) -/

/-- The seed satisfies the bundle (T3's init obligations,
`ElectionSafety.lean` `votes_init`/`cronies_init` class: everything
is vacuous over empty ghosts and no leaders). -/
theorem FullInv.of_seed {voters : List Nat} {N : SNet}
    (hs : Seed N) : FullInv voters N where
  votesLe v t c hin := absurd hin (hs.votesEmpty v t c)
  oneVote v t c _ hin _ := absurd hin (hs.votesEmpty v t c)
  coherent v t c hin _ := absurd hin (hs.votesEmpty v t c)
  nonzero v t c hin := absurd hin (hs.votesEmpty v t c)
  leaderVictory i hlead := absurd hlead (hs.noLeaders i)

/-- **The one obligation-parametric preservation lemma** — T3's
per-handler `votes_ok_*` ring (ElectionSafety.lean:265-463, six step
kinds) plus the cronies preservation, re-plumbed to consume ONLY
signature members. The reasoning per conjunct is T3's, re-anchored:

- `votesLe`: old entries ride O1 (termMono); new entries are AT the
  post-term by O3b.
- `coherent`: a new entry is coherent by O3b; an old entry at the
  post-term forces (via votesLe + O1) an unchanged term, so O2
  (votePersist) pins the vote — the `nonzero` auxiliary rules out
  the reset-to-None escape.
- `oneVote`: two old entries ride the IH; ANY new entry pins the
  post-term to `t`, so post-`coherent` (just established) equates
  both candidates with the post-vote — T3's argument, shortened by
  the bundle order.
- `leaderVictory`: a STAYING leader keeps its term (O5b), its
  victory (O5a), and its quorum's votes (O3a); a NEW leader is
  exactly O4's conclusion. (The ADAPTS shape: T3 re-derives the
  leader's tally here; the victory ghost carries it instead.) -/
theorem FullInv.step {voters : List Nat} {step : SNet → SNet → Prop}
    (ob : ElectObligations voters step) {N N' : SNet}
    (hI : FullInv voters N) (hs : step N N') : FullInv voters N' := by
  -- votesLe
  have hle : ∀ v t c, (t, c) ∈ N'.ghost.votes v → t ≤ (N'.node v).term := by
    intro v t c hin
    by_cases hold : (t, c) ∈ N.ghost.votes v
    · exact Nat.le_trans (hI.votesLe v t c hold) (ob.termMono hs v)
    · exact Nat.le_of_eq (ob.ghostVotesNew hs v t c hin hold).1.symm
  -- nonzero
  have hnz : ∀ v t c, (t, c) ∈ N'.ghost.votes v → c ≠ 0 := by
    intro v t c hin
    by_cases hold : (t, c) ∈ N.ghost.votes v
    · exact hI.nonzero v t c hold
    · exact (ob.ghostVotesNew hs v t c hin hold).2.2
  -- coherent
  have hco : ∀ v t c, (t, c) ∈ N'.ghost.votes v →
      (N'.node v).term = t → (N'.node v).vote = c := by
    intro v t c hin hterm
    by_cases hold : (t, c) ∈ N.ghost.votes v
    · -- old entry at the post-term: the term cannot have moved.
      have h1 : t ≤ (N.node v).term := hI.votesLe v t c hold
      have h2 : (N.node v).term ≤ (N'.node v).term := ob.termMono hs v
      have hpre : (N.node v).term = t := by omega
      have hvote : (N.node v).vote = c := hI.coherent v t c hold hpre
      by_cases hch : (N'.node v).vote = (N.node v).vote
      · rw [hch, hvote]
      · rcases ob.votePersist hs v hch with h0 | hlt
        · exact absurd (hvote ▸ h0) (hI.nonzero v t c hold)
        · omega
    · rcases ob.ghostVotesNew hs v t c hin hold with ⟨-, hv, -⟩
      exact hv
  -- oneVote
  have hone : ∀ v t c c', (t, c) ∈ N'.ghost.votes v →
      (t, c') ∈ N'.ghost.votes v → c = c' := by
    intro v t c c' hc hc'
    by_cases holdc : (t, c) ∈ N.ghost.votes v
    · by_cases holdc' : (t, c') ∈ N.ghost.votes v
      · exact hI.oneVote v t c c' holdc holdc'
      · -- (t, c') new pins the post-term; post-coherence equates both.
        have ht := (ob.ghostVotesNew hs v t c' hc' holdc').1
        rw [← hco v t c hc ht, ← hco v t c' hc' ht]
    · have ht := (ob.ghostVotesNew hs v t c hc holdc).1
      rw [← hco v t c hc ht, ← hco v t c' hc' ht]
  refine ⟨hle, hone, hco, hnz, ?_⟩
  -- leaderVictory
  intro i hlead'
  by_cases hpre : (N.node i).state = 2
  · obtain ⟨q, hq, hvic, hvotes⟩ := hI.leaderVictory i hpre
    have hterm : (N'.node i).term = (N.node i).term :=
      ob.leaderStable hs i hpre hlead'
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hterm]; exact ob.victoriesMono hs _ hvic
    · intro v hv
      rw [hterm]; exact ob.ghostVotesMono hs v _ _ (hvotes v hv)
  · exact ob.leaderEntry hs i hpre hlead'

/-- The bundle holds on the whole seeded reachable set — the
induction principle applied once. -/
theorem fullInv_reachable {voters : List Nat}
    {step : SNet → SNet → Prop} (ob : ElectObligations voters step)
    {N₀ N : SNet} (hseed : Seed N₀) (hr : ReachRel step N₀ N) :
    FullInv voters N :=
  invariance (fun hP hs => hP.step ob hs) (FullInv.of_seed hseed) hr

/-! ## The native `one_leader_per_term` (the exit) -/

/-- **THE NATIVE `one_leader_per_term`** — election safety for EVERY
dialect that discharges the S1 obligation signature, from any seeded
start, over its whole reachable set (T3
`one_leader_per_term_invariant`, ElectionSafety.lean:1750, re-plumbed;
the assembly is SC1's PROVED LINK 2). First-order and
dialect-parametric: `voters` is the only configuration parameter
(n-generic — T2's `num_parties` instantiates it), `step` the only
dialect parameter. -/
theorem native_one_leader_per_term {voters : List Nat}
    {step : SNet → SNet → Prop} (ob : ElectObligations voters step)
    {N₀ N : SNet} (hseed : Seed N₀) (hreach : ReachRel step N₀ N) :
    oneLeaderPerTerm N :=
  oneLeaderPerTerm_of_chainInv (fullInv_reachable ob hseed hreach).toChainInv

/-- **CROSS-TIME election safety** — the form the twin's S1 check
actually consumes (twin-lib.go harvest: `leaderOf : term ↦ node`
accumulates claims ACROSS harvests, so the checked property compares
leaders observed at DIFFERENT points of one trace, not one net's
simultaneous leaders). No extra signature member is needed: the
observation at the earlier net is carried forward by vote
monotonicity (O3a starred) — the common quorum voter's two ghost
votes meet in the LATER net, where `oneVote` closes. (This is the
victory-ghost device paying for exactly what it was promoted for.) -/
theorem native_one_leader_per_term_cross_time {voters : List Nat}
    {step : SNet → SNet → Prop} (ob : ElectObligations voters step)
    {N₀ N₁ N₂ : SNet} (hseed : Seed N₀)
    (h01 : ReachRel step N₀ N₁) (h12 : ReachRel step N₁ N₂)
    {t i j : Nat}
    (hi : (N₁.node i).state = 2) (hit : (N₁.node i).term = t)
    (hj : (N₂.node j).state = 2) (hjt : (N₂.node j).term = t) :
    i = j := by
  obtain ⟨q, hq, -, hvotes⟩ :=
    (fullInv_reachable ob hseed h01).leaderVictory i hi
  have hI2 := fullInv_reachable ob hseed (h01.trans h12)
  obtain ⟨q', hq', -, hvotes'⟩ := hI2.leaderVictory j hj
  obtain ⟨v, hvq, hvq'⟩ := majority_quorums_intersect hq hq'
  have h1v : (t, i) ∈ N₂.ghost.votes v :=
    ghostVotes_mono_star ob h12 (hit ▸ hvotes v hvq)
  have h2v : (t, j) ∈ N₂.ghost.votes v := hjt ▸ hvotes' v hvq'
  exact hI2.oneVote v t i j h1v h2v

/-! ## The SC1 skeletons, discharged

Each named Prop from `NativeObligations.lean`'s port ledger is proved
at the `GoodReach` instantiation, obligation-parametrically — one
theorem per skeleton, for every discharging dialect at once. -/

theorem skel_votesLeCurrentTerm_proved (voters : List Nat)
    (step : SNet → SNet → Prop) (ob : ElectObligations voters step) :
    Skel_votesLeCurrentTerm voters step (GoodReach step) :=
  fun _ _ ⟨hseed, hr⟩ v t c hin =>
    (fullInv_reachable ob hseed hr).votesLe v t c hin

theorem skel_votesCorrect_proved (voters : List Nat)
    (step : SNet → SNet → Prop) (ob : ElectObligations voters step) :
    Skel_votesCorrect voters step (GoodReach step) :=
  fun _ _ ⟨hseed, hr⟩ =>
    ⟨(fullInv_reachable ob hseed hr).oneVote,
     (fullInv_reachable ob hseed hr).coherent⟩

theorem skel_leaderVictory_proved (voters : List Nat)
    (step : SNet → SNet → Prop) (ob : ElectObligations voters step) :
    Skel_leaderVictory voters step (GoodReach step) :=
  fun _ _ ⟨hseed, hr⟩ => (fullInv_reachable ob hseed hr).leaderVictory

theorem skel_oneLeaderPerTerm_proved (voters : List Nat)
    (step : SNet → SNet → Prop) (ob : ElectObligations voters step) :
    Skel_oneLeaderPerTerm voters step (GoodReach step) :=
  fun _ _ ⟨hseed, hr⟩ => native_one_leader_per_term ob hseed hr

end GoLean.RaftSeam.NativeSpec
