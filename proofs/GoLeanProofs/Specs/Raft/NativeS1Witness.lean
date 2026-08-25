import GoLeanProofs.Specs.Raft.NativeS1CheckerLeaf

/-! # C3 — the non-vacuity witness for the native S1 chain
(scoping lane `campaign-arc4b`, unit C3, 2026-08-27.)

The project's non-vacuity gate (CLAUDE.md): axiom-clean is not
enough — a law ships with a discharge witness that instantiates it
on a concrete instance and discharges every premise but the
genuinely-external ones. This module is that witness for the C3
chain: a CONCRETE four-step election run (the twin's shape — three
nodes over the seeded snapshot, node 1 campaigns, self-vote
response, one grant, victory at two of three) on which

- every `EStep` premise (`hfrom`/`htally`/`hgen`/`hc`/`hi` and the
  `hspec` defining equations) is discharged by computation,
- the headline `etcd_one_leader_per_term` applies and its subject
  net REALLY HAS a leader (`witness_leader` — the theorem is not
  vacuous over this net), and
- the S1 leaf fires end-to-end through a concrete `ClaimTrace` and
  a concrete interface instance (with the delta itself as the
  violation Prop — the one genuinely-external premise, the
  checker-side instantiation, exercised in its minimal form).

`voters3 = [1, 2, 3]` is an INSTANCE of the n-generic parameter —
the literal lives only here, never in the theory (I3 discipline).

Constructing this witness is what surfaced the self-vote ghost rule
(the `EStep` docstring's modeling-fidelity note): without it, this
very run — the subject's actual election shape — was unsimulable. -/

namespace GoLean.RaftSeam.NativeSpec

def voters3 : List Nat := [1, 2, 3]

/-- The boot node: follower over the seeded snapshot entry
(index 1, term 1) — twin-lib.go:198-202. -/
def wNode : ENode :=
  { state := 0, term := 1, vote := 0, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [] }

def wG0 : Ghost := { votes := fun _ => [], victories := [] }

/-- The boot net: all followers, empty ghost. -/
def wN0 : SNet := { node := fun _ => wNode, ghost := wG0 }

/-- Step 1 — node 1 campaigns (candidate, term 2, self ghost-vote). -/
def wN1 : SNet :=
  updNode wN0 1 (specBecomeCandidate (wN0.node 1) 1)
    (pushVote wN0.ghost 1 ((wN0.node 1).term + 1) 1)

theorem wStep1 : EStep voters3 wN0 wN1 := .campaign wN0 1 (by decide)

/-- Step 2's node result — the self-response is counted (tally
`[(1, true)]`), one of three is no quorum. -/
def wR2 : ENode :=
  { state := 1, term := 2, vote := 1, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [(1, true)] }

def wN2 : SNet := updNode wN1 1 wR2 wN1.ghost

theorem wStep2 : EStep voters3 wN1 wN2 :=
  .recvVoteResp wN1 1 1 false wR2 false (by decide)
    ⟨by decide, by decide, by decide⟩ (fun _ => by decide) (by rfl)

/-- Step 3's node result — node 2 grants (preamble to term 2, then
the up-to-date check passes on equal last entries). -/
def wR3 : ENode :=
  { state := 0, term := 2, vote := 1, lead := 0, log := [(1, 1)],
    committed := 1, votesRec := [] }

def wN3 : SNet := updNode wN2 2 wR3 (pushVote wN2.ghost 2 wR3.term 1)

theorem wStep3 : EStep voters3 wN2 wN3 :=
  .recvVote wN2 2 1 2 1 1 wR3 true (by decide) (by rfl)

/-- Step 4's node result — node 2's grant arrives; tally
`[(2,true),(1,true)]` is two of three: VICTORY. `becomeLeader`
clears the tally (the ADAPTS driver, live in the witness) and
appends the noop `(2, 2)`. -/
def wR4 : ENode :=
  { state := 2, term := 2, vote := 1, lead := 1,
    log := [(2, 2), (1, 1)], committed := 1, votesRec := [] }

def wN4 : SNet :=
  updNode wN3 1 wR4 (pushVictory wN3.ghost 2 1 [2, 1])

theorem wStep4 : EStep voters3 wN3 wN4 :=
  .recvVoteResp wN3 1 2 false wR4 true (by decide)
    ⟨by decide, by decide, by decide⟩ (fun _ => by decide) (by rfl)

/-- The whole run. -/
theorem wReach : ReachRel (EStep voters3) wN0 wN4 :=
  .tail (.tail (.tail (.tail (.refl _) wStep1) wStep2) wStep3) wStep4

theorem wSeed_votes : ∀ v t c, (t, c) ∉ wN0.ghost.votes v :=
  fun _ _ _ h => nomatch h

theorem wSeed_noLeaders : ∀ i, (wN0.node i).state ≠ 2 :=
  fun _ => by show wNode.state ≠ 2; decide

/-- The final net really has a leader — the headline below is not
vacuous over this net. -/
theorem witness_leader :
    (wN4.node 1).state = 2 ∧ (wN4.node 1).term = 2 := by decide

/-- **WITNESS 1** — the headline theorem applied to the concrete
run: every premise discharged, subject net has a leader. -/
theorem witness_oneLeaderPerTerm : oneLeaderPerTerm wN4 :=
  etcd_one_leader_per_term voters3 wSeed_votes wSeed_noLeaders wReach

/-- **WITNESS 2** — the S1 leaf end-to-end on the concrete run: the
observation trace records the leader claim `(2, 1)` at the final
net; the interface instance takes the delta Prop itself as the
violation (the minimal checker-side instantiation — the real
checker's is the arc-4 lane's I2 work); the leaf concludes no
delta. -/
theorem witness_s1_leaf : ¬ S1Delta [(2, 1)] :=
  etcd_s1_leaf voters3 wSeed_votes wSeed_noLeaders (.refl _)
    ⟨.obs wReach witness_leader.1 witness_leader.2 (.done _), id⟩

/-- **WITNESS 3** — the `TallyOK` redundancy corollary on the
concrete run (the guard premise is derivable at the final net, as
the reachability argument promises). -/
theorem witness_tallyOK : ∀ i, TallyOK voters3 wN4 i :=
  tallyOK_reachable (fun _ => rfl) wReach

end GoLean.RaftSeam.NativeSpec
