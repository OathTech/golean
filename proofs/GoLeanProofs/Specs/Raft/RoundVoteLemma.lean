import GoLeanProofs.Specs.Raft.RoundVoteEquation
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.Relocate

/-!
# A4-U23: THE R-FORM'S SECOND PROVED INSTANCE — the MsgVote
real-vote-family ROUND LEMMA

`roundVote_lemma` proves `RoundLemmaShape canonVote canonVote'
roundVoteC0 19291 πVote` — the R-form's SECOND instance (first:
`RoundMa.roundMa_lemma`, A4-U22), at the first ELECTION-kind round.
From ANY `FrameSim` placement of the canonical MsgVote-round
loop-head state, the full round (m.Term > r.Term → becomeFollower(1,
None) → the vote grant on the up-to-date check → the hardstate-only
harvest ring → driver suffix) completes in 19,291 steps consuming
exactly the censused nine-draw prefix, RETURNS to the same loop-head
configuration, and the post-state is a placement of the successor
family (closure).

## Construction

Exactly the U22 assembly (canonical run + wholesale weak transport
via `stepFnIter_sim`; LINEAGE: Abadi–Lamport refinement mapping, as
the R-form's docstring pins) — this unit's test of U22's marginal-
cost claim: ADDING A ROUND KIND COSTS ITS WINDOWS ONLY. One template
delta, reported in the log: the boundary schedule is AUTO-DISCOVERED
from the mirror's own quit sites (`artifacts/probe/RoundVoteGen2.lean`)
because the vote round has a crossing the choice census cannot see —
becomeFollower's Visit-loop mapIterK exhaustion-EXIT (round step
3793), a choice-FREE mirror quit site (`roundVote_visitExit`, stated
∀-stream).

## The draw prefix and the choice-invariance seam

`πVote = [pick] ++ latitude` — position 0 is THE SEMANTIC DELIVERY
PICK; positions 1–4 the Visit mapIters (latitude: map-iteration
order — SC1's becomeFollower reset bucket at instance level);
positions 5–8 latitude appendSpills (capacity only). The factored
form awaits the arc4c ~, exactly as U22 recorded; the latitude
positions are identified per-crossing in the RoundVoteEq*
docstrings.

## The round-kind matrix (census U21, now proved at lemma level)

The vote round writes the HARD STATE (SetHardState — Term/Vote
persistence) but produces NO storage-resp arms (no entries/commit
movement): Advance is the no-op shell, and committed/applying/applied
stay 1 on both ends (readouts below). Round-kind matrix:
heartbeat = no ring work (T1-vacuous); MsgVote = hardstate-only ring;
MsgApp-append = the full storage-resp ring (U21/U22).

## Fixture-family preconditions

The real vote family at the decoded snapshot-boot log (Term 1 REAL,
the up-to-date check against the (1,1) last entry; probe
`TwinVoteFixProbe.lean`); canonical zero draws; the RE-SPILL residual
family for the ∀-stream envelope — the C2c convention. MsgVote rounds
are REACHABLE and load-bearing (the pinned run's real vote rounds:
19,611/19,973 steps — U18 census; this fixture 19,291, in range).
-/

namespace GoLean.RaftSeam.RoundVote

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The zero valuation (the literals carry no atoms). -/
def rvρ0 : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }

/-- The pinned-table carrier. -/
def rvσT : ExecState := bfTB.toState

theorem rvAgrees : bfTB.Agrees rvσT := ⟨rfl, rfl, rfl, rfl⟩

/-- **The canonical MsgVote-round loop-head state** (the R-form's
`canon`). -/
def canonVote : ExecState := γS rvρ0 rvσT mvSB0

/-- The successor canonical state (`canon'`): the end-anchor state. -/
def canonVote' : ExecState := γS rvρ0 rvσT mvSB26

/-- The shared loop-head configuration (the R-form's `C0`). -/
def roundVoteC0 : Config := γC rvρ0 mvCB0

/-- **SELF-RETURNING at the machine level, kernel-checked** (closed;
the Sym literals differ representationally — reflected vs
mirror-propagated — but their machine images are IDENTICAL; #eval'd
true before stating, per the eval-first rule). -/
theorem roundVote_selfReturn_conc : γC rvρ0 mvCB26 = roundVoteC0 := by
  kernel_rfl

/-- The canonical run at the concrete states, returning to
`roundVoteC0`. -/
theorem roundVote_run_conc (rest : Choices) :
    stepFnIter 19291 canonVote roundVoteC0 (πVote ++ rest)
      = .ok (roundVoteC0, canonVote', rest) := by
  have h := roundVote_run rvρ0 rvσT rvAgrees rest
  rwa [roundVote_selfReturn_conc] at h

/-- **THE R-FORM'S SECOND PROVED INSTANCE**: the MsgVote
real-vote-family round lemma — from ANY FrameSim placement of
`canonVote`, the round completes self-returning with the censused
prefix consumed, and the post-state is a placement of the successor
family at the SAME frame indexes (closure). -/
theorem roundVote_lemma :
    RoundLemmaShape canonVote canonVote' roundVoteC0 19291 πVote := by
  intro r na₀ na fr σF hF ch
  have hrun := roundVote_run_conc ch
  have hsim := stepFnIter_sim (ρ := r) (na₀ := na₀) (na := na) (fr := fr)
    19291 hF roundVoteC0 (πVote ++ ch)
  obtain ⟨⟨cF, σF', chF⟩, hrunF, hcfg, hfs, hch⟩ := hsim.ok_inv hrun
  dsimp only at hcfg hfs hch
  subst hcfg
  subst hch
  exact ⟨σF', hrunF, na, fr, hfs⟩

/-! ## The witness (witness-in-same-slice; the R-form instance
discharged at concrete placements) -/

/-- The identity-placement witness: `roundVote_lemma` applied at
`RoundFam.self`'s placement gives back the canonical run — every
premise concrete, no placement left abstract. -/
theorem roundVote_witness_identity :
    ∃ σF', stepFnIter 19291 canonVote
        (renameConfig (ρT canonVote.nextAddr 0) roundVoteC0) (πVote ++ [])
        = .ok (renameConfig (ρT canonVote.nextAddr 0) roundVoteC0, σF', [])
      ∧ ∃ na' fr', FrameSim (ρT canonVote.nextAddr 0) canonVote.nextAddr
          na' fr' canonVote' σF' := by
  have hF : FrameSim (ρT canonVote.nextAddr 0) canonVote.nextAddr
      canonVote.nextAddr [] canonVote canonVote :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero canonVote.nextAddr f.body)
  exact roundVote_lemma _ _ _ _ canonVote hF []

/-- The family CLOSURE at the identity witness: the successor state
is a `RoundFam` member of the successor canon — the induction's
carried membership, re-established. -/
theorem roundVote_closure :
    ∃ σF', RoundFam canonVote' σF' := by
  obtain ⟨σF', _, na', fr', hfs⟩ := roundVote_witness_identity
  exact ⟨σF', ρT canonVote.nextAddr 0, canonVote.nextAddr, na', fr', hfs⟩

/-! ## The abstract round delta (readouts at the concrete anchors;
every value #eval-checked first — `artifacts/probe/
RoundVoteReadoutProbe.lean` → `roundvotereadout.out`) -/

/-- The twin cell (cell 121 — the fixture's, as U21/U22's). -/
def rvTwinLoc : Loc := .base ⟨121⟩

/-- PRE: counters zero, ONE live MsgVote (typ 5, 1 → 2) in flight. -/
theorem roundVote_pre_read :
    (absTwinRead canonVote rvTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(true, 5, 1, 2)]) := by
  kernel_rfl

/-- POST: counters unchanged (violations 0 — the checker held), the
MsgVote marked DEAD, the MsgVoteResp (typ 6, 2 → 1) appended LIVE. -/
theorem roundVote_post_read :
    (absTwinRead canonVote' rvTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(false, 5, 1, 2), (true, 6, 2, 1)]) := by
  kernel_rfl

/-- POST, the delivered node through the deep reader: node 2's raft
`Term` became 1 (the m.Term > r.Term becomeFollower branch — the
vote round's hardstate half). -/
theorem roundVote_post_term :
    (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "Term")
      = some 1 := by
  kernel_rfl

theorem roundVote_pre_term :
    (absTwinNodeRaft canonVote rvTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVote a ⟨"raft.raft"⟩ "Term")
      = some 0 := by
  kernel_rfl

/-- POST: node 2's raft `Vote` became 1 (the grant — the vote round's
OTHER hardstate half; both persisted by the ring's SetHardState). -/
theorem roundVote_post_vote :
    (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "Vote")
      = some 1 := by
  kernel_rfl

theorem roundVote_pre_vote :
    (absTwinNodeRaft canonVote rvTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVote a ⟨"raft.raft"⟩ "Vote")
      = some 0 := by
  kernel_rfl

/-- POST: node 2 remains a follower with NO leader (`lead = 0` —
granting a vote names no leader; state = 0 = StateFollower). -/
theorem roundVote_post_lead :
    (absTwinNodeRaft canonVote' rvTwinLoc 1).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVote' a ⟨"raft.raft"⟩ "lead")
      = some 0 := by
  kernel_rfl

end GoLean.RaftSeam.RoundVote
