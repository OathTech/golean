import GoLeanProofs.Specs.Raft.RoundVrEquation
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.Relocate

/-!
# A4-U25: THE R-FORM'S FOURTH PROVED INSTANCE — the MsgVoteResp
ELECTION-COMPLETION ROUND LEMMA (candidate → leader)

`roundVr_lemma` proves `RoundLemmaShape canonVr canonVr' roundVrC0
33274 πVr` — the round-kind matrix's LAST structural ring shape: the
CANDIDATE handles the quorum-completing MsgVoteResp
(`poll(2, granted)` → quorum won → `becomeLeader()` → the noop
append → `bcastAppend`), i.e. THE ANCHOR 2→3 TRANSITION of the real
pinned run, replayed at a doctored single-message fixture. The
LEADERSHIP CLAIM IS BORN in this round: the twin's harvest records
node 1's claim at becomeLeader (claims 0 → 1 through `absTwinRead`),
which is exactly the event the S1 checker chain
(`NativeS1Chain`/`NativeCheckerBridge`) folds over — the round that
MANUFACTURES an S1 claim, closing the structural ring-shape matrix
the round induction will quantify over.

## The fixture (anchor 2 — the doctor+prune template)

Anchor 2 (cum step 139,898) is the last CANDIDATE loop head (node 1:
state=1, Term=1, Vote=1 — the self-vote already polled). Doctor: the
single live MsgVoteResp {Type 6, From 2, To 1, Term 1, Reject nil =
GRANTED}; prune: 49 cells (probe `TwinVrFixProbe.lean` →
`vrfix.out`). Round: **33,274 steps / 25 draws, self-returning**.
POST (all #eval'd first, `roundvrreadout.out`): state 1→2, lead
0→1, Term 1→1; committed/applied 1→1 (the noop is APPENDED but its
quorum-commit is the Mar family's round — the matrix's rows
compose); net: the resp DEAD, TWO MsgApp (1→2, 1→3, the noop
broadcast) LIVE.

## The draw prefix

`πVr` = 25 zeros: position 0 THE SEMANTIC DELIVERY PICK; the rest
latitude — 16 tracker/map Visit mapIters (four Visit clusters:
poll bookkeeping, becomeLeader's progress resets, bcastAppend's
peer walk; table-pinned per the U23 finding) + 8 appendSpills (the
noop storage-append ring + send assemblies). FIVE choice-free Visit
exhaustion-exits crossed ∀-stream (the auto-discovery template's
crossings — the FOURTH round kind confirming the census cannot see
them). The factored ∀-latitude form awaits the arc4c ~, as
U22/U23/U24 recorded.
-/

namespace GoLean.RaftSeam.RoundVr

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The zero valuation (the literals carry no atoms). -/
def vrρ0 : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }

/-- The pinned-table carrier. -/
def vrσT : ExecState := bfTB.toState

theorem vrAgrees : bfTB.Agrees vrσT := ⟨rfl, rfl, rfl, rfl⟩

/-- **The canonical election-completion loop-head state**. -/
def canonVr : ExecState := γS vrρ0 vrσT vrSB0

/-- The successor canonical state (node 1 LEADER). -/
def canonVr' : ExecState := γS vrρ0 vrσT vrSB69

/-- The shared loop-head configuration. -/
def roundVrC0 : Config := γC vrρ0 vrCB0

/-- Self-returning at the machine level (#eval'd true first). -/
theorem roundVr_selfReturn_conc : γC vrρ0 vrCB69 = roundVrC0 := by
  kernel_rfl

/-- The canonical run at the concrete states. -/
theorem roundVr_run_conc (rest : Choices) :
    stepFnIter 33274 canonVr roundVrC0 (πVr ++ rest)
      = .ok (roundVrC0, canonVr', rest) := by
  have h := roundVr_run vrρ0 vrσT vrAgrees rest
  rwa [roundVr_selfReturn_conc] at h

/-- **THE R-FORM'S FOURTH PROVED INSTANCE**: the election-completion
round lemma — candidate → leader, from ANY FrameSim placement,
self-returning with the censused 25-draw prefix consumed, closure at
the successor family. -/
theorem roundVr_lemma :
    RoundLemmaShape canonVr canonVr' roundVrC0 33274 πVr := by
  intro r na₀ na fr σF hF ch
  have hrun := roundVr_run_conc ch
  have hsim := stepFnIter_sim (ρ := r) (na₀ := na₀) (na := na) (fr := fr)
    33274 hF roundVrC0 (πVr ++ ch)
  obtain ⟨⟨cF, σF', chF⟩, hrunF, hcfg, hfs, hch⟩ := hsim.ok_inv hrun
  dsimp only at hcfg hfs hch
  subst hcfg
  subst hch
  exact ⟨σF', hrunF, na, fr, hfs⟩

/-! ## The witness (witness-in-same-slice) -/

theorem roundVr_witness_identity :
    ∃ σF', stepFnIter 33274 canonVr
        (renameConfig (ρT canonVr.nextAddr 0) roundVrC0) (πVr ++ [])
        = .ok (renameConfig (ρT canonVr.nextAddr 0) roundVrC0, σF', [])
      ∧ ∃ na' fr', FrameSim (ρT canonVr.nextAddr 0) canonVr.nextAddr
          na' fr' canonVr' σF' := by
  have hF : FrameSim (ρT canonVr.nextAddr 0) canonVr.nextAddr
      canonVr.nextAddr [] canonVr canonVr :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero canonVr.nextAddr f.body)
  exact roundVr_lemma _ _ _ _ canonVr hF []

/-- Family closure: the successor state is a `RoundFam` member of
the successor canon. -/
theorem roundVr_closure :
    ∃ σF', RoundFam canonVr' σF' := by
  obtain ⟨σF', _, na', fr', hfs⟩ := roundVr_witness_identity
  exact ⟨σF', ρT canonVr.nextAddr 0, canonVr.nextAddr, na', fr', hfs⟩

/-! ## The abstract round delta (readouts; every value #eval'd first
— `artifacts/probe/RoundVrReadoutProbe.lean` → `roundvrreadout.out`) -/

def vrTwinLoc : Loc := .base ⟨121⟩

/-- PRE: violations 0, claims 0 — NO leadership claim exists yet;
ONE live MsgVoteResp (typ 6, 2 → 1) in flight. -/
theorem roundVr_pre_read :
    (absTwinRead canonVr vrTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(true, 6, 2, 1)]) := by
  kernel_rfl

/-- POST: **THE CLAIM IS BORN** — claims 0 → 1 (node 1's leadership
claim, harvested at becomeLeader IN THIS ROUND), violations 0 (the
checker held: a first claim of term 1 violates nothing); the resp
DEAD; TWO MsgApp (1→2 and 1→3, the noop broadcast) LIVE. -/
theorem roundVr_post_read :
    (absTwinRead canonVr' vrTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 1, 0, [(false, 6, 2, 1), (true, 3, 1, 2), (true, 3, 1, 3)]) := by
  kernel_rfl

/-- **THE ELECTION COMPLETED**: node 1's raft state 1 → 2
(candidate → leader) through the deep reader. -/
theorem roundVr_post_state :
    (absTwinNodeRaft canonVr' vrTwinLoc 0).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVr' a ⟨"raft.raft"⟩ "state")
      = some 2 := by
  kernel_rfl

theorem roundVr_pre_state :
    (absTwinNodeRaft canonVr vrTwinLoc 0).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVr a ⟨"raft.raft"⟩ "state")
      = some 1 := by
  kernel_rfl

/-- The leader field follows: lead 0 → 1 (node 1 names itself). -/
theorem roundVr_post_lead :
    (absTwinNodeRaft canonVr' vrTwinLoc 0).bind
      (fun a => GoLean.Lens.fieldReadU64 canonVr' a ⟨"raft.raft"⟩ "lead")
      = some 1 := by
  kernel_rfl

/-- NO commit movement: committed stays 1 (the noop is appended;
its quorum-commit is the maybeCommit round's job — the matrix's
rows compose). -/
theorem roundVr_post_committed :
    (absTwinNodeRaft canonVr' vrTwinLoc 0).bind
      (fun a => (GoLean.Lens.fieldRead canonVr' a ⟨"raft.raft"⟩ "raftLog").bind
        (fun v => match v with
          | .addr (.base la) =>
              GoLean.Lens.fieldReadU64 canonVr' la ⟨"raft.raftLog"⟩ "committed"
          | _ => none)) = some 1 := by
  kernel_rfl

end GoLean.RaftSeam.RoundVr
