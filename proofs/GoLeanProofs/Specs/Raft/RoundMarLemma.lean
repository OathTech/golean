import GoLeanProofs.Specs.Raft.RoundMarEquation
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.Relocate

/-!
# A4-U24: THE R-FORM'S THIRD PROVED INSTANCE — the MsgAppResp
MAYBECOMMIT-family ROUND LEMMA (commit movement WITHOUT append)

`roundMar_lemma` proves `RoundLemmaShape canonMar canonMar'
roundMarC0 26224 πMar` — the round-kind matrix's untested row: the
LEADER handles the quorum-completing MsgAppResp
(`pr.MaybeUpdate(2)` → `maybeCommit` → `commitTo(2)`), then the
commit RING (apply entry 2 + SetHardState{Commit:2} + the nested
MsgStorageApplyResp arm) with **NO MemoryStorage.Append** — commit
and apply movement with zero entry movement. Post-commit,
`bcastAppend` emits ONE MsgApp (to node 2, the responder; node 3's
probe-state flow is paused — read off the fixture, not assumed).

## THE ETCD-DIALECT COMMIT STORY, AT THE INTERPRETER LEVEL

This is the exact behavior the A4 dialect mismatch lived on
(commit-advance without new entries — the mismatch axis the
obligation signature's commit members carve out): the spec side
discharges it as `leaderCommitOk`'s quorum evidence and the follower
side as `followerCommitOk`'s `min lc matched` envelope
(`NativeS23Route`/`NativeEtcdDischarge`); THIS lemma is the
interpreter-level half — the twin's leader really performs the
commit-without-append transition, kernel-checked end to end at a
DOCTORED, PRUNED fixture derived from the pinned run's anchor-3
state (§ below; the U26 canon probe established that pruned fixtures
are open terms with dangling references — NOT reachable states; the
round FAMILY is exercised by the real run, whose own commit lands at
anchor 7 by exactly this family, AnchorScan probe — but the R-form's
applicability to the real run is the A5 replay's obligation, not
this fixture's). The two halves meet at the T1 assembly. (Wording
corrected at the landing fix round: this paragraph previously called
the fixture "reachable".)

## The fixture (anchor 3 — the U24 template extension)

The doctor+prune template at a NON-INITIAL anchor for the first
time: anchor 3 (cum step 173,666) is the first loop head where node
1 is LEADER (state=2, lead=1) with the becomeLeader noop (entry 2,
term 1) appended, STABLE, and pending quorum (committed=1). Doctor:
the single live MsgAppResp {Type 4, From 2, To 1, Term 1, Index 2};
prune: 49 cells (probe `TwinMarFixProbe.lean` → `marfix.out`).
Round: **26,224 steps / 10 draws, self-returning**.

## The draw prefix

`πMar = [pick] ++ latitude`: position 0 THE SEMANTIC DELIVERY PICK;
positions 1–6 the two tracker-Visit mapIter triplets (maybeCommit's
quorum walk `trk.Committed()`, bcastAppend's peer walk — latitude,
table-pinned per the U23 finding: the tracker map's value type is
defined); positions 7–9 latitude appendSpills. TWO choice-free
Visit exhaustion-exits crossed ∀-stream (the U23 auto-discovery
template's crossings — a THIRD round kind now confirms the census
cannot see them). The factored ∀-latitude form awaits the arc4c ~,
as U22/U23 recorded.
-/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-- The zero valuation (the literals carry no atoms). -/
def rmρ0 : Valuation :=
  { ints := fun _ => 0, bools := fun _ => false,
    vals := fun _ => .nil, cells := fun _ => ⟨none, .nil⟩ }

/-- The pinned-table carrier. -/
def rmσT : ExecState := bfTB.toState

theorem rmAgrees : bfTB.Agrees rmσT := ⟨rfl, rfl, rfl, rfl⟩

/-- **The canonical maybeCommit-round loop-head state**. -/
def canonMar : ExecState := γS rmρ0 rmσT mrSB0

/-- The successor canonical state. -/
def canonMar' : ExecState := γS rmρ0 rmσT mrSB33

/-- The shared loop-head configuration. -/
def roundMarC0 : Config := γC rmρ0 mrCB0

/-- Self-returning at the machine level (#eval'd true first). -/
theorem roundMar_selfReturn_conc : γC rmρ0 mrCB33 = roundMarC0 := by
  kernel_rfl

/-- The canonical run at the concrete states. -/
theorem roundMar_run_conc (rest : Choices) :
    stepFnIter 26224 canonMar roundMarC0 (πMar ++ rest)
      = .ok (roundMarC0, canonMar', rest) := by
  have h := roundMar_run rmρ0 rmσT rmAgrees rest
  rwa [roundMar_selfReturn_conc] at h

/-- **THE R-FORM'S THIRD PROVED INSTANCE**: the maybeCommit round
lemma — commit-without-append, from ANY FrameSim placement,
self-returning with the censused ten-draw prefix consumed, closure
at the successor family. -/
theorem roundMar_lemma :
    RoundLemmaShape canonMar canonMar' roundMarC0 26224 πMar := by
  intro r na₀ na fr σF hF ch
  have hrun := roundMar_run_conc ch
  have hsim := stepFnIter_sim (ρ := r) (na₀ := na₀) (na := na) (fr := fr)
    26224 hF roundMarC0 (πMar ++ ch)
  obtain ⟨⟨cF, σF', chF⟩, hrunF, hcfg, hfs, hch⟩ := hsim.ok_inv hrun
  dsimp only at hcfg hfs hch
  subst hcfg
  subst hch
  exact ⟨σF', hrunF, na, fr, hfs⟩

/-! ## The witness (witness-in-same-slice) -/

theorem roundMar_witness_identity :
    ∃ σF', stepFnIter 26224 canonMar
        (renameConfig (ρT canonMar.nextAddr 0) roundMarC0) (πMar ++ [])
        = .ok (renameConfig (ρT canonMar.nextAddr 0) roundMarC0, σF', [])
      ∧ ∃ na' fr', FrameSim (ρT canonMar.nextAddr 0) canonMar.nextAddr
          na' fr' canonMar' σF' := by
  have hF : FrameSim (ρT canonMar.nextAddr 0) canonMar.nextAddr
      canonMar.nextAddr [] canonMar canonMar :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero canonMar.nextAddr f.body)
  exact roundMar_lemma _ _ _ _ canonMar hF []

/-- Family closure: the successor state is a `RoundFam` member of
the successor canon. -/
theorem roundMar_closure :
    ∃ σF', RoundFam canonMar' σF' := by
  obtain ⟨σF', _, na', fr', hfs⟩ := roundMar_witness_identity
  exact ⟨σF', ρT canonMar.nextAddr 0, canonMar.nextAddr, na', fr', hfs⟩

/-! ## The abstract round delta (readouts; every value #eval'd first
— `artifacts/probe/RoundMarReadoutProbe.lean` → `roundmarreadout.out`) -/

def rmTwinLoc : Loc := .base ⟨121⟩

/-- PRE: violations 0, claims 1 (node 1's leadership claim, recorded
at its becomeLeader harvest — round 2→3), ONE live MsgAppResp
(typ 4, 2 → 1) in flight. -/
theorem roundMar_pre_read :
    (absTwinRead canonMar rmTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 1, 0, [(true, 4, 2, 1)]) := by
  kernel_rfl

/-- POST: counters unchanged (violations 0 — the checker held; the
applied entry is the empty noop, so the twin's committed counter
stays 0), the resp DEAD, ONE post-commit MsgApp (typ 3, 1 → 2)
appended LIVE. -/
theorem roundMar_post_read :
    (absTwinRead canonMar' rmTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 1, 0, [(false, 4, 2, 1), (true, 3, 1, 2)]) := by
  kernel_rfl

/-- **THE COMMIT MOVED**: node 1's raftLog committed 1 → 2 through
the deep reader — maybeCommit's quorum commit, with NO append. -/
theorem roundMar_post_committed :
    (absTwinNodeRaft canonMar' rmTwinLoc 0).bind
      (fun a => (GoLean.Lens.fieldRead canonMar' a ⟨"raft.raft"⟩ "raftLog").bind
        (fun v => match v with
          | .addr (.base la) =>
              GoLean.Lens.fieldReadU64 canonMar' la ⟨"raft.raftLog"⟩ "committed"
          | _ => none)) = some 2 := by
  kernel_rfl

theorem roundMar_pre_committed :
    (absTwinNodeRaft canonMar rmTwinLoc 0).bind
      (fun a => (GoLean.Lens.fieldRead canonMar a ⟨"raft.raft"⟩ "raftLog").bind
        (fun v => match v with
          | .addr (.base la) =>
              GoLean.Lens.fieldReadU64 canonMar la ⟨"raft.raftLog"⟩ "committed"
          | _ => none)) = some 1 := by
  kernel_rfl

/-- The apply followed inside the same round: applied 1 → 2. -/
theorem roundMar_post_applied :
    (absTwinNodeRaft canonMar' rmTwinLoc 0).bind
      (fun a => (GoLean.Lens.fieldRead canonMar' a ⟨"raft.raft"⟩ "raftLog").bind
        (fun v => match v with
          | .addr (.base la) =>
              GoLean.Lens.fieldReadU64 canonMar' la ⟨"raft.raftLog"⟩ "applied"
          | _ => none)) = some 2 := by
  kernel_rfl

end GoLean.RaftSeam.RoundMar
