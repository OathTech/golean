import GoLeanProofs.Specs.Raft.RoundMaEquation
import GoLeanProofs.Specs.Raft.RoundStatement
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.Relocate

/-!
# A4-U22 (C2d): THE R-FORM'S FIRST PROVED INSTANCE — the MsgApp
append-family ROUND LEMMA

**THE ROUND LEMMA, END TO END**: `roundMa_lemma` proves
`RoundLemmaShape canonMa canonMa' roundC0 23488 πMa` — the U18
statement former's first instance, retiring the `RoundLemmaShape`
SCAFFOLD marker's "no proved instance" caveat. From ANY `FrameSim`
placement of the canonical MsgApp-round loop-head state, the full
round (arm + harvest ring incl. BOTH storage-resp arms + driver
suffix) completes in 23,488 steps consuming exactly the censused
eight-draw prefix, RETURNS to the same loop-head configuration, and
the post-state is a placement of the successor family (closure).

## Construction (the compositional assembly)

1. **The canonical run** (`RoundMaEqA/B/C` + `RoundMaEquation`):
   12 mirror windows + 8 crossings in the tree-propagation template
   at the round fixture (39-cell doctored+pruned anchor, the C2c
   generator run shared as chartered), composed to `roundMa_run` —
   ∀ρ/∀σ-tables/∀stream-tail.
2. **The transport**: `stepFnIter_sim` (the WEAK frame simulation's
   iteration theorem, `Frame/Transfer.lean`) lifts the concrete run
   to every placement in ONE application — the R-form's ∀-placement
   quantifier is discharged by the C1 instrument wholesale, no
   per-window re-derivation (LINEAGE: Abadi–Lamport refinement
   mapping, as the R-form's docstring pins).

## The draw prefix and the choice-invariance seam (coordinator note,
campaign log 2026-08-27)

`πMa = [pick] ++ latitude` — position 0 is THE SEMANTIC DELIVERY
PICK (selects WHICH live message the round delivers; at this
fixture's singleton net, slot 0 = the doctored MsgApp); positions
1–7 are latitude appendSpills (capacity only). The R-form's `π` is
the concrete censused prefix; the FACTORED form — latitude tail
absorbed under the ~ equivalence, the pick explicit — awaits the
arc4c lane's ~; the lemma as stated is the factoring's INPUT (the
latitude positions are identified per-crossing in the RoundMaEq*
docstrings), not a substitute for it. No ~ was needed for this
instance to state cleanly (the stop-condition did not fire).

## DESIGN FINDING for the coordinator (reported, not shimmed)

The charter's "five ring spans consumed via span_consume" clause is
NOT how this instance composes, for a structural reason worth the
record: `span_consume`/`FrameSimS`'s shape clause hands back
`ren pre ++ fr ++ ren post` — the frame CONTIGUOUS at one list
splice. A sub-fixture obtained by PRUNING (the ring's 27 cells) sits
INTERLEAVED in the outer round state's heap list (both among the
fixture cells and among the arm's allocations), so no FrameSimS
placement of the ring fixture into the round state exists — the
constructors (`relocate`+`extend`) require the frame off-image, and
the shape clause requires one splice. Sub-span REUSE inside a bigger
walk therefore needs either a multi-splice FrameSimS or a
heap-permutation/finmap quotient (the arc4c ~ CLASS, state edition).
The round lemma does not need it — the R-form's conclusion is the
WEAK relation, transported wholesale — so this instance RE-WALKS the
ring segment at the round fixture (~8 extra minutes of one-time
kernel) and the C2c spans stand as the per-arm interface statements
plus the composition-witness demonstration at their own fixture.

## Fixture-family preconditions

As C2c's (the append-and-commit family at the decoded snapshot-boot
log; canonical zero draws; the RE-SPILL residual family for the
∀-stream envelope) — see `RingEquation.lean`'s docstring. The
heartbeat round-kind's T1-vacuity does NOT apply here: MsgApp rounds
are REACHABLE and load-bearing (12 of the pinned run's 28 deliver
rounds; U18 census).
-/

namespace GoLean.RaftSeam.RoundMa

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

/-- **The canonical MsgApp-round loop-head state** (the R-form's
`canon`): the concrete machine state of the doctored+pruned fixture
at the anchor. -/
def canonMa : ExecState := γS rmρ0 rmσT maSR0

/-- The successor canonical state (`canon'`): the end-anchor state. -/
def canonMa' : ExecState := γS rmρ0 rmσT maSR4

/-- The shared loop-head configuration (the R-form's `C0`). -/
def roundC0 : Config := γC rmρ0 maCR0

/-- **SELF-RETURNING at the machine level, kernel-checked** (closed;
the Sym literals differ representationally — reflected vs
mirror-propagated — but their machine images are IDENTICAL, the
census's config-identity as a definitional fact). -/
theorem roundMa_selfReturn_conc : γC rmρ0 maCR4 = roundC0 := by
  kernel_rfl

/-- The canonical run at the concrete states, returning to `roundC0`. -/
theorem roundMa_run_conc (rest : Choices) :
    stepFnIter 23488 canonMa roundC0 (πMa ++ rest)
      = .ok (roundC0, canonMa', rest) := by
  have h := roundMa_run rmρ0 rmσT rmAgrees rest
  rwa [roundMa_selfReturn_conc] at h

/-- **THE R-FORM'S FIRST PROVED INSTANCE** (the U18 scaffold's C2
obligation, discharged): the MsgApp append-family round lemma — from
ANY FrameSim placement of `canonMa`, the round completes
self-returning with the censused prefix consumed, and the post-state
is a placement of the successor family at the SAME frame indexes
(closure). -/
theorem roundMa_lemma :
    RoundLemmaShape canonMa canonMa' roundC0 23488 πMa := by
  intro r na₀ na fr σF hF ch
  have hrun := roundMa_run_conc ch
  have hsim := stepFnIter_sim (ρ := r) (na₀ := na₀) (na := na) (fr := fr)
    23488 hF roundC0 (πMa ++ ch)
  obtain ⟨⟨cF, σF', chF⟩, hrunF, hcfg, hfs, hch⟩ := hsim.ok_inv hrun
  dsimp only at hcfg hfs hch
  subst hcfg
  subst hch
  exact ⟨σF', hrunF, na, fr, hfs⟩

/-! ## The witness (witness-in-same-slice; the R-form instance
discharged at concrete placements) -/

/-- The identity-placement witness: `roundMa_lemma` applied at
`RoundFam.self`'s placement gives back the canonical run — every
premise concrete, no placement left abstract. -/
theorem roundMa_witness_identity :
    ∃ σF', stepFnIter 23488 canonMa
        (renameConfig (ρT canonMa.nextAddr 0) roundC0) (πMa ++ [])
        = .ok (renameConfig (ρT canonMa.nextAddr 0) roundC0, σF', [])
      ∧ ∃ na' fr', FrameSim (ρT canonMa.nextAddr 0) canonMa.nextAddr
          na' fr' canonMa' σF' := by
  have hF : FrameSim (ρT canonMa.nextAddr 0) canonMa.nextAddr
      canonMa.nextAddr [] canonMa canonMa :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero canonMa.nextAddr f.body)
  exact roundMa_lemma _ _ _ _ canonMa hF []

/-- The family CLOSURE at the identity witness: the successor state
is a `RoundFam` member of the successor canon — the induction's
carried membership, re-established (the R-form's whole point). -/
theorem roundMa_closure :
    ∃ σF', RoundFam canonMa' σF' := by
  obtain ⟨σF', _, na', fr', hfs⟩ := roundMa_witness_identity
  exact ⟨σF', ρT canonMa.nextAddr 0, canonMa.nextAddr, na', fr', hfs⟩

/-! ## The abstract round delta (readouts at the concrete anchors;
every value #eval-checked before being stated) -/

/-- The twin cell (cell 121 — the fixture's, as the ring census's). -/
def rmTwinLoc : Loc := .base ⟨121⟩

/-- PRE: counters zero, ONE live MsgApp (typ 3, 1 → 2) in flight. -/
theorem roundMa_pre_read :
    (absTwinRead canonMa rmTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(true, 3, 1, 2)]) := by
  kernel_rfl

/-- POST: counters unchanged (violations 0 — the checker held), the
MsgApp marked DEAD, the MsgAppResp (typ 4, 2 → 1) appended LIVE. -/
theorem roundMa_post_read :
    (absTwinRead canonMa' rmTwinLoc).map
      (fun a => (a.violations, a.claims, a.committed,
                 a.net.map (fun p => (p.1, p.2.typ, p.2.src, p.2.dst))))
      = some (0, 0, 0, [(false, 3, 1, 2), (true, 4, 2, 1)]) := by
  kernel_rfl

/-- POST, the delivered node's log through the deep reader: node 2's
raftLog applied = 2 (the round's storage-resp payload, at ROUND
scale — committed and applied both moved 1 → 2 across the round;
committed moved in the ARM, applied in the RING). -/
theorem roundMa_post_applied :
    (absTwinNodeRaft canonMa' rmTwinLoc 1).bind
      (fun a => (GoLean.Lens.fieldRead canonMa' a ⟨"raft.raft"⟩ "raftLog").bind
        (fun v => match v with
          | .addr (.base la) =>
              GoLean.Lens.fieldReadU64 canonMa' la ⟨"raft.raftLog"⟩ "applied"
          | _ => none)) = some 2 := by
  kernel_rfl

theorem roundMa_pre_applied :
    (absTwinNodeRaft canonMa rmTwinLoc 1).bind
      (fun a => (GoLean.Lens.fieldRead canonMa a ⟨"raft.raft"⟩ "raftLog").bind
        (fun v => match v with
          | .addr (.base la) =>
              GoLean.Lens.fieldReadU64 canonMa la ⟨"raft.raftLog"⟩ "applied"
          | _ => none)) = some 1 := by
  kernel_rfl

end GoLean.RaftSeam.RoundMa
