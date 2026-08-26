import GoLeanProofs.Specs.Raft.RingEqW1
import GoLeanProofs.Specs.Raft.RingEqW2
import GoLeanProofs.Specs.Raft.RingEqW345
import GoLeanProofs.Sym.KernelRfl
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# A4-U21 (C2c): THE STORAGE-RESP SUB-RING SPANS — the harvest ring's
five per-arm statements at the MsgApp append-family round fixture

**LINEAGE: the handler-equation mirror-chain form (`HhEquation.lean`'s
window–crossing–window spine over `symEvalWindowTB` + kernel-checked
links), applied one ring up — SC1's harvest-granularity verdict
("per-arm sub-ring equations … the shells are the same code across
round kinds") executed as C2c's charter.** The crossings ride DIRECT
`kernel_rfl` machine steps (concrete draw head) instead of the
atom-carried `stepFn_appendSpill_transport` — see the family note.

## The fixture and the segment map

The MsgApp append-family round fixture (`TwinMsgAppFixProbe`: the U18
doctor+prune template's second instantiation — the real first
loop-head state, net/live doctored to ONE live MsgApp `1→2, Term 0
local, Index 1/LogTerm 1` matching node 2's snapshot-boot log
`[dummy (1,1)]`, one entry `(Index 2, Term 1)`, `Commit 2`). The ring
segment = round steps 7,425–21,295 (the `main.twin.harvest` call to
the `main.twin.projection` call), 13,870 steps, re-pruned to its own
**27-cell read-before-write footprint** (the I2
footprint-for-preconditions census; generator
`artifacts/probe/MsgAppRingGen.lean`). Census anchors
(`artifacts/probe/msgappring.out`, ring-relative):

| span | steps | draws | contents |
|---|---|---|---|
| `ring_w1_span` | 3,327 | 1 | HasReady → Ready → readyWithoutAccept → applyUnstableEntries (the Ready ASSEMBLY; X1 = a `[]*Message` spill) |
| `ring_w2_span` | 5,185 | 4 | acceptReady → newStorageAppendRespMsg (X2) → newStorageApplyRespMsg → MemoryStorage.SetHardState → MemoryStorage.Append (X3 = the ents spill) → the harness net/live sends (X4/X5) |
| `ring_w3_span` | 324 | 0 | `main.twin.apply` (the checker apply) |
| `ring_w4_span` | 3,202 | 0 | **Advance + BOTH nested `raft.raft.Step` storage-resp arms** (MsgStorageAppendResp → `unstable.stableTo`; MsgStorageApplyResp → `raftLog.appliedTo`) — the U20 finding's target, unreachable from the heartbeat fixture |
| `ring_w5_span` | 1,832 | 0 | the second `HasReady` (false exit, incl. the second applyUnstableEntries) |

`ring_full_span` composes all five: 13,870 steps, exactly 5 draws.

## Statement form (the compositional mode's shape at this scale)

Every span is ∀ρ (valuation) ∀σ (table-carrier, `bfTB.Agrees` — the
pinned twin program) ∀rest (stream tail): `stepFnIter N (γS ρ σ maSᵢ)
(γC ρ maCᵢ) (draws ++ rest) = .ok (γC ρ maCⱼ, γS ρ σ maSⱼ, rest)`.
Heap-placement freedom is NOT in the span statement — it enters
through `span_consume`/`FrameSimS` (the C2a instrument), which is
exactly how the composition witness in `RingWitness.lean` consumes
`ring_w4_span` at a non-identity placement. Consumer-facing
bounded-completion corollaries (`ring_w4_completes`, `ring_completes`)
state the ∃-form the I2 mode prefers.

## FIXTURE-FAMILY preconditions (recorded, the U3 fine-print pattern)

- **The canonical zero draws.** Every spill crossing is stated at
  stream head 0 (gc's deterministic growth-formula pick — the pinned
  run's stream). The hh equation absorbed its ONE spill choice as
  valuation atoms because nothing downstream re-read the spilled
  artifact; here the artifacts ARE consumed downstream (the ents
  backing by the second Ready, the responses by the nested Steps), so
  choice-symbolism inside the ring is REFUTED at this fixture — the
  atom route would quit the mirror at the first re-read. The
  ∀-stream envelope over draw values is the RE-SPILL residual family
  the handler equations already carry (SC1's caveat, unchanged).
- **The append-and-commit family**: node 2 at the snapshot-boot log
  (`[dummy (1,1)]`, committed=applied=1), one appended entry, commit
  bump to 2. Other MsgApp families (stale, reject, multi-entry) have
  the same shells with different arm prefixes — the cross-kind reuse
  SC1's pricing rides on; they are NOT witnessed here.
- **Payload parametricity, honestly stated**: the ρ/σ-quantification
  makes every span table-generic and valuation-generic; the payload
  CELLS (entry Index/Term at 6081/6080, Commit at 6079) are concrete
  literals in this family because the ring BRANCHES on them
  (HasReady's hardstate comparison, commitTo/appliedTo guards,
  stableTo index arithmetic) — a symbolic payload quits the mirror at
  the first such branch, which is the same refutation the hh
  equation recorded for `From`-symbolism. Field-symbolism where the
  ring genuinely does not branch is future refinement, on demand.

## Mode-justification (the I2 sanction, explicit)

The flexibility redesign (§3 I2) sanctions equation-shaped work
before the prover exists when it carries explicit justification:
these five statements are SC1's harvest-granularity RECOMMENDATION
(per-arm over batched, ~5-6× cross-kind reuse), adopted by the C2c
charter; their conclusions are consumed compositionally
(`span_consume`, bounded-completion corollaries), not as per-net
literal chains. The window links double as drift alarms on the
pinned lowering (a frontend re-lowering that reshapes the ring turns
them red).
-/

namespace GoLean.RaftSeam.Ring

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

/-! ## The composed ring -/

/-- **THE FULL HARVEST-RING SPAN** at the MsgApp append-family round:
13,870 steps, exactly five draws (all appendSpill — SC1's
classification, re-verified at this fixture by the census), from the
`main.twin.harvest` call to the `main.twin.projection` call. -/
theorem ring_full_span (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    stepFnIter 13870 (γS ρ σ maS0) (γC ρ maC0)
      (0 :: 0 :: 0 :: 0 :: 0 :: rest)
      = .ok (γC ρ maC5, γS ρ σ maS5, rest) := by
  have h1 := ring_w1_span ρ σ hag (0 :: 0 :: 0 :: 0 :: rest)
  have h2 := ring_w2_span ρ σ hag rest
  have h3 := ring_w3_span ρ σ hag rest
  have h4 := ring_w4_span ρ σ hag rest
  have h5 := ring_w5_span ρ σ hag rest
  exact Surface.stepFnIter_chain
    (Surface.stepFnIter_chain
      (Surface.stepFnIter_chain
        (Surface.stepFnIter_chain h1 h2) h3) h4) h5

/-! ## Bounded-completion corollaries (the I2 consumer forms) -/

/-- The storage-resp arms complete within 3,202 steps (the
bounded-completion form a round-lemma consumer composes with). -/
theorem ring_w4_completes (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (ch : Choices) :
    ∃ m, m ≤ 3202 ∧
      stepFnIter m (γS ρ σ maS3) (γC ρ maC3) ch
        = .ok (γC ρ maC4, γS ρ σ maS4, ch) :=
  ⟨3202, Nat.le_refl _, ring_w4_span ρ σ hag ch⟩

/-- The whole ring completes within 13,870 steps consuming exactly
the five canonical draws. -/
theorem ring_completes (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (rest : Choices) :
    ∃ m, m ≤ 13870 ∧
      stepFnIter m (γS ρ σ maS0) (γC ρ maC0)
        (0 :: 0 :: 0 :: 0 :: 0 :: rest)
        = .ok (γC ρ maC5, γS ρ σ maS5, rest) :=
  ⟨13870, Nat.le_refl _, ring_full_span ρ σ hag rest⟩

/-! ## The abstract readouts (the storage-resp axis's payload facts,
kernel-evaluated at the endpoint literals; every value #eval-checked
before being stated — `artifacts/probe/RingReadout*.out`). Cells
1949 (node-2 raftLog), 1779 (its MemoryStorage), 121 (the twin) sit
in the 27-cell footprint; 6080/6081/6082 are the doctored entry's
Term/Index/struct cells. -/

/-- Pre-ring: applied = 1 (the arm committed 2 but applied nothing —
apply is the RING's work). -/
theorem ring_pre_applied (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldReadU64 (γS ρ σ maS0) ⟨1949⟩ ⟨"raft.raftLog"⟩ "applied"
      = some 1 := by
  kernel_rfl

/-- Post-ring: applied = 2 — the MsgStorageApplyResp arm's
`appliedTo` landed. -/
theorem ring_post_applied (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldReadU64 (γS ρ σ maS5) ⟨1949⟩ ⟨"raft.raftLog"⟩ "applied"
      = some 2 := by
  kernel_rfl

/-- Committed is 2 on BOTH ends — the ARM raised it (commitTo before
the ring); the ring stabilizes and applies. -/
theorem ring_pre_committed (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldReadU64 (γS ρ σ maS0) ⟨1949⟩ ⟨"raft.raftLog"⟩ "committed"
      = some 2 := by
  kernel_rfl

theorem ring_post_committed (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldReadU64 (γS ρ σ maS5) ⟨1949⟩ ⟨"raft.raftLog"⟩ "committed"
      = some 2 := by
  kernel_rfl

/-- Pre-ring storage: ents = the boot dummy only. -/
theorem ring_pre_storage_ents (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldRead (γS ρ σ maS0) ⟨1779⟩ ⟨"raft.MemoryStorage"⟩ "ents"
      = some (.slice ⟨some (.base ⟨1900⟩), 0, 1, 1⟩) := by
  kernel_rfl

/-- **Post-ring storage: ents grew** — the MemoryStorage.Append
(crossing X3) landed the appended entry; the new backing holds the
dummy pointer and THE DOCTORED ENTRY's pointer. -/
theorem ring_post_storage_ents (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldRead (γS ρ σ maS5) ⟨1779⟩ ⟨"raft.MemoryStorage"⟩ "ents"
      = some (.slice ⟨some (.base ⟨6990⟩), 0, 2, 2⟩) := by
  kernel_rfl

theorem ring_post_ents_backing (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ maS5).heap (.base ⟨6990⟩)
      = some ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
          .array #[.addr (.base ⟨1898⟩), .addr (.base ⟨6082⟩)]⟩ := by
  kernel_rfl

/-- The appended entry's payload cells (Index 2, Term 1 — the
doctored MsgApp's entry, now STABLE storage content). -/
theorem ring_post_entry2_index (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ maS5).heap (.base ⟨6081⟩)
      = some ⟨some (.int .uint64), .int 2 .uint64⟩ := by
  kernel_rfl

theorem ring_post_entry2_term (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ maS5).heap (.base ⟨6080⟩)
      = some ⟨some (.int .uint64), .int 1 .uint64⟩ := by
  kernel_rfl

/-- Pre-ring: no HardState persisted yet. -/
theorem ring_pre_hardstate (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldRead (γS ρ σ maS0) ⟨1779⟩ ⟨"raft.MemoryStorage"⟩ "hardState"
      = some .nil := by
  kernel_rfl

/-- **Post-ring: SetHardState persisted `{Term 0, Vote 0, Commit 2}`**
(the commit bump reaching stable storage — the storage-resp axis's
second write; proto pointer fields, deref cells below). -/
theorem ring_post_hardstate (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldRead (γS ρ σ maS5) ⟨1779⟩ ⟨"raft.MemoryStorage"⟩ "hardState"
      = some (.addr (.base ⟨6654⟩)) := by
  kernel_rfl

theorem ring_post_hardstate_commit (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ maS5).heap (.base ⟨6651⟩)
      = some ⟨some (.int .uint64), .int 2 .uint64⟩ := by
  kernel_rfl

/-- Post-ring: the unstable log is EMPTIED at offset 3 — the
MsgStorageAppendResp arm's `stableTo` retired the appended entry
into storage. -/
theorem ring_post_unstable (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldRead (γS ρ σ maS5) ⟨1949⟩ ⟨"raft.raftLog"⟩ "unstable"
      = some (.struct ⟨"raft.unstable"⟩ #[
          ("snapshot", .nil),
          ("entries", .slice ⟨none, 0, 0, 0⟩),
          ("offset", .int 3 .uint64),
          ("snapshotInProgress", .bool false),
          ("offsetInProgress", .int 3 .uint64),
          ("logger", .interface
            (.pointer (.defined ⟨"main.harnessLogger"⟩))
            (.addr (.base ⟨97⟩)))]) := by
  kernel_rfl

/-- Post-ring net: two messages — the delivered MsgApp's pointer and
the arm's MsgAppResp pointer (crossing X4's append; the STRUCTURAL
readout — the message-CONTENT cells are provably outside the ring's
footprint, so content readouts belong to the round scope). -/
theorem ring_post_net (ρ : Valuation) (σ : ExecState) :
    GoLean.Lens.fieldRead (γS ρ σ maS5) ⟨121⟩ ⟨"main.twin"⟩ "net"
      = some (.slice ⟨some (.base ⟨7009⟩), 0, 2, 2⟩) := by
  kernel_rfl

theorem ring_post_net_backing (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ maS5).heap (.base ⟨7009⟩)
      = some ⟨some (.array 2 (.pointer (.defined ⟨"raftpb.Message"⟩))),
          .array #[.addr (.base ⟨6076⟩), .addr (.base ⟨6456⟩)]⟩ := by
  kernel_rfl

/-- Post-ring liveness: the delivered MsgApp DEAD, the response LIVE
(crossing X5's append). -/
theorem ring_post_live_backing (ρ : Valuation) (σ : ExecState) :
    GoCore.Heap.lookup (γS ρ σ maS5).heap (.base ⟨7013⟩)
      = some ⟨some (.array 2 .bool), .array #[.bool false, .bool true]⟩ := by
  kernel_rfl

end GoLean.RaftSeam.Ring
