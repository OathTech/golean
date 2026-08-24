import GoLeanProofs.Lens
import GoLeanProofs.Specs.Raft.BecomeFollowerWitness
import GoLeanProofs.Sym.KernelRfl

/-!
# Lens instances at the pinned twin tables (A4-U8 slice C — the target
half of the field-lens layer)

**LINEAGE: goose proofgen's generated per-field instances
(`deps/goose/proofgen/tmpl/types.tmpl:65-77` — one load + one store
instance per struct field).** Here each instance is ONE kernel-checked
`fieldTy?` fact at the pinned table, because the general layer
(`GoLeanProofs/Lens.lean`) already carries the shape-generic
normalization data: pointer/slice/bool/interface fields are identity
under the store path's re-normalization (`norm_*_id`), int fields need
only the in-range fact (`norm_int_stable`), and the single
defined-scalar chain on the wave-2 path (`raft.StateType`) gets its
two helpers below.

**[AGENT] HAND-WRITTEN, GENERATOR NOT BUILT (the U8 dispatch's
"hand-write first" call, logged):** the design's costing assumed ~2
lemmas × 75 fields of error-prone literal content. The projection
trick below (`fdsOf` extracts the field-def array FROM the pinned
table, so no literal is ever copied) collapses each instance to one
one-line kernel fact whose truth is recomputed against the table on
every build — a pin move re-checks everything, which is exactly the
generator's drift-alarm trust story with zero instrument code. At the
wave-2 field count (40 facts + 6 table facts + 2 chains) the
hand-written form is smaller than the generator would be. REVISIT if a
later wave needs the full 75+ or per-field STORE forms
(`types.tmpl`'s shape); the U4 literal-printer promotion row is
unchanged by this call.

**[AGENT] No custom simp attribute (design §3 deviation, logged):**
the design prescribed a `@[raft_lens]` simp set as the footprint
search. A `register_simp_attr` cannot live in the module that uses it,
and the general layer should not import `Lean` just for ergonomics; at
40 instances the named-fact table below serves the same
fail-loud-on-missing-instance role (unknown identifier / unsolved
goal). REVISIT at wave-2 proof buildout if simp-driven search earns
its import.

Field scope (the dispatch's wave-2 list): `raft.raft`'s
message-handler-relevant fields, `raft.raftLog`, `raft.unstable`, the
storage projections (`raft.MemoryStorage`), and the `raftpb`
Entry/Message shapes for absState v2. `tracker.Progress` is wave-3
and deliberately absent.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.Lens

/-- The pinned type table (the ground every instance is checked
against). -/
abbrev wTypes : TypeEnv := wBase.types

/-- Field-def arrays extracted BY PROJECTION from the pinned table —
never literal copies (module docstring: the build is the drift
alarm). -/
def fdsOf (tid : TypeId) : Array FieldDef :=
  match TypeEnv.lookup wTypes tid with
  | some (.struct fds) => fds
  | _ => #[]

def raftFds : Array FieldDef := fdsOf ⟨"raft.raft"⟩
def raftLogFds : Array FieldDef := fdsOf ⟨"raft.raftLog"⟩
def unstableFds : Array FieldDef := fdsOf ⟨"raft.unstable"⟩
def memStorFds : Array FieldDef := fdsOf ⟨"raft.MemoryStorage"⟩
def entryFds : Array FieldDef := fdsOf ⟨"raftpb.Entry"⟩
def messageFds : Array FieldDef := fdsOf ⟨"raftpb.Message"⟩

/-! ## Per-type table facts (what the L2/L3 laws' `hty` premise
discharges with, at any state whose types equal the pin) -/

theorem raftRaft_lookup :
    TypeEnv.lookup wTypes ⟨"raft.raft"⟩ = some (.struct raftFds) := by
  kernel_rfl

theorem raftLog_lookup :
    TypeEnv.lookup wTypes ⟨"raft.raftLog"⟩ = some (.struct raftLogFds) := by
  kernel_rfl

theorem unstable_lookup :
    TypeEnv.lookup wTypes ⟨"raft.unstable"⟩ = some (.struct unstableFds) := by
  kernel_rfl

theorem memStor_lookup :
    TypeEnv.lookup wTypes ⟨"raft.MemoryStorage"⟩
      = some (.struct memStorFds) := by
  kernel_rfl

theorem entry_lookup :
    TypeEnv.lookup wTypes ⟨"raftpb.Entry"⟩ = some (.struct entryFds) := by
  kernel_rfl

theorem message_lookup :
    TypeEnv.lookup wTypes ⟨"raftpb.Message"⟩ = some (.struct messageFds) := by
  kernel_rfl

theorem stateType_lookup :
    TypeEnv.lookup wTypes ⟨"raft.StateType"⟩
      = some (.defined (.int .uint64)) := by
  kernel_rfl

/-! ## Per-field declared-type facts (the instance table; one
kernel-checked fact per (type, field), each recomputed against the pin
on every build) -/

/-! ### `raft.raft` — the message-handler-relevant fields -/

theorem raft_id_ty : fieldTy? raftFds.toList "id" = some (.int .uint64) := by
  kernel_rfl
theorem raft_Term_ty :
    fieldTy? raftFds.toList "Term" = some (.int .uint64) := by kernel_rfl
theorem raft_Vote_ty :
    fieldTy? raftFds.toList "Vote" = some (.int .uint64) := by kernel_rfl
theorem raft_lead_ty :
    fieldTy? raftFds.toList "lead" = some (.int .uint64) := by kernel_rfl
theorem raft_leadTransferee_ty :
    fieldTy? raftFds.toList "leadTransferee" = some (.int .uint64) := by
  kernel_rfl
theorem raft_state_ty :
    fieldTy? raftFds.toList "state"
      = some (.defined ⟨"raft.StateType"⟩) := by kernel_rfl
theorem raft_raftLog_ty :
    fieldTy? raftFds.toList "raftLog"
      = some (.pointer (.defined ⟨"raft.raftLog"⟩)) := by kernel_rfl
theorem raft_msgs_ty :
    fieldTy? raftFds.toList "msgs"
      = some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))) := by
  kernel_rfl
theorem raft_msgsAfterAppend_ty :
    fieldTy? raftFds.toList "msgsAfterAppend"
      = some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))) := by
  kernel_rfl
theorem raft_electionElapsed_ty :
    fieldTy? raftFds.toList "electionElapsed" = some (.int .int) := by
  kernel_rfl
theorem raft_heartbeatElapsed_ty :
    fieldTy? raftFds.toList "heartbeatElapsed" = some (.int .int) := by
  kernel_rfl

/-! ### `raft.raftLog` -/

theorem raftLog_storage_ty :
    fieldTy? raftLogFds.toList "storage"
      = some (.interface ⟨"raft.Storage"⟩) := by kernel_rfl
theorem raftLog_unstable_ty :
    fieldTy? raftLogFds.toList "unstable"
      = some (.defined ⟨"raft.unstable"⟩) := by kernel_rfl
theorem raftLog_committed_ty :
    fieldTy? raftLogFds.toList "committed" = some (.int .uint64) := by
  kernel_rfl
theorem raftLog_applying_ty :
    fieldTy? raftLogFds.toList "applying" = some (.int .uint64) := by
  kernel_rfl
theorem raftLog_applied_ty :
    fieldTy? raftLogFds.toList "applied" = some (.int .uint64) := by
  kernel_rfl

/-! ### `raft.unstable` -/

theorem unstable_entries_ty :
    fieldTy? unstableFds.toList "entries"
      = some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))) := by
  kernel_rfl
theorem unstable_offset_ty :
    fieldTy? unstableFds.toList "offset" = some (.int .uint64) := by
  kernel_rfl
theorem unstable_offsetInProgress_ty :
    fieldTy? unstableFds.toList "offsetInProgress" = some (.int .uint64) := by
  kernel_rfl

/-! ### `raft.MemoryStorage` (the storage projections; `callStats`
deliberately absent — the U4 unread-field call) -/

theorem memStor_ents_ty :
    fieldTy? memStorFds.toList "ents"
      = some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))) := by
  kernel_rfl
theorem memStor_hardState_ty :
    fieldTy? memStorFds.toList "hardState"
      = some (.pointer (.defined ⟨"raftpb.HardState"⟩)) := by kernel_rfl
theorem memStor_snapshot_ty :
    fieldTy? memStorFds.toList "snapshot"
      = some (.pointer (.defined ⟨"raftpb.Snapshot"⟩)) := by kernel_rfl

/-! ### `raftpb.Entry` (plainpb: every scalar behind a pointer) -/

theorem entry_Term_ty :
    fieldTy? entryFds.toList "Term"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem entry_Index_ty :
    fieldTy? entryFds.toList "Index"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem entry_Type_ty :
    fieldTy? entryFds.toList "Type"
      = some (.pointer (.defined ⟨"raftpb.EntryType"⟩)) := by kernel_rfl
theorem entry_Data_ty :
    fieldTy? entryFds.toList "Data"
      = some (.slice (.int .uint8)) := by kernel_rfl

/-! ### `raftpb.Message` (all 14; `Responses` recursive — the
GAP-V2-1 census consumer) -/

theorem message_Type_ty :
    fieldTy? messageFds.toList "Type"
      = some (.pointer (.defined ⟨"raftpb.MessageType"⟩)) := by kernel_rfl
theorem message_To_ty :
    fieldTy? messageFds.toList "To"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_From_ty :
    fieldTy? messageFds.toList "From"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_Term_ty :
    fieldTy? messageFds.toList "Term"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_LogTerm_ty :
    fieldTy? messageFds.toList "LogTerm"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_Index_ty :
    fieldTy? messageFds.toList "Index"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_Entries_ty :
    fieldTy? messageFds.toList "Entries"
      = some (.slice (.pointer (.defined ⟨"raftpb.Entry"⟩))) := by
  kernel_rfl
theorem message_Commit_ty :
    fieldTy? messageFds.toList "Commit"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_Vote_ty :
    fieldTy? messageFds.toList "Vote"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_Snapshot_ty :
    fieldTy? messageFds.toList "Snapshot"
      = some (.pointer (.defined ⟨"raftpb.Snapshot"⟩)) := by kernel_rfl
theorem message_Reject_ty :
    fieldTy? messageFds.toList "Reject"
      = some (.pointer .bool) := by kernel_rfl
theorem message_RejectHint_ty :
    fieldTy? messageFds.toList "RejectHint"
      = some (.pointer (.int .uint64)) := by kernel_rfl
theorem message_Context_ty :
    fieldTy? messageFds.toList "Context"
      = some (.slice (.int .uint8)) := by kernel_rfl
theorem message_Responses_ty :
    fieldTy? messageFds.toList "Responses"
      = some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩))) := by
  kernel_rfl

/-! ## The one defined-scalar stability chain on the wave-2 path
(`raft.raft.state : raft.StateType`; every other wave-2 field is a
direct int kind or an identity shape) -/

/-- Store-miss stability for the `state` field at any pinned-table
state. -/
theorem norm_stateType_stable {σ : ExecState} (hσ : σ.types = wTypes)
    {v : Int} (hv : IntKind.normalize .uint64 v = v) :
    normalizeValueForTyFuel 1023 σ (.defined ⟨"raft.StateType"⟩)
      (.int v .uint64) = .ok (.int v .uint64) := by
  have hlk : TypeEnv.lookup σ.types ⟨"raft.StateType"⟩
      = some (.defined (.int .uint64)) := by
    rw [hσ]; exact stateType_lookup
  rw [show (1023 : Nat) = 1022 + 1 from rfl, norm_defined_step hlk,
    show (1022 : Nat) = 1021 + 1 from rfl]
  exact norm_int_stable hv σ 1021

/-- Store-hit form for the `state` field: any incoming uint64 wraps. -/
theorem norm_stateType_hit {σ : ExecState} (hσ : σ.types = wTypes)
    (v : Int) (k' : IntKind) :
    normalizeValueForTyFuel 1023 σ (.defined ⟨"raft.StateType"⟩)
      (.int v k')
      = .ok (.int (IntKind.normalize .uint64 v) .uint64) := by
  have hlk : TypeEnv.lookup σ.types ⟨"raft.StateType"⟩
      = some (.defined (.int .uint64)) := by
    rw [hσ]; exact stateType_lookup
  rw [show (1023 : Nat) = 1022 + 1 from rfl, norm_defined_step hlk,
    show (1022 : Nat) = 1021 + 1 from rfl]
  exact norm_int_hit .uint64 v k' σ 1021

/-! ## Discharge witness (§3.3): the L2/L3 laws applied on the REAL
pinned `raft.raft` shape — the machine's own default cell, a real
`storeLoc` to `Term`, hit + miss readouts, every premise discharged
from the instance table above. Probe-first
(`artifacts/probe/LensInstProbe.lean`): store OK, Term reads 5, Vote
preserved at 0. -/

private def σW : ExecState :=
  { wBase with heap := [(.base ⟨0⟩, ⟨some tyRaft, wRaftVal⟩),
                        (.base ⟨1⟩, ⟨some tyRaftLog, wLogVal⟩)],
               nextAddr := 2 }

theorem lensInst_witness :
    ∀ σ' : ExecState,
      storeLoc σW (.field (.base ⟨0⟩) ⟨"raft.raft"⟩ "Term")
        (.int 5 .uint64) = .ok σ' →
      fieldRead σ' ⟨0⟩ ⟨"raft.raft"⟩ "Term" = some (.int 5 .uint64)
      ∧ fieldRead σ' ⟨0⟩ ⟨"raft.raft"⟩ "Vote" = some (.int 0 .uint64) := by
  intro σ' hst
  have hc : Heap.lookup σW.heap (.base ⟨0⟩)
      = some ⟨some tyRaft, wRaftVal⟩ := by kernel_rfl
  have hv : (⟨some tyRaft, wRaftVal⟩ : HeapCell).value
      = .struct ⟨"raft.raft"⟩ wRaftFields := by kernel_rfl
  have hd : (⟨some tyRaft, wRaftVal⟩ : HeapCell).declaredTy
      = some (.defined ⟨"raft.raft"⟩) := by kernel_rfl
  refine ⟨?_, ?_⟩
  · exact fieldRead_store_hit hst hc hv hd raftRaft_lookup raft_Term_ty
      (by kernel_rfl)
  · exact fieldRead_store_miss hst hc hv hd raftRaft_lookup
      (by decide) raft_Vote_ty (by kernel_rfl) (by kernel_rfl)

/-- The store itself succeeds (so `lensInst_witness` is live, not
vacuous): existence by closed evaluation. -/
theorem lensInst_witness_store_ok :
    ∃ σ' : ExecState,
      storeLoc σW (.field (.base ⟨0⟩) ⟨"raft.raft"⟩ "Term")
        (.int 5 .uint64) = .ok σ' := by
  refine ⟨(storeLoc σW (.field (.base ⟨0⟩) ⟨"raft.raft"⟩ "Term")
    (.int 5 .uint64)).toOption.getD σW, ?_⟩
  kernel_rfl

end GoLean.RaftSeam
