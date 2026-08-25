import GoLeanProofs.Specs.Raft.SfHbLit
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# A4-U15: THE stepFollower × MsgHeartbeat DISPATCH-ARM EQUATION —
the FIRST dispatch-layer equation (wave 3 opens at the theorem level)

**LINEAGE: the landed handleHeartbeat equation template
(`HhEquation.lean`, symbolic-from-birth + `stepFn_appendSpill_transport`)
at the DISPATCH fixture** — same window/spill/window chain, different
census (U14/U15: 1,710 steps, ONE choice at 1581, ZERO static reads).

**PROOF ROUTE (the U15 composition verdict, recorded in the arc-4
log): this proof WALKS the arm's own windows (the literal window
chain, linear kernel cost) rather than composing the landed
`handleHeartbeat_handler_eq_alloc`.** The composition mechanics were
probed to the bottom this unit: the seam config at step 282 is
hhC0's exact drained-call shape, window links are continuation-bottom
parametric (kernel-checked with a FREE bottom at the full 1,299-step
window), and the seam heap is canonical-++-frame on the nose — but a
MID-RUN application of the relocated handler span yields its
post-state only RELATIONALLY (`∃σFfin` + `FrameSim`, which carries no
heap-completeness clause), and the arm's suffix glue writes FRAME
cells (er 68, $res0), so no literal window can resume from it.
Handler-proof reuse inside a longer literal chain is therefore an
INSTRUMENT gap (completeness-strengthened FrameSim or stepFn
heap-extensionality — the consume-on-demand ledger row), not a
statement-form gap. **The STATEMENT below is route-independent**:
layer C consumes it identically under either proof mode.

The chain (probe-validated end-to-end by `artifacts/probe/SfHbGen.lean`
BEFORE any theorem here; γ==machine at c = 0/3/31): the born-re-sited
bf31 heap + the Message argument at 52 with a REAL Type cell
(55 ↦ 8 = MsgHeartbeat — the switch ladder's driver, the first
fixture to carry one) + caller cells r/m/er at 66/67/68 (the
StaticCellsExt consumer rule: OFF the {61,65} payloads), na₀ 69.
Windows **[1581, 128]** + ONE spill crossing (elems 150, tgt 151,
backing born at 152, response message at 100) = **1,710 machine
steps**, the U14 census exactly. The arm = ~256 dispatch-glue steps
(GetType deref chain, switch compare ladder, electionElapsed := 0,
lead := m.From) + the full handleHeartbeat no-op span + the shell
return (er := nil).

FIXTURE-FAMILY preconditions (the U3 fine-print pattern):
- `m.Type = 8` (MsgHeartbeat) CONCRETE — the switch ladder branches
  on it; other Type values are OTHER arm families;
- `m.Commit = committed = 1` — the no-op `commitTo` branch (the Hh
  commit-advance family lifts to this arm the same way);
- `m.From = 2 ≠ r.id = 1` CONCRETE (send's self-addressed guard; the
  From-symbolic upgrade is the landed U14 branch-transport template);
- r's Vote/leadTransferee/state ride SYMBOLIC (x₁/x₄/x₃); r.lead x₂
  is DEAD on this path (the MsgProp lead==0 check is another arm) and
  overwritten by the glue with m.From — the post-lead readout is the
  CONCRETE 2, the arm's dispatch-visible state change.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/SfHbGen.lean` — the
window links below re-check the literals against these defs). -/

/-- The Message with a REAL Type cell: the Hh message + Type ↦ &55. -/
def sfhbMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def sfhbS0 : SymState :=
  { heap := bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) sfhbMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 8) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def sfhbEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

/-- The drained caller shape: `er := raft.stepFollower(r, m)`. -/
def sfhbC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepFollower"⟩ #[Expr.var "r", Expr.var "m"])
    sfhbEnv .stop

/-- The backing-cell payload at stream head `c`: the response-message
pointer (cell 100), then default-`nil` padding to the realized
capacity (`hhCap` reused — same nil-base one-element append envelope). -/
def sfhbBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨sfhbMsgPtr⟩)] ++ List.replicate (hhCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atom 0 (value) = the spilled
handle; atom 0 (cell) = the backing cell. Everything else rides. -/
def sfρ' (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨sfhbBacking⟩), 0, 1, hhCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) hhElemTy), sfhbBackingVal c⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms). -/

theorem sfhbW1_out :
    symEvalWindowTB bfTB sfhbW1n sfhbS0 sfhbC0 = (sfhbW1n, sfhbS1, sfhbC1) := by
  kernel_rfl

/-- The post-spill continuation/env, extracted from the quit config. -/
def sfhbK1 : GoLean.Sym.Cont symDom := match sfhbC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def sfhbE1 : LocalEnv := match sfhbC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem sfhbC1_shape : sfhbC1 = .retV (.slice ⟨some (.base ⟨sfhbElems⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨sfhbTgt⟩)] [] sfhbE1 sfhbK1) := by
  kernel_rfl

theorem sfhbW2_out : symEvalWindowTB bfTB sfhbW2n sfhbS2 (.next sfhbK1)
    = (sfhbW2n, sfhbS3, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem sfhbWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter sfhbW1n (γS ρ σ sfhbS0) (γC ρ sfhbC0) ch
      = .ok (γC ρ sfhbC1, γS ρ σ sfhbS1, ch) :=
  symEvalWindowTB_refines sfhbW1_out ρ σ ch hag

theorem sfhbWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter sfhbW2n (γS ρ σ sfhbS2) (γC ρ (.next sfhbK1)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ sfhbS3, ch) :=
  symEvalWindowTB_refines sfhbW2_out ρ σ ch hag

/-! ## THE SPILL CROSSING (the transport instantiated; every premise
discharged at the literal, the choice entering through `sfρ'`). -/

theorem sfhb_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (sfρ' ρ c₁) σ sfhbS1) (γC (sfρ' ρ c₁) sfhbC1) (c₁ :: rest)
      = .ok (γC (sfρ' ρ c₁) (.next sfhbK1), γS (sfρ' ρ c₁) σ sfhbS2, rest) := by
  have hvisE : sliceVisibleValues (γS (sfρ' ρ c₁) σ sfhbS1)
      ⟨some (.base ⟨sfhbElems⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨sfhbMsgPtr⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (sfρ' ρ c₁) σ sfhbS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (sfρ' ρ c₁) σ sfhbS1) hhElemTy
      #[] #[.addr (.base ⟨sfhbMsgPtr⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (sfhbBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨sfhbMsgPtr⟩)],
        normalizeValueForTy (γS (sfρ' ρ c₁) σ sfhbS1) hhElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (sfρ' ρ c₁) σ sfhbS1) hhElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (sfρ' ρ c₁) σ sfhbS1) (elem := hhElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨sfhbMsgPtr⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [sfhbBackingVal, hhCap] using h
  have htgt : storeLoc { γS (sfρ' ρ c₁) σ sfhbS1 with
        heap := GoCore.Heap.set (γS (sfρ' ρ c₁) σ sfhbS1).heap
          (.base ⟨(γS (sfρ' ρ c₁) σ sfhbS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) hhElemTy),
           sfhbBackingVal c₁⟩,
        nextAddr := (γS (sfρ' ρ c₁) σ sfhbS1).nextAddr + 1 } (.base ⟨sfhbTgt⟩)
      (.slice ⟨some (.base ⟨(γS (sfρ' ρ c₁) σ sfhbS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (sfρ' ρ c₁) σ sfhbS2) := by
    kernel_rfl
  rw [sfhbC1_shape]
  exact stepFn_appendSpill_transport (sfρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 1,710-step span. -/

theorem sfhb_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 1710 (γS (sfρ' ρ c₁) σ sfhbS0) (γC (sfρ' ρ c₁) sfhbC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (sfρ' ρ c₁) σ sfhbS3, ch) := by
  have h := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => sfhbWin1 (sfρ' ρ c₁) σ chx hag)
    (sfhb_spill_step ρ σ c₁ ch)
    (fun chx => sfhbWin2 (sfρ' ρ c₁) σ chx hag)
  have hstop : γC (sfρ' ρ c₁) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  show stepFnIter 1710 _ _ _ = _
  exact h

/-! ## Projection facts at the literals. -/

/-- The pre-state message record: the FIRST fixture whose `absMessage`
carries a REAL Type (typ = 8 = MsgHeartbeat, read through the Type
cell — the dispatch layer's branching datum). -/
theorem sfhb_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ sfhbS0) (.addr (.base ⟨52⟩))
      = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem sfhb_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ sfhbS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem sfhb_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (sfρ' ρ c₁) σ sfhbS3) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

/-- The er result cell: stepFollower returned nil (no error) — the
dispatch shell's own conclusion, read raw (renameCell-fixed: the cell
carries no locations). -/
theorem sfhb_post_er (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (sfρ' ρ c₁) σ sfhbS3).heap (.base ⟨68⟩)
      = some ⟨some (.interface ⟨"error"⟩), .nil⟩ := by
  kernel_rfl

/-- The msgs field of the post state reads the spilled handle. -/
theorem sfhb_post_msgs_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (sfρ' ρ c₁) σ sfhbS3) ⟨31⟩ ⟨"raft.raft"⟩ "msgs"
      = some (.slice ⟨some (.base ⟨sfhbBacking⟩), 0, 1, hhCap c₁⟩) := by
  kernel_rfl

/-- The backing cell of the post state (the cell atom's image). -/
theorem sfhb_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (sfρ' ρ c₁) σ sfhbS3).heap (.base ⟨sfhbBacking⟩)
      = some ⟨some (.array (hhCap c₁) hhElemTy), sfhbBackingVal c₁⟩ := by
  kernel_rfl

/-- The response message cell projects to the spec record. -/
theorem sfhb_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (sfρ' ρ c₁) σ sfhbS3) (.addr (.base ⟨sfhbMsgPtr⟩))
      = some (specHeartbeatResp 1 2 0) := by
  kernel_rfl

/-- The backing's head element (choice-generic: the padding never
enters — `List.getElem?` reduces at the cons head). -/
theorem sfhbBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨sfhbMsgPtr⟩)] ++ List.replicate (hhCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨sfhbMsgPtr⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (the HhEquation pattern verbatim). -/
theorem sfhb_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (sfρ' ρ c₁) σ sfhbS3) ⟨31⟩ "msgs"
      = some [specHeartbeatResp 1 2 0] := by
  rw [absOutbox]
  rw [sfhb_post_msgs_field ρ σ c₁]
  show sliceRead (γS (sfρ' ρ c₁) σ sfhbS3)
    (.slice ⟨some (.base ⟨sfhbBacking⟩), 0, 1, hhCap c₁⟩) _ = _
  rw [sliceRead]
  rw [sfhb_post_backing ρ σ c₁]
  show sliceElems (γS (sfρ' ρ c₁) σ sfhbS3)
    ⟨[GoValue.addr (.base ⟨sfhbMsgPtr⟩)] ++ List.replicate (hhCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, sfhbBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [sfhb_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

/-- The msgsAfterAppend outbox stays EMPTY (this arm appends to
`msgs`; the two outboxes are distinguished at the arm level). -/
theorem sfhb_post_absOutbox_maa (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (sfρ' ρ c₁) σ sfhbS3) ⟨31⟩ "msgsAfterAppend"
      = some [] := by
  kernel_rfl

/-- The dispatch-visible state change: `r.lead := m.From` = 2, the
glue's own write (CONCRETE — the symbolic pre-lead x₂ is dead on this
arm and overwritten). -/
theorem sfhb_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (sfρ' ρ c₁) σ sfhbS3) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some 2 := by
  kernel_rfl

/-- Untouched-scalar readout: Vote rides TRIPLE-wrapped (the U3
norm-wrap story at arm depth: the glue's two raft-struct stores +
the handler's one each re-normalize the surviving symbolic scalar —
probe `VoteWrap`: Vote = norm³(var 1)). The range side condition
collapses all three wraps in the equation. -/
theorem sfhb_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (sfρ' ρ c₁) σ sfhbS3) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (IntKind.normalize .uint64
          (IntKind.normalize .uint64 (ρ.ints 1)))) := by
  kernel_rfl

theorem sfhb_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (sfρ' ρ c₁) σ sfhbS3) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic, placement LIVE at
the born-re-sited fixture). -/

/-- **THE stepFollower × MsgHeartbeat DISPATCH-ARM EQUATION** (no-op
commitTo family): from the drained `er := stepFollower(r, m)` call at
ANY placement of the fixture footprint (relocation `r` + disjoint
frame `fr`, one `FrameSim` premise), over EVERY consumed choice
prefix (∀ streams `c₁ :: ch` — the handler's appendSpill capacity
choice), the run returns in exactly **1,710 steps** with one choice
consumed, and: the message argument projects by `absMessage` with the
REAL Type (typ 8, From 2, Commit 1); the log view is PRESERVED; the
`msgs` outbox gains EXACTLY the heartbeat response
(`[specHeartbeatResp r.id m.From r.Term]`) while `msgsAfterAppend`
stays empty; **er = nil** (the shell's no-error conclusion);
**lead = m.From = 2** (the arm's dispatch-visible state change); and
Vote/Term read back unchanged. Side condition `hvote`: the surviving
symbolic scalar's uint64-range fact. -/
theorem stepFollower_heartbeat_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ sfhbS0) σF) :
    ∃ σFfin,
      stepFnIter 1710 σF (renameConfig r (γC ρ sfhbC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (sfρ' ρ c₁) σ sfhbS3) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σFfin.heap (.base ⟨r 68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ sfhbS0 = γS (sfρ' ρ c₁) σ sfhbS0 := by kernel_rfl
  have hpreC : γC ρ sfhbC0 = γC (sfρ' ρ c₁) sfhbC0 := by kernel_rfl
  have hrun : stepFnIter 1710 (γS ρ σ sfhbS0) (γC ρ sfhbC0) (c₁ :: ch)
      = .ok (.next .stop, γS (sfρ' ρ c₁) σ sfhbS3, ch) := by
    rw [hpre, hpreC]
    exact sfhb_full_span ρ σ hag c₁ ch
  obtain ⟨σFfin, htF, hs⟩ := span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := sfhb_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (sfhb_pre_absRaftLog ρ σ)
  · have h := hs.lookup_some (sfhb_post_er ρ σ c₁)
    have hcell : renameCell r (⟨some (.interface ⟨"error"⟩), .nil⟩ : HeapCell)
        = ⟨some (.interface ⟨"error"⟩), .nil⟩ := rfl
    rw [hcell] at h
    exact h
  · exact absOutbox_ren hs (sfhb_post_absOutbox ρ σ c₁)
  · exact absOutbox_ren hs (sfhb_post_absOutbox_maa ρ σ c₁)
  · exact absRaftLog_ren hs (sfhb_post_absRaftLog ρ σ c₁)
  · exact fieldReadU64_ren hs (sfhb_post_lead ρ σ c₁)
  · have h := sfhb_post_vote ρ σ c₁
    simp only [hvote] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (sfhb_post_term ρ σ c₁)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture). -/
theorem stepFollower_heartbeat_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 1710 (γS ρ σ sfhbS0) (γC ρ sfhbC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ sfhbS0) (.addr (.base ⟨52⟩))
          = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ sfhbS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 69 0) 69 69 [] (γS ρ σ sfhbS0) (γS ρ σ sfhbS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 69 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, her, hob, hmaa, hlog1, hl, hv, ht⟩ :=
    stepFollower_heartbeat_eq_alloc ρ σ hag hvote c₁ ch hF
  have hcall : renameConfig (ρT 69 0) (γC ρ sfhbC0) = γC ρ sfhbC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT 69 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT 69 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 69 0 32⟩ : Addr) = ⟨32⟩ := rfl
  have h68 : (⟨ρT 69 0 68⟩ : Addr) = ⟨68⟩ := rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h68] at her
  rw [h31] at hob hmaa hl hv ht
  exact ⟨σfin, hrun, hmsg, hlog0, her, hob, hmaa, hlog1, hl, hv, ht⟩

/-! ## §3.3 discharge witness (the probe's values: Vote 7, lead 2,
state 0, leadTransferee 5; stream head 3 — realized capacity 7). -/

def sfhbρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem stepFollower_heartbeat_eq_witness :
    ∃ σfin,
      stepFnIter 1710 (γS sfhbρw wBase sfhbS0) (γC sfhbρw sfhbC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS sfhbρw wBase sfhbS0) (.addr (.base ⟨52⟩))
          = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS sfhbρw wBase sfhbS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  stepFollower_heartbeat_eq sfhbρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) 3 []

end GoLean.RaftSeam
