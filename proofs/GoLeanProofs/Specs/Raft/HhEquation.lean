import GoLeanProofs.Specs.Raft.HhLit
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# A4-U10: THE handleHeartbeat EQUATION — the first message-handler
equation, symbolic-from-birth on the full lens machinery

**LINEAGE: as `Bf31.lean` (the wave-2 charter's symbolic-from-birth
form) with the spill crossing via `stepFn_appendSpill_transport`
(SpillTransport.lean) instead of a map pick.**

The chain (probe-validated end-to-end by `artifacts/probe/HhGen.lean`
and `HhU10Probe{,2,4}.lean` BEFORE any theorem here): fixture BORN
RE-SITED (the bf31 heap — raft cell at 31, vars x₁..x₄ =
Vote/lead/state/leadTransferee — plus the Message argument at 52 with
Commit→cell 53 = 1 CONCRETE and From→cell 54 = 2 CONCRETE), pre-window
**1299** steps to the appendSlice SPILL quit (`.q3Choice`), ONE
spill crossing consuming the stream head, post-window **25** steps to
`.next .stop` — 1325 machine steps, exactly U9's census. The
choice-dependent artifacts enter the post fixture as VALUATION atoms
(value-atom 0 = the spilled `r.msgs` handle at the target temp 125;
cell-atom 0 = the fresh backing cell at 126 — `Valuation.cells`'
design case), so ONE post-window literal serves every consumed choice
(§4(ii) at the spill site); `hhρ'` absorbs the choice.

FIXTURE-FAMILY preconditions (recorded, the U3 fine-print pattern):
- `m.Commit = committed = 1` — the NO-OP `commitTo` branch (the
  commit-ADVANCE branch is the named second fixture family);
- `m.From = 2 ≠ r.id = 1` and CONCRETE — `send`'s self-addressed
  panic guard (`raft.go:601`-ish, `m.GetTo() == r.id`) BRANCHES on
  the response's To = m.From's value, so a symbolic From needs a
  branch crossing (side condition `m.From ≠ r.id` — the subject's own
  precondition); recorded as the follow-on refinement, not attempted
  here ([AGENT], the probe finding that refuted From-symbolism at
  zero crossings);
- `r.Term = 0`, `r.id = 1` concrete (the response's term/src).

Conclusions go through absState v2 (`absMessage`/`absRaftLog`/
`absOutbox`) and the Lens readers; the outbox readout is proved by
LEMMA COMPOSITION over the lens combinators (`sliceElems` is
array-index-based, so a choice-generic backing does not close by
reduction — the anti-grinding doctrine's preferred shape anyway).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/HhGen.lean` — the
window links below re-check the literals against these defs). -/

def hhMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def hhS0 : SymState :=
  { heap := bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) hhMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64))],
    nextAddr := 55 }

/-- The drained call configuration of `handleHeartbeat(&m)`. -/
def hhC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def hhElemTy : Ty := .pointer (.defined ⟨"raftpb.Message"⟩)

/-- The realized backing capacity at stream head `c` (nil old slice,
one appended element: width 32, envelope [1, 32]). -/
def hhCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- The backing-cell payload at stream head `c`: the response-message
pointer, then default-`nil` padding to the realized capacity. -/
def hhBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨74⟩)] ++ List.replicate (hhCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atom 0 (value) = the spilled
handle; atom 0 (cell) = the backing cell. Everything else rides. -/
def hhρ' (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) hhElemTy), hhBackingVal c⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms). -/

theorem hhW1_out : symEvalWindowTB bfTB 1299 hhS0 hhC0 = (1299, hhS1, hhC1) := by
  kernel_rfl

/-- The post-spill continuation, extracted from the quit config. -/
def hhK1 : GoLean.Sym.Cont symDom := match hhC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def hhE1 : LocalEnv := match hhC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem hhC1_shape : hhC1 = .retV (.slice ⟨some (.base ⟨124⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨125⟩)] [] hhE1 hhK1) := by
  kernel_rfl

theorem hhW2_out : symEvalWindowTB bfTB 25 hhS2 (.next hhK1)
    = (25, hhS3, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem hhWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 1299 (γS ρ σ hhS0) (γC ρ hhC0) ch
      = .ok (γC ρ hhC1, γS ρ σ hhS1, ch) :=
  symEvalWindowTB_refines hhW1_out ρ σ ch hag

theorem hhWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 25 (γS ρ σ hhS2) (γC ρ (.next hhK1)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ hhS3, ch) :=
  symEvalWindowTB_refines hhW2_out ρ σ ch hag

/-! ## THE SPILL CROSSING (the transport instantiated; every premise
discharged at the literal, the choice entering through `hhρ'`). -/

theorem hh_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (hhρ' ρ c₁) σ hhS1) (γC (hhρ' ρ c₁) hhC1) (c₁ :: rest)
      = .ok (γC (hhρ' ρ c₁) (.next hhK1), γS (hhρ' ρ c₁) σ hhS2, rest) := by
  have hvisE : sliceVisibleValues (γS (hhρ' ρ c₁) σ hhS1)
      ⟨some (.base ⟨124⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨74⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (hhρ' ρ c₁) σ hhS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (hhρ' ρ c₁) σ hhS1) hhElemTy
      #[] #[.addr (.base ⟨74⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (hhBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨74⟩)],
        normalizeValueForTy (γS (hhρ' ρ c₁) σ hhS1) hhElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (hhρ' ρ c₁) σ hhS1) hhElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (hhρ' ρ c₁) σ hhS1) (elem := hhElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨74⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [hhBackingVal, hhCap] using h
  have htgt : storeLoc { γS (hhρ' ρ c₁) σ hhS1 with
        heap := GoCore.Heap.set (γS (hhρ' ρ c₁) σ hhS1).heap
          (.base ⟨(γS (hhρ' ρ c₁) σ hhS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) hhElemTy),
           hhBackingVal c₁⟩,
        nextAddr := (γS (hhρ' ρ c₁) σ hhS1).nextAddr + 1 } (.base ⟨125⟩)
      (.slice ⟨some (.base ⟨(γS (hhρ' ρ c₁) σ hhS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (hhρ' ρ c₁) σ hhS2) := by
    kernel_rfl
  rw [hhC1_shape]
  exact stepFn_appendSpill_transport (hhρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 1,325-step span. -/

theorem hh_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 1325 (γS (hhρ' ρ c₁) σ hhS0) (γC (hhρ' ρ c₁) hhC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (hhρ' ρ c₁) σ hhS3, ch) := by
  have h := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => hhWin1 (hhρ' ρ c₁) σ chx hag)
    (hh_spill_step ρ σ c₁ ch)
    (fun chx => hhWin2 (hhρ' ρ c₁) σ chx hag)
  have hstop : γC (hhρ' ρ c₁) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  exact h

/-! ## Spec-side vocabulary (re-grounded; compat/verdi never imported).

`specHeartbeatResp src dst term` — the record `send` produces for a
heartbeat response (`raft.go:1854-1857`: `handleHeartbeat` sends
`{To: m.From, Type: MsgHeartbeatResp (=9), Context: m.GetContext()}`;
`raft.go:533+`: `send` fills `From := r.id` (the nil-From arm) and
`Term := r.Term` (HeartbeatResp is in neither the vote group nor
Prop/ReadIndex)). Verdi correspondence: the heartbeat is verdi-raft's
empty AppendEntries; its reply enters the net exactly one message per
delivery — the outbox gains ONE record. -/
def specHeartbeatResp (src dst term : Int) : AbsMessage :=
  ⟨9, dst, src, term, 0, 0, 0, 0, 0, false, [], []⟩

/-- The fixture family's log view (the NO-OP `commitTo` branch:
`m.Commit = committed`, so the whole log view is PRESERVED). -/
def hhAbsLog : AbsLog := ⟨[(1, 1)], [], 2, 1, 1, 1⟩

/-! ## Projection facts at the literals. -/

theorem hh_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ hhS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem hh_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ hhS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem hh_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (hhρ' ρ c₁) σ hhS3) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

/-- The msgs field of the post state reads the spilled handle. -/
theorem hh_post_msgs_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (hhρ' ρ c₁) σ hhS3) ⟨31⟩ ⟨"raft.raft"⟩ "msgs"
      = some (.slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c₁⟩) := by
  kernel_rfl

/-- The backing cell of the post state (the cell atom's image). -/
theorem hh_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (hhρ' ρ c₁) σ hhS3).heap (.base ⟨126⟩)
      = some ⟨some (.array (hhCap c₁) hhElemTy), hhBackingVal c₁⟩ := by
  kernel_rfl

/-- The response message cell projects to the spec record (the cell
and its deref cells are concrete literals — choice-free). -/
theorem hh_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (hhρ' ρ c₁) σ hhS3) (.addr (.base ⟨74⟩))
      = some (specHeartbeatResp 1 2 0) := by
  kernel_rfl

/-- The backing's head element (choice-generic: the padding never
enters — `List.getElem?` reduces at the cons head). -/
theorem hhBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨74⟩)] ++ List.replicate (hhCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨74⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (no window re-evaluation, no per-choice case split). -/
theorem hh_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (hhρ' ρ c₁) σ hhS3) ⟨31⟩ "msgs"
      = some [specHeartbeatResp 1 2 0] := by
  rw [absOutbox]
  rw [hh_post_msgs_field ρ σ c₁]
  show sliceRead (γS (hhρ' ρ c₁) σ hhS3)
    (.slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c₁⟩) _ = _
  rw [sliceRead]
  rw [hh_post_backing ρ σ c₁]
  show sliceElems (γS (hhρ' ρ c₁) σ hhS3)
    ⟨[GoValue.addr (.base ⟨74⟩)] ++ List.replicate (hhCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, hhBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [hh_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

/-- Untouched-scalar readouts (post): the store-time whole-struct
re-normalization wraps each surviving symbolic scalar ONCE (depth
probed at the literal); the range side conditions collapse it. -/
theorem hh_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhρ' ρ c₁) σ hhS3) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem hh_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhρ' ρ c₁) σ hhS3) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem hh_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhρ' ρ c₁) σ hhS3) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic, placement LIVE at
the born-re-sited fixture — wave-2 charter items 1–2). -/

/-- **THE handleHeartbeat HANDLER EQUATION** (no-op commitTo family):
from the drained `handleHeartbeat(&m)` call at ANY placement of the
fixture footprint (relocation `r` + disjoint frame `fr`, one
`FrameSim` premise), over EVERY consumed choice prefix (∀ streams
`c₁ :: ch` — the appendSpill capacity choice), the run returns in
exactly **1,325 steps** with one choice consumed, and:
the message argument projects by `absMessage` (From 2, Commit 1);
the log view is PRESERVED (`absRaftLog` before = after = `hhAbsLog` —
the no-op branch); the outbox gains EXACTLY the heartbeat response
(`absOutbox` = `[specHeartbeatResp r.id m.From r.Term]`); and the
untouched scalars read back unchanged (`fieldReadU64`, the lens
readers). Side conditions `hvote`/`hlead`: the surviving symbolic
scalars' uint64-range facts (the U3 norm-wrap story). -/
theorem handleHeartbeat_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ hhS0) σF) :
    ∃ σFfin,
      stepFnIter 1325 σF (renameConfig r (γC ρ hhC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (hhρ' ρ c₁) σ hhS3) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ hhS0 = γS (hhρ' ρ c₁) σ hhS0 := by kernel_rfl
  have hpreC : γC ρ hhC0 = γC (hhρ' ρ c₁) hhC0 := by kernel_rfl
  have hrun : stepFnIter 1325 (γS ρ σ hhS0) (γC ρ hhC0) (c₁ :: ch)
      = .ok (.next .stop, γS (hhρ' ρ c₁) σ hhS3, ch) := by
    rw [hpre, hpreC]
    exact hh_full_span ρ σ hag c₁ ch
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 1325 hF
    (γC ρ hhC0) (c₁ :: ch)
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hh_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (hh_pre_absRaftLog ρ σ)
  · have h := hh_post_absOutbox ρ σ c₁
    exact absOutbox_ren hs h
  · exact absRaftLog_ren hs (hh_post_absRaftLog ρ σ c₁)
  · have h := hh_post_vote ρ σ c₁
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := hh_post_lead ρ σ c₁
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (hh_post_term ρ σ c₁)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture). -/
theorem handleHeartbeat_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 1325 (γS ρ σ hhS0) (γC ρ hhC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ hhS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ hhS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 55 0) 55 55 [] (γS ρ σ hhS0) (γS ρ σ hhS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 55 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hlog1, hv, hl, ht⟩ :=
    handleHeartbeat_handler_eq_alloc ρ σ hag hvote hlead c₁ ch hF
  have hcall : renameConfig (ρT 55 0) (γC ρ hhC0) = γC ρ hhC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT 55 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT 55 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 55 0 32⟩ : Addr) = ⟨32⟩ := rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h31] at hob hv hl ht
  exact ⟨σfin, hrun, hmsg, hlog0, hob, hlog1, hv, hl, ht⟩

/-! ## §3.3 discharge witness (the probe's values: Vote 7, lead 2,
state 0, leadTransferee 5; stream head 3 — realized capacity 7). -/

def hhρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleHeartbeat_handler_eq_witness :
    ∃ σfin,
      stepFnIter 1325 (γS hhρw wBase hhS0) (γC hhρw hhC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS hhρw wBase hhS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS hhρw wBase hhS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleHeartbeat_handler_eq hhρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 []

end GoLean.RaftSeam
