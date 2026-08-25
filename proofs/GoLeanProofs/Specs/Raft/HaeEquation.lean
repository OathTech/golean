import GoLeanProofs.Specs.Raft.HaeLit
import GoLeanProofs.Specs.Raft.HhEquation

/-!
# A4-U11: THE handleAppendEntries EQUATION — the SUCCESS/EMPTY-ENTRIES
family (the second message-handler equation; pure assembly on the
A4-U10 spill transport, per the U10 census)

**LINEAGE: as `HhEquation.lean` verbatim** — the chain differs only in
the fixture (LogTerm→55 = 1, Index→56 = 1 — matching prev at
lastIndex), the window schedule [2798, 29], the crossing cells (temp
225, elems 224 → response message 183, backing born at 226), and the
outbox: `send` routes MsgAppResp (typ 4) to **`msgsAfterAppend`**
(the async-storage group), so the `msgs` outbox stays EMPTY — both
facts are conclusions. Probe-validated end-to-end by
`artifacts/probe/{HaeProbe,HaeGen}.lean` before any theorem here
(γ==machine at c=0/3/31; one choice at step 2798; the whole
maybeAppend/term-match/commitTo chain in-window on landed classes —
ZERO new machinery, the U10 census's prediction).

FIXTURE-FAMILY preconditions (recorded): matching prev
(`m.Index = lastIndex = 1`, `m.LogTerm = term(1) = 1`), EMPTY entries
(the non-empty log-append family is deliverable 3's census),
`m.Commit = committed = 1` (no commit advance), `m.From = 2 ≠ r.id`
concrete (the U10 self-addressed-guard finding), `r.Term = 0`.
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

def haeMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)), ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def haeS0 : SymState :=
  { heap := bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) haeMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨56⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64))],
    nextAddr := 57 }

/-- The drained call configuration of `handleHeartbeat(&m)`. -/
def haeC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def haeElemTy : Ty := .pointer (.defined ⟨"raftpb.Message"⟩)

/-- The realized backing capacity at stream head `c` (nil old slice,
one appended element: width 32, envelope [1, 32]). -/
def haeCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- The backing-cell payload at stream head `c`: the response-message
pointer, then default-`nil` padding to the realized capacity. -/
def haeBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨183⟩)] ++ List.replicate (haeCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atom 0 (value) = the spilled
handle; atom 0 (cell) = the backing cell. Everything else rides. -/
def haeρ' (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨226⟩), 0, 1, haeCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (haeCap c) haeElemTy), haeBackingVal c⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms). -/

theorem haeW1_out : symEvalWindowTB bfTB 2798 haeS0 haeC0 = (2798, haeS1, haeC1) := by
  kernel_rfl

/-- The post-spill continuation, extracted from the quit config. -/
def haeK1 : GoLean.Sym.Cont symDom := match haeC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def haeE1 : LocalEnv := match haeC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem haeC1_shape : haeC1 = .retV (.slice ⟨some (.base ⟨224⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice haeElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨225⟩)] [] haeE1 haeK1) := by
  kernel_rfl

theorem haeW2_out : symEvalWindowTB bfTB 29 haeS2 (.next haeK1)
    = (29, haeS3, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem haeWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 2798 (γS ρ σ haeS0) (γC ρ haeC0) ch
      = .ok (γC ρ haeC1, γS ρ σ haeS1, ch) :=
  symEvalWindowTB_refines haeW1_out ρ σ ch hag

theorem haeWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 29 (γS ρ σ haeS2) (γC ρ (.next haeK1)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ haeS3, ch) :=
  symEvalWindowTB_refines haeW2_out ρ σ ch hag

/-! ## THE SPILL CROSSING (the transport instantiated; every premise
discharged at the literal, the choice entering through `haeρ'`). -/

theorem hae_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (haeρ' ρ c₁) σ haeS1) (γC (haeρ' ρ c₁) haeC1) (c₁ :: rest)
      = .ok (γC (haeρ' ρ c₁) (.next haeK1), γS (haeρ' ρ c₁) σ haeS2, rest) := by
  have hvisE : sliceVisibleValues (γS (haeρ' ρ c₁) σ haeS1)
      ⟨some (.base ⟨224⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨183⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (haeρ' ρ c₁) σ haeS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (haeρ' ρ c₁) σ haeS1) haeElemTy
      #[] #[.addr (.base ⟨183⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (haeBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨183⟩)],
        normalizeValueForTy (γS (haeρ' ρ c₁) σ haeS1) haeElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (haeρ' ρ c₁) σ haeS1) haeElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (haeρ' ρ c₁) σ haeS1) (elem := haeElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨183⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [haeBackingVal, haeCap] using h
  have htgt : storeLoc { γS (haeρ' ρ c₁) σ haeS1 with
        heap := GoCore.Heap.set (γS (haeρ' ρ c₁) σ haeS1).heap
          (.base ⟨(γS (haeρ' ρ c₁) σ haeS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) haeElemTy),
           haeBackingVal c₁⟩,
        nextAddr := (γS (haeρ' ρ c₁) σ haeS1).nextAddr + 1 } (.base ⟨225⟩)
      (.slice ⟨some (.base ⟨(γS (haeρ' ρ c₁) σ haeS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (haeρ' ρ c₁) σ haeS2) := by
    kernel_rfl
  rw [haeC1_shape]
  exact stepFn_appendSpill_transport (haeρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 1,325-step span. -/

theorem hae_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 2828 (γS (haeρ' ρ c₁) σ haeS0) (γC (haeρ' ρ c₁) haeC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (haeρ' ρ c₁) σ haeS3, ch) := by
  have h := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => haeWin1 (haeρ' ρ c₁) σ chx hag)
    (hae_spill_step ρ σ c₁ ch)
    (fun chx => haeWin2 (haeρ' ρ c₁) σ chx hag)
  have hstop : γC (haeρ' ρ c₁) (.next .stop) = .next .stop := rfl
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
def specAppResp (src dst term index : Int) : AbsMessage :=
  ⟨4, dst, src, term, 0, index, 0, 0, 0, false, [], []⟩

/- The fixture family's log view is `hhAbsLog` (imported from
`HhEquation` — the same heap family; the NO-OP `commitTo` branch
preserves the whole view). -/

/-! ## Projection facts at the literals. -/

theorem hae_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ haeS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem hae_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ haeS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem hae_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (haeρ' ρ c₁) σ haeS3) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

/-- The msgs field of the post state reads the spilled handle. -/
theorem hae_post_maa_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (haeρ' ρ c₁) σ haeS3) ⟨31⟩ ⟨"raft.raft"⟩ "msgsAfterAppend"
      = some (.slice ⟨some (.base ⟨226⟩), 0, 1, haeCap c₁⟩) := by
  kernel_rfl

/-- The backing cell of the post state (the cell atom's image). -/
theorem hae_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (haeρ' ρ c₁) σ haeS3).heap (.base ⟨226⟩)
      = some ⟨some (.array (haeCap c₁) haeElemTy), haeBackingVal c₁⟩ := by
  kernel_rfl

/-- The response message cell projects to the spec record (the cell
and its deref cells are concrete literals — choice-free). -/
theorem hae_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (haeρ' ρ c₁) σ haeS3) (.addr (.base ⟨183⟩))
      = some (specAppResp 1 2 0 1) := by
  kernel_rfl

/-- The backing's head element (choice-generic: the padding never
enters — `List.getElem?` reduces at the cons head). -/
theorem haeBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨183⟩)] ++ List.replicate (haeCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨183⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (no window re-evaluation, no per-choice case split). -/
theorem hae_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (haeρ' ρ c₁) σ haeS3) ⟨31⟩ "msgsAfterAppend"
      = some [specAppResp 1 2 0 1] := by
  rw [absOutbox]
  rw [hae_post_maa_field ρ σ c₁]
  show sliceRead (γS (haeρ' ρ c₁) σ haeS3)
    (.slice ⟨some (.base ⟨226⟩), 0, 1, haeCap c₁⟩) _ = _
  rw [sliceRead]
  rw [hae_post_backing ρ σ c₁]
  show sliceElems (γS (haeρ' ρ c₁) σ haeS3)
    ⟨[GoValue.addr (.base ⟨183⟩)] ++ List.replicate (haeCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, haeBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [hae_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

/-- Untouched-scalar readouts (post): the store-time whole-struct
re-normalization wraps each surviving symbolic scalar ONCE (depth
probed at the literal); the range side conditions collapse it. -/
theorem hae_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (haeρ' ρ c₁) σ haeS3) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem hae_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (haeρ' ρ c₁) σ haeS3) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem hae_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (haeρ' ρ c₁) σ haeS3) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-- Generic span relocation: the `stepFnIter_sim`/`ok_inv` plumbing
ONCE, at opaque states — every handler's alloc form applies this
instead of re-running the sim elimination inline. (Also the guard
against the elaborator pathology found at this handler: an
inline `hsim.ok_inv hrun` with a WRONG step count sends the
elaborator into whnf-unfolding both `stepFnIter` spines; here `n` is
shared by construction.) LINEAGE: the SL frame-lift plumbing
(Yang–O'Hearn), packaged. -/
theorem span_relocate {n : Nat} {σ0 σfin σF : ExecState}
    {c : Machine.Config} {chIn chOut : Choices}
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    (hrun : stepFnIter n σ0 c chIn = .ok (.next .stop, σfin, chOut))
    (hF : FrameSim r na₀ na fr σ0 σF) :
    ∃ σFfin, stepFnIter n σF (renameConfig r c) chIn
        = .ok (.next .stop, σFfin, chOut)
      ∧ FrameSim r na₀ na fr σfin σFfin := by
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) n hF c chIn
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  exact ⟨σFfin, htF, hs⟩

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
theorem handleAppendEntries_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ haeS0) σF) :
    ∃ σFfin,
      stepFnIter 2828 σF (renameConfig r (γC ρ haeC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (haeρ' ρ c₁) σ haeS3) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 1]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ haeS0 = γS (haeρ' ρ c₁) σ haeS0 := by kernel_rfl
  have hpreC : γC ρ haeC0 = γC (haeρ' ρ c₁) haeC0 := by kernel_rfl
  have hrun : stepFnIter 2828 (γS ρ σ haeS0) (γC ρ haeC0) (c₁ :: ch)
      = .ok (.next .stop, γS (haeρ' ρ c₁) σ haeS3, ch) := by
    rw [hpre, hpreC]
    exact hae_full_span ρ σ hag c₁ ch
  obtain ⟨σFfin, htF, hs⟩ := span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hae_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (hae_pre_absRaftLog ρ σ)
  · have h := hae_post_absOutbox ρ σ c₁
    exact absOutbox_ren hs h
  · exact absOutbox_ren hs (show absOutbox (γS (haeρ' ρ c₁) σ haeS3) ⟨31⟩
      "msgs" = some [] by kernel_rfl)
  · exact absRaftLog_ren hs (hae_post_absRaftLog ρ σ c₁)
  · have h := hae_post_vote ρ σ c₁
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := hae_post_lead ρ σ c₁
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (hae_post_term ρ σ c₁)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture). -/
theorem handleAppendEntries_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 2828 (γS ρ σ haeS0) (γC ρ haeC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ haeS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ haeS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 1]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 57 0) 57 57 [] (γS ρ σ haeS0) (γS ρ σ haeS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 57 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩ :=
    handleAppendEntries_handler_eq_alloc ρ σ hag hvote hlead c₁ ch hF
  have hcall : renameConfig (ρT 57 0) (γC ρ haeC0) = γC ρ haeC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT 57 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT 57 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 57 0 32⟩ : Addr) = ⟨32⟩ := rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h31] at hob hobm hv hl ht
  exact ⟨σfin, hrun, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩

/-! ## §3.3 discharge witness (the probe's values: Vote 7, lead 2,
state 0, leadTransferee 5; stream head 3 — realized capacity 7). -/

def haeρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleAppendEntries_handler_eq_witness :
    ∃ σfin,
      stepFnIter 2828 (γS haeρw wBase haeS0) (γC haeρw haeC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS haeρw wBase haeS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS haeρw wBase haeS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 1]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleAppendEntries_handler_eq haeρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 []

end GoLean.RaftSeam
