import GoLeanProofs.Specs.Raft.HhFromLit

/-!
# A4-U14: THE From-SYMBOLIC handleHeartbeat EQUATION — the branch
transport's discharge demonstration (the U10 message-field-symbolism
residual CLOSED at its first consumer)

**LINEAGE: `HhEquation.lean` upgraded through
`Sym/BranchTransport.lean`** (path-condition splitting, King 1976 —
the PickTransport/SpillTransport pattern's third member). U10's
probe REFUTED From-symbolism at zero crossings: `send`'s
self-addressed panic guard (raft.go:601-ish, `m.GetTo() == r.id`
where the response's To aliases m.From) BRANCHES on the From value.
This module states the handleHeartbeat no-op equation with **m.From
SYMBOLIC (var 5)** under the subject's own precondition as a side
condition — `hfrom_ne : ρ.ints 5 ≠ 1 (= r.id)`, plus the uint64
range fact `hfrom` — and crosses the guard with
`stepFn_branch_transport` (the path condition `eqI(norm²(x₅), 1)`
concretizes FALSE, the else arm is the empty `seqn #[]`).

Chain (probe-validated end-to-end by `artifacts/probe/{HhFromProbe,
HhFromGen}.lean` BEFORE any theorem; γ==machine at c = 0/3/31 at
ints₅ = 2): windows **[1259, 39, 25]** + the BRANCH crossing (state
and stream RIDE — the crossing is pure control) + the spill crossing
(the Hh cells VERBATIM: elems 124, target 125, backing 126, response
message 74 — the branch detour does not change the allocation
schedule) = **1,325 steps, one choice** — the same span and stream
shape as the shipped concrete equation, which stays untouched.

THE PAYOFF, stated honestly: the response's To field aliases the
argument's From cell (plainpb pointer copy), which holds RAW var 5 —
so the outbox conclusion is **`[specHeartbeatResp 1 (ρ.ints 5) 0]`**:
the response's destination is proved to be m.From's VALUE for EVERY
non-self-addressed sender, not for the fixture constant 2. The
shipped `handleHeartbeat_handler_eq` is this equation's ints₅ := 2
instance (side conditions `by decide`).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture: the shipped Hh no-op fixture with cell 54 (the
From deref cell) SYMBOLIC (MUST match `artifacts/probe/HhFromGen.lean`
— the window links re-check the literals against this def). -/

def hhFromS0 : SymState :=
  { heap := hhS0.heap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
      if p.1 == .base ⟨54⟩ then
        (p.1, .mk (some (.int .uint64)) (.int (.var 5) .uint64))
      else p),
    nextAddr := 55 }

/-! ## The branch-quit pieces, extracted from the generated literal
(the `hhFromC1_shape` kernel link re-checks the decomposition). -/

def hhFromCond : SymBool := match hhFromC1 with
  | .retV (GoLean.Sym.Value.bool sb) _ => sb
  | _ => .lit true

def hhFromThen : Stmt := match hhFromC1 with
  | .retV _ (.ifK t _ _ _) => t
  | _ => .seqn #[]
def hhFromElse : Stmt := match hhFromC1 with
  | .retV _ (.ifK _ e _ _) => e
  | _ => .seqn #[]
def hhFromEnv1 : LocalEnv := match hhFromC1 with
  | .retV _ (.ifK _ _ env _) => env
  | _ => []
def hhFromK1 : GoLean.Sym.Cont symDom := match hhFromC1 with
  | .retV _ (.ifK _ _ _ k) => k
  | _ => .stop

theorem hhFromC1_shape : hhFromC1
    = .retV (.bool hhFromCond) (.ifK hhFromThen hhFromElse hhFromEnv1 hhFromK1) := by
  kernel_rfl

/-- The path condition IS the self-addressed check: `norm²(x₅) == 1`. -/
theorem hhFromCond_form (ρ : Valuation) :
    γB ρ hhFromCond
      = (IntKind.normalize .uint64 (IntKind.normalize .uint64 (ρ.ints 5))
          == (1 : Int)) := by
  with_unfolding_all rfl

/-! ## The spill-quit pieces. -/

def hhFromE2 : LocalEnv := match hhFromC2 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []
def hhFromK2 : GoLean.Sym.Cont symDom := match hhFromC2 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop

theorem hhFromC2_shape : hhFromC2 = .retV (.slice ⟨some (.base ⟨124⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨hhFromTgt⟩)] [] hhFromE2 hhFromK2) := by
  kernel_rfl

/-! ## The window LINK theorems (kernel-checked against the
evaluator; the step counts are the GENERATOR-EMITTED
`hhFromW1n`/`hhFromW2n`/`hhFromW3n`). -/

theorem hhFromW1_out : symEvalWindowTB bfTB hhFromW1n hhFromS0 hhC0
    = (hhFromW1n, hhFromS1, hhFromC1) := by
  kernel_rfl

theorem hhFromW2_out : symEvalWindowTB bfTB hhFromW2n hhFromS1
    (.exec hhFromElse hhFromEnv1 hhFromK1)
    = (hhFromW2n, hhFromS2, hhFromC2) := by
  kernel_rfl

theorem hhFromW3_out : symEvalWindowTB bfTB hhFromW3n hhFromS3 (.next hhFromK2)
    = (hhFromW3n, hhFromS4, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem hhFromWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter hhFromW1n (γS ρ σ hhFromS0) (γC ρ hhC0) ch
      = .ok (γC ρ hhFromC1, γS ρ σ hhFromS1, ch) :=
  symEvalWindowTB_refines hhFromW1_out ρ σ ch hag

theorem hhFromWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter hhFromW2n (γS ρ σ hhFromS1)
      (γC ρ (.exec hhFromElse hhFromEnv1 hhFromK1)) ch
      = .ok (γC ρ hhFromC2, γS ρ σ hhFromS2, ch) :=
  symEvalWindowTB_refines hhFromW2_out ρ σ ch hag

theorem hhFromWin3 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter hhFromW3n (γS ρ σ hhFromS3) (γC ρ (.next hhFromK2)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ hhFromS4, ch) :=
  symEvalWindowTB_refines hhFromW3_out ρ σ ch hag

/-! ## THE BRANCH CROSSING (`stepFn_branch_transport` discharged by
the subject's own precondition — the side conditions
`hfrom`/`hfrom_ne`). State and stream ride through. -/

theorem hhFrom_branch_step (ρ : Valuation) (σ : ExecState)
    (hfrom : IntKind.normalize .uint64 (ρ.ints 5) = ρ.ints 5)
    (hfrom_ne : ρ.ints 5 ≠ 1) (ch : Choices) :
    stepFn (γS ρ σ hhFromS1) (γC ρ hhFromC1) ch
      = .ok (γC ρ (.exec hhFromElse hhFromEnv1 hhFromK1), γS ρ σ hhFromS1, ch) := by
  have hbeq : (ρ.ints 5 == (1 : Int)) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact hfrom_ne
  have hb : concV (symInterp ρ) (GoLean.Sym.Value.bool hhFromCond)
      = .bool false := by
    have h1 : concV (symInterp ρ) (GoLean.Sym.Value.bool hhFromCond)
        = .bool (γB ρ hhFromCond) := by
      with_unfolding_all rfl
    rw [h1, hhFromCond_form ρ, hfrom, hfrom, hbeq]
  rw [hhFromC1_shape]
  exact stepFn_branch_transport ρ σ (b := false) hb

/-! ## THE SPILL CROSSING (the Hh crossing at the From-symbolic
literals: the choice-absorbing valuation is the shipped `hhρ'` —
elems 124, target 125, backing 126, all generator-confirmed). -/

theorem hhFrom_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (hhρ' ρ c₁) σ hhFromS2) (γC (hhρ' ρ c₁) hhFromC2) (c₁ :: rest)
      = .ok (γC (hhρ' ρ c₁) (.next hhFromK2), γS (hhρ' ρ c₁) σ hhFromS3, rest) := by
  have hvisE : sliceVisibleValues (γS (hhρ' ρ c₁) σ hhFromS2)
      ⟨some (.base ⟨124⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨hhFromMsgPtr⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (hhρ' ρ c₁) σ hhFromS2)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (hhρ' ρ c₁) σ hhFromS2) hhElemTy
      #[] #[.addr (.base ⟨hhFromMsgPtr⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (hhBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨hhFromMsgPtr⟩)],
        normalizeValueForTy (γS (hhρ' ρ c₁) σ hhFromS2) hhElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (hhρ' ρ c₁) σ hhFromS2) hhElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (hhρ' ρ c₁) σ hhFromS2) (elem := hhElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨hhFromMsgPtr⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [hhBackingVal, hhCap, hhFromMsgPtr] using h
  have htgt : storeLoc { γS (hhρ' ρ c₁) σ hhFromS2 with
        heap := GoCore.Heap.set (γS (hhρ' ρ c₁) σ hhFromS2).heap
          (.base ⟨(γS (hhρ' ρ c₁) σ hhFromS2).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) hhElemTy),
           hhBackingVal c₁⟩,
        nextAddr := (γS (hhρ' ρ c₁) σ hhFromS2).nextAddr + 1 } (.base ⟨hhFromTgt⟩)
      (.slice ⟨some (.base ⟨(γS (hhρ' ρ c₁) σ hhFromS2).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (hhρ' ρ c₁) σ hhFromS3) := by
    kernel_rfl
  rw [hhFromC2_shape]
  exact stepFn_appendSpill_transport (hhρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 1,325-step span (window ∘ branch ∘ window ∘
spill ∘ window — `stepFnIter_chain` at the branch, the pick-window
spine at the spill). -/

theorem hhFrom_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (hfrom : IntKind.normalize .uint64 (ρ.ints 5) = ρ.ints 5)
    (hfrom_ne : ρ.ints 5 ≠ 1)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 1325 (γS (hhρ' ρ c₁) σ hhFromS0) (γC (hhρ' ρ c₁) hhC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (hhρ' ρ c₁) σ hhFromS4, ch) := by
  have hfrom' : IntKind.normalize .uint64 ((hhρ' ρ c₁).ints 5)
      = (hhρ' ρ c₁).ints 5 := hfrom
  have hne' : (hhρ' ρ c₁).ints 5 ≠ 1 := hfrom_ne
  have h12 := GoLean.Surface.stepFnIter_chain
    (hhFromWin1 (hhρ' ρ c₁) σ (c₁ :: ch) hag)
    (GoLean.Surface.stepFnIter_one
      (hhFrom_branch_step (hhρ' ρ c₁) σ hfrom' hne' (c₁ :: ch)))
  have h345 := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => hhFromWin2 (hhρ' ρ c₁) σ chx hag)
    (hhFrom_spill_step ρ σ c₁ ch)
    (fun chx => hhFromWin3 (hhρ' ρ c₁) σ chx hag)
  have h := GoLean.Surface.stepFnIter_chain h12 h345
  have hstop : γC (hhρ' ρ c₁) (.next .stop) = .next .stop := rfl
  have hn : hhFromW1n + 1 + (hhFromW2n + 1 + hhFromW3n) = 1325 := rfl
  rw [← hstop, ← hn]
  exact h

/-! ## Projection facts at the literals. -/

/-- The message argument, From-symbolic: src = ρ.ints 5. -/
theorem hhFrom_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ hhFromS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, ρ.ints 5, 0, 0, 0, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem hhFrom_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ hhFromS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem hhFrom_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (hhρ' ρ c₁) σ hhFromS4) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem hhFrom_post_msgs_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (hhρ' ρ c₁) σ hhFromS4) ⟨31⟩ ⟨"raft.raft"⟩ "msgs"
      = some (.slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c₁⟩) := by
  kernel_rfl

theorem hhFrom_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (hhρ' ρ c₁) σ hhFromS4).heap (.base ⟨126⟩)
      = some ⟨some (.array (hhCap c₁) hhElemTy), hhBackingVal c₁⟩ := by
  kernel_rfl

/-- **The From-symbolic response record**: the To field aliases the
argument's From cell (raw var 5) — dst = ρ.ints 5, UNWRAPPED. -/
theorem hhFrom_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (hhρ' ρ c₁) σ hhFromS4) (.addr (.base ⟨hhFromMsgPtr⟩))
      = some (specHeartbeatResp 1 (ρ.ints 5) 0) := by
  kernel_rfl

/-- **THE OUTBOX READOUT** (lemma composition, the Hh pattern): the
outbox gains the heartbeat response addressed to the SYMBOLIC
sender. -/
theorem hhFrom_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (hhρ' ρ c₁) σ hhFromS4) ⟨31⟩ "msgs"
      = some [specHeartbeatResp 1 (ρ.ints 5) 0] := by
  rw [absOutbox]
  rw [hhFrom_post_msgs_field ρ σ c₁]
  show sliceRead (γS (hhρ' ρ c₁) σ hhFromS4)
    (.slice ⟨some (.base ⟨126⟩), 0, 1, hhCap c₁⟩) _ = _
  rw [sliceRead]
  rw [hhFrom_post_backing ρ σ c₁]
  show sliceElems (γS (hhρ' ρ c₁) σ hhFromS4)
    ⟨[GoValue.addr (.base ⟨74⟩)] ++ List.replicate (hhCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, hhBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [show (⟨74⟩ : Addr) = ⟨hhFromMsgPtr⟩ from rfl]
  rw [hhFrom_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

theorem hhFrom_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhρ' ρ c₁) σ hhFromS4) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem hhFrom_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhρ' ρ c₁) σ hhFromS4) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem hhFrom_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhρ' ρ c₁) σ hhFromS4) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic; the sim plumbing =
the lifted `Frame.span_relocate`). -/

/-- **THE From-SYMBOLIC handleHeartbeat EQUATION** (no-op commitTo
family): the shipped equation's statement with m.From a SYMBOLIC
value — from the drained call at ANY placement (one `FrameSim`
premise), over EVERY consumed choice prefix, under the subject's own
precondition (`hfrom_ne : ρ.ints 5 ≠ r.id = 1`, plus the uint64 range
fact), the run returns in 1,325 steps with one choice consumed, and
the outbox gains EXACTLY `[specHeartbeatResp r.id m.From r.Term]` at
the SYMBOLIC From — the response destination proved for every
non-self-addressed sender at once. The shipped concrete equation is
this statement's ints₅ := 2 instance. -/
theorem handleHeartbeat_fromSym_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (hfrom : IntKind.normalize .uint64 (ρ.ints 5) = ρ.ints 5)
    (hfrom_ne : ρ.ints 5 ≠ 1)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ hhFromS0) σF) :
    ∃ σFfin,
      stepFnIter 1325 σF (renameConfig r (γC ρ hhC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (hhρ' ρ c₁) σ hhFromS4) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, ρ.ints 5, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs"
          = some [specHeartbeatResp 1 (ρ.ints 5) 0]
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ hhFromS0 = γS (hhρ' ρ c₁) σ hhFromS0 := by kernel_rfl
  have hpreC : γC ρ hhC0 = γC (hhρ' ρ c₁) hhC0 := by kernel_rfl
  have hrun : stepFnIter 1325 (γS ρ σ hhFromS0) (γC ρ hhC0) (c₁ :: ch)
      = .ok (.next .stop, γS (hhρ' ρ c₁) σ hhFromS4, ch) := by
    rw [hpre, hpreC]
    exact hhFrom_full_span ρ σ hag hfrom hfrom_ne c₁ ch
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hhFrom_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (hhFrom_pre_absRaftLog ρ σ)
  · exact absOutbox_ren hs (hhFrom_post_absOutbox ρ σ c₁)
  · exact absRaftLog_ren hs (hhFrom_post_absRaftLog ρ σ c₁)
  · have h := hhFrom_post_vote ρ σ c₁
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := hhFrom_post_lead ρ σ c₁
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (hhFrom_post_term ρ σ c₁)

/-- The identity-placement corollary. -/
theorem handleHeartbeat_fromSym_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (hfrom : IntKind.normalize .uint64 (ρ.ints 5) = ρ.ints 5)
    (hfrom_ne : ρ.ints 5 ≠ 1)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 1325 (γS ρ σ hhFromS0) (γC ρ hhC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ hhFromS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, ρ.ints 5, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ hhFromS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 (ρ.ints 5) 0]
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 55 0) 55 55 [] (γS ρ σ hhFromS0) (γS ρ σ hhFromS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 55 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hlog1, hv, hl, ht⟩ :=
    handleHeartbeat_fromSym_eq_alloc ρ σ hag hvote hlead hfrom hfrom_ne c₁ ch hF
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

/-! ## §3.3 discharge witness (Vote 7, lead 2, ldT 5, **From = ints₅
= 9** — a value NO shipped fixture used, demonstrating genuine
From-generality; stream head 3). -/

def hhFromρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5, 9].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleHeartbeat_fromSym_eq_witness :
    ∃ σfin,
      stepFnIter 1325 (γS hhFromρw wBase hhFromS0) (γC hhFromρw hhC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS hhFromρw wBase hhFromS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 9, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS hhFromρw wBase hhFromS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 9 0]
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleHeartbeat_fromSym_eq hhFromρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) 3 []

end GoLean.RaftSeam
