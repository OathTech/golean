import GoLeanProofs.Specs.Raft.HhAdvLit

/-!
# A4-U13: THE handleHeartbeat COMMIT-ADVANCE EQUATION — the second
handleHeartbeat family (the U10 residual taken): handleHeartbeat is
now COMPLETE (no-op at U10, advance here)

**LINEAGE: `HhAdvEquation`'s assembly shape at the heartbeat call** —
the chain differs in the fixture (the TWO-ENTRY stable log at
`committed = 1` — lastIndex = 2, advance HEADROOM — with the
heartbeat message carrying `m.Commit = 2`), the windows [1655, 25]
(the pre-window is Hh's plus the ADVANCE branch of `commitTo`:
`committed < tocommit` concrete-true, `lastIndex()` through the full
Bf dispatch chain — unstable.maybeLastIndex's len read on the
CONCRETE empty unstable, the Storage interface dispatch, mutex,
callStats — then `committed := 2`), and the crossing cells (elems
150 → response message 100, target temp 151, backing born at 152).
Probe-validated end-to-end by `artifacts/probe/{HhAdvProbe,
HhAdvGen}.lean` before any theorem (γ==machine at c=0/3/31; one
choice at step 1655; zero new machinery — pure assembly).

THE HEADLINE CONCLUSION: **`absRaftLog` committed 1 → 2 with the log
VIEW untouched** (`hha_committed_advanced`, axiom-free) — the first
equation whose post-state ADVANCES the commit index; the response is
the same `specHeartbeatResp 1 2 0` record as the no-op family, into
`msgs` (the sync group).

FIXTURE-FAMILY preconditions (recorded): `committed = 1 < m.Commit =
2 ≤ lastIndex = 2` (the advance guard's panic branch is
concrete-false — m.Commit ≤ lastIndex), `m.From = 2 ≠ r.id`,
`r.Term = 0`.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/HhAdvGen.lean` — the
window links below re-check the literals against these defs). -/

def hhaIfaceHarnessG : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))

/-- The two-entry stable log at committed = 1 (advance headroom). -/
def hhaLogValG : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
      ("offset", .int 3 .uint64),
      ("snapshotInProgress", .bool false), ("offsetInProgress", .int 3 .uint64),
      ("logger", hhaIfaceHarnessG)]),
    ("committed", .int 1 .uint64), ("applying", .int 1 .uint64),
    ("applied", .int 1 .uint64),
    ("logger", hhaIfaceHarnessG), ("maxApplyingEntsSize", .int 1048576 .uint64),
    ("applyingEntsSize", .int 0 .uint64), ("applyingEntsPaused", .bool false)]

def hhaMsgValG : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def hhaSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨32⟩ then
      (p.1, .mk (some (.defined ⟨"raft.raftLog"⟩)) (embedGo hhaLogValG))
    else if p.1 == .base ⟨37⟩ then
      (p.1, .mk (some (.defined ⟨"raft.MemoryStorage"⟩)) (embedGo staleMsValG))
    else if p.1 == .base ⟨46⟩ then
      (p.1, .mk (some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))))
        (embedGo (.array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)])))
    else p)) ++
  [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) (embedGo hhaMsgValG)),
   (.base ⟨53⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64))),
   (.base ⟨54⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64))),
   (.base ⟨57⟩, .mk (some (.defined ⟨"raftpb.Entry"⟩)) (embedGo staleEntry2G)),
   (.base ⟨58⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨59⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64)))]

def hhaS0 : SymState := { heap := hhaSymHeap, nextAddr := 60 }

/-- The drained call configuration of `handleAppendEntries(&m)`. -/
def hhaC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleHeartbeat"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def hhaElemTy : Ty := .pointer (.defined ⟨"raftpb.Message"⟩)

/-- The realized backing capacity at stream head `c` (nil old slice,
one appended element: width 32, envelope [1, 32]). -/
def hhaCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- The backing-cell payload at stream head `c`: the response-message
pointer (cell 93), then default-`nil` padding to the realized
capacity. -/
def hhaBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨100⟩)] ++ List.replicate (hhaCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atom 0 (value) = the spilled
handle; atom 0 (cell) = the backing cell. Everything else rides. -/
def hhaρ' (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨152⟩), 0, 1, hhaCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (hhaCap c) hhaElemTy), hhaBackingVal c⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms). -/

theorem hhaW1_out : symEvalWindowTB bfTB 1655 hhaS0 hhaC0
    = (1655, hhaS1, hhaC1) := by
  kernel_rfl

/-- The post-spill continuation, extracted from the quit config. -/
def hhaK1 : GoLean.Sym.Cont symDom := match hhaC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def hhaE1 : LocalEnv := match hhaC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem hhaC1_shape : hhaC1 = .retV (.slice ⟨some (.base ⟨150⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhaElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨151⟩)] [] hhaE1 hhaK1) := by
  kernel_rfl

theorem hhaW2_out : symEvalWindowTB bfTB 25 hhaS2 (.next hhaK1)
    = (25, hhaS3, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem hhaWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 1655 (γS ρ σ hhaS0) (γC ρ hhaC0) ch
      = .ok (γC ρ hhaC1, γS ρ σ hhaS1, ch) :=
  symEvalWindowTB_refines hhaW1_out ρ σ ch hag

theorem hhaWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 25 (γS ρ σ hhaS2) (γC ρ (.next hhaK1)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ hhaS3, ch) :=
  symEvalWindowTB_refines hhaW2_out ρ σ ch hag

/-! ## THE SPILL CROSSING (the transport instantiated; every premise
discharged at the literal, the choice entering through `hhaρ'`). -/

theorem hha_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (hhaρ' ρ c₁) σ hhaS1) (γC (hhaρ' ρ c₁) hhaC1) (c₁ :: rest)
      = .ok (γC (hhaρ' ρ c₁) (.next hhaK1), γS (hhaρ' ρ c₁) σ hhaS2, rest) := by
  have hvisE : sliceVisibleValues (γS (hhaρ' ρ c₁) σ hhaS1)
      ⟨some (.base ⟨150⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨100⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (hhaρ' ρ c₁) σ hhaS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (hhaρ' ρ c₁) σ hhaS1) hhaElemTy
      #[] #[.addr (.base ⟨100⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (hhaBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨100⟩)],
        normalizeValueForTy (γS (hhaρ' ρ c₁) σ hhaS1) hhaElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (hhaρ' ρ c₁) σ hhaS1) hhaElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (hhaρ' ρ c₁) σ hhaS1) (elem := hhaElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨100⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [hhaBackingVal, hhaCap] using h
  have htgt : storeLoc { γS (hhaρ' ρ c₁) σ hhaS1 with
        heap := GoCore.Heap.set (γS (hhaρ' ρ c₁) σ hhaS1).heap
          (.base ⟨(γS (hhaρ' ρ c₁) σ hhaS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) hhaElemTy),
           hhaBackingVal c₁⟩,
        nextAddr := (γS (hhaρ' ρ c₁) σ hhaS1).nextAddr + 1 } (.base ⟨151⟩)
      (.slice ⟨some (.base ⟨(γS (hhaρ' ρ c₁) σ hhaS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (hhaρ' ρ c₁) σ hhaS2) := by
    kernel_rfl
  rw [hhaC1_shape]
  exact stepFn_appendSpill_transport (hhaρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 1,681-step span. -/

theorem hha_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 1681 (γS (hhaρ' ρ c₁) σ hhaS0) (γC (hhaρ' ρ c₁) hhaC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (hhaρ' ρ c₁) σ hhaS3, ch) := by
  have h := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => hhaWin1 (hhaρ' ρ c₁) σ chx hag)
    (hha_spill_step ρ σ c₁ ch)
    (fun chx => hhaWin2 (hhaρ' ρ c₁) σ chx hag)
  have hstop : γC (hhaρ' ρ c₁) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  exact h

/-! ## The fixture family's log view (spec-side; the STALE branch
touches nothing — pre = post). -/

def hhaAbsLogPre : AbsLog := ⟨[(1, 1), (2, 1)], [], 3, 1, 1, 1⟩
def hhaAbsLogPost : AbsLog := ⟨[(1, 1), (2, 1)], [], 3, 2, 1, 1⟩

/-- **THE COMMIT ADVANCED**: committed 1 → 2 = m.Commit, the log VIEW
untouched. Axiom-free spec-side fact. -/
theorem hha_committed_advanced :
    hhaAbsLogPost.committed = 2 ∧ hhaAbsLogPre.committed = 1
      ∧ AbsLog.view hhaAbsLogPost = AbsLog.view hhaAbsLogPre
      ∧ hhaAbsLogPost.stable = hhaAbsLogPre.stable := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Projection facts at the literals. -/

theorem hha_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ hhaS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, 2, 0, 0, 0, 2, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem hha_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ hhaS0) ⟨32⟩ = some hhaAbsLogPre := by
  kernel_rfl

theorem hha_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (hhaρ' ρ c₁) σ hhaS3) ⟨32⟩ = some hhaAbsLogPost := by
  kernel_rfl

/-- The msgs field of the post state reads the spilled handle. -/
theorem hha_post_msgs_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (hhaρ' ρ c₁) σ hhaS3) ⟨31⟩ ⟨"raft.raft"⟩ "msgs"
      = some (.slice ⟨some (.base ⟨152⟩), 0, 1, hhaCap c₁⟩) := by
  kernel_rfl

/-- The backing cell of the post state (the cell atom's image). -/
theorem hha_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (hhaρ' ρ c₁) σ hhaS3).heap (.base ⟨152⟩)
      = some ⟨some (.array (hhaCap c₁) hhaElemTy), hhaBackingVal c₁⟩ := by
  kernel_rfl

/-- The response record: the SAME `specHeartbeatResp` as the no-op
family — the two families differ only in the log's committed. -/
theorem hha_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (hhaρ' ρ c₁) σ hhaS3) (.addr (.base ⟨100⟩))
      = some (specHeartbeatResp 1 2 0) := by
  kernel_rfl

/-- The backing's head element (choice-generic: the padding never
enters — `List.getElem?` reduces at the cons head). -/
theorem hhaBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨100⟩)] ++ List.replicate (hhaCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨100⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (no window re-evaluation, no per-choice case split). -/
theorem hha_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (hhaρ' ρ c₁) σ hhaS3) ⟨31⟩ "msgs"
      = some [specHeartbeatResp 1 2 0] := by
  rw [absOutbox]
  rw [hha_post_msgs_field ρ σ c₁]
  show sliceRead (γS (hhaρ' ρ c₁) σ hhaS3)
    (.slice ⟨some (.base ⟨152⟩), 0, 1, hhaCap c₁⟩) _ = _
  rw [sliceRead]
  rw [hha_post_backing ρ σ c₁]
  show sliceElems (γS (hhaρ' ρ c₁) σ hhaS3)
    ⟨[GoValue.addr (.base ⟨100⟩)] ++ List.replicate (hhaCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, hhaBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [hha_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

/-- Untouched-scalar readouts (post): the store-time whole-struct
re-normalization wraps each surviving symbolic scalar ONCE; the range
side conditions collapse it. -/
theorem hha_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhaρ' ρ c₁) σ hhaS3) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem hha_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhaρ' ρ c₁) σ hhaS3) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem hha_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (hhaρ' ρ c₁) σ hhaS3) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic, placement LIVE at
the born-re-sited fixture; the sim plumbing = the LIFTED
`Frame.span_relocate`, slice 0 — its second consumer). -/

/-- **THE handleHeartbeat COMMIT-ADVANCE EQUATION**: from the drained
`handleHeartbeat(&m)` call at ANY placement of the fixture footprint,
over EVERY consumed choice prefix (∀ streams `c₁ :: ch`), the run
returns in exactly **1,681 steps** with one choice consumed, and:
the message argument projects by `absMessage` (Commit = 2); **the
commit index ADVANCES — `absRaftLog` committed 1 → 2 = m.Commit with
the log view untouched** (`hha_committed_advanced`); the outbox
gains EXACTLY the heartbeat response into `msgs` (the sync group;
the SAME record as the no-op family — the families differ only in
the log); `msgsAfterAppend` stays empty; and the untouched scalars
read back unchanged. -/
theorem handleHeartbeat_advance_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ hhaS0) σF) :
    ∃ σFfin,
      stepFnIter 1681 σF (renameConfig r (γC ρ hhaC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (hhaρ' ρ c₁) σ hhaS3) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, 2, 0, 0, 0, 2, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhaAbsLogPre
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhaAbsLogPost
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ hhaS0 = γS (hhaρ' ρ c₁) σ hhaS0 := by kernel_rfl
  have hpreC : γC ρ hhaC0 = γC (hhaρ' ρ c₁) hhaC0 := by kernel_rfl
  have hrun : stepFnIter 1681 (γS ρ σ hhaS0) (γC ρ hhaC0) (c₁ :: ch)
      = .ok (.next .stop, γS (hhaρ' ρ c₁) σ hhaS3, ch) := by
    rw [hpre, hpreC]
    exact hha_full_span ρ σ hag c₁ ch
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hha_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (hha_pre_absRaftLog ρ σ)
  · have h := hha_post_absOutbox ρ σ c₁
    exact absOutbox_ren hs h
  · exact absOutbox_ren hs (show absOutbox (γS (hhaρ' ρ c₁) σ hhaS3) ⟨31⟩
      "msgsAfterAppend" = some [] by kernel_rfl)
  · exact absRaftLog_ren hs (hha_post_absRaftLog ρ σ c₁)
  · have h := hha_post_vote ρ σ c₁
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := hha_post_lead ρ σ c₁
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (hha_post_term ρ σ c₁)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture). -/
theorem handleHeartbeat_advance_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 1681 (γS ρ σ hhaS0) (γC ρ hhaC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ hhaS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 0, 0, 2, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ hhaS0) ⟨32⟩ = some hhaAbsLogPre
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhaAbsLogPost
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 60 0) 60 60 [] (γS ρ σ hhaS0) (γS ρ σ hhaS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 60 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩ :=
    handleHeartbeat_advance_eq_alloc ρ σ hag hvote hlead c₁ ch hF
  have hcall : renameConfig (ρT 60 0) (γC ρ hhaC0) = γC ρ hhaC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT 60 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT 60 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 60 0 32⟩ : Addr) = ⟨32⟩ := rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h31] at hob hobm hv hl ht
  exact ⟨σfin, hrun, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩

/-! ## §3.3 discharge witness (the probe's values: Vote 7, lead 2,
state 0, leadTransferee 5; stream head 3 — realized capacity 7). -/

def hhaρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleHeartbeat_advance_eq_witness :
    ∃ σfin,
      stepFnIter 1681 (γS hhaρw wBase hhaS0) (γC hhaρw hhaC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS hhaρw wBase hhaS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 0, 0, 2, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS hhaρw wBase hhaS0) ⟨32⟩ = some hhaAbsLogPre
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhaAbsLogPost
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleHeartbeat_advance_eq hhaρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 []

end GoLean.RaftSeam
