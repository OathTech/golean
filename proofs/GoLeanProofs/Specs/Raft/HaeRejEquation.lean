import GoLeanProofs.Specs.Raft.HaeRejLit
import GoLeanProofs.Specs.Raft.HaeEquation

/-!
# A4-U14: THE handleAppendEntries REJECT-FAMILY EQUATION — the last
censused branch: handleAppendEntries is the FIRST FULLY-COMPLETE
message handler (success/empty U11, stale U12, log-append U12,
REJECT here)

**LINEAGE: as `StaleEquation.lean` verbatim** (two windows + the
A4-U10 spill transport — zero new machinery; the U14 census's mirror
walk ran the whole reject path CLEAN on landed TableExt classes). The
chain differs in the fixture — the two-entry TERM-DIVERGENT log:
storage ents (index 1, term 1), (index 2, **term 2**), committed = 1
(< prev.index = 2, so NOT stale), unstable empty at offset 3 — and
the message (LogTerm = 1, **Index = 2**): `matchTerm{term 1, index
2}` FAILS (`term(2) = 2 ≠ 1`), so `maybeAppend` returns false and the
REJECT branch runs (raft.go:1824-1853): the Debugf argument chain
(`zeroTermOnOutOfBounds ∘ term` — the err = nil early arm; the
harness logger body is empty), `hintIndex = min(m.Index 2, lastIndex
2) = 2`, and **`findConflictByTerm(2, 1)` with TWO live iterations**
(term(2) = 2 > 1 → decrement; term(1) = 1 ≤ 1 → return (1, 1)) —
both loop arms exercised. The response routes MsgAppResp to
`msgsAfterAppend`: **the first Reject = true record** ⟨Type 4, To =
m.From, Index = m.Index = 2, Reject = true, RejectHint = 1, LogTerm =
hintTerm = 1⟩.

Probe-validated end-to-end BEFORE any theorem here
(`artifacts/probe/{HaeRejProbe,HaeRejGen}.lean`): machine **6,951
steps / ONE choice at 6925 / ZERO static [20,31) reads** (every
`term()` on this path returns err = nil before any sentinel compare —
no static-cell complement needed); mirror windows [6925, 25] — the
LARGEST single window yet, checked against the anti-grinding smell:
the link replays once in the kernel at the landed ~linear cost class,
far below the stop threshold, so no loop-boundary split is needed;
γ==machine at c = 0/3/31. The window step counts and crossing
addresses (`haeRejW1n`/`haeRejW2n`/`haeRejMsgPtr`/`haeRejTgt`/
`haeRejBacking`) are GENERATOR-EMITTED defs consumed here — the U13
printer improvement: the U11 numeric-mismatch class is
unrepresentable at template time.

FIXTURE-FAMILY preconditions (recorded): `m.Index = 2 ≥ committed =
1` (not stale) with `term(m.Index) ≠ m.LogTerm` (reject); `m.From =
2 ≠ r.id` concrete (the U10 self-addressed-guard finding); `r.Term =
0`; the log is a CONSISTENT raft state (committed 1 ≤ lastIndex 2,
entry terms nondecreasing).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/HaeRejGen.lean` — the
window links below re-check the literals against these defs). -/

def haeRejIfaceHarnessG : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))

/-- The two-entry raftLog cell value (at 32; committed = 1 <
lastIndex = 2 — prev.index 2 is NOT stale here). -/
def haeRejLogValG : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
      ("offset", .int 3 .uint64),
      ("snapshotInProgress", .bool false), ("offsetInProgress", .int 3 .uint64),
      ("logger", haeRejIfaceHarnessG)]),
    ("committed", .int 1 .uint64), ("applying", .int 1 .uint64),
    ("applied", .int 1 .uint64),
    ("logger", haeRejIfaceHarnessG), ("maxApplyingEntsSize", .int 1048576 .uint64),
    ("applyingEntsSize", .int 0 .uint64), ("applyingEntsPaused", .bool false)]

/-- MemoryStorage with the 2-entry ents slice (at 37). -/
def haeRejMsValG : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨46⟩), offset := 0, len := 2, cap := 2 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", .int 0 .int), ("firstIndex", .int 0 .int),
      ("lastIndex", .int 0 .int),
      ("entries", .int 0 .int), ("term", .int 0 .int),
      ("snapshot", .int 0 .int)])]

/-- The message: LogTerm→55 = 1, **Index→56 = 2** (vs the
success/stale families' Index = 1). -/
def haeRejMsgValG : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)), ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- Entry 2 with **TERM 2** (the divergent tip; 58 = Term, 59 = Index). -/
def haeRejEntry2G : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨58⟩)), ("Index", .addr (.base ⟨59⟩)),
    ("Type", .nil), ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def haeRejSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨32⟩ then
      (p.1, .mk (some (.defined ⟨"raft.raftLog"⟩)) (embedGo haeRejLogValG))
    else if p.1 == .base ⟨37⟩ then
      (p.1, .mk (some (.defined ⟨"raft.MemoryStorage"⟩)) (embedGo haeRejMsValG))
    else if p.1 == .base ⟨46⟩ then
      (p.1, .mk (some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))))
        (embedGo (.array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)])))
    else p)) ++
  [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) (embedGo haeRejMsgValG)),
   (.base ⟨53⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨54⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64))),
   (.base ⟨55⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨56⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64))),
   (.base ⟨57⟩, .mk (some (.defined ⟨"raftpb.Entry"⟩)) (embedGo haeRejEntry2G)),
   (.base ⟨58⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64))),
   (.base ⟨59⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64)))]

def haeRejS0 : SymState := { heap := haeRejSymHeap, nextAddr := 60 }

/-- The drained call configuration of `handleAppendEntries(&m)`. -/
def haeRejC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def haeRejElemTy : Ty := .pointer (.defined ⟨"raftpb.Message"⟩)

/-- The realized backing capacity at stream head `c` (nil old slice,
one appended element: width 32, envelope [1, 32]). -/
def haeRejCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- The backing-cell payload at stream head `c`: the response-message
pointer (the generator-emitted `haeRejMsgPtr`), then default-`nil`
padding to the realized capacity. -/
def haeRejBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨haeRejMsgPtr⟩)] ++ List.replicate (haeRejCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atom 0 (value) = the spilled
handle; atom 0 (cell) = the backing cell. Everything else rides. -/
def haeRejρ' (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨haeRejBacking⟩), 0, 1, haeRejCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (haeRejCap c) haeRejElemTy), haeRejBackingVal c⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms; the step counts
are the GENERATOR-EMITTED `haeRejW1n`/`haeRejW2n`). -/

theorem haeRejW1_out : symEvalWindowTB bfTB haeRejW1n haeRejS0 haeRejC0
    = (haeRejW1n, haeRejS1, haeRejC1) := by
  kernel_rfl

/-- The post-spill continuation, extracted from the quit config. -/
def haeRejK1 : GoLean.Sym.Cont symDom := match haeRejC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def haeRejE1 : LocalEnv := match haeRejC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem haeRejC1_shape : haeRejC1 = .retV (.slice ⟨some (.base ⟨488⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice haeRejElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨haeRejTgt⟩)] [] haeRejE1 haeRejK1) := by
  kernel_rfl

theorem haeRejW2_out : symEvalWindowTB bfTB haeRejW2n haeRejS2 (.next haeRejK1)
    = (haeRejW2n, haeRejS3, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem haeRejWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter haeRejW1n (γS ρ σ haeRejS0) (γC ρ haeRejC0) ch
      = .ok (γC ρ haeRejC1, γS ρ σ haeRejS1, ch) :=
  symEvalWindowTB_refines haeRejW1_out ρ σ ch hag

theorem haeRejWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter haeRejW2n (γS ρ σ haeRejS2) (γC ρ (.next haeRejK1)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ haeRejS3, ch) :=
  symEvalWindowTB_refines haeRejW2_out ρ σ ch hag

/-! ## THE SPILL CROSSING (the transport instantiated; every premise
discharged at the literal, the choice entering through `haeRejρ'`). -/

theorem haeRej_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (haeRejρ' ρ c₁) σ haeRejS1) (γC (haeRejρ' ρ c₁) haeRejC1) (c₁ :: rest)
      = .ok (γC (haeRejρ' ρ c₁) (.next haeRejK1), γS (haeRejρ' ρ c₁) σ haeRejS2, rest) := by
  have hvisE : sliceVisibleValues (γS (haeRejρ' ρ c₁) σ haeRejS1)
      ⟨some (.base ⟨488⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨haeRejMsgPtr⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (haeRejρ' ρ c₁) σ haeRejS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (haeRejρ' ρ c₁) σ haeRejS1) haeRejElemTy
      #[] #[.addr (.base ⟨haeRejMsgPtr⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (haeRejBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨haeRejMsgPtr⟩)],
        normalizeValueForTy (γS (haeRejρ' ρ c₁) σ haeRejS1) haeRejElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (haeRejρ' ρ c₁) σ haeRejS1) haeRejElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (haeRejρ' ρ c₁) σ haeRejS1) (elem := haeRejElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨haeRejMsgPtr⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [haeRejBackingVal, haeRejCap] using h
  have htgt : storeLoc { γS (haeRejρ' ρ c₁) σ haeRejS1 with
        heap := GoCore.Heap.set (γS (haeRejρ' ρ c₁) σ haeRejS1).heap
          (.base ⟨(γS (haeRejρ' ρ c₁) σ haeRejS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) haeRejElemTy),
           haeRejBackingVal c₁⟩,
        nextAddr := (γS (haeRejρ' ρ c₁) σ haeRejS1).nextAddr + 1 } (.base ⟨haeRejTgt⟩)
      (.slice ⟨some (.base ⟨(γS (haeRejρ' ρ c₁) σ haeRejS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (haeRejρ' ρ c₁) σ haeRejS2) := by
    kernel_rfl
  rw [haeRejC1_shape]
  exact stepFn_appendSpill_transport (haeRejρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 6,951-step span. -/

theorem haeRej_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 6951 (γS (haeRejρ' ρ c₁) σ haeRejS0) (γC (haeRejρ' ρ c₁) haeRejC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (haeRejρ' ρ c₁) σ haeRejS3, ch) := by
  have h := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => haeRejWin1 (haeRejρ' ρ c₁) σ chx hag)
    (haeRej_spill_step ρ σ c₁ ch)
    (fun chx => haeRejWin2 (haeRejρ' ρ c₁) σ chx hag)
  have hstop : γC (haeRejρ' ρ c₁) (.next .stop) = .next .stop := rfl
  have hn : haeRejW1n + 1 + haeRejW2n = 6951 := rfl
  rw [← hstop, ← hn]
  exact h

/-! ## Spec-side vocabulary (re-grounded; compat/verdi never imported). -/

/-- `specAppRejResp src dst term index hintIndex hintTerm` — the
REJECT response record (raft.go:1845-1853): `To = m.From`, `Type =
MsgAppResp (4)`, `Index = m.Index`, **`Reject = true`**, `RejectHint =
hintIndex`, `LogTerm = hintTerm` (the findConflictByTerm guess);
`send` fills `From := r.id` and `Term := r.Term` (log.go:182-194:
the returned pair is the max guessIndex ≤ index with term(guessIndex)
≤ term, and its term). Verdi correspondence: the reject reply of
verdi-raft's AppendEntries — the follower's log does not match at
prev, no state change, one reply enters the net. -/
def specAppRejResp (src dst term index hintIndex hintTerm : Int) : AbsMessage :=
  ⟨4, dst, src, term, hintTerm, index, 0, 0, hintIndex, true, [], []⟩

/-- The fixture family's log view (the REJECT branch touches
NOTHING — `maybeAppend` fails before any write; pre = post). -/
def haeRejAbsLog : AbsLog := ⟨[(1, 1), (2, 2)], [], 3, 1, 1, 1⟩

/-! ## Projection facts at the literals. -/

theorem haeRej_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ haeRejS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, 2, 0, 1, 2, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem haeRej_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ haeRejS0) ⟨32⟩ = some haeRejAbsLog := by
  kernel_rfl

theorem haeRej_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨32⟩ = some haeRejAbsLog := by
  kernel_rfl

/-- The msgsAfterAppend field of the post state reads the spilled
handle. -/
theorem haeRej_post_maa_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨31⟩ ⟨"raft.raft"⟩ "msgsAfterAppend"
      = some (.slice ⟨some (.base ⟨haeRejBacking⟩), 0, 1, haeRejCap c₁⟩) := by
  kernel_rfl

/-- The backing cell of the post state (the cell atom's image). -/
theorem haeRej_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (haeRejρ' ρ c₁) σ haeRejS3).heap (.base ⟨haeRejBacking⟩)
      = some ⟨some (.array (haeRejCap c₁) haeRejElemTy), haeRejBackingVal c₁⟩ := by
  kernel_rfl

/-- The response message cell projects to the spec record: **the
first Reject = true record** — Index = m.Index = 2, RejectHint = 1,
LogTerm = 1 — observably distinct from every landed family's record
(none carries Reject). -/
theorem haeRej_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (haeRejρ' ρ c₁) σ haeRejS3) (.addr (.base ⟨haeRejMsgPtr⟩))
      = some (specAppRejResp 1 2 0 2 1 1) := by
  kernel_rfl

/-- The backing's head element (choice-generic: the padding never
enters — `List.getElem?` reduces at the cons head). -/
theorem haeRejBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨haeRejMsgPtr⟩)] ++ List.replicate (haeRejCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨haeRejMsgPtr⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (no window re-evaluation, no per-choice case split). -/
theorem haeRej_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨31⟩ "msgsAfterAppend"
      = some [specAppRejResp 1 2 0 2 1 1] := by
  rw [absOutbox]
  rw [haeRej_post_maa_field ρ σ c₁]
  show sliceRead (γS (haeRejρ' ρ c₁) σ haeRejS3)
    (.slice ⟨some (.base ⟨haeRejBacking⟩), 0, 1, haeRejCap c₁⟩) _ = _
  rw [sliceRead]
  rw [haeRej_post_backing ρ σ c₁]
  show sliceElems (γS (haeRejρ' ρ c₁) σ haeRejS3)
    ⟨[GoValue.addr (.base ⟨haeRejMsgPtr⟩)] ++ List.replicate (haeRejCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, haeRejBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [haeRej_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

/-- Untouched-scalar readouts (post): the store-time whole-struct
re-normalization wraps each surviving symbolic scalar ONCE (the
msgsAfterAppend write-back); the range side conditions collapse it. -/
theorem haeRej_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem haeRej_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem haeRej_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic, placement LIVE at
the born-re-sited fixture; sim plumbing = the lifted
`Frame.span_relocate`). -/

/-- **THE handleAppendEntries REJECT-FAMILY EQUATION**: from the
drained `handleAppendEntries(&m)` call at ANY placement of the
fixture footprint (relocation `r` + disjoint frame `fr`, one
`FrameSim` premise), over EVERY consumed choice prefix (∀ streams
`c₁ :: ch` — the appendSpill capacity choice), the run returns in
exactly **6,951 steps** with one choice consumed, and: the message
argument projects by `absMessage` (LogTerm 1, Index 2 — the
term-divergent probe); the log view is PRESERVED (`absRaftLog` before
= after = `haeRejAbsLog` — the reject branch writes nothing); the
outbox gains EXACTLY the reject response (`absOutbox
"msgsAfterAppend"` = `[specAppRejResp 1 2 0 2 1 1]` — **Reject =
true, RejectHint/LogTerm = findConflictByTerm's (1, 1)**); `absOutbox
"msgs"` stays empty (the async-group routing); and the untouched
scalars read back unchanged. Side conditions `hvote`/`hlead`: the
surviving symbolic scalars' uint64-range facts. -/
theorem handleAppendEntries_reject_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ haeRejS0) σF) :
    ∃ σFfin,
      stepFnIter 6951 σF (renameConfig r (γC ρ haeRejC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (haeRejρ' ρ c₁) σ haeRejS3) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, 2, 0, 1, 2, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some haeRejAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend"
          = some [specAppRejResp 1 2 0 2 1 1]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some haeRejAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ haeRejS0 = γS (haeRejρ' ρ c₁) σ haeRejS0 := by kernel_rfl
  have hpreC : γC ρ haeRejC0 = γC (haeRejρ' ρ c₁) haeRejC0 := by kernel_rfl
  have hrun : stepFnIter 6951 (γS ρ σ haeRejS0) (γC ρ haeRejC0) (c₁ :: ch)
      = .ok (.next .stop, γS (haeRejρ' ρ c₁) σ haeRejS3, ch) := by
    rw [hpre, hpreC]
    exact haeRej_full_span ρ σ hag c₁ ch
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := haeRej_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (haeRej_pre_absRaftLog ρ σ)
  · have h := haeRej_post_absOutbox ρ σ c₁
    exact absOutbox_ren hs h
  · exact absOutbox_ren hs (show absOutbox (γS (haeRejρ' ρ c₁) σ haeRejS3) ⟨31⟩
      "msgs" = some [] by kernel_rfl)
  · exact absRaftLog_ren hs (haeRej_post_absRaftLog ρ σ c₁)
  · have h := haeRej_post_vote ρ σ c₁
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := haeRej_post_lead ρ σ c₁
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (haeRej_post_term ρ σ c₁)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture). -/
theorem handleAppendEntries_reject_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 6951 (γS ρ σ haeRejS0) (γC ρ haeRejC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ haeRejS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 2, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ haeRejS0) ⟨32⟩ = some haeRejAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend"
          = some [specAppRejResp 1 2 0 2 1 1]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some haeRejAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 60 0) 60 60 [] (γS ρ σ haeRejS0) (γS ρ σ haeRejS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 60 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩ :=
    handleAppendEntries_reject_eq_alloc ρ σ hag hvote hlead c₁ ch hF
  have hcall : renameConfig (ρT 60 0) (γC ρ haeRejC0) = γC ρ haeRejC0 := by
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

def haeRejρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleAppendEntries_reject_eq_witness :
    ∃ σfin,
      stepFnIter 6951 (γS haeRejρw wBase haeRejS0) (γC haeRejρw haeRejC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS haeRejρw wBase haeRejS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 2, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS haeRejρw wBase haeRejS0) ⟨32⟩ = some haeRejAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend"
          = some [specAppRejResp 1 2 0 2 1 1]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some haeRejAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleAppendEntries_reject_eq haeRejρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 []

end GoLean.RaftSeam
