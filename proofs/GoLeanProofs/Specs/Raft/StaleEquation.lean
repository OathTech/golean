import GoLeanProofs.Specs.Raft.StaleLit
import GoLeanProofs.Specs.Raft.HaeEquation

/-!
# A4-U12: THE handleAppendEntries STALE-FAMILY EQUATION (the third
message-handler equation family; pure assembly on the A4-U10 spill
transport, per the U11 census — zero new machinery)

**LINEAGE: as `HaeEquation.lean` verbatim** — the chain differs only
in the fixture (the TWO-ENTRY log: storage ents (index 1, term 1),
(index 2, term 1); `committed = 2 = lastIndex`; unstable offset 3 —
the U11 fixture-value note taken: the stale and success families'
records now differ OBSERVABLY, resp Index = committed = 2 vs the
landed success record's Index = 1), the window schedule [1307, 28],
the crossing cells (temp 135, elems 134 → response message 93,
backing born at 136), and the branch: `prev.index = 1 < committed =
2` takes the STALE early return (raft.go:1815-1818) — the log is
UNTOUCHED (`maybeAppend` never runs), and the response goes to
`msgsAfterAppend` with `Index = r.raftLog.committed`.
Probe-validated end-to-end by `artifacts/probe/{StaleProbe3,
StaleGen}.lean` before any theorem here (γ==machine at c=0/3/31; one
choice at step 1307; mirror clean to the spill quit — the U11
census's "zero new machinery" prediction, confirmed at the two-entry
fixture: 1,336 steps both).

The message cells are the Hae SUCCESS fixture's VERBATIM (From 2,
LogTerm 1, Index 1, Commit 1): the two families differ ONLY in the
pre-state log — the equation pair exhibits the handler branching on
STATE, not on the message.

FIXTURE-FAMILY preconditions (recorded): `m.Index = 1 < committed =
2` (stale), `m.From = 2 ≠ r.id` concrete (the U10
self-addressed-guard finding), `r.Term = 0`; the log is a CONSISTENT
raft state (committed = lastIndex = 2, applied = applying = 2,
unstable empty at offset 3).

This module consumes the LIFTED `GoLean.Frame.span_relocate`
(slice 0) — its second consumer, as the promotion row predicted.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/StaleGen.lean` — the
window links below re-check the literals against these defs). -/

def staleIfaceHarnessG : GoValue :=
  .interface (.pointer (.defined ⟨"main.harnessLogger"⟩)) (.addr (.base ⟨36⟩))

/-- The two-entry raftLog cell value (at 32; committed = lastIndex = 2),
concrete — the sym fixture embeds it (`embedGo`, matching the
generator's construction exactly). -/
def staleLogValG : GoValue :=
  .struct ⟨"raft.raftLog"⟩ #[
    ("storage", .interface (.pointer (.defined ⟨"raft.MemoryStorage"⟩)) (.addr (.base ⟨37⟩))),
    ("unstable", .struct ⟨"raft.unstable"⟩ #[
      ("snapshot", .nil), ("entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
      ("offset", .int 3 .uint64),
      ("snapshotInProgress", .bool false), ("offsetInProgress", .int 3 .uint64),
      ("logger", staleIfaceHarnessG)]),
    ("committed", .int 2 .uint64), ("applying", .int 2 .uint64),
    ("applied", .int 2 .uint64),
    ("logger", staleIfaceHarnessG), ("maxApplyingEntsSize", .int 1048576 .uint64),
    ("applyingEntsSize", .int 0 .uint64), ("applyingEntsPaused", .bool false)]

/-- MemoryStorage with the 2-entry ents slice (at 37). -/
def staleMsValG : GoValue :=
  .struct ⟨"raft.MemoryStorage"⟩ #[
    ("Mutex", .syncData (.mutex false)), ("hardState", .nil), ("snapshot", .nil),
    ("ents", .slice { base := some (.base ⟨46⟩), offset := 0, len := 2, cap := 2 }),
    ("callStats", .struct ⟨"raft.inMemStorageCallStats"⟩ #[
      ("initialState", .int 0 .int), ("firstIndex", .int 0 .int),
      ("lastIndex", .int 0 .int),
      ("entries", .int 0 .int), ("term", .int 0 .int),
      ("snapshot", .int 0 .int)])]

def staleMsgValG : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)), ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def staleEntry2G : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨58⟩)), ("Index", .addr (.base ⟨59⟩)),
    ("Type", .nil), ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def staleSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨32⟩ then
      (p.1, .mk (some (.defined ⟨"raft.raftLog"⟩)) (embedGo staleLogValG))
    else if p.1 == .base ⟨37⟩ then
      (p.1, .mk (some (.defined ⟨"raft.MemoryStorage"⟩)) (embedGo staleMsValG))
    else if p.1 == .base ⟨46⟩ then
      (p.1, .mk (some (.array 2 (.pointer (.defined ⟨"raftpb.Entry"⟩))))
        (embedGo (.array #[.addr (.base ⟨47⟩), .addr (.base ⟨57⟩)])))
    else p)) ++
  [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) (embedGo staleMsgValG)),
   (.base ⟨53⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨54⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64))),
   (.base ⟨55⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨56⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨57⟩, .mk (some (.defined ⟨"raftpb.Entry"⟩)) (embedGo staleEntry2G)),
   (.base ⟨58⟩, .mk (some (.int .uint64)) (embedGo (.int 1 .uint64))),
   (.base ⟨59⟩, .mk (some (.int .uint64)) (embedGo (.int 2 .uint64)))]

def staleS0 : SymState := { heap := staleSymHeap, nextAddr := 60 }

/-- The drained call configuration of `handleAppendEntries(&m)`. -/
def staleC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def staleElemTy : Ty := .pointer (.defined ⟨"raftpb.Message"⟩)

/-- The realized backing capacity at stream head `c` (nil old slice,
one appended element: width 32, envelope [1, 32]). -/
def staleCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- The backing-cell payload at stream head `c`: the response-message
pointer (cell 93), then default-`nil` padding to the realized
capacity. -/
def staleBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨93⟩)] ++ List.replicate (staleCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atom 0 (value) = the spilled
handle; atom 0 (cell) = the backing cell. Everything else rides. -/
def staleρ' (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨136⟩), 0, 1, staleCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (staleCap c) staleElemTy), staleBackingVal c⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms). -/

theorem staleW1_out : symEvalWindowTB bfTB 1307 staleS0 staleC0
    = (1307, staleS1, staleC1) := by
  kernel_rfl

/-- The post-spill continuation, extracted from the quit config. -/
def staleK1 : GoLean.Sym.Cont symDom := match staleC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def staleE1 : LocalEnv := match staleC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem staleC1_shape : staleC1 = .retV (.slice ⟨some (.base ⟨134⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice staleElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨135⟩)] [] staleE1 staleK1) := by
  kernel_rfl

theorem staleW2_out : symEvalWindowTB bfTB 28 staleS2 (.next staleK1)
    = (28, staleS3, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem staleWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 1307 (γS ρ σ staleS0) (γC ρ staleC0) ch
      = .ok (γC ρ staleC1, γS ρ σ staleS1, ch) :=
  symEvalWindowTB_refines staleW1_out ρ σ ch hag

theorem staleWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ staleS2) (γC ρ (.next staleK1)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ staleS3, ch) :=
  symEvalWindowTB_refines staleW2_out ρ σ ch hag

/-! ## THE SPILL CROSSING (the transport instantiated; every premise
discharged at the literal, the choice entering through `staleρ'`). -/

theorem stale_spill_step (ρ : Valuation) (σ : ExecState) (c₁ : Nat)
    (rest : Choices) :
    stepFn (γS (staleρ' ρ c₁) σ staleS1) (γC (staleρ' ρ c₁) staleC1) (c₁ :: rest)
      = .ok (γC (staleρ' ρ c₁) (.next staleK1), γS (staleρ' ρ c₁) σ staleS2, rest) := by
  have hvisE : sliceVisibleValues (γS (staleρ' ρ c₁) σ staleS1)
      ⟨some (.base ⟨134⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨93⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (staleρ' ρ c₁) σ staleS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (staleρ' ρ c₁) σ staleS1) staleElemTy
      #[] #[.addr (.base ⟨93⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (staleBackingVal c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨93⟩)],
        normalizeValueForTy (γS (staleρ' ρ c₁) σ staleS1) staleElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (staleρ' ρ c₁) σ staleS1) staleElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (staleρ' ρ c₁) σ staleS1) (elem := staleElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨93⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [staleBackingVal, staleCap] using h
  have htgt : storeLoc { γS (staleρ' ρ c₁) σ staleS1 with
        heap := GoCore.Heap.set (γS (staleρ' ρ c₁) σ staleS1).heap
          (.base ⟨(γS (staleρ' ρ c₁) σ staleS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) staleElemTy),
           staleBackingVal c₁⟩,
        nextAddr := (γS (staleρ' ρ c₁) σ staleS1).nextAddr + 1 } (.base ⟨135⟩)
      (.slice ⟨some (.base ⟨(γS (staleρ' ρ c₁) σ staleS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (staleρ' ρ c₁) σ staleS2) := by
    kernel_rfl
  rw [staleC1_shape]
  exact stepFn_appendSpill_transport (staleρ' ρ c₁) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 1,336-step span. -/

theorem stale_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ : Nat) (ch : Choices) :
    stepFnIter 1336 (γS (staleρ' ρ c₁) σ staleS0) (γC (staleρ' ρ c₁) staleC0)
      (c₁ :: ch)
      = .ok (.next .stop, γS (staleρ' ρ c₁) σ staleS3, ch) := by
  have h := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => staleWin1 (staleρ' ρ c₁) σ chx hag)
    (stale_spill_step ρ σ c₁ ch)
    (fun chx => staleWin2 (staleρ' ρ c₁) σ chx hag)
  have hstop : γC (staleρ' ρ c₁) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  exact h

/-! ## The fixture family's log view (spec-side; the STALE branch
touches nothing — pre = post). -/

def staleAbsLog : AbsLog := ⟨[(1, 1), (2, 1)], [], 3, 2, 2, 2⟩

/-! ## Projection facts at the literals. -/

theorem stale_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ staleS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem stale_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ staleS0) ⟨32⟩ = some staleAbsLog := by
  kernel_rfl

theorem stale_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absRaftLog (γS (staleρ' ρ c₁) σ staleS3) ⟨32⟩ = some staleAbsLog := by
  kernel_rfl

/-- The msgsAfterAppend field of the post state reads the spilled
handle. -/
theorem stale_post_maa_field (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldRead (γS (staleρ' ρ c₁) σ staleS3) ⟨31⟩ ⟨"raft.raft"⟩ "msgsAfterAppend"
      = some (.slice ⟨some (.base ⟨136⟩), 0, 1, staleCap c₁⟩) := by
  kernel_rfl

/-- The backing cell of the post state (the cell atom's image). -/
theorem stale_post_backing (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    GoCore.Heap.lookup (γS (staleρ' ρ c₁) σ staleS3).heap (.base ⟨136⟩)
      = some ⟨some (.array (staleCap c₁) staleElemTy), staleBackingVal c₁⟩ := by
  kernel_rfl

/-- The response message cell projects to the spec record: **Index =
committed = 2** — the stale family's record, observably distinct from
the success family's `specAppResp 1 2 0 1`. -/
theorem stale_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absMessage (γS (staleρ' ρ c₁) σ staleS3) (.addr (.base ⟨93⟩))
      = some (specAppResp 1 2 0 2) := by
  kernel_rfl

/-- The backing's head element (choice-generic: the padding never
enters — `List.getElem?` reduces at the cons head). -/
theorem staleBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨93⟩)] ++ List.replicate (staleCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨93⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (no window re-evaluation, no per-choice case split). -/
theorem stale_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    absOutbox (γS (staleρ' ρ c₁) σ staleS3) ⟨31⟩ "msgsAfterAppend"
      = some [specAppResp 1 2 0 2] := by
  rw [absOutbox]
  rw [stale_post_maa_field ρ σ c₁]
  show sliceRead (γS (staleρ' ρ c₁) σ staleS3)
    (.slice ⟨some (.base ⟨136⟩), 0, 1, staleCap c₁⟩) _ = _
  rw [sliceRead]
  rw [stale_post_backing ρ σ c₁]
  show sliceElems (γS (staleρ' ρ c₁) σ staleS3)
    ⟨[GoValue.addr (.base ⟨93⟩)] ++ List.replicate (staleCap c₁ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, staleBackingVal_head c₁]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [stale_post_respMsg ρ σ c₁]
  simp only [hbind]
  rfl

/-- Untouched-scalar readouts (post): the store-time whole-struct
re-normalization wraps each surviving symbolic scalar ONCE; the range
side conditions collapse it. -/
theorem stale_post_vote (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (staleρ' ρ c₁) σ staleS3) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem stale_post_lead (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (staleρ' ρ c₁) σ staleS3) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem stale_post_term (ρ : Valuation) (σ : ExecState) (c₁ : Nat) :
    fieldReadU64 (γS (staleρ' ρ c₁) σ staleS3) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic, placement LIVE at
the born-re-sited fixture; the sim plumbing = the LIFTED
`Frame.span_relocate`, slice 0 — its second consumer). -/

/-- **THE handleAppendEntries STALE-FAMILY EQUATION**: from the
drained `handleAppendEntries(&m)` call at ANY placement of the
fixture footprint (relocation `r` + disjoint frame `fr`, one
`FrameSim` premise), over EVERY consumed choice prefix (∀ streams
`c₁ :: ch` — the appendSpill capacity choice), the run returns in
exactly **1,336 steps** with one choice consumed, and: the message
argument projects by `absMessage` (the Hae success fixture's record
VERBATIM — the families differ only in the log); the log view is
PRESERVED (`absRaftLog` before = after = `staleAbsLog`, committed =
lastIndex = 2 — the stale branch touches nothing); the outbox gains
EXACTLY the stale response (`absOutbox "msgsAfterAppend"` =
`[specAppResp 1 2 0 2]` — **Index = committed**, observably distinct
from the success family's Index = mlastIndex = 1); `absOutbox "msgs"`
stays empty (the async-group routing); and the untouched scalars read
back unchanged. Side conditions `hvote`/`hlead`: the surviving
symbolic scalars' uint64-range facts (the U3 norm-wrap story). -/
theorem handleAppendEntries_stale_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ staleS0) σF) :
    ∃ σFfin,
      stepFnIter 1336 σF (renameConfig r (γC ρ staleC0)) (c₁ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (staleρ' ρ c₁) σ staleS3) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some staleAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 2]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some staleAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ staleS0 = γS (staleρ' ρ c₁) σ staleS0 := by kernel_rfl
  have hpreC : γC ρ staleC0 = γC (staleρ' ρ c₁) staleC0 := by kernel_rfl
  have hrun : stepFnIter 1336 (γS ρ σ staleS0) (γC ρ staleC0) (c₁ :: ch)
      = .ok (.next .stop, γS (staleρ' ρ c₁) σ staleS3, ch) := by
    rw [hpre, hpreC]
    exact stale_full_span ρ σ hag c₁ ch
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := stale_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (stale_pre_absRaftLog ρ σ)
  · have h := stale_post_absOutbox ρ σ c₁
    exact absOutbox_ren hs h
  · exact absOutbox_ren hs (show absOutbox (γS (staleρ' ρ c₁) σ staleS3) ⟨31⟩
      "msgs" = some [] by kernel_rfl)
  · exact absRaftLog_ren hs (stale_post_absRaftLog ρ σ c₁)
  · have h := stale_post_vote ρ σ c₁
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := stale_post_lead ρ σ c₁
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (stale_post_term ρ σ c₁)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture). -/
theorem handleAppendEntries_stale_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 1336 (γS ρ σ staleS0) (γC ρ staleC0) (c₁ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ staleS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ staleS0) ⟨32⟩ = some staleAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 2]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some staleAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 60 0) 60 60 [] (γS ρ σ staleS0) (γS ρ σ staleS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 60 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩ :=
    handleAppendEntries_stale_eq_alloc ρ σ hag hvote hlead c₁ ch hF
  have hcall : renameConfig (ρT 60 0) (γC ρ staleC0) = γC ρ staleC0 := by
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

def staleρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleAppendEntries_stale_eq_witness :
    ∃ σfin,
      stepFnIter 1336 (γS staleρw wBase staleS0) (γC staleρw staleC0) (3 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS staleρw wBase staleS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS staleρw wBase staleS0) ⟨32⟩ = some staleAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 2]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some staleAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleAppendEntries_stale_eq staleρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 []

end GoLean.RaftSeam
