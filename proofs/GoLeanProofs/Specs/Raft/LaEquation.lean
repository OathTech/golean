import GoLeanProofs.Specs.Raft.LaLit
import GoLeanProofs.Specs.Raft.HaeEquation

/-!
# A4-U12: THE handleAppendEntries LOG-APPEND EQUATION — the first
equation through the REAL log-write path (non-empty entries), the
first TWO-choice message-handler equation, and GAP-V1-1b's unstable
overlay exercised for the first time

**LINEAGE: the `HhEquation`/`HaeEquation` chain shape, iterated** —
THREE windows / TWO spill crossings / ONE strict-op crossing:

- W1 (3,573 steps): the full success path through `maybeAppend` —
  `logSliceFromMsgApp`, the term-match walk (Storage dispatch +
  mutex + callStats), `findConflict`'s entry walk INCLUDING the
  `term(2) > lastIndex` ERROR branch reading the static
  `ErrUnavailable` cell 25 and `zeroTermOnOutOfBounds`'s comparisons
  against cells 23/25 — live ONLY because the fixture carries THE
  STATIC-CELL COMPLEMENT (`StaticCells.lean`; the U11 stuck, cleared)
  — to the `unstable.entries` append spill (the LOG WRITE: elems =
  the message's own Entries array cell 57, element = the entry cell
  58; nil old slice).
- Crossing 1 (`stepFn_appendSpill_transport`, atoms 0): the
  choice-dependent backing (capacity envelope [1,32]) born at 324.
- W2a (83 steps) to **the ONE in-window atom read**:
  `len(u.entries)` — `StrictOp.lengthOf` on the atom-carried handle.
- **The LENGTH CROSSING** (`stepFn_strict_apply` ∘
  `applyStrictOp_len_slice`, both landed kit lemmas — ZERO new
  machinery): the spilled handle's len is 1 for EVERY capacity
  choice, so the read's result is choice-INDEPENDENT and the mirror
  resumes on one literal. This is the first contact of the
  atom-absorption pattern with an in-window re-read of the absorbed
  value; the finding and its resolution shape are recorded in the
  arc log (A4-U12 slice 3).
- W2b (1,140 steps): `offsetInProgress` bookkeeping, `commitTo`
  (no-op at this fixture), response construction — to the
  `msgsAfterAppend` response spill (elems cell 388, response message
  347, target 389).
- Crossing 2 (the same transport, atoms 1): backing born at 390.
- W3 (29 steps) to `.next .stop`.

Total **4,828 steps, TWO choices consumed** (∀ streams
`c₁ :: c₂ :: ch`). Probe-validated end-to-end by
`artifacts/probe/{LaProbe3,LaGen}.lean` before any theorem here
(γ==machine at (c₁,c₂) = (0,0)/(3,5)/(31,31); the schedule and every
crossing cell from the generator's validated run).

FIXTURE-FAMILY preconditions (recorded): matching prev
(`m.Index = lastIndex = 1`, `m.LogTerm = term(1) = 1`), ONE entry
(index 2, term 1) — `after == offset + len(entries)` (the clean
append arm of `truncateAndAppend`), `m.Commit = committed = 1` (no
commit advance), `m.From = 2 ≠ r.id`, `r.Term = 0`; the static-cell
complement present with `nextAddr₀ = staticComplementNa = 98`.

THE OVERLAY CONCLUSIONS (GAP-V1-1b live): `absRaftLog` pre =
`hhAbsLog` (unstable EMPTY) and post = `laAbsLogPost` (unstable
`[(2,1)]` at offset 2) — the log VIEW grows by exactly the appended
entry (`la_log_grew`), lastIndex 1 → 2, stable half and committed
untouched.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower
  applyStrictOp_len_slice)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/LaGen.lean` — the
window links below re-check the literals against these defs). -/

def laMsgValG : GoValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .nil), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .addr (.base ⟨55⟩)),
    ("Index", .addr (.base ⟨56⟩)),
    ("Entries", .slice { base := some (.base ⟨57⟩), offset := 0, len := 1, cap := 1 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def laEntry1G : GoValue :=
  .struct ⟨"raftpb.Entry"⟩ #[
    ("Term", .addr (.base ⟨59⟩)), ("Index", .addr (.base ⟨60⟩)),
    ("Type", .nil), ("Data", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def laExtraG : List (Loc × GoCore.HeapCell) :=
  [(.base ⟨52⟩, ⟨some (.defined ⟨"raftpb.Message"⟩), laMsgValG⟩),
   (.base ⟨53⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨54⟩, ⟨some (.int .uint64), .int 2 .uint64⟩),
   (.base ⟨55⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨56⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨57⟩, ⟨some (.array 1 (.pointer (.defined ⟨"raftpb.Entry"⟩))),
      .array #[.addr (.base ⟨58⟩)]⟩),
   (.base ⟨58⟩, ⟨some (.defined ⟨"raftpb.Entry"⟩), laEntry1G⟩),
   (.base ⟨59⟩, ⟨some (.int .uint64), .int 1 .uint64⟩),
   (.base ⟨60⟩, ⟨some (.int .uint64), .int 2 .uint64⟩)]

def laSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  bf31SymHeap ++
  laExtraG.map (fun (p : Loc × GoCore.HeapCell) =>
    (p.1, .mk p.2.declaredTy (embedGo p.2.value))) ++
  staticComplementSym

def laS0 : SymState := { heap := laSymHeap, nextAddr := staticComplementNa }

/-- The drained call configuration of `handleAppendEntries(&m)`. -/
def laC0 : SymConfig :=
  .retV (.addr (.base ⟨52⟩))
    (.callArgsK ⟨"raft.raft.handleAppendEntries"⟩ [] [.addr (.base ⟨31⟩)] [] [] .stop)

def laElemTyE : Ty := .pointer (.defined ⟨"raftpb.Entry"⟩)
def laElemTyM : Ty := .pointer (.defined ⟨"raftpb.Message"⟩)

/-- The realized backing capacity at a stream head (nil old slice,
one appended element: width 32, envelope [1, 32] — the SAME envelope
at both spill sites). -/
def laCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- Backing 1 (the log write): the appended ENTRY pointer — the
message's own entry cell 58 — plus default-`nil` padding. -/
def laBacking1 (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨58⟩)] ++ List.replicate (laCap c - 1) .nil⟩

/-- Backing 2 (the response): the response-message pointer (cell 347)
plus default-`nil` padding. -/
def laBacking2 (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨347⟩)] ++ List.replicate (laCap c - 1) .nil⟩

/-- The choice-absorbing valuation: atoms 0 = the `unstable.entries`
append spill (handle → backing 324), atoms 1 = the `msgsAfterAppend`
response spill (handle → backing 390). Everything else rides. -/
def laρ' (ρ : Valuation) (c₁ c₂ : Nat) : Valuation :=
  { ρ with
    vals := fun i =>
      if i = 0 then .slice ⟨some (.base ⟨324⟩), 0, 1, laCap c₁⟩
      else if i = 1 then .slice ⟨some (.base ⟨390⟩), 0, 1, laCap c₂⟩
      else ρ.vals i,
    cells := fun i =>
      if i = 0 then ⟨some (.array (laCap c₁) laElemTyE), laBacking1 c₁⟩
      else if i = 1 then ⟨some (.array (laCap c₂) laElemTyM), laBacking2 c₂⟩
      else ρ.cells i }

/-! ## The window LINK theorems (kernel-checked against the evaluator
— the literals' correctness proofs and drift alarms). -/

theorem laW1_out : symEvalWindowTB bfTB 3573 laS0 laC0
    = (3573, laS1, laC1) := by
  kernel_rfl

def laK1 : GoLean.Sym.Cont symDom := match laC1 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def laE1 : LocalEnv := match laC1 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem laC1_shape : laC1 = .retV (.slice ⟨some (.base ⟨57⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice laElemTyE) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨323⟩)] [] laE1 laK1) := by
  kernel_rfl

theorem laW2a_out : symEvalWindowTB bfTB 83 laS2 (.next laK1)
    = (83, laS2a, laC2a) := by
  kernel_rfl

def laKLen : GoLean.Sym.Cont symDom := match laC2a with
  | .retV _ (.strictK _ _ _ _ k') => k'
  | _ => .stop
def laE2a : LocalEnv := match laC2a with
  | .retV _ (.strictK _ _ _ e _) => e
  | _ => []

theorem laC2a_shape : laC2a = .retV (.atom 0)
    (.strictK (.lengthOf (some (.slice laElemTyE))) [] [] laE2a laKLen) := by
  kernel_rfl

theorem laW2b_out : symEvalWindowTB bfTB 1140 laS2a
    (.retV (.int (.lit 1) .int) laKLen) = (1140, laS3, laC3) := by
  kernel_rfl

def laK3 : GoLean.Sym.Cont symDom := match laC3 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def laE3 : LocalEnv := match laC3 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

theorem laC3_shape : laC3 = .retV (.slice ⟨some (.base ⟨388⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice laElemTyM) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨389⟩)] [] laE3 laK3) := by
  kernel_rfl

theorem laW3_out : symEvalWindowTB bfTB 29 laS4 (.next laK3)
    = (29, laS5, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem laWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 3573 (γS ρ σ laS0) (γC ρ laC0) ch
      = .ok (γC ρ laC1, γS ρ σ laS1, ch) :=
  symEvalWindowTB_refines laW1_out ρ σ ch hag

theorem laWin2a (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 83 (γS ρ σ laS2) (γC ρ (.next laK1)) ch
      = .ok (γC ρ laC2a, γS ρ σ laS2a, ch) :=
  symEvalWindowTB_refines laW2a_out ρ σ ch hag

theorem laWin2b (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 1140 (γS ρ σ laS2a) (γC ρ (.retV (.int (.lit 1) .int) laKLen)) ch
      = .ok (γC ρ laC3, γS ρ σ laS3, ch) :=
  symEvalWindowTB_refines laW2b_out ρ σ ch hag

theorem laWin3 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 29 (γS ρ σ laS4) (γC ρ (.next laK3)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ laS5, ch) :=
  symEvalWindowTB_refines laW3_out ρ σ ch hag

/-! ## CROSSING 1 — the log-write spill (the transport at elem type
`*raftpb.Entry`; the appended element is the message's own entry
cell 58). -/

theorem la_spill1_step (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat)
    (rest : Choices) :
    stepFn (γS (laρ' ρ c₁ c₂) σ laS1) (γC (laρ' ρ c₁ c₂) laC1) (c₁ :: rest)
      = .ok (γC (laρ' ρ c₁ c₂) (.next laK1), γS (laρ' ρ c₁ c₂) σ laS2, rest) := by
  have hvisE : sliceVisibleValues (γS (laρ' ρ c₁ c₂) σ laS1)
      ⟨some (.base ⟨57⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨58⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (laρ' ρ c₁ c₂) σ laS1)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₁ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₁ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (laρ' ρ c₁ c₂) σ laS1) laElemTyE
      #[] #[.addr (.base ⟨58⟩)] (appendRealizedCap 0 (0 + 1) (c₁ % 32))
      = .ok (laBacking1 c₁) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨58⟩)],
        normalizeValueForTy (γS (laρ' ρ c₁ c₂) σ laS1) laElemTyE v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (laρ' ρ c₁ c₂) σ laS1) laElemTyE = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (laρ' ρ c₁ c₂) σ laS1) (elem := laElemTyE)
      (l₁ := []) (l₂ := [.addr (.base ⟨58⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₁ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32))
    simpa [laBacking1, laCap] using h
  have htgt : storeLoc { γS (laρ' ρ c₁ c₂) σ laS1 with
        heap := GoCore.Heap.set (γS (laρ' ρ c₁ c₂) σ laS1).heap
          (.base ⟨(γS (laρ' ρ c₁ c₂) σ laS1).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₁ % 32)) laElemTyE),
           laBacking1 c₁⟩,
        nextAddr := (γS (laρ' ρ c₁ c₂) σ laS1).nextAddr + 1 } (.base ⟨323⟩)
      (.slice ⟨some (.base ⟨(γS (laρ' ρ c₁ c₂) σ laS1).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₁ % 32)⟩)
      = .ok (γS (laρ' ρ c₁ c₂) σ laS2) := by
    kernel_rfl
  rw [laC1_shape]
  exact stepFn_appendSpill_transport (laρ' ρ c₁ c₂) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## THE LENGTH CROSSING — `len(u.entries)` on the atom-carried
handle: choice-INDEPENDENT result (the spilled slice's len is 1 at
every capacity), discharged by LANDED kit lemmas
(`applyStrictOp_len_slice` + `stepFn_strict_apply`) — zero new
machinery. -/

theorem la_len_step (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat)
    (ch : Choices) :
    stepFn (γS (laρ' ρ c₁ c₂) σ laS2a) (γC (laρ' ρ c₁ c₂) laC2a) ch
      = .ok (γC (laρ' ρ c₁ c₂) (.retV (.int (.lit 1) .int) laKLen),
             γS (laρ' ρ c₁ c₂) σ laS2a, ch) := by
  have h1 : γC (laρ' ρ c₁ c₂) laC2a
      = .retV (.slice ⟨some (.base ⟨324⟩), 0, 1, laCap c₁⟩)
          (.strictK (.lengthOf (some (.slice laElemTyE))) [] [] laE2a
            (concK (symInterp (laρ' ρ c₁ c₂)) laKLen)) := by
    kernel_rfl
  have h2 : γC (laρ' ρ c₁ c₂) (.retV (.int (.lit 1) .int) laKLen)
      = .retV (.int 1 .int) (concK (symInterp (laρ' ρ c₁ c₂)) laKLen) := by
    kernel_rfl
  rw [h1, h2]
  exact stepFn_strict_apply (applyStrictOp_len_slice
    (by simpa [laCap] using appendRealizedCap_lower 0 (0 + 1) (c₁ % 32)))

/-! ## CROSSING 2 — the response spill (elem `*raftpb.Message`,
response message cell 347, backing born at 390). -/

theorem la_spill2_step (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat)
    (rest : Choices) :
    stepFn (γS (laρ' ρ c₁ c₂) σ laS3) (γC (laρ' ρ c₁ c₂) laC3) (c₂ :: rest)
      = .ok (γC (laρ' ρ c₁ c₂) (.next laK3), γS (laρ' ρ c₁ c₂) σ laS4, rest) := by
  have hvisE : sliceVisibleValues (γS (laρ' ρ c₁ c₂) σ laS3)
      ⟨some (.base ⟨388⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨347⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (laρ' ρ c₁ c₂) σ laS3)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₂ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₂ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (laρ' ρ c₁ c₂) σ laS3) laElemTyM
      #[] #[.addr (.base ⟨347⟩)] (appendRealizedCap 0 (0 + 1) (c₂ % 32))
      = .ok (laBacking2 c₂) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨347⟩)],
        normalizeValueForTy (γS (laρ' ρ c₁ c₂) σ laS3) laElemTyM v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (laρ' ρ c₁ c₂) σ laS3) laElemTyM = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (laρ' ρ c₁ c₂) σ laS3) (elem := laElemTyM)
      (l₁ := []) (l₂ := [.addr (.base ⟨347⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₂ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₂ % 32))
    simpa [laBacking2, laCap] using h
  have htgt : storeLoc { γS (laρ' ρ c₁ c₂) σ laS3 with
        heap := GoCore.Heap.set (γS (laρ' ρ c₁ c₂) σ laS3).heap
          (.base ⟨(γS (laρ' ρ c₁ c₂) σ laS3).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₂ % 32)) laElemTyM),
           laBacking2 c₂⟩,
        nextAddr := (γS (laρ' ρ c₁ c₂) σ laS3).nextAddr + 1 } (.base ⟨389⟩)
      (.slice ⟨some (.base ⟨(γS (laρ' ρ c₁ c₂) σ laS3).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₂ % 32)⟩)
      = .ok (γS (laρ' ρ c₁ c₂) σ laS4) := by
    kernel_rfl
  rw [laC3_shape]
  exact stepFn_appendSpill_transport (laρ' ρ c₁ c₂) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 4,828-step span. -/

theorem la_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ : Nat) (ch : Choices) :
    stepFnIter 4828 (γS (laρ' ρ c₁ c₂) σ laS0) (γC (laρ' ρ c₁ c₂) laC0)
      (c₁ :: c₂ :: ch)
      = .ok (.next .stop, γS (laρ' ρ c₁ c₂) σ laS5, ch) := by
  have hA := GoLean.Sym.stepFnIter_window_pick_window
    (fun chx => laWin1 (laρ' ρ c₁ c₂) σ chx hag)
    (la_spill1_step ρ σ c₁ c₂ (c₂ :: ch))
    (fun chx => laWin2a (laρ' ρ c₁ c₂) σ chx hag)
  have hB := GoLean.Surface.stepFnIter_chain hA
    (GoLean.Surface.stepFnIter_one (la_len_step ρ σ c₁ c₂ (c₂ :: ch)))
  have hC := GoLean.Surface.stepFnIter_chain hB
    (laWin2b (laρ' ρ c₁ c₂) σ (c₂ :: ch) hag)
  have hD := GoLean.Surface.stepFnIter_chain hC
    (GoLean.Surface.stepFnIter_one (la_spill2_step ρ σ c₁ c₂ ch))
  have hE := GoLean.Surface.stepFnIter_chain hD
    (laWin3 (laρ' ρ c₁ c₂) σ ch hag)
  have hstop : γC (laρ' ρ c₁ c₂) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  exact hE

/-! ## The fixture family's log views: PRE = `hhAbsLog` (unstable
EMPTY — the same log the Hh/Hae families read); POST = the overlay
GROWN by the appended entry. -/

def laAbsLogPost : AbsLog := ⟨[(1, 1)], [(2, 1)], 2, 1, 1, 1⟩

/-- **THE LOG GREW**: the derived view gains exactly the appended
entry (index 2, term 1); nothing else moves. Pure spec-side fact —
the overlay algebra of GAP-V1-1b, exercised. -/
theorem la_log_grew :
    AbsLog.view laAbsLogPost = AbsLog.view hhAbsLog ++ [(2, 1)]
      ∧ AbsLog.lastIndex laAbsLogPost = some 2
      ∧ laAbsLogPost.stable = hhAbsLog.stable
      ∧ laAbsLogPost.committed = hhAbsLog.committed := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Projection facts at the literals. -/

theorem la_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ laS0) (.addr (.base ⟨52⟩))
      = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [(2, 1)], []⟩ := by
  kernel_rfl

theorem la_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ laS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem la_post_absRaftLog (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    absRaftLog (γS (laρ' ρ c₁ c₂) σ laS5) ⟨32⟩ = some laAbsLogPost := by
  kernel_rfl

theorem la_post_maa_field (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    fieldRead (γS (laρ' ρ c₁ c₂) σ laS5) ⟨31⟩ ⟨"raft.raft"⟩ "msgsAfterAppend"
      = some (.slice ⟨some (.base ⟨390⟩), 0, 1, laCap c₂⟩) := by
  kernel_rfl

theorem la_post_backing (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    GoCore.Heap.lookup (γS (laρ' ρ c₁ c₂) σ laS5).heap (.base ⟨390⟩)
      = some ⟨some (.array (laCap c₂) laElemTyM), laBacking2 c₂⟩ := by
  kernel_rfl

/-- The response record: **Index = mlastIndex = 2** (the success
form at the grown log). -/
theorem la_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    absMessage (γS (laρ' ρ c₁ c₂) σ laS5) (.addr (.base ⟨347⟩))
      = some (specAppResp 1 2 0 2) := by
  kernel_rfl

theorem laBacking2_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨347⟩)] ++ List.replicate (laCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨347⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition over the lens
combinators (no window re-evaluation, no per-choice case split). -/
theorem la_post_absOutbox (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    absOutbox (γS (laρ' ρ c₁ c₂) σ laS5) ⟨31⟩ "msgsAfterAppend"
      = some [specAppResp 1 2 0 2] := by
  rw [absOutbox]
  rw [la_post_maa_field ρ σ c₁ c₂]
  show sliceRead (γS (laρ' ρ c₁ c₂) σ laS5)
    (.slice ⟨some (.base ⟨390⟩), 0, 1, laCap c₂⟩) _ = _
  rw [sliceRead]
  rw [la_post_backing ρ σ c₁ c₂]
  show sliceElems (γS (laρ' ρ c₁ c₂) σ laS5)
    ⟨[GoValue.addr (.base ⟨347⟩)] ++ List.replicate (laCap c₂ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, laBacking2_head c₂]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [la_post_respMsg ρ σ c₁ c₂]
  simp only [hbind]
  rfl

theorem la_post_vote (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    fieldReadU64 (γS (laρ' ρ c₁ c₂) σ laS5) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (IntKind.normalize .uint64 (ρ.ints 1)) := by
  kernel_rfl

theorem la_post_lead (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    fieldReadU64 (γS (laρ' ρ c₁ c₂) σ laS5) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (IntKind.normalize .uint64 (ρ.ints 2)) := by
  kernel_rfl

theorem la_post_term (ρ : Valuation) (σ : ExecState) (c₁ c₂ : Nat) :
    fieldReadU64 (γS (laρ' ρ c₁ c₂) σ laS5) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic, placement LIVE;
the sim plumbing = the LIFTED `Frame.span_relocate` — third
consumer). -/

/-- **THE handleAppendEntries LOG-APPEND EQUATION**: from the drained
`handleAppendEntries(&m)` call at ANY placement of the fixture
footprint (relocation `r` + disjoint frame `fr`, one `FrameSim`
premise), over EVERY consumed choice prefix (∀ streams
`c₁ :: c₂ :: ch` — the log-write spill capacity, then the response
spill capacity), the run returns in exactly **4,828 steps** with two
choices consumed, and: the message argument projects by `absMessage`
WITH its entry (`entries = [(2,1)]`); the log view GROWS by exactly
the appended entry (`absRaftLog` pre = `hhAbsLog`, post =
`laAbsLogPost` — the unstable overlay `[(2,1)]`, GAP-V1-1b live;
see `la_log_grew`); the outbox gains EXACTLY the success response
(`absOutbox "msgsAfterAppend"` = `[specAppResp 1 2 0 2]` — Index =
mlastIndex = 2); `absOutbox "msgs"` stays empty; and the untouched
scalars read back unchanged. Side conditions `hvote`/`hlead`: the
surviving symbolic scalars' uint64-range facts. -/
theorem handleAppendEntries_logAppend_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ c₂ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ laS0) σF) :
    ∃ σFfin,
      stepFnIter 4828 σF (renameConfig r (γC ρ laC0)) (c₁ :: c₂ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (laρ' ρ c₁ c₂) σ laS5) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [(2, 1)], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 2]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some laAbsLogPost
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ laS0 = γS (laρ' ρ c₁ c₂) σ laS0 := by kernel_rfl
  have hpreC : γC ρ laC0 = γC (laρ' ρ c₁ c₂) laC0 := by kernel_rfl
  have hrun : stepFnIter 4828 (γS ρ σ laS0) (γC ρ laC0) (c₁ :: c₂ :: ch)
      = .ok (.next .stop, γS (laρ' ρ c₁ c₂) σ laS5, ch) := by
    rw [hpre, hpreC]
    exact la_full_span ρ σ hag c₁ c₂ ch
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := la_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (la_pre_absRaftLog ρ σ)
  · have h := la_post_absOutbox ρ σ c₁ c₂
    exact absOutbox_ren hs h
  · exact absOutbox_ren hs (show absOutbox (γS (laρ' ρ c₁ c₂) σ laS5) ⟨31⟩
      "msgs" = some [] by kernel_rfl)
  · exact absRaftLog_ren hs (la_post_absRaftLog ρ σ c₁ c₂)
  · have h := la_post_vote ρ σ c₁ c₂
    rw [hvote] at h
    exact fieldReadU64_ren hs h
  · have h := la_post_lead ρ σ c₁ c₂
    rw [hlead] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (la_post_term ρ σ c₁ c₂)

/-- The identity-placement corollary (the concrete equation at the
born-re-sited fixture; `na₀ = staticComplementNa = 98`). -/
theorem handleAppendEntries_logAppend_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (c₁ c₂ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 4828 (γS ρ σ laS0) (γC ρ laC0) (c₁ :: c₂ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ laS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [(2, 1)], []⟩
      ∧ absRaftLog (γS ρ σ laS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 2]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some laAbsLogPost
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 98 0) 98 98 [] (γS ρ σ laS0) (γS ρ σ laS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 98 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩ :=
    handleAppendEntries_logAppend_eq_alloc ρ σ hag hvote hlead c₁ c₂ ch hF
  have hcall : renameConfig (ρT 98 0) (γC ρ laC0) = γC ρ laC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT 98 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT 98 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 98 0 32⟩ : Addr) = ⟨32⟩ := rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h31] at hob hobm hv hl ht
  exact ⟨σfin, hrun, hmsg, hlog0, hob, hobm, hlog1, hv, hl, ht⟩

/-! ## §3.3 discharge witness (the probe's values: Vote 7, lead 2,
state 0, leadTransferee 5; stream heads 3, 5 — realized capacities
7 and 9). -/

def laρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem handleAppendEntries_logAppend_eq_witness :
    ∃ σfin,
      stepFnIter 4828 (γS laρw wBase laS0) (γC laρw laC0) (3 :: 5 :: [])
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS laρw wBase laS0) (.addr (.base ⟨52⟩))
          = some ⟨0, 0, 2, 0, 1, 1, 1, 0, 0, false, [(2, 1)], []⟩
      ∧ absRaftLog (γS laρw wBase laS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 2 0 2]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some laAbsLogPost
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  handleAppendEntries_logAppend_eq laρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) 3 5 []

end GoLean.RaftSeam
