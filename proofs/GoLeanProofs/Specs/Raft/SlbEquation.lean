import GoLeanProofs.Specs.Raft.SlbLit
import GoLeanProofs.Specs.Raft.Bc31
import GoLeanProofs.Specs.Raft.BfEquation
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# A4-U17: THE stepLeader × MsgBeat DISPATCH-ARM EQUATION — the
LEADER side's first arm, closing the heartbeat round-kind's arm
triple (sF/sC/sL)

**LINEAGE: the SfHb/SCHb dispatch-arm template (literal bounded
window chains + the transport family) with ONE new crossing class —
the IN-PLACE SECOND APPEND** (`stepFn_appendInPlace_transport`,
landed in `Sym/SpillTransport.lean` this unit: the U12 atom-re-read
watch-item's first LIVE instance — the second `r.send` re-reads the
first send's spilled `msgs` handle, riding as valuation atom 0).

The chain (probe-validated end-to-end by `artifacts/probe/SlbGen.lean`
BEFORE any theorem here; γ==machine at four 4-choice tuples incl. the
cap-2 boundary c₄ = 30): bf31SymHeap AS-IS (all four raft scalars
SYMBOLIC — this arm branches on none of them, the first arm family
with a fully-symbolic scalar pack) + the Message with Type 55 ↦ 1
(MsgBeat) + caller cells [66,69), na₀ 69. Windows
**[288, 28, 28, 28, 3, 1474, 1393, 113]** + 7 crossings (3 Visit
picks over the prs map at 33, range-stop, sort collapse, the msgs
spill, the in-place second append) = **3,362 machine steps / FOUR
choices** — the U16 stepLeader census exactly.

FIXTURE-FAMILY preconditions (the U3 fine-print pattern):
- `m.Type = 1` (MsgBeat) CONCRETE — the switch driver; other Type
  values are other arm families;
- r's Vote/lead/state/leadTransferee ALL ride SYMBOLIC (x₁-x₄): the
  bcastHeartbeat path reads r.id (concrete 1), the prs map, and the
  log's committed — never the four scalars; each surviving scalar's
  readout carries its uint64-range side condition (wrap depth 2 —
  the two msgs field stores; generator-probed per §4c);
- **`2 ≤ hhCap c₄` — THE FIRST CHOICE-VALUE side condition** (the
  §4c watch-item, fired): the spill's realized capacity must leave
  room for the second peer's in-place append. The complement (`c₄ % 32 = 29`,
  realized cap 1) is the RE-SPILL family — a different, longer chain
  (5 choices; machine-witnessed by the generator's divergence probe),
  logged as a named residual family, NOT covered here.

Both sends are Type-8 heartbeats to the sorted peers [2, 3] (self 1
skipped), commit = 0 (min(pr.Match = 0, committed = 1) at this
tracker fixture) — choice-INDEPENDENT records: the sort collapse
makes the send order concrete for every pick order.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/SlbGen.lean`). -/

def slbMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

def slbS0 : SymState :=
  { heap := bf31SymHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) slbMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 1) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def slbEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

/-- The drained caller shape: `er := raft.stepLeader(r, m)`. -/
def slbC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepLeader"⟩ #[Expr.var "r", Expr.var "m"])
    slbEnv .stop

/-! ## The crossing outputs (even indices; the Bf31 pattern —
crossings reduce in one step from the generated odd literals). -/

def slbP2 : SymState × SymConfig := uCrossPick 6 .uint64 slbS1 slbC1
def slbS2 : SymState := slbP2.1
def slbC2 : SymConfig := slbP2.2
def slbP4 : SymState × SymConfig := uCrossPick 7 .uint64 slbS3 slbC3
def slbS4 : SymState := slbP4.1
def slbC4 : SymConfig := slbP4.2
def slbP6 : SymState × SymConfig := uCrossPick 8 .uint64 slbS5 slbC5
def slbS6 : SymState := slbP6.1
def slbC6 : SymConfig := slbP6.2
def slbP8 : SymState × SymConfig := uCrossStop slbS7 slbC7
def slbS8 : SymState := slbP8.1
def slbC8 : SymConfig := slbP8.2
def slbP10 : SymState × SymConfig := uCrossSort slbS9 slbC9
def slbS10 : SymState := slbP10.1
def slbC10 : SymConfig := slbP10.2

/-- The post-spill continuation/env, extracted from the quit config. -/
def slbK11 : GoLean.Sym.Cont symDom := match slbC11 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def slbE11 : LocalEnv := match slbC11 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

/-- The spill crossing's post state (the generator's construction:
target ↦ value-atom 0, backing born as cell-atom 0). -/
def slbS12 : SymState :=
  { heap := (GoLean.Sym.Heap.set slbS11.heap (.base ⟨slbTgt⟩)
      (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩)))) (.atom 0)))
      ++ [(.base ⟨slbBacking⟩, .atom 0)],
    nextAddr := slbBacking + 1 }

/-- The post-in-place continuation/env. -/
def slbK13 : GoLean.Sym.Cont symDom := match slbC13 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def slbE13 : LocalEnv := match slbC13 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

/-- The IN-PLACE crossing's post state (the generator's construction:
backing cell-atom 0 → cell-atom 1, target ↦ value-atom 1; no
allocation, `nextAddr` unchanged). -/
def slbS14 : SymState :=
  { heap := GoLean.Sym.Heap.set
      (GoLean.Sym.Heap.set slbS13.heap (.base ⟨slbBacking⟩) (.atom 1))
      (.base ⟨slbTgt2⟩)
      (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩)))) (.atom 1)),
    nextAddr := slbS13.nextAddr }

/-- The backing payload at spill head `c` after the FIRST send. -/
def slbBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨slbMsgPtr⟩)] ++ List.replicate (hhCap c - 1) .nil⟩

/-- The backing payload after the SECOND (in-place) send: both
heartbeat pointers, padding `hhCap c - 2` (needs `2 ≤ hhCap c`). -/
def slbBackingVal2 (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨slbMsgPtr⟩), .addr (.base ⟨slbMsg2Ptr⟩)]
    ++ List.replicate (hhCap c - 2) .nil⟩

/-- The spill/in-place atom absorber (atoms 0 = post-spill len 1,
atoms 1 = post-in-place len 2; composes with `uρ` — disjoint fields). -/
def slbρA (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i =>
      if i = 0 then .slice ⟨some (.base ⟨slbBacking⟩), 0, 1, hhCap c⟩
      else if i = 1 then .slice ⟨some (.base ⟨slbBacking⟩), 0, 2, hhCap c⟩
      else ρ.vals i,
    cells := fun i =>
      if i = 0 then ⟨some (.array (hhCap c) hhElemTy), slbBackingVal c⟩
      else if i = 1 then ⟨some (.array (hhCap c) hhElemTy), slbBackingVal2 c⟩
      else ρ.cells i }

/-- The full prefix-derived valuation: Visit pick vars 6-8 + the two
atom generations (var 5 is unused by this chain and pinned 0). -/
def slbρ' (ρ : Valuation) (c₁ c₂ c₄ : Nat) : Valuation :=
  uρ (slbρA ρ c₄) 0 (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)

/-! ## The window LINK theorems (kernel-checked — the drift alarms). -/

theorem slbW1_out : symEvalWindowTB bfTB slbW1n slbS0 slbC0 = (slbW1n, slbS1, slbC1) := by
  kernel_rfl
theorem slbW2_out : symEvalWindowTB bfTB slbW2n slbS2 slbC2 = (slbW2n, slbS3, slbC3) := by
  kernel_rfl
theorem slbW3_out : symEvalWindowTB bfTB slbW3n slbS4 slbC4 = (slbW3n, slbS5, slbC5) := by
  kernel_rfl
theorem slbW4_out : symEvalWindowTB bfTB slbW4n slbS6 slbC6 = (slbW4n, slbS7, slbC7) := by
  kernel_rfl
theorem slbW5_out : symEvalWindowTB bfTB slbW5n slbS8 slbC8 = (slbW5n, slbS9, slbC9) := by
  kernel_rfl
theorem slbW6_out : symEvalWindowTB bfTB slbW6n slbS10 slbC10 = (slbW6n, slbS11, slbC11) := by
  kernel_rfl
theorem slbW7_out : symEvalWindowTB bfTB slbW7n slbS12 (.next slbK11)
    = (slbW7n, slbS13, slbC13) := by
  kernel_rfl
theorem slbW8_out : symEvalWindowTB bfTB slbW8n slbS14 (.next slbK13)
    = (slbW8n, slbS15, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem slbWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW1n (γS ρ σ slbS0) (γC ρ slbC0) ch
      = .ok (γC ρ slbC1, γS ρ σ slbS1, ch) :=
  symEvalWindowTB_refines slbW1_out ρ σ ch hag
theorem slbWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW2n (γS ρ σ slbS2) (γC ρ slbC2) ch
      = .ok (γC ρ slbC3, γS ρ σ slbS3, ch) :=
  symEvalWindowTB_refines slbW2_out ρ σ ch hag
theorem slbWin3 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW3n (γS ρ σ slbS4) (γC ρ slbC4) ch
      = .ok (γC ρ slbC5, γS ρ σ slbS5, ch) :=
  symEvalWindowTB_refines slbW3_out ρ σ ch hag
theorem slbWin4 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW4n (γS ρ σ slbS6) (γC ρ slbC6) ch
      = .ok (γC ρ slbC7, γS ρ σ slbS7, ch) :=
  symEvalWindowTB_refines slbW4_out ρ σ ch hag
theorem slbWin5 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW5n (γS ρ σ slbS8) (γC ρ slbC8) ch
      = .ok (γC ρ slbC9, γS ρ σ slbS9, ch) :=
  symEvalWindowTB_refines slbW5_out ρ σ ch hag
theorem slbWin6 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW6n (γS ρ σ slbS10) (γC ρ slbC10) ch
      = .ok (γC ρ slbC11, γS ρ σ slbS11, ch) :=
  symEvalWindowTB_refines slbW6_out ρ σ ch hag
theorem slbWin7 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW7n (γS ρ σ slbS12) (γC ρ (.next slbK11)) ch
      = .ok (γC ρ slbC13, γS ρ σ slbS13, ch) :=
  symEvalWindowTB_refines slbW7_out ρ σ ch hag
theorem slbWin8 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter slbW8n (γS ρ σ slbS14) (γC ρ (.next slbK13)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ slbS15, ch) :=
  symEvalWindowTB_refines slbW8_out ρ σ ch hag

/-! ## Site 1 — Visit pick 1 (prs map at base 33, `x₆ = uKey1 c₁`;
`bc31Cands3`/`bc31Cands3_get` reused from Bc31). -/

def slbB1 : Stmt := match slbC1 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def slbE1 : LocalEnv := match slbC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def slbK1 : GoLean.Sym.Cont symDom := match slbC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def slbStart1 : Array SymValue := match slbC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem slbC1_shape : slbC1 = .next (.mapIterK (some "id") none uTyK uTyProg
    slbB1 (some (.base ⟨33⟩)) #[] slbStart1 slbE1 slbK1) := by
  kernel_rfl

theorem slbS2_eq : slbS2 = (slbS1.alloc uKeyV2 (some uTyK)).2 := by
  unfold slbS2 slbP2
  rw [slbC1_shape]
  rfl

theorem slbC2_eq : slbC2 = .exec slbB1
    ((slbE1.pushScope).declare "id" (slbS1.alloc uKeyV2 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg slbB1 (some (.base ⟨33⟩))
      (Array.push #[] uKeyV2) slbStart1 slbE1 slbK1) := by
  unfold slbC2 slbP2
  rw [slbC1_shape]
  rfl

theorem slbEntries1 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ slbS1) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem slbCands1_fact (ρ : Valuation) (σ : ExecState) :
    mapIterCandidates (γS ρ σ slbS1) uTyK uTyProg (some (.base ⟨33⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok bc31Cands3 := by
  simp only [mapIterCandidates, slbEntries1 ρ σ, Bind.bind, Except.bind]
  with_unfolding_all rfl

theorem slbPick1_step (ρ : Valuation) (σ : ExecState)
    (a c d : Int) (c₁ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₁) c d) σ slbS1)
      (γC (uρ ρ a (uKey1 c₁) c d) slbC1) (c₁ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₁) c d) slbC2,
          γS (uρ ρ a (uKey1 c₁) c d) σ slbS2, rest) := by
  have h1 : c₁ % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [slbC1_shape, slbC2_eq, slbS2_eq]
  refine stepFn_pick_transport _ σ (slbCands1_fact _ σ)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    ?_ (bc31Cands3_get _ h1) (by with_unfolding_all rfl) ?_
  · show Choices.consume (c₁ :: rest) (bc31Cands3.size + _) = _
    simp only [Choices.consume]
    rfl
  · have hn := normalize_small .uint64 ((c₁ : Int) % 3 + 1)
      (by omega) (by omega)
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [normalizeValueForTyFuel, hn, uTyK]

/-! ## Site 2 — Visit pick 2 (`x₇ = uKey2 c₁ c₂`; 6-leaf case
analysis, the Bf31/SCHb pattern). -/

theorem slbC3_shape : slbC3 = .next (.mapIterK (some "id") none uTyK uTyProg
    slbB1 (some (.base ⟨33⟩)) #[uKeyV2] slbStart1 slbE1 slbK1) := by
  kernel_rfl

theorem slbS4_eq : slbS4 = (slbS3.alloc uKeyV3 (some uTyK)).2 := by
  unfold slbS4 slbP4
  rw [slbC3_shape]
  rfl

theorem slbC4_eq : slbC4 = .exec slbB1
    ((slbE1.pushScope).declare "id" (slbS3.alloc uKeyV3 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg slbB1 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2] uKeyV3) slbStart1 slbE1 slbK1) := by
  unfold slbC4 slbP4
  rw [slbC3_shape]
  rfl

theorem slbEntries3 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ slbS3) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem slbPick2_step (ρ : Valuation) (σ : ExecState)
    (a d : Int) (c₁ c₂ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) d) σ slbS3)
      (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) d) slbC3) (c₂ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) d) slbC4,
          γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) d) σ slbS4, rest) := by
  rw [slbC3_shape, slbC4_eq, slbS4_eq]
  rcases (show c₁ % 3 = 0 ∨ c₁ % 3 = 1 ∨ c₁ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₂ % 2 = 0 ∨ c₂ % 2 = 1 by omega) with h3|h3
  all_goals first
  | (rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries3 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₂ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries3 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₂ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries3 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₂ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries3 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₂ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries3 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₂ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries3 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₂ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)

/-! ## Site 3 — Visit pick 3 (`x₈ = uKey3`, the leftover; width 1). -/

theorem slbC5_shape : slbC5 = .next (.mapIterK (some "id") none uTyK uTyProg
    slbB1 (some (.base ⟨33⟩)) #[uKeyV2, uKeyV3] slbStart1 slbE1 slbK1) := by
  kernel_rfl

theorem slbS6_eq : slbS6 = (slbS5.alloc uKeyV4 (some uTyK)).2 := by
  unfold slbS6 slbP6
  rw [slbC5_shape]
  rfl

theorem slbC6_eq : slbC6 = .exec slbB1
    ((slbE1.pushScope).declare "id" (slbS5.alloc uKeyV4 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg slbB1 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2, uKeyV3] uKeyV4) slbStart1 slbE1 slbK1) := by
  unfold slbC6 slbP6
  rw [slbC5_shape]
  rfl

theorem slbEntries5 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ slbS5) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem slbPick3_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₁ c₂ c₃ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) σ slbS5)
      (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) slbC5)
      (c₃ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) slbC6,
          γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) σ slbS6,
          rest) := by
  rw [slbC5_shape, slbC6_eq, slbS6_eq]
  rcases (show c₁ % 3 = 0 ∨ c₁ % 3 = 1 ∨ c₁ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₂ % 2 = 0 ∨ c₂ % 2 = 1 by omega) with h3|h3
  all_goals first
  | (rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₁ c₂ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₁ c₂ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₁ c₂ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₁ c₂ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₁ c₂ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₁ c₂ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, slbEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)

/-! ## Site 4 — the range STOP (whole-step kernel facts per leaf). -/

theorem slbStop_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ slbS7) (γC (uρ ρ a 1 2 3) slbC7) ch
      = .ok (γC (uρ ρ a 1 2 3) slbC8, γS (uρ ρ a 1 2 3) σ slbS8, ch) := by
  kernel_rfl
theorem slbStop_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ slbS7) (γC (uρ ρ a 1 3 2) slbC7) ch
      = .ok (γC (uρ ρ a 1 3 2) slbC8, γS (uρ ρ a 1 3 2) σ slbS8, ch) := by
  kernel_rfl
theorem slbStop_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ slbS7) (γC (uρ ρ a 2 1 3) slbC7) ch
      = .ok (γC (uρ ρ a 2 1 3) slbC8, γS (uρ ρ a 2 1 3) σ slbS8, ch) := by
  kernel_rfl
theorem slbStop_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ slbS7) (γC (uρ ρ a 2 3 1) slbC7) ch
      = .ok (γC (uρ ρ a 2 3 1) slbC8, γS (uρ ρ a 2 3 1) σ slbS8, ch) := by
  kernel_rfl
theorem slbStop_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ slbS7) (γC (uρ ρ a 3 1 2) slbC7) ch
      = .ok (γC (uρ ρ a 3 1 2) slbC8, γS (uρ ρ a 3 1 2) σ slbS8, ch) := by
  kernel_rfl
theorem slbStop_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ slbS7) (γC (uρ ρ a 3 2 1) slbC7) ch
      = .ok (γC (uρ ρ a 3 2 1) slbC8, γS (uρ ρ a 3 2 1) σ slbS8, ch) := by
  kernel_rfl

theorem slbStop_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₁ c₂ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) σ slbS7)
      (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) slbC7) ch
      = .ok (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) slbC8,
          γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) σ slbS8,
          ch) := by
  rcases (show c₁ % 3 = 0 ∨ c₁ % 3 = 1 ∨ c₁ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₂ % 2 = 0 ∨ c₂ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbStop_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbStop_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbStop_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbStop_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbStop_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbStop_leaf_21 ρ σ a ch

/-! ## Site 5 — the sortSlice COLLAPSE (every leaf's post state is
`slbS10`: ids = [1,2,3]). -/

theorem slbSort_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ slbS9) (γC (uρ ρ a 1 2 3) slbC9) ch
      = .ok (γC (uρ ρ a 1 2 3) slbC10, γS (uρ ρ a 1 2 3) σ slbS10, ch) := by
  kernel_rfl
theorem slbSort_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ slbS9) (γC (uρ ρ a 1 3 2) slbC9) ch
      = .ok (γC (uρ ρ a 1 3 2) slbC10, γS (uρ ρ a 1 3 2) σ slbS10, ch) := by
  kernel_rfl
theorem slbSort_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ slbS9) (γC (uρ ρ a 2 1 3) slbC9) ch
      = .ok (γC (uρ ρ a 2 1 3) slbC10, γS (uρ ρ a 2 1 3) σ slbS10, ch) := by
  kernel_rfl
theorem slbSort_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ slbS9) (γC (uρ ρ a 2 3 1) slbC9) ch
      = .ok (γC (uρ ρ a 2 3 1) slbC10, γS (uρ ρ a 2 3 1) σ slbS10, ch) := by
  kernel_rfl
theorem slbSort_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ slbS9) (γC (uρ ρ a 3 1 2) slbC9) ch
      = .ok (γC (uρ ρ a 3 1 2) slbC10, γS (uρ ρ a 3 1 2) σ slbS10, ch) := by
  kernel_rfl
theorem slbSort_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ slbS9) (γC (uρ ρ a 3 2 1) slbC9) ch
      = .ok (γC (uρ ρ a 3 2 1) slbC10, γS (uρ ρ a 3 2 1) σ slbS10, ch) := by
  kernel_rfl

theorem slbSort_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₁ c₂ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) σ slbS9)
      (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) slbC9) ch
      = .ok (γC (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) slbC10,
          γS (uρ ρ a (uKey1 c₁) (uKey2 c₁ c₂) (uKey3 c₁ c₂)) σ slbS10,
          ch) := by
  rcases (show c₁ % 3 = 0 ∨ c₁ % 3 = 1 ∨ c₁ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₂ % 2 = 0 ∨ c₂ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbSort_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₁ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbSort_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbSort_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₁ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbSort_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbSort_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₁ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₁ c₂ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₁ c₂ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact slbSort_leaf_21 ρ σ a ch

/-! ## Site 6 — THE SPILL CROSSING (the SfHb/SCHb pattern; the first
send's `r.msgs` append reallocates from the nil slice). -/

theorem slbC11_shape : slbC11 = .retV (.slice ⟨some (.base ⟨slbElems⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨slbTgt⟩)] [] slbE11 slbK11) := by
  kernel_rfl

theorem slbSpill_step (ρ : Valuation) (σ : ExecState) (c₄ : Nat)
    (rest : Choices) :
    stepFn (γS (slbρA ρ c₄) σ slbS11) (γC (slbρA ρ c₄) slbC11) (c₄ :: rest)
      = .ok (γC (slbρA ρ c₄) (.next slbK11), γS (slbρA ρ c₄) σ slbS12, rest) := by
  have hvisE : sliceVisibleValues (γS (slbρA ρ c₄) σ slbS11)
      ⟨some (.base ⟨slbElems⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨slbMsgPtr⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (slbρA ρ c₄) σ slbS11)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₄ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₄ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (slbρA ρ c₄) σ slbS11) hhElemTy
      #[] #[.addr (.base ⟨slbMsgPtr⟩)] (appendRealizedCap 0 (0 + 1) (c₄ % 32))
      = .ok (slbBackingVal c₄) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨slbMsgPtr⟩)],
        normalizeValueForTy (γS (slbρA ρ c₄) σ slbS11) hhElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (slbρA ρ c₄) σ slbS11) hhElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (slbρA ρ c₄) σ slbS11) (elem := hhElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨slbMsgPtr⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₄ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₄ % 32))
    simpa [slbBackingVal, hhCap] using h
  have htgt : storeLoc { γS (slbρA ρ c₄) σ slbS11 with
        heap := GoCore.Heap.set (γS (slbρA ρ c₄) σ slbS11).heap
          (.base ⟨(γS (slbρA ρ c₄) σ slbS11).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₄ % 32)) hhElemTy),
           slbBackingVal c₄⟩,
        nextAddr := (γS (slbρA ρ c₄) σ slbS11).nextAddr + 1 } (.base ⟨slbTgt⟩)
      (.slice ⟨some (.base ⟨(γS (slbρA ρ c₄) σ slbS11).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₄ % 32)⟩)
      = .ok (γS (slbρA ρ c₄) σ slbS12) := by
    kernel_rfl
  rw [slbC11_shape]
  exact stepFn_appendSpill_transport (slbρA ρ c₄) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## Site 7 — THE IN-PLACE SECOND APPEND (the new crossing class:
`stepFn_appendInPlace_transport` + `storeLoc_spilled_backing_index1`,
landed in Sym/SpillTransport.lean this unit; the choice-value side
condition `2 ≤ hhCap c₄` enters here and ONLY here). -/

theorem slbC13_shape : slbC13 = .retV (.slice ⟨some (.base ⟨slbElems2⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhElemTy) 1
      [.atom 0, .addr (.base ⟨slbTgt2⟩)] [] slbE13 slbK13) := by
  kernel_rfl

theorem slbInplace_step (ρ : Valuation) (σ : ExecState) (c₄ : Nat)
    (hcap : 2 ≤ hhCap c₄) (ch : Choices) :
    stepFn (γS (slbρA ρ c₄) σ slbS13) (γC (slbρA ρ c₄) slbC13) ch
      = .ok (γC (slbρA ρ c₄) (.next slbK13), γS (slbρA ρ c₄) σ slbS14, ch) := by
  have hvisE : sliceVisibleValues (γS (slbρA ρ c₄) σ slbS13)
      ⟨some (.base ⟨slbElems2⟩), 0, 1, 1⟩
      = .ok #[.addr (.base ⟨slbMsg2Ptr⟩)] := by
    kernel_rfl
  have hlook : GoCore.Heap.lookup (γS (slbρA ρ c₄) σ slbS13).heap
      (.base ⟨slbBacking⟩)
      = some ⟨some (.array (hhCap c₄) (.pointer (.defined ⟨"raftpb.Message"⟩))),
          .array ⟨[.addr (.base ⟨slbMsgPtr⟩)]
            ++ List.replicate (hhCap c₄ - 1) .nil⟩⟩ := by
    kernel_rfl
  have hst1 := storeLoc_spilled_backing_index1
    (σ := γS (slbρA ρ c₄) σ slbS13) (b := ⟨slbBacking⟩)
    (w := .addr (.base ⟨slbMsg2Ptr⟩)) hcap rfl hlook
  have hst2 : storeLoc ({ γS (slbρA ρ c₄) σ slbS13 with
        heap := GoCore.Heap.set (γS (slbρA ρ c₄) σ slbS13).heap
          (.base ⟨slbBacking⟩)
          (⟨some (.array (hhCap c₄) (.pointer (.defined ⟨"raftpb.Message"⟩))),
            .array ⟨[.addr (.base ⟨slbMsgPtr⟩), .addr (.base ⟨slbMsg2Ptr⟩)]
              ++ List.replicate (hhCap c₄ - 2) .nil⟩⟩ : GoCore.HeapCell) })
      (.base ⟨slbTgt2⟩)
      (.slice ⟨some (.base ⟨slbBacking⟩), 0, 1 + 1, hhCap c₄⟩)
      = .ok (γS (slbρA ρ c₄) σ slbS14) := by
    kernel_rfl
  have hold : concV (symInterp (slbρA ρ c₄))
      (GoLean.Sym.Value.atom (D := symDom) 0)
      = GoValue.slice ⟨some (.base ⟨slbBacking⟩), 0, 1, hhCap c₄⟩ := by
    with_unfolding_all rfl
  rw [slbC13_shape]
  exact stepFn_appendInPlace_transport (slbρA ρ c₄) σ _
    hold (by simpa using hcap) (by decide)
    hvisE hst1 hst2

/-! ## The composed 3,362-step span. -/

theorem slb_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ : Nat) (hcap : 2 ≤ hhCap c₄) (ch : Choices) :
    stepFnIter 3362 (γS (slbρ' ρ c₁ c₂ c₄) σ slbS0)
      (γC (slbρ' ρ c₁ c₂ c₄) slbC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: ch)
      = .ok (.next .stop, γS (slbρ' ρ c₁ c₂ c₄) σ slbS15, ch) := by
  have w1 := fun chx => slbWin1 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w2 := fun chx => slbWin2 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w3 := fun chx => slbWin3 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w4 := fun chx => slbWin4 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w5 := fun chx => slbWin5 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w6 := fun chx => slbWin6 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w7 := fun chx => slbWin7 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have w8 := fun chx => slbWin8 (slbρ' ρ c₁ c₂ c₄) σ chx hag
  have p1 := slbPick1_step (slbρA ρ c₄) σ 0 (uKey2 c₁ c₂)
    (uKey3 c₁ c₂) c₁ (c₂ :: c₃ :: c₄ :: ch)
  have p2 := slbPick2_step (slbρA ρ c₄) σ 0 (uKey3 c₁ c₂)
    c₁ c₂ (c₃ :: c₄ :: ch)
  have p3 := slbPick3_step (slbρA ρ c₄) σ 0 c₁ c₂ c₃ (c₄ :: ch)
  have pstop := slbStop_step (slbρA ρ c₄) σ 0 c₁ c₂ (c₄ :: ch)
  have psort := slbSort_step (slbρA ρ c₄) σ 0 c₁ c₂ (c₄ :: ch)
  have pspill := slbSpill_step (uρ ρ 0 (uKey1 c₁) (uKey2 c₁ c₂)
    (uKey3 c₁ c₂)) σ c₄ ch
  have pip := slbInplace_step (uρ ρ 0 (uKey1 c₁) (uKey2 c₁ c₂)
    (uKey3 c₁ c₂)) σ c₄ hcap ch
  have hcommS : slbρA (uρ ρ 0 (uKey1 c₁) (uKey2 c₁ c₂)
      (uKey3 c₁ c₂)) c₄ = slbρ' ρ c₁ c₂ c₄ := by
    with_unfolding_all rfl
  rw [hcommS] at pspill pip
  have h := GoLean.Surface.stepFnIter_chain
    (GoLean.Surface.stepFnIter_chain
      (GoLean.Surface.stepFnIter_chain
        (GoLean.Surface.stepFnIter_chain
          (GoLean.Surface.stepFnIter_chain
            (GoLean.Surface.stepFnIter_chain
              (GoLean.Surface.stepFnIter_chain
                (GoLean.Surface.stepFnIter_chain
                  (GoLean.Surface.stepFnIter_chain
                    (GoLean.Surface.stepFnIter_chain
                      (GoLean.Surface.stepFnIter_chain
                        (GoLean.Surface.stepFnIter_chain
                          (GoLean.Surface.stepFnIter_chain
                            (GoLean.Surface.stepFnIter_chain
                              (w1 (c₁ :: c₂ :: c₃ :: c₄ :: ch))
                              (GoLean.Surface.stepFnIter_one p1))
                            (w2 (c₂ :: c₃ :: c₄ :: ch)))
                          (GoLean.Surface.stepFnIter_one p2))
                        (w3 (c₃ :: c₄ :: ch)))
                      (GoLean.Surface.stepFnIter_one p3))
                    (w4 (c₄ :: ch)))
                  (GoLean.Surface.stepFnIter_one pstop))
                (w5 (c₄ :: ch)))
              (GoLean.Surface.stepFnIter_one psort))
            (w6 (c₄ :: ch)))
          (GoLean.Surface.stepFnIter_one pspill))
        (w7 ch))
      (GoLean.Surface.stepFnIter_one pip))
    (w8 ch)
  have hstop : γC (slbρ' ρ c₁ c₂ c₄) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  show stepFnIter 3362 _ _ _ = _
  exact h

/-! ## Projection facts at the literals. -/

/-- The leader's outgoing heartbeat record (Type 8 = MsgHeartbeat;
commit = min(pr.Match, committed) = 0 at this tracker fixture). -/
def specHeartbeat (src dst commit : Int) : AbsMessage :=
  ⟨8, dst, src, 0, 0, 0, commit, 0, 0, false, [], []⟩

/-- The pre-state message record: typ 1 = MsgBeat (the local tick's
message; From/Commit ride the shared fixture cells). -/
theorem slb_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ slbS0) (.addr (.base ⟨52⟩))
      = some ⟨1, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem slb_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ slbS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem slb_post_absRaftLog (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₄ : Nat) :
    absRaftLog (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem slb_post_er (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    GoCore.Heap.lookup (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15).heap (.base ⟨68⟩)
      = some ⟨some (.interface ⟨"error"⟩), .nil⟩ := by
  kernel_rfl

/-- The msgs field reads the len-2 in-place handle (atom 1's image). -/
theorem slb_post_msgs_field (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₄ : Nat) :
    fieldRead (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ ⟨"raft.raft"⟩ "msgs"
      = some (.slice ⟨some (.base ⟨slbBacking⟩), 0, 2, hhCap c₄⟩) := by
  kernel_rfl

theorem slb_post_backing (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    GoCore.Heap.lookup (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15).heap
      (.base ⟨slbBacking⟩)
      = some ⟨some (.array (hhCap c₄) hhElemTy), slbBackingVal2 c₄⟩ := by
  kernel_rfl

theorem slb_post_hb1 (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    absMessage (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) (.addr (.base ⟨slbMsgPtr⟩))
      = some (specHeartbeat 1 2 0) := by
  kernel_rfl

theorem slb_post_hb2 (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    absMessage (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) (.addr (.base ⟨slbMsg2Ptr⟩))
      = some (specHeartbeat 1 3 0) := by
  kernel_rfl

/-- The backing's two live elements (choice-generic: the padding
never enters — `getElem?` reduces at the cons heads). -/
theorem slbBackingVal2_head0 (c : Nat) :
    (⟨[GoValue.addr (.base ⟨slbMsgPtr⟩), .addr (.base ⟨slbMsg2Ptr⟩)]
      ++ List.replicate (hhCap c - 2) .nil⟩ : Array GoValue)[0]?
      = some (.addr (.base ⟨slbMsgPtr⟩)) := by
  rw [List.cons_append]
  rfl

theorem slbBackingVal2_head1 (c : Nat) :
    (⟨[GoValue.addr (.base ⟨slbMsgPtr⟩), .addr (.base ⟨slbMsg2Ptr⟩)]
      ++ List.replicate (hhCap c - 2) .nil⟩ : Array GoValue)[1]?
      = some (.addr (.base ⟨slbMsg2Ptr⟩)) := by
  rw [List.cons_append, List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**: both heartbeats, in the sort-collapsed
peer order [2, 3] — by lemma composition over the lens combinators. -/
theorem slb_post_absOutbox (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₄ : Nat) :
    absOutbox (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ "msgs"
      = some [specHeartbeat 1 2 0, specHeartbeat 1 3 0] := by
  rw [absOutbox]
  rw [slb_post_msgs_field ρ σ c₁ c₂ c₄]
  show sliceRead (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15)
    (.slice ⟨some (.base ⟨slbBacking⟩), 0, 2, hhCap c₄⟩) _ = _
  rw [sliceRead]
  rw [slb_post_backing ρ σ c₁ c₂ c₄]
  show sliceElems (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15)
    ⟨[GoValue.addr (.base ⟨slbMsgPtr⟩), .addr (.base ⟨slbMsg2Ptr⟩)]
      ++ List.replicate (hhCap c₄ - 2) .nil⟩
    (fun σ v => absMessage σ v) 0 2 = _
  rw [sliceElems, slbBackingVal2_head0 c₄]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [slb_post_hb1 ρ σ c₁ c₂ c₄]
  simp only [hbind]
  rw [sliceElems, slbBackingVal2_head1 c₄]
  simp only [hbind]
  rw [slb_post_hb2 ρ σ c₁ c₂ c₄]
  simp only [hbind]
  rfl

/-- The msgsAfterAppend outbox stays EMPTY. -/
theorem slb_post_maa (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    absOutbox (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ "msgsAfterAppend"
      = some [] := by
  kernel_rfl

/-! Untouched-scalar readouts: ALL FOUR raft scalars ride symbolic on
this arm; wrap depth 2 (the two msgs field stores re-normalize the
struct — generator-probed per §4c). -/

theorem slb_post_state (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    fieldReadU64 (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ ⟨"raft.raft"⟩ "state"
      = some (unrm 2 (ρ.ints 3)) := by
  kernel_rfl

theorem slb_post_lead (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    fieldReadU64 (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some (unrm 2 (ρ.ints 2)) := by
  kernel_rfl

theorem slb_post_vote (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    fieldReadU64 (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (unrm 2 (ρ.ints 1)) := by
  kernel_rfl

theorem slb_post_term (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₄ : Nat) :
    fieldReadU64 (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic). -/

/-- **THE stepLeader × MsgBeat DISPATCH-ARM EQUATION** (the leader
side's first arm — the heartbeat round-kind's arm set is now sF/sC/sL
COMPLETE): from the drained `er := stepLeader(r, m)` call at ANY
placement (FrameSim premise), over every consumed 4-choice prefix
(`c₁ c₂ c₃ c₄ :: ch` — three Visit picks and the msgs appendSpill)
whose spill choice leaves room for the second peer's in-place
append
(**`2 ≤ hhCap c₄`, the first choice-VALUE side condition**; the
`c₄ % 32 = 29` complement is the separately-censused RE-SPILL
residual family), the run returns in exactly **3,362 steps** with
four choices consumed, and: the message projects with typ 1
(MsgBeat); the `msgs` outbox gains EXACTLY the two Type-8 heartbeats
to the sorted peers ([specHeartbeat 1 2 0, specHeartbeat 1 3 0] —
send order is pick-order-INDEPENDENT, the sort collapse);
`msgsAfterAppend` stays empty; er = nil; the log view is preserved;
and ALL FOUR raft scalars (state/lead/Vote riding symbolic, Term
concrete) read back unchanged — the leader stays the leader. Side
conditions `hvote`/`hlead`/`hstate`: uint64-range facts for the
surviving symbolic scalars (wrap depth 2). -/
theorem stepLeader_beat_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (hstate : IntKind.normalize .uint64 (ρ.ints 3) = ρ.ints 3)
    (c₁ c₂ c₃ c₄ : Nat) (hcap : 2 ≤ hhCap c₄) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ slbS0) σF) :
    ∃ σFfin,
      stepFnIter 3362 σF (renameConfig r (γC ρ slbC0))
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (slbρ' ρ c₁ c₂ c₄) σ slbS15) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨1, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σFfin.heap (.base ⟨r 68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs"
          = some [specHeartbeat 1 2 0, specHeartbeat 1 3 0]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "state" = some (ρ.ints 3)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ slbS0 = γS (slbρ' ρ c₁ c₂ c₄) σ slbS0 := by kernel_rfl
  have hpreC : γC ρ slbC0 = γC (slbρ' ρ c₁ c₂ c₄) slbC0 := by kernel_rfl
  have hrun : stepFnIter 3362 (γS ρ σ slbS0) (γC ρ slbC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: ch)
      = .ok (.next .stop, γS (slbρ' ρ c₁ c₂ c₄) σ slbS15, ch) := by
    rw [hpre, hpreC]
    exact slb_full_span ρ σ hag c₁ c₂ c₃ c₄ hcap ch
  obtain ⟨σFfin, htF, hs⟩ := span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := slb_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (slb_pre_absRaftLog ρ σ)
  · have h := hs.lookup_some (slb_post_er ρ σ c₁ c₂ c₄)
    have hcell : renameCell r (⟨some (.interface ⟨"error"⟩), .nil⟩ : HeapCell)
        = ⟨some (.interface ⟨"error"⟩), .nil⟩ := rfl
    rw [hcell] at h
    exact h
  · exact absOutbox_ren hs (slb_post_absOutbox ρ σ c₁ c₂ c₄)
  · exact absOutbox_ren hs (slb_post_maa ρ σ c₁ c₂ c₄)
  · exact absRaftLog_ren hs (slb_post_absRaftLog ρ σ c₁ c₂ c₄)
  · have h := slb_post_state ρ σ c₁ c₂ c₄
    rw [unrm_id hstate 2] at h
    exact fieldReadU64_ren hs h
  · have h := slb_post_lead ρ σ c₁ c₂ c₄
    rw [unrm_id hlead 2] at h
    exact fieldReadU64_ren hs h
  · have h := slb_post_vote ρ σ c₁ c₂ c₄
    rw [unrm_id hvote 2] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (slb_post_term ρ σ c₁ c₂ c₄)

/-- The identity-placement corollary. -/
theorem stepLeader_beat_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (hlead : IntKind.normalize .uint64 (ρ.ints 2) = ρ.ints 2)
    (hstate : IntKind.normalize .uint64 (ρ.ints 3) = ρ.ints 3)
    (c₁ c₂ c₃ c₄ : Nat) (hcap : 2 ≤ hhCap c₄) (ch : Choices) :
    ∃ σfin,
      stepFnIter 3362 (γS ρ σ slbS0) (γC ρ slbC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ slbS0) (.addr (.base ⟨52⟩))
          = some ⟨1, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ slbS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs"
          = some [specHeartbeat 1 2 0, specHeartbeat 1 3 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "state" = some (ρ.ints 3)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some (ρ.ints 2)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 69 0) 69 69 [] (γS ρ σ slbS0) (γS ρ σ slbS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 69 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, her, hob, hmaa, hlog1, hst, hl, hv, ht⟩ :=
    stepLeader_beat_eq_alloc ρ σ hag hvote hlead hstate c₁ c₂ c₃ c₄ hcap ch hF
  have hcall : renameConfig (ρT 69 0) (γC ρ slbC0) = γC ρ slbC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h52 : (⟨ρT 69 0 52⟩ : Addr) = ⟨52⟩ := rfl
  have h31 : (⟨ρT 69 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 69 0 32⟩ : Addr) = ⟨32⟩ := rfl
  have h68 : (⟨ρT 69 0 68⟩ : Addr) = ⟨68⟩ := rfl
  rw [h52] at hmsg
  rw [h32] at hlog0 hlog1
  rw [h68] at her
  rw [h31] at hob hmaa hst hl hv ht
  exact ⟨σfin, hrun, hmsg, hlog0, her, hob, hmaa, hlog1, hst, hl, hv, ht⟩

/-! ## §3.3 discharge witness (Vote 7, lead 2, state 2 = leader,
ldT 5; the probe's validated tuple (2, 1, 0, 5) — realized cap
hhCap 5 = 9 ≥ 2). -/

def slbρw : Valuation :=
  { ints := fun i => [0, 7, 2, 2, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem stepLeader_beat_eq_witness :
    ∃ σfin,
      stepFnIter 3362 (γS slbρw wBase slbS0) (γC slbρw slbC0) [2, 1, 0, 5]
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS slbρw wBase slbS0) (.addr (.base ⟨52⟩))
          = some ⟨1, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS slbρw wBase slbS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs"
          = some [specHeartbeat 1 2 0, specHeartbeat 1 3 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "state" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  stepLeader_beat_eq slbρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) 2 1 0 5 (by decide) []

end GoLean.RaftSeam
