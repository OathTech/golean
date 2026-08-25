import GoLeanProofs.Specs.Raft.BlLit
import GoLeanProofs.Specs.Raft.LaEquation

/-!
# A4-U13: THE becomeLeader EQUATION — the last wave-2 becomeX handler,
the SIX-choice span (the largest chain yet: 10 windows / 9 crossings),
and the leader's self-ack through the log-append machinery

**LINEAGE: the `Bf31` reset spine + the `LaEquation` tail, composed.**
Chain (census `BlProbe2/3`, walker-validated; generator `BlGen`
γ-validated at (c₅,c₆) = (0,0)/(3,5)/(31,31) before any theorem):

- W1..W6 [659,183,28,28,28,3]: the state guard (state = 1 CONCRETE —
  the `state == StateFollower` panic guard branches on it, the BPC
  fixture-family precondition pattern), `r.step = stepLeader`,
  `reset(r.Term)` — the TERM-EQUAL branch (Vote SURVIVES symbolic):
  Intn pick (var 5, map at 61) + three Visit picks (vars 6/7/8, map
  at 33) + the range-STOP + the sortSlice COLLAPSE — the Bf31 spine
  verbatim at the becomeLeader placement.
- W7 (4,236): `r.tick`/`r.lead = r.id`/`r.state = StateLeader`,
  `BecomeReplicate`, `pendingConfIndex = lastIndex()`, and
  appendEntry's preamble — `proto.Clone(es[i]).(*pb.Entry)` (the
  U13-consumed typeAssert arms), `entryPayloadSize` conversions (the
  convert-at-defined arm), Term/Index plainpb stores — to the
  `unstable.entries` append spill (the LOG WRITE of the leader's
  EMPTY entry: elems = the cloned-entries array 269, element = the
  clone cell 287).
- Crossing (atoms 0), W8 (83) to the ONE atom read (`len(u.entries)`
  — the la_len class, choice-independent 1), the length crossing,
  W9 (1,096) through the SELF-addressed `send` to the
  `msgsAfterAppend` self-ack spill (message cell 353), crossing
  (atoms 1), W10 (113) to `.next .stop`.

Total **6,466 steps, SIX choices** (∀ streams
`c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch`): the reset picks c₁..c₄
absorbed by the pick vars (uρ'), the two spill capacities by atoms
0/1 (blρA). ZERO new machinery — every crossing is a landed transport
or landed-kit composition.

FIXTURE-FAMILY preconditions (recorded): state = 1 (candidate; the
follower guard), r.Term = 0 (term-equal reset — Vote survives, the
side condition `hvote`), r.id = 1, the one-entry stable log
(lastIndex 1 → the empty entry lands at index 2, TERM 0), empty
outboxes; no static-complement dependence (census: the path reads no
[20,31) cell).
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

/-! ## The fixture (MUST match `artifacts/probe/BlGen.lean`). -/

/-- state CONCRETE 1 (candidate), Vote/lead/ldT symbolic (vars 1/2/4)
— the BC pattern at state = 1. -/
def blSymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (renameValue shBfc (uRaftVal 0 0 1 0)))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def blSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 1 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (renameLoc shBfc l, .mk c.declaredTy blSymRaft)
    else (renameLoc shBfc l,
      .mk c.declaredTy (embedGo (renameValue shBfc c.value))))

def blS0 : SymState := { heap := blSymHeap, nextAddr := 52 }

/-- The drained call configuration of `becomeLeader()` (receiver
only). -/
def blC0 : SymConfig :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomeLeader"⟩ [] [] [] [] .stop)

def blCap (c : Nat) : Nat := appendRealizedCap 0 1 (c % 32)

/-- Backing 1 (the log write): the CLONED empty entry (cell 287). -/
def blBacking1 (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨287⟩)] ++ List.replicate (blCap c - 1) .nil⟩

/-- Backing 2 (the self-ack): the response message (cell 353). -/
def blBacking2 (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨353⟩)] ++ List.replicate (blCap c - 1) .nil⟩

/-- The spill-absorbing valuation extension (atoms 0/1; the pick vars
ride to `uρ'`). -/
def blρA (ρ : Valuation) (c₅ c₆ : Nat) : Valuation :=
  { ρ with
    vals := fun i =>
      if i = 0 then .slice ⟨some (.base ⟨329⟩), 0, 1, blCap c₅⟩
      else if i = 1 then .slice ⟨some (.base ⟨396⟩), 0, 1, blCap c₆⟩
      else ρ.vals i,
    cells := fun i =>
      if i = 0 then ⟨some (.array (blCap c₅) (.pointer (.defined ⟨"raftpb.Entry"⟩))), blBacking1 c₅⟩
      else if i = 1 then ⟨some (.array (blCap c₆) (.pointer (.defined ⟨"raftpb.Message"⟩))), blBacking2 c₆⟩
      else ρ.cells i }

/-- The full prefix-derived valuation (picks + spills). -/
def blρ' (ρ : Valuation) (c₁ c₂ c₃ c₅ c₆ : Nat) : Valuation :=
  uρ' (blρA ρ c₅ c₆) c₁ c₂ c₃

/-! ## The crossing outputs (derived from the literals — the Bf31
pattern). -/

def blP2 : SymState × SymConfig := uCrossPick 5 .int blS1 blC1
def blS2 : SymState := blP2.1
def blC2 : SymConfig := blP2.2
def blP4 : SymState × SymConfig := uCrossPick 6 .uint64 blS3 blC3
def blS4 : SymState := blP4.1
def blC4 : SymConfig := blP4.2
def blP6 : SymState × SymConfig := uCrossPick 7 .uint64 blS5 blC5
def blS6 : SymState := blP6.1
def blC6 : SymConfig := blP6.2
def blP8 : SymState × SymConfig := uCrossPick 8 .uint64 blS7 blC7
def blS8 : SymState := blP8.1
def blC8 : SymConfig := blP8.2
def blP10 : SymState × SymConfig := uCrossStop blS9 blC9
def blS10 : SymState := blP10.1
def blC10 : SymConfig := blP10.2
def blP12 : SymState × SymConfig := uCrossSort blS11 blC11
def blS12 : SymState := blP12.1
def blC12 : SymConfig := blP12.2

def blK13 : GoLean.Sym.Cont symDom := match blC13 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def blE13 : LocalEnv := match blC13 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []
def blKLen : GoLean.Sym.Cont symDom := match blC15 with
  | .retV _ (.strictK _ _ _ _ k') => k'
  | _ => .stop
def blE15 : LocalEnv := match blC15 with
  | .retV _ (.strictK _ _ _ e _) => e
  | _ => []
def blK17 : GoLean.Sym.Cont symDom := match blC17 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def blE17 : LocalEnv := match blC17 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

/-! ## The window LINK theorems (kernel — the drift alarms). -/

theorem blW1_out : symEvalWindowTB bfTB 659 blS0 blC0 = (659, blS1, blC1) := by
  kernel_rfl
theorem blW2_out : symEvalWindowTB bfTB 183 blS2 blC2 = (183, blS3, blC3) := by
  kernel_rfl
theorem blW3_out : symEvalWindowTB bfTB 28 blS4 blC4 = (28, blS5, blC5) := by
  kernel_rfl
theorem blW4_out : symEvalWindowTB bfTB 28 blS6 blC6 = (28, blS7, blC7) := by
  kernel_rfl
theorem blW5_out : symEvalWindowTB bfTB 28 blS8 blC8 = (28, blS9, blC9) := by
  kernel_rfl
theorem blW6_out : symEvalWindowTB bfTB 3 blS10 blC10 = (3, blS11, blC11) := by
  kernel_rfl
theorem blW7_out : symEvalWindowTB bfTB 4236 blS12 blC12 = (4236, blS13, blC13) := by
  kernel_rfl
theorem blW8_out : symEvalWindowTB bfTB 83 blS14 (.next blK13) = (83, blS15, blC15) := by
  kernel_rfl
theorem blW9_out : symEvalWindowTB bfTB 1096 blS15
    (.retV (.int (.lit 1) .int) blKLen) = (1096, blS17, blC17) := by
  kernel_rfl
theorem blW10_out : symEvalWindowTB bfTB 113 blS18 (.next blK17)
    = (113, blS19, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem blWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 659 (γS ρ σ blS0) (γC ρ blC0) ch
      = .ok (γC ρ blC1, γS ρ σ blS1, ch) :=
  symEvalWindowTB_refines blW1_out ρ σ ch hag

theorem blWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 183 (γS ρ σ blS2) (γC ρ blC2) ch
      = .ok (γC ρ blC3, γS ρ σ blS3, ch) :=
  symEvalWindowTB_refines blW2_out ρ σ ch hag

theorem blWin3 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ blS4) (γC ρ blC4) ch
      = .ok (γC ρ blC5, γS ρ σ blS5, ch) :=
  symEvalWindowTB_refines blW3_out ρ σ ch hag

theorem blWin4 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ blS6) (γC ρ blC6) ch
      = .ok (γC ρ blC7, γS ρ σ blS7, ch) :=
  symEvalWindowTB_refines blW4_out ρ σ ch hag

theorem blWin5 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 28 (γS ρ σ blS8) (γC ρ blC8) ch
      = .ok (γC ρ blC9, γS ρ σ blS9, ch) :=
  symEvalWindowTB_refines blW5_out ρ σ ch hag

theorem blWin6 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 3 (γS ρ σ blS10) (γC ρ blC10) ch
      = .ok (γC ρ blC11, γS ρ σ blS11, ch) :=
  symEvalWindowTB_refines blW6_out ρ σ ch hag

theorem blWin7 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 4236 (γS ρ σ blS12) (γC ρ blC12) ch
      = .ok (γC ρ blC13, γS ρ σ blS13, ch) :=
  symEvalWindowTB_refines blW7_out ρ σ ch hag

theorem blWin8 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 83 (γS ρ σ blS14) (γC ρ (.next blK13)) ch
      = .ok (γC ρ blC15, γS ρ σ blS15, ch) :=
  symEvalWindowTB_refines blW8_out ρ σ ch hag

theorem blWin9 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 1096 (γS ρ σ blS15) (γC ρ (.retV (.int (.lit 1) .int) blKLen)) ch
      = .ok (γC ρ blC17, γS ρ σ blS17, ch) :=
  symEvalWindowTB_refines blW9_out ρ σ ch hag

theorem blWin10 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 113 (γS ρ σ blS18) (γC ρ (.next blK17)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ blS19, ch) :=
  symEvalWindowTB_refines blW10_out ρ σ ch hag

/-! ## Site 1 — the Intn pick (map keys 0..9 at base 61, `x₅`). -/

def blB1 : Stmt := match blC1 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def blE1 : LocalEnv := match blC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def blK1 : GoLean.Sym.Cont symDom := match blC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def blStart1 : Array SymValue := match blC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem blC1_shape : blC1 = .next (.mapIterK (some "k") none uTyU uTySt
    blB1 (some (.base ⟨61⟩)) #[] blStart1 blE1 blK1) := by
  kernel_rfl

theorem blS2_eq : blS2 = (blS1.alloc uKeyV1 (some uTyU)).2 := by
  unfold blS2 blP2
  rw [blC1_shape]
  rfl

theorem blC2_eq : blC2 = .exec blB1
    ((blE1.pushScope).declare "k" (blS1.alloc uKeyV1 (some uTyU)).1)
    (.mapIterK (some "k") none uTyU uTySt blB1 (some (.base ⟨61⟩))
      (Array.push #[] uKeyV1) blStart1 blE1 blK1) := by
  unfold blC2 blP2
  rw [blC1_shape]
  rfl

theorem blEntries1 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ blS1) (some (.base ⟨61⟩))
      = .ok uCands1 := by
  kernel_rfl

theorem blCands1_fact (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) :
    mapIterCandidates (γS ρ σ blS1) uTyU uTySt (some (.base ⟨61⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok uCands1 := by
  have ht : (γS ρ σ blS1).types = bfTB.types := hag.1
  simp only [mapIterCandidates, blEntries1 ρ σ, Bind.bind, Except.bind, ht]
  with_unfolding_all rfl

theorem blPick1_step (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (b c d : Int) (c₁ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ blS1)
      (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) blC1) (c₁ :: rest)
      = .ok (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) blC2,
          γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ blS2, rest) := by
  have h10 : c₁ % 10 < 10 := Nat.mod_lt _ (by decide)
  rw [blC1_shape, blC2_eq, blS2_eq]
  refine stepFn_pick_transport _ σ (blCands1_fact _ σ hag)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    ?_ (uCands1_get _ h10) (by with_unfolding_all rfl) ?_
  · show Choices.consume (c₁ :: rest) (uCands1.size + _) = _
    simp only [Choices.consume]
    rfl
  · have hn := normalize_small .int ((c₁ : Int) % 10)
      (by omega) (by omega)
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [normalizeValueForTyFuel, hn, uTyU]

/-! ## Site 2 — Visit pick 1 (map at 33, `x₆ = uKey1 c₂`). -/

def blB3 : Stmt := match blC3 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def blE3 : LocalEnv := match blC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def blK3 : GoLean.Sym.Cont symDom := match blC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def blStart3 : Array SymValue := match blC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem blC3_shape : blC3 = .next (.mapIterK (some "id") none uTyK uTyProg
    blB3 (some (.base ⟨33⟩)) #[] blStart3 blE3 blK3) := by
  kernel_rfl

theorem blS4_eq : blS4 = (blS3.alloc uKeyV2 (some uTyK)).2 := by
  unfold blS4 blP4
  rw [blC3_shape]
  rfl

theorem blC4_eq : blC4 = .exec blB3
    ((blE3.pushScope).declare "id" (blS3.alloc uKeyV2 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg blB3 (some (.base ⟨33⟩))
      (Array.push #[] uKeyV2) blStart3 blE3 blK3) := by
  unfold blC4 blP4
  rw [blC3_shape]
  rfl

theorem blEntries3 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ blS3) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem blCands3_fact (ρ : Valuation) (σ : ExecState) :
    mapIterCandidates (γS ρ σ blS3) uTyK uTyProg (some (.base ⟨33⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok bc31Cands3 := by
  simp only [mapIterCandidates, blEntries3 ρ σ, Bind.bind, Except.bind]
  with_unfolding_all rfl

theorem blPick2_step (ρ : Valuation) (σ : ExecState)
    (a c d : Int) (c₂ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) c d) σ blS3)
      (γC (uρ ρ a (uKey1 c₂) c d) blC3) (c₂ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) c d) blC4,
          γS (uρ ρ a (uKey1 c₂) c d) σ blS4, rest) := by
  have h3 : c₂ % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [blC3_shape, blC4_eq, blS4_eq]
  refine stepFn_pick_transport _ σ (blCands3_fact _ σ)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    ?_ (bc31Cands3_get _ h3) (by with_unfolding_all rfl) ?_
  · show Choices.consume (c₂ :: rest) (bc31Cands3.size + _) = _
    simp only [Choices.consume]
    rfl
  · have hn := normalize_small .uint64 ((c₂ : Int) % 3 + 1)
      (by omega) (by omega)
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [normalizeValueForTyFuel, hn, uTyK]

/-! ## Site 3 — Visit pick 2 (`x₇ = uKey2 c₂ c₃`; 6-leaf analysis). -/

theorem blC5_shape : blC5 = .next (.mapIterK (some "id") none uTyK uTyProg
    blB3 (some (.base ⟨33⟩)) #[uKeyV2] blStart3 blE3 blK3) := by
  kernel_rfl

theorem blS6_eq : blS6 = (blS5.alloc uKeyV3 (some uTyK)).2 := by
  unfold blS6 blP6
  rw [blC5_shape]
  rfl

theorem blC6_eq : blC6 = .exec blB3
    ((blE3.pushScope).declare "id" (blS5.alloc uKeyV3 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg blB3 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2] uKeyV3) blStart3 blE3 blK3) := by
  unfold blC6 blP6
  rw [blC5_shape]
  rfl

theorem blEntries5 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ blS5) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem blPick3_step (ρ : Valuation) (σ : ExecState)
    (a d : Int) (c₂ c₃ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) σ blS5)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) blC5) (c₃ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) blC6,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) σ blS6, rest) := by
  rw [blC5_shape, blC6_eq, blS6_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₃ % 2, rest) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₃ % 2, rest) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₃ % 2, rest) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₃ % 2, rest) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₃ % 2, rest) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₃ % 2, rest) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl

/-! ## Site 4 — Visit pick 3 (`x₈ = uKey3`, the leftover; width 1). -/

theorem blC7_shape : blC7 = .next (.mapIterK (some "id") none uTyK uTyProg
    blB3 (some (.base ⟨33⟩)) #[uKeyV2, uKeyV3] blStart3 blE3 blK3) := by
  kernel_rfl

theorem blS8_eq : blS8 = (blS7.alloc uKeyV4 (some uTyK)).2 := by
  unfold blS8 blP8
  rw [blC7_shape]
  rfl

theorem blC8_eq : blC8 = .exec blB3
    ((blE3.pushScope).declare "id" (blS7.alloc uKeyV4 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg blB3 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2, uKeyV3] uKeyV4) blStart3 blE3 blK3) := by
  unfold blC8 blP8
  rw [blC7_shape]
  rfl

theorem blEntries7 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ blS7) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem blPick4_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ c₄ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ blS7)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) blC7)
      (c₄ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) blC8,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ blS8,
          rest) := by
  rw [blC7_shape, blC8_eq, blS8_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₄ % 1, rest) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₄ % 1, rest) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₄ % 1, rest) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₄ % 1, rest) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₄ % 1, rest) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, blEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [Choices.consume]
      change (c₄ % 1, rest) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl

/-! ## The range-Stop crossing: whole-step kernel facts per leaf. -/

theorem blStop_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ blS9) (γC (uρ ρ a 1 2 3) blC9) ch
      = .ok (γC (uρ ρ a 1 2 3) blC10, γS (uρ ρ a 1 2 3) σ blS10, ch) := by
  kernel_rfl

theorem blStop_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ blS9) (γC (uρ ρ a 1 3 2) blC9) ch
      = .ok (γC (uρ ρ a 1 3 2) blC10, γS (uρ ρ a 1 3 2) σ blS10, ch) := by
  kernel_rfl

theorem blStop_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ blS9) (γC (uρ ρ a 2 1 3) blC9) ch
      = .ok (γC (uρ ρ a 2 1 3) blC10, γS (uρ ρ a 2 1 3) σ blS10, ch) := by
  kernel_rfl

theorem blStop_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ blS9) (γC (uρ ρ a 2 3 1) blC9) ch
      = .ok (γC (uρ ρ a 2 3 1) blC10, γS (uρ ρ a 2 3 1) σ blS10, ch) := by
  kernel_rfl

theorem blStop_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ blS9) (γC (uρ ρ a 3 1 2) blC9) ch
      = .ok (γC (uρ ρ a 3 1 2) blC10, γS (uρ ρ a 3 1 2) σ blS10, ch) := by
  kernel_rfl

theorem blStop_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ blS9) (γC (uρ ρ a 3 2 1) blC9) ch
      = .ok (γC (uρ ρ a 3 2 1) blC10, γS (uρ ρ a 3 2 1) σ blS10, ch) := by
  kernel_rfl

theorem blStop_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ blS9)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) blC9) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) blC10,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ blS10,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blStop_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blStop_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blStop_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blStop_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blStop_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blStop_leaf_21 ρ σ a ch

/-! ## The range-Sort crossing: whole-step kernel facts per leaf. -/

theorem blSort_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ blS11) (γC (uρ ρ a 1 2 3) blC11) ch
      = .ok (γC (uρ ρ a 1 2 3) blC12, γS (uρ ρ a 1 2 3) σ blS12, ch) := by
  kernel_rfl

theorem blSort_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ blS11) (γC (uρ ρ a 1 3 2) blC11) ch
      = .ok (γC (uρ ρ a 1 3 2) blC12, γS (uρ ρ a 1 3 2) σ blS12, ch) := by
  kernel_rfl

theorem blSort_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ blS11) (γC (uρ ρ a 2 1 3) blC11) ch
      = .ok (γC (uρ ρ a 2 1 3) blC12, γS (uρ ρ a 2 1 3) σ blS12, ch) := by
  kernel_rfl

theorem blSort_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ blS11) (γC (uρ ρ a 2 3 1) blC11) ch
      = .ok (γC (uρ ρ a 2 3 1) blC12, γS (uρ ρ a 2 3 1) σ blS12, ch) := by
  kernel_rfl

theorem blSort_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ blS11) (γC (uρ ρ a 3 1 2) blC11) ch
      = .ok (γC (uρ ρ a 3 1 2) blC12, γS (uρ ρ a 3 1 2) σ blS12, ch) := by
  kernel_rfl

theorem blSort_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ blS11) (γC (uρ ρ a 3 2 1) blC11) ch
      = .ok (γC (uρ ρ a 3 2 1) blC12, γS (uρ ρ a 3 2 1) σ blS12, ch) := by
  kernel_rfl

theorem blSort_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ blS11)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) blC11) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) blC12,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ blS12,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blSort_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blSort_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blSort_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blSort_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blSort_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact blSort_leaf_21 ρ σ a ch

/-! ## CROSSING 7 — the log-write spill (atoms 0; elems = the
cloned-entries array 269, element = the clone cell 287, target temp
328, backing born at 329). -/

theorem blC13_shape : blC13 = .retV (.slice ⟨some (.base ⟨269⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice laElemTyE) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨328⟩)] [] blE13 blK13) := by
  kernel_rfl

theorem bl_spill1_step (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) (rest : Choices) :
    stepFn (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13)
      (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) blC13) (c₅ :: rest)
      = .ok (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) (.next blK13),
          γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS14, rest) := by
  have hvisE : sliceVisibleValues (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13)
      ⟨some (.base ⟨269⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨287⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₅ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₅ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13)
      laElemTyE #[] #[.addr (.base ⟨287⟩)]
      (appendRealizedCap 0 (0 + 1) (c₅ % 32))
      = .ok (blBacking1 c₅) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨287⟩)],
        normalizeValueForTy (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13) laElemTyE v
          = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13) laElemTyE
        = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13) (elem := laElemTyE)
      (l₁ := []) (l₂ := [.addr (.base ⟨287⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₅ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₅ % 32))
    simpa [blBacking1, blCap] using h
  have htgt : storeLoc { γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13 with
        heap := GoCore.Heap.set (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13).heap
          (.base ⟨(γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₅ % 32)) laElemTyE),
           blBacking1 c₅⟩,
        nextAddr := (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13).nextAddr + 1 }
      (.base ⟨328⟩)
      (.slice ⟨some (.base ⟨(γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS13).nextAddr⟩),
        0, 0 + 1, appendRealizedCap 0 (0 + 1) (c₅ % 32)⟩)
      = .ok (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS14) := by
    kernel_rfl
  rw [blC13_shape]
  exact stepFn_appendSpill_transport (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## CROSSING 8 — `len(u.entries)` on the atom handle (the la_len
class; landed-kit composition, choice-independent result 1). -/

theorem blC15_shape : blC15 = .retV (.atom 0)
    (.strictK (.lengthOf (some (.slice laElemTyE))) [] [] blE15 blKLen) := by
  kernel_rfl

theorem bl_len_step (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) (ch : Choices) :
    stepFn (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS15)
      (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) blC15) ch
      = .ok (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) (.retV (.int (.lit 1) .int) blKLen),
             γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS15, ch) := by
  have h1 : γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) blC15
      = .retV (.slice ⟨some (.base ⟨329⟩), 0, 1, blCap c₅⟩)
          (.strictK (.lengthOf (some (.slice laElemTyE))) [] [] blE15
            (concK (symInterp (blρ' ρ c₁ c₂ c₃ c₅ c₆)) blKLen)) := by
    kernel_rfl
  have h2 : γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) (.retV (.int (.lit 1) .int) blKLen)
      = .retV (.int 1 .int) (concK (symInterp (blρ' ρ c₁ c₂ c₃ c₅ c₆)) blKLen) := by
    kernel_rfl
  rw [h1, h2]
  exact stepFn_strict_apply (applyStrictOp_len_slice
    (by simpa [blCap] using appendRealizedCap_lower 0 (0 + 1) (c₅ % 32)))

/-! ## CROSSING 9 — the self-ack spill (atoms 1; elems 394, response
message 353, target 395, backing born at 396). -/

theorem blC17_shape : blC17 = .retV (.slice ⟨some (.base ⟨394⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice laElemTyM) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨395⟩)] [] blE17 blK17) := by
  kernel_rfl

theorem bl_spill2_step (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) (rest : Choices) :
    stepFn (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17)
      (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) blC17) (c₆ :: rest)
      = .ok (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) (.next blK17),
          γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS18, rest) := by
  have hvisE : sliceVisibleValues (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17)
      ⟨some (.base ⟨394⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨353⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₆ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₆ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17)
      laElemTyM #[] #[.addr (.base ⟨353⟩)]
      (appendRealizedCap 0 (0 + 1) (c₆ % 32))
      = .ok (blBacking2 c₆) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨353⟩)],
        normalizeValueForTy (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17) laElemTyM v
          = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17) laElemTyM
        = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17) (elem := laElemTyM)
      (l₁ := []) (l₂ := [.addr (.base ⟨353⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₆ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₆ % 32))
    simpa [blBacking2, blCap] using h
  have htgt : storeLoc { γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17 with
        heap := GoCore.Heap.set (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17).heap
          (.base ⟨(γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₆ % 32)) laElemTyM),
           blBacking2 c₆⟩,
        nextAddr := (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17).nextAddr + 1 }
      (.base ⟨395⟩)
      (.slice ⟨some (.base ⟨(γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS17).nextAddr⟩),
        0, 0 + 1, appendRealizedCap 0 (0 + 1) (c₆ % 32)⟩)
      = .ok (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS18) := by
    kernel_rfl
  rw [blC17_shape]
  exact stepFn_appendSpill_transport (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 6,466-step span. -/

theorem bl_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ c₅ c₆ : Nat) (ch : Choices) :
    stepFnIter 6466 (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS0)
      (γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) blC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch)
      = .ok (.next .stop, γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19, ch) := by
  have w1 := fun chx => blWin1 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w2 := fun chx => blWin2 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w3 := fun chx => blWin3 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w4 := fun chx => blWin4 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w5 := fun chx => blWin5 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w6 := fun chx => blWin6 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w7 := fun chx => blWin7 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w8 := fun chx => blWin8 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w9 := fun chx => blWin9 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have w10 := fun chx => blWin10 (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ chx hag
  have p1 := blPick1_step (blρA ρ c₅ c₆) σ hag (uKey1 c₂) (uKey2 c₂ c₃)
    (uKey3 c₂ c₃) c₁ (c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch)
  have p2 := blPick2_step (blρA ρ c₅ c₆) σ ((c₁ % 10 : Nat) : Int)
    (uKey2 c₂ c₃) (uKey3 c₂ c₃) c₂ (c₃ :: c₄ :: c₅ :: c₆ :: ch)
  have p3 := blPick3_step (blρA ρ c₅ c₆) σ ((c₁ % 10 : Nat) : Int)
    (uKey3 c₂ c₃) c₂ c₃ (c₄ :: c₅ :: c₆ :: ch)
  have p4 := blPick4_step (blρA ρ c₅ c₆) σ ((c₁ % 10 : Nat) : Int)
    c₂ c₃ c₄ (c₅ :: c₆ :: ch)
  have pstop := blStop_step (blρA ρ c₅ c₆) σ ((c₁ % 10 : Nat) : Int)
    c₂ c₃ (c₅ :: c₆ :: ch)
  have psort := blSort_step (blρA ρ c₅ c₆) σ ((c₁ % 10 : Nat) : Int)
    c₂ c₃ (c₅ :: c₆ :: ch)
  have sp1 := bl_spill1_step ρ σ c₁ c₂ c₃ c₅ c₆ (c₆ :: ch)
  have plen := bl_len_step ρ σ c₁ c₂ c₃ c₅ c₆ (c₆ :: ch)
  have sp2 := bl_spill2_step ρ σ c₁ c₂ c₃ c₅ c₆ ch
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
                              (GoLean.Surface.stepFnIter_chain
                                (GoLean.Surface.stepFnIter_chain
                                  (GoLean.Surface.stepFnIter_chain
                                    (GoLean.Surface.stepFnIter_chain
                                      (w1 (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch))
                                      (GoLean.Surface.stepFnIter_one p1))
                                    (w2 (c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch)))
                                  (GoLean.Surface.stepFnIter_one p2))
                                (w3 (c₃ :: c₄ :: c₅ :: c₆ :: ch)))
                              (GoLean.Surface.stepFnIter_one p3))
                            (w4 (c₄ :: c₅ :: c₆ :: ch)))
                          (GoLean.Surface.stepFnIter_one p4))
                        (w5 (c₅ :: c₆ :: ch)))
                      (GoLean.Surface.stepFnIter_one pstop))
                    (w6 (c₅ :: c₆ :: ch)))
                  (GoLean.Surface.stepFnIter_one psort))
                (w7 (c₅ :: c₆ :: ch)))
              (GoLean.Surface.stepFnIter_one sp1))
            (w8 (c₆ :: ch)))
          (GoLean.Surface.stepFnIter_one plen))
        (w9 (c₆ :: ch)))
      (GoLean.Surface.stepFnIter_one sp2))
    (w10 ch)
  have hstop : γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) (.next .stop)
      = Machine.Config.next .stop := rfl
  rw [← hstop]
  exact h

/-! ## The fixture family's log views: the leader's EMPTY entry at
(index 2, TERM 0). -/

def blAbsLogPost : AbsLog := ⟨[(1, 1)], [(2, 0)], 2, 1, 1, 1⟩

/-- **THE LOG GREW BY THE LEADER'S EMPTY ENTRY** (index 2, term 0 =
r.Term); nothing else moves. Axiom-free spec-side fact. -/
theorem bl_log_grew :
    AbsLog.view blAbsLogPost = AbsLog.view hhAbsLog ++ [(2, 0)]
      ∧ AbsLog.lastIndex blAbsLogPost = some 2
      ∧ blAbsLogPost.stable = hhAbsLog.stable
      ∧ blAbsLogPost.committed = hhAbsLog.committed := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Projection facts at the literals. -/

theorem bl_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ blS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem bl_post_absRaftLog (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    absRaftLog (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨32⟩
      = some blAbsLogPost := by
  kernel_rfl

theorem bl_post_maa_field (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    fieldRead (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ ⟨"raft.raft"⟩
      "msgsAfterAppend"
      = some (.slice ⟨some (.base ⟨396⟩), 0, 1, blCap c₆⟩) := by
  kernel_rfl

theorem bl_post_backing (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    GoCore.Heap.lookup (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19).heap
      (.base ⟨396⟩)
      = some ⟨some (.array (blCap c₆) laElemTyM), blBacking2 c₆⟩ := by
  kernel_rfl

/-- The self-ack record: **To = From = r.id = 1, Index = 2** (the
appended entry's index) — the leader acks its own append into the
async-storage group. -/
theorem bl_post_respMsg (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    absMessage (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) (.addr (.base ⟨353⟩))
      = some (specAppResp 1 1 0 2) := by
  kernel_rfl

theorem blBacking2_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨353⟩)] ++ List.replicate (blCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨353⟩)) := by
  rw [List.cons_append]
  rfl

/-- **THE OUTBOX READOUT**, by lemma composition (no window
re-evaluation, no per-choice case split). -/
theorem bl_post_absOutbox (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    absOutbox (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ "msgsAfterAppend"
      = some [specAppResp 1 1 0 2] := by
  rw [absOutbox]
  rw [bl_post_maa_field ρ σ c₁ c₂ c₃ c₅ c₆]
  show sliceRead (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19)
    (.slice ⟨some (.base ⟨396⟩), 0, 1, blCap c₆⟩) _ = _
  rw [sliceRead]
  rw [bl_post_backing ρ σ c₁ c₂ c₃ c₅ c₆]
  show sliceElems (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19)
    ⟨[GoValue.addr (.base ⟨353⟩)] ++ List.replicate (blCap c₆ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, blBacking2_head c₆]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [bl_post_respMsg ρ σ c₁ c₂ c₃ c₅ c₆]
  simp only [hbind]
  rfl

/-- Vote survives the term-equal reset SYMBOLIC, wrapped by the
store-time re-normalizations (depth 16, probed at the literal). -/
theorem bl_post_vote (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    fieldReadU64 (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ ⟨"raft.raft"⟩
      "Vote" = some (unrm 16 (ρ.ints 1)) := by
  kernel_rfl

theorem bl_post_lead (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    fieldReadU64 (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ ⟨"raft.raft"⟩
      "lead" = some 1 := by
  kernel_rfl

theorem bl_post_state (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    fieldReadU64 (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ ⟨"raft.raft"⟩
      "state" = some 2 := by
  kernel_rfl

theorem bl_post_pci (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    fieldReadU64 (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ ⟨"raft.raft"⟩
      "pendingConfIndex" = some 1 := by
  kernel_rfl

theorem bl_post_term (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ c₆ : Nat) :
    fieldReadU64 (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ ⟨"raft.raft"⟩
      "Term" = some 0 := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic; the sim plumbing =
the LIFTED `Frame.span_relocate` — fourth consumer). -/

/-- **THE becomeLeader EQUATION**: from the drained `becomeLeader()`
call at ANY placement of the fixture footprint, over EVERY consumed
choice prefix (∀ streams `c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch` —
the reset's Intn + three Visit picks, then the log-write and
self-ack spill capacities), the run returns in exactly **6,466
steps** with six choices consumed, and: the log view GROWS by the
leader's EMPTY entry (pre `hhAbsLog`, post `blAbsLogPost` — the
unstable overlay `[(2,0)]`; `bl_log_grew`); the outbox gains EXACTLY
the SELF-ack (`absOutbox "msgsAfterAppend"` = `[specAppResp 1 1 0 2]`
— To = From = r.id, Index = the appended index); `msgs` stays empty;
Vote SURVIVES symbolic (`hvote` collapses the 16-deep store-time
norm-wrap); lead = r.id = 1; **state = 2 (StateLeader)** — the
transition readout; pendingConfIndex = lastIndex-at-entry = 1;
Term = 0 (term-equal reset). -/
theorem becomeLeader_handler_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (c₁ c₂ c₃ c₄ c₅ c₆ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ blS0) σF) :
    ∃ σFfin,
      stepFnIter 6466 σF (renameConfig r (γC ρ blC0))
        (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) σFfin
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some [specAppResp 1 1 0 2]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some blAbsLogPost
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some 1
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "state" = some 2
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "pendingConfIndex" = some 1
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ blS0 = γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS0 := by
    kernel_rfl
  have hpreC : γC ρ blC0 = γC (blρ' ρ c₁ c₂ c₃ c₅ c₆) blC0 := by
    kernel_rfl
  have hrun : stepFnIter 6466 (γS ρ σ blS0) (γC ρ blC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch)
      = .ok (.next .stop, γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19, ch) := by
    rw [hpre, hpreC]
    exact bl_full_span ρ σ hag c₁ c₂ c₃ c₄ c₅ c₆ ch
  obtain ⟨σFfin, htF, hs⟩ := GoLean.Frame.span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact absRaftLog_ren hF (bl_pre_absRaftLog ρ σ)
  · exact absOutbox_ren hs (bl_post_absOutbox ρ σ c₁ c₂ c₃ c₅ c₆)
  · exact absOutbox_ren hs (show absOutbox
      (γS (blρ' ρ c₁ c₂ c₃ c₅ c₆) σ blS19) ⟨31⟩ "msgs" = some []
      by kernel_rfl)
  · exact absRaftLog_ren hs (bl_post_absRaftLog ρ σ c₁ c₂ c₃ c₅ c₆)
  · have h := bl_post_vote ρ σ c₁ c₂ c₃ c₅ c₆
    rw [unrm_id hvote 16] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (bl_post_lead ρ σ c₁ c₂ c₃ c₅ c₆)
  · exact fieldReadU64_ren hs (bl_post_state ρ σ c₁ c₂ c₃ c₅ c₆)
  · exact fieldReadU64_ren hs (bl_post_pci ρ σ c₁ c₂ c₃ c₅ c₆)
  · exact fieldReadU64_ren hs (bl_post_term ρ σ c₁ c₂ c₃ c₅ c₆)

/-- The identity-placement corollary. -/
theorem becomeLeader_handler_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (c₁ c₂ c₃ c₄ c₅ c₆ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 6466 (γS ρ σ blS0) (γC ρ blC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: c₆ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftLog (γS ρ σ blS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 1 0 2]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some blAbsLogPost
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 1
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "state" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "pendingConfIndex" = some 1
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 52 0) 52 52 [] (γS ρ σ blS0) (γS ρ σ blS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 52 f.body)
  obtain ⟨σfin, hrun, _, hlog0, hob, hobm, hlog1, hv, hl, hst, hp, ht⟩ :=
    becomeLeader_handler_eq_alloc ρ σ hag hvote c₁ c₂ c₃ c₄ c₅ c₆ ch hF
  have hcall : renameConfig (ρT 52 0) (γC ρ blC0) = γC ρ blC0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have h31 : (⟨ρT 52 0 31⟩ : Addr) = ⟨31⟩ := rfl
  have h32 : (⟨ρT 52 0 32⟩ : Addr) = ⟨32⟩ := rfl
  rw [h32] at hlog0 hlog1
  rw [h31] at hob hobm hv hl hst hp ht
  exact ⟨σfin, hrun, hlog0, hob, hobm, hlog1, hv, hl, hst, hp, ht⟩

/-! ## §3.3 discharge witness (the probe's values: Vote 7, lead 2,
ldT 5; stream [3, 1, 0, 0, 3, 5]). -/

def blρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem becomeLeader_handler_eq_witness :
    ∃ σfin,
      stepFnIter 6466 (γS blρw wBase blS0) (γC blρw blC0)
        [3, 1, 0, 0, 3, 5]
        = .ok (.next .stop, σfin, [])
      ∧ absRaftLog (γS blρw wBase blS0) ⟨32⟩ = some hhAbsLog
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some [specAppResp 1 1 0 2]
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some blAbsLogPost
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 1
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "state" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "pendingConfIndex" = some 1
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  becomeLeader_handler_eq blρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) 3 1 0 0 3 5 []

end GoLean.RaftSeam
