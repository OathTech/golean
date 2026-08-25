import GoLeanProofs.Specs.Raft.SCHbLit
import GoLeanProofs.Specs.Raft.Bc31
import GoLeanProofs.Specs.Raft.BfEquation
import GoLeanProofs.Specs.Raft.AbsStateV2

/-!
# A4-U16: THE stepCandidate × MsgHeartbeat DISPATCH-ARM EQUATION —
the first DEPTH-2 arm (bf reset spine + Hh tail under dispatch glue)
and the round lemma's dress rehearsal

**LINEAGE: the Bf31 chain template (4 picks + range-stop + sort
collapse, `stepFn_pick_transport` + the uKey/uCross machinery reused
VERBATIM) composed with the SfHb spill template — 8 windows, 7
crossings, FIVE choices** (`c₁` Intn, `c₂ c₃ c₄` Visit picks, `c₅`
the Hh appendSpill), 4,969 machine steps = the U14/U15 census
exactly. Proof route: the sanctioned literal window chain (§4c; the
U15 composition verdict) — the landed becomeFollower/handleHeartbeat
equations are this arm's VOCABULARY and VALIDATION SET, not mid-walk
sub-proofs.

Probe-validated end-to-end by `artifacts/probe/SCHbGen.lean` BEFORE
any theorem here: windows **[983, 183, 28, 28, 28, 3, 3620, 89]**;
spill operands elems 321 / tgt 322 / backing born 323 / response
message 271 (generator-emitted defs); γ==machine at three full
5-choice tuples ((0,0,0,0,0)/(3,1,1,0,5)/(9,2,1,1,31)).

FIXTURE-FAMILY preconditions (§4c form):
- `m.Type = 8` (MsgHeartbeat) CONCRETE — the switch driver;
- **`r.state = 1` (candidate) CONCRETE** — `stepCandidate` computes
  `myVoteRespType(r.state)` up front (probe: symbolic x₃ quits
  q1Branch at step 20), so the candidate family is state-concrete;
- `m.Term = 0 = r.Term` (the equal-term heartbeat: becomeFollower's
  reset runs its no-term-change branch); `m.From = 2 ≠ r.id`,
  `m.Commit = committed = 1` (the Hh no-op family);
- Vote (x₁) rides symbolic through the WHOLE depth-2 span — stored
  wrap depth **norm¹⁴** (probe `SCDepth`, the §4c read-the-literal
  rule; the becomeFollower spine's stores dominate), collapsed by
  `unrm_id hvote 14`; pre-lead (x₂) and pre-leadTransferee (x₄) are
  DEAD (reset overwrites both).

THE DEPTH-2 HEADLINE CONCLUSIONS: **state 1 → 0** (the candidate
falls back to follower) and **lead := m.From = 2** — the two
dispatch-visible transitions of a heartbeat received mid-candidacy —
plus the same heartbeat response record as the sF arm
(`specHeartbeatResp 1 2 0` into `msgs`), the log view preserved, and
er = nil.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame
open GoLean.SliceMem (appendRealizedCap appendRealizedCap_lower)
open GoLean.Lens

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## The fixture (MUST match `artifacts/probe/SCHbGen.lean`). -/

def scMsgSym : SymValue :=
  .struct ⟨"raftpb.Message"⟩ #[
    ("Type", .addr (.base ⟨55⟩)), ("To", .nil), ("From", .addr (.base ⟨54⟩)),
    ("Term", .nil), ("LogTerm", .nil), ("Index", .nil),
    ("Entries", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Commit", .addr (.base ⟨53⟩)), ("Vote", .nil), ("Snapshot", .nil),
    ("Reject", .nil), ("RejectHint", .nil),
    ("Context", .slice { base := none, offset := 0, len := 0, cap := 0 }),
    ("Responses", .slice { base := none, offset := 0, len := 0, cap := 0 })]

/-- bf31SymHeap with state (x₃) FORCED to concrete 1. -/
def scRaftHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  bf31SymHeap.map (fun (p : Loc × GoLean.Sym.HeapCell symDom) =>
    if p.1 == .base ⟨31⟩ then
      (p.1, match p.2 with
        | .mk dty (.struct tid fs) =>
            .mk dty (.struct tid (fs.map (fun (q : String × SymValue) =>
              if q.1 == "state" then (q.1, .int (.lit 1) .uint64) else q)))
        | c => c)
    else p)

def scS0 : SymState :=
  { heap := scRaftHeap ++
      [(.base ⟨52⟩, .mk (some (.defined ⟨"raftpb.Message"⟩)) scMsgSym),
       (.base ⟨53⟩, .mk (some (.int .uint64)) (.int (.lit 1) .uint64)),
       (.base ⟨54⟩, .mk (some (.int .uint64)) (.int (.lit 2) .uint64)),
       (.base ⟨55⟩, .mk (some (.int .int32)) (.int (.lit 8) .int32)),
       (.base ⟨66⟩, .mk (some (.pointer (.defined ⟨"raft.raft"⟩))) (.addr (.base ⟨31⟩))),
       (.base ⟨67⟩, .mk (some (.pointer (.defined ⟨"raftpb.Message"⟩))) (.addr (.base ⟨52⟩))),
       (.base ⟨68⟩, .mk (some (.interface ⟨"error"⟩)) .nil)],
    nextAddr := 69 }

def scEnv : LocalEnv := [[("r", .base ⟨66⟩), ("m", .base ⟨67⟩), ("er", .base ⟨68⟩)]]

/-- The drained caller shape: `er := raft.stepCandidate(r, m)`. -/
def scC0 : SymConfig :=
  .exec (.call #[.var "er"] ⟨"raft.stepCandidate"⟩ #[Expr.var "r", Expr.var "m"])
    scEnv .stop

/-! ## The crossing outputs (even indices; the Bf31 pattern —
crossings reduce in one step from the generated odd literals). -/

def scP2 : SymState × SymConfig := uCrossPick 5 .int scS1 scC1
def scS2 : SymState := scP2.1
def scC2 : SymConfig := scP2.2
def scP4 : SymState × SymConfig := uCrossPick 6 .uint64 scS3 scC3
def scS4 : SymState := scP4.1
def scC4 : SymConfig := scP4.2
def scP6 : SymState × SymConfig := uCrossPick 7 .uint64 scS5 scC5
def scS6 : SymState := scP6.1
def scC6 : SymConfig := scP6.2
def scP8 : SymState × SymConfig := uCrossPick 8 .uint64 scS7 scC7
def scS8 : SymState := scP8.1
def scC8 : SymConfig := scP8.2
def scP10 : SymState × SymConfig := uCrossStop scS9 scC9
def scS10 : SymState := scP10.1
def scC10 : SymConfig := scP10.2
def scP12 : SymState × SymConfig := uCrossSort scS11 scC11
def scS12 : SymState := scP12.1
def scC12 : SymConfig := scP12.2

/-- The post-spill continuation/env, extracted from the quit config. -/
def scK13 : GoLean.Sym.Cont symDom := match scC13 with
  | .retV _ (.stmtOpK _ _ _ _ _ k') => k'
  | _ => .stop
def scE13 : LocalEnv := match scC13 with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []

/-- The spill crossing's post state (the generator's construction,
restated as a def: target ↦ value-atom 0, backing born as cell-atom
0). -/
def scS14 : SymState :=
  { heap := (GoLean.Sym.Heap.set scS13.heap (.base ⟨scTgt⟩)
      (.mk (some (.slice (.pointer (.defined ⟨"raftpb.Message"⟩)))) (.atom 0)))
      ++ [(.base ⟨scBacking⟩, .atom 0)],
    nextAddr := scBacking + 1 }

/-- The backing-cell payload at spill head `c`. -/
def scBackingVal (c : Nat) : GoValue :=
  .array ⟨[.addr (.base ⟨scMsgPtr⟩)] ++ List.replicate (hhCap c - 1) .nil⟩

/-- The spill-atom absorber (composes with `uρ` — disjoint fields). -/
def scρA (ρ : Valuation) (c : Nat) : Valuation :=
  { ρ with
    vals := fun i => if i = 0
      then .slice ⟨some (.base ⟨scBacking⟩), 0, 1, hhCap c⟩ else ρ.vals i,
    cells := fun i => if i = 0
      then ⟨some (.array (hhCap c) hhElemTy), scBackingVal c⟩
      else ρ.cells i }

/-- The full prefix-derived valuation: pick vars 5-8 (uρ') + the
spill atoms. -/
def scρ' (ρ : Valuation) (c₁ c₂ c₃ c₅ : Nat) : Valuation :=
  uρ' (scρA ρ c₅) c₁ c₂ c₃

/-! ## The window LINK theorems (kernel-checked — the drift alarms). -/

theorem scW1_out : symEvalWindowTB bfTB scW1n scS0 scC0 = (scW1n, scS1, scC1) := by
  kernel_rfl
theorem scW2_out : symEvalWindowTB bfTB scW2n scS2 scC2 = (scW2n, scS3, scC3) := by
  kernel_rfl
theorem scW3_out : symEvalWindowTB bfTB scW3n scS4 scC4 = (scW3n, scS5, scC5) := by
  kernel_rfl
theorem scW4_out : symEvalWindowTB bfTB scW4n scS6 scC6 = (scW4n, scS7, scC7) := by
  kernel_rfl
theorem scW5_out : symEvalWindowTB bfTB scW5n scS8 scC8 = (scW5n, scS9, scC9) := by
  kernel_rfl
theorem scW6_out : symEvalWindowTB bfTB scW6n scS10 scC10 = (scW6n, scS11, scC11) := by
  kernel_rfl
theorem scW7_out : symEvalWindowTB bfTB scW7n scS12 scC12 = (scW7n, scS13, scC13) := by
  kernel_rfl
theorem scW8_out : symEvalWindowTB bfTB scW8n scS14 (.next scK13)
    = (scW8n, scS15, .next .stop) := by
  kernel_rfl

/-! ## The transported windows. -/

theorem scWin1 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW1n (γS ρ σ scS0) (γC ρ scC0) ch
      = .ok (γC ρ scC1, γS ρ σ scS1, ch) :=
  symEvalWindowTB_refines scW1_out ρ σ ch hag
theorem scWin2 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW2n (γS ρ σ scS2) (γC ρ scC2) ch
      = .ok (γC ρ scC3, γS ρ σ scS3, ch) :=
  symEvalWindowTB_refines scW2_out ρ σ ch hag
theorem scWin3 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW3n (γS ρ σ scS4) (γC ρ scC4) ch
      = .ok (γC ρ scC5, γS ρ σ scS5, ch) :=
  symEvalWindowTB_refines scW3_out ρ σ ch hag
theorem scWin4 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW4n (γS ρ σ scS6) (γC ρ scC6) ch
      = .ok (γC ρ scC7, γS ρ σ scS7, ch) :=
  symEvalWindowTB_refines scW4_out ρ σ ch hag
theorem scWin5 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW5n (γS ρ σ scS8) (γC ρ scC8) ch
      = .ok (γC ρ scC9, γS ρ σ scS9, ch) :=
  symEvalWindowTB_refines scW5_out ρ σ ch hag
theorem scWin6 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW6n (γS ρ σ scS10) (γC ρ scC10) ch
      = .ok (γC ρ scC11, γS ρ σ scS11, ch) :=
  symEvalWindowTB_refines scW6_out ρ σ ch hag
theorem scWin7 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW7n (γS ρ σ scS12) (γC ρ scC12) ch
      = .ok (γC ρ scC13, γS ρ σ scS13, ch) :=
  symEvalWindowTB_refines scW7_out ρ σ ch hag
theorem scWin8 (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter scW8n (γS ρ σ scS14) (γC ρ (.next scK13)) ch
      = .ok (γC ρ (.next .stop), γS ρ σ scS15, ch) :=
  symEvalWindowTB_refines scW8_out ρ σ ch hag

/-! ## Site 1 — the Intn pick (map keys 0..9 at born base 96,
`x₅ = ↑(c₁ % 10)`; `uCands1`/`uCands1_get` reused from BfSteps). -/

def scB1 : Stmt := match scC1 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def scE1 : LocalEnv := match scC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def scK1 : GoLean.Sym.Cont symDom := match scC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def scStart1 : Array SymValue := match scC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem scC1_shape : scC1 = .next (.mapIterK (some "k") none uTyU uTySt
    scB1 (some (.base ⟨96⟩)) #[] scStart1 scE1 scK1) := by
  kernel_rfl

theorem scS2_eq : scS2 = (scS1.alloc uKeyV1 (some uTyU)).2 := by
  unfold scS2 scP2
  rw [scC1_shape]
  rfl

theorem scC2_eq : scC2 = .exec scB1
    ((scE1.pushScope).declare "k" (scS1.alloc uKeyV1 (some uTyU)).1)
    (.mapIterK (some "k") none uTyU uTySt scB1 (some (.base ⟨96⟩))
      (Array.push #[] uKeyV1) scStart1 scE1 scK1) := by
  unfold scC2 scP2
  rw [scC1_shape]
  rfl

theorem scEntries1 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ scS1) (some (.base ⟨96⟩))
      = .ok uCands1 := by
  kernel_rfl

theorem scCands1_fact (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) :
    mapIterCandidates (γS ρ σ scS1) uTyU uTySt (some (.base ⟨96⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok uCands1 := by
  have ht : (γS ρ σ scS1).types = bfTB.types := hag.1
  simp only [mapIterCandidates, scEntries1 ρ σ, Bind.bind, Except.bind, ht]
  with_unfolding_all rfl

theorem scPick1_step (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (b c d : Int) (c₁ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ scS1)
      (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) scC1) (c₁ :: rest)
      = .ok (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) scC2,
          γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ scS2, rest) := by
  have h10 : c₁ % 10 < 10 := Nat.mod_lt _ (by decide)
  rw [scC1_shape, scC2_eq, scS2_eq]
  refine stepFn_pick_transport _ σ (scCands1_fact _ σ hag)
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

/-! ## Site 2 — Visit pick 1 (prs map at base 33, `x₆ = uKey1 c₂`;
`bc31Cands3`/`bc31Cands3_get` reused from Bc31). -/

def scB3 : Stmt := match scC3 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def scE3 : LocalEnv := match scC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def scK3 : GoLean.Sym.Cont symDom := match scC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def scStart3 : Array SymValue := match scC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem scC3_shape : scC3 = .next (.mapIterK (some "id") none uTyK uTyProg
    scB3 (some (.base ⟨33⟩)) #[] scStart3 scE3 scK3) := by
  kernel_rfl

theorem scS4_eq : scS4 = (scS3.alloc uKeyV2 (some uTyK)).2 := by
  unfold scS4 scP4
  rw [scC3_shape]
  rfl

theorem scC4_eq : scC4 = .exec scB3
    ((scE3.pushScope).declare "id" (scS3.alloc uKeyV2 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg scB3 (some (.base ⟨33⟩))
      (Array.push #[] uKeyV2) scStart3 scE3 scK3) := by
  unfold scC4 scP4
  rw [scC3_shape]
  rfl

theorem scEntries3 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ scS3) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem scCands3_fact (ρ : Valuation) (σ : ExecState) :
    mapIterCandidates (γS ρ σ scS3) uTyK uTyProg (some (.base ⟨33⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok bc31Cands3 := by
  simp only [mapIterCandidates, scEntries3 ρ σ, Bind.bind, Except.bind]
  with_unfolding_all rfl

theorem scPick2_step (ρ : Valuation) (σ : ExecState)
    (a c d : Int) (c₂ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) c d) σ scS3)
      (γC (uρ ρ a (uKey1 c₂) c d) scC3) (c₂ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) c d) scC4,
          γS (uρ ρ a (uKey1 c₂) c d) σ scS4, rest) := by
  have h3 : c₂ % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [scC3_shape, scC4_eq, scS4_eq]
  refine stepFn_pick_transport _ σ (scCands3_fact _ σ)
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

/-! ## Site 3 — Visit pick 2 (`x₇ = uKey2 c₂ c₃`; 6-leaf case
analysis, the Bf31 pattern). -/

theorem scC5_shape : scC5 = .next (.mapIterK (some "id") none uTyK uTyProg
    scB3 (some (.base ⟨33⟩)) #[uKeyV2] scStart3 scE3 scK3) := by
  kernel_rfl

theorem scS6_eq : scS6 = (scS5.alloc uKeyV3 (some uTyK)).2 := by
  unfold scS6 scP6
  rw [scC5_shape]
  rfl

theorem scC6_eq : scC6 = .exec scB3
    ((scE3.pushScope).declare "id" (scS5.alloc uKeyV3 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg scB3 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2] uKeyV3) scStart3 scE3 scK3) := by
  unfold scC6 scP6
  rw [scC5_shape]
  rfl

theorem scEntries5 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ scS5) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem scPick3_step (ρ : Valuation) (σ : ExecState)
    (a d : Int) (c₂ c₃ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) σ scS5)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) scC5) (c₃ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) scC6,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) σ scS6, rest) := by
  rw [scC5_shape, scC6_eq, scS6_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  all_goals first
  | (rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries5 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₃ % 2, rest) = _
       rw [h3]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)

/-! ## Site 4 — Visit pick 3 (`x₈ = uKey3`, the leftover; width 1). -/

theorem scC7_shape : scC7 = .next (.mapIterK (some "id") none uTyK uTyProg
    scB3 (some (.base ⟨33⟩)) #[uKeyV2, uKeyV3] scStart3 scE3 scK3) := by
  kernel_rfl

theorem scS8_eq : scS8 = (scS7.alloc uKeyV4 (some uTyK)).2 := by
  unfold scS8 scP8
  rw [scC7_shape]
  rfl

theorem scC8_eq : scC8 = .exec scB3
    ((scE3.pushScope).declare "id" (scS7.alloc uKeyV4 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg scB3 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2, uKeyV3] uKeyV4) scStart3 scE3 scK3) := by
  unfold scC8 scP8
  rw [scC7_shape]
  rfl

theorem scEntries7 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ scS7) (some (.base ⟨33⟩))
      = .ok bc31Cands3 := by
  kernel_rfl

theorem scPick4_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ c₄ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ scS7)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) scC7)
      (c₄ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) scC8,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ scS8,
          rest) := by
  rw [scC7_shape, scC8_eq, scS8_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  all_goals first
  | (rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries7 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₄ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries7 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₄ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries7 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₄ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries7 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₄ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries7 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₄ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)
  | (rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
        (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
        (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
     apply stepFn_pick_transport _ σ
     case hcands =>
       simp only [mapIterCandidates, scEntries7 _ σ, Bind.bind, Except.bind]
       with_unfolding_all rfl
     case hne => with_unfolding_all rfl
     case hmand => with_unfolding_all rfl
     case hconsume =>
       simp only [Choices.consume]
       change (c₄ % 1, rest) = _
       rw [Nat.mod_one]
     case hget => with_unfolding_all rfl
     case hkey => with_unfolding_all rfl
     case hnorm => with_unfolding_all rfl)

/-! ## Site 5 — the range STOP (whole-step kernel facts per leaf). -/

theorem scStop_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ scS9) (γC (uρ ρ a 1 2 3) scC9) ch
      = .ok (γC (uρ ρ a 1 2 3) scC10, γS (uρ ρ a 1 2 3) σ scS10, ch) := by
  kernel_rfl
theorem scStop_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ scS9) (γC (uρ ρ a 1 3 2) scC9) ch
      = .ok (γC (uρ ρ a 1 3 2) scC10, γS (uρ ρ a 1 3 2) σ scS10, ch) := by
  kernel_rfl
theorem scStop_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ scS9) (γC (uρ ρ a 2 1 3) scC9) ch
      = .ok (γC (uρ ρ a 2 1 3) scC10, γS (uρ ρ a 2 1 3) σ scS10, ch) := by
  kernel_rfl
theorem scStop_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ scS9) (γC (uρ ρ a 2 3 1) scC9) ch
      = .ok (γC (uρ ρ a 2 3 1) scC10, γS (uρ ρ a 2 3 1) σ scS10, ch) := by
  kernel_rfl
theorem scStop_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ scS9) (γC (uρ ρ a 3 1 2) scC9) ch
      = .ok (γC (uρ ρ a 3 1 2) scC10, γS (uρ ρ a 3 1 2) σ scS10, ch) := by
  kernel_rfl
theorem scStop_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ scS9) (γC (uρ ρ a 3 2 1) scC9) ch
      = .ok (γC (uρ ρ a 3 2 1) scC10, γS (uρ ρ a 3 2 1) σ scS10, ch) := by
  kernel_rfl

theorem scStop_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ scS9)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) scC9) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) scC10,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ scS10,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scStop_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scStop_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scStop_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scStop_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scStop_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scStop_leaf_21 ρ σ a ch

/-! ## Site 6 — the sortSlice COLLAPSE (every leaf's post state is
`scS12`: ids = [1,2,3]). -/

theorem scSort_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ scS11) (γC (uρ ρ a 1 2 3) scC11) ch
      = .ok (γC (uρ ρ a 1 2 3) scC12, γS (uρ ρ a 1 2 3) σ scS12, ch) := by
  kernel_rfl
theorem scSort_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ scS11) (γC (uρ ρ a 1 3 2) scC11) ch
      = .ok (γC (uρ ρ a 1 3 2) scC12, γS (uρ ρ a 1 3 2) σ scS12, ch) := by
  kernel_rfl
theorem scSort_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ scS11) (γC (uρ ρ a 2 1 3) scC11) ch
      = .ok (γC (uρ ρ a 2 1 3) scC12, γS (uρ ρ a 2 1 3) σ scS12, ch) := by
  kernel_rfl
theorem scSort_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ scS11) (γC (uρ ρ a 2 3 1) scC11) ch
      = .ok (γC (uρ ρ a 2 3 1) scC12, γS (uρ ρ a 2 3 1) σ scS12, ch) := by
  kernel_rfl
theorem scSort_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ scS11) (γC (uρ ρ a 3 1 2) scC11) ch
      = .ok (γC (uρ ρ a 3 1 2) scC12, γS (uρ ρ a 3 1 2) σ scS12, ch) := by
  kernel_rfl
theorem scSort_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ scS11) (γC (uρ ρ a 3 2 1) scC11) ch
      = .ok (γC (uρ ρ a 3 2 1) scC12, γS (uρ ρ a 3 2 1) σ scS12, ch) := by
  kernel_rfl

theorem scSort_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ scS11)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) scC11) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) scC12,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ scS12,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scSort_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scSort_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scSort_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scSort_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scSort_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact scSort_leaf_21 ρ σ a ch

/-! ## Site 7 — THE SPILL CROSSING (the SfHb pattern at the depth-2
literals; the choice enters through `scρA`). -/

theorem scC13_shape : scC13 = .retV (.slice ⟨some (.base ⟨scElems⟩), 0, 1, 1⟩)
    (.stmtOpK (.appendSlice hhElemTy) 1
      [.slice ⟨none, 0, 0, 0⟩, .addr (.base ⟨scTgt⟩)] [] scE13 scK13) := by
  kernel_rfl

theorem scSpill_step (ρ : Valuation) (σ : ExecState) (c₅ : Nat)
    (rest : Choices) :
    stepFn (γS (scρA ρ c₅) σ scS13) (γC (scρA ρ c₅) scC13) (c₅ :: rest)
      = .ok (γC (scρA ρ c₅) (.next scK13), γS (scρA ρ c₅) σ scS14, rest) := by
  have hvisE : sliceVisibleValues (γS (scρA ρ c₅) σ scS13)
      ⟨some (.base ⟨scElems⟩), 0, 1, 1⟩ = .ok #[.addr (.base ⟨scMsgPtr⟩)] := by
    kernel_rfl
  have hvisO : sliceVisibleValues (γS (scρA ρ c₅) σ scS13)
      ⟨none, 0, 0, 0⟩ = .ok #[] := by
    kernel_rfl
  have hcons : Choices.consume (c₅ :: rest) (appendSpillWidth 0 (0 + 1))
      = (c₅ % 32, rest) := by
    simp only [Choices.consume]
    rfl
  have hbuild : buildAppendBackingValue (γS (scρA ρ c₅) σ scS13) hhElemTy
      #[] #[.addr (.base ⟨scMsgPtr⟩)] (appendRealizedCap 0 (0 + 1) (c₅ % 32))
      = .ok (scBackingVal c₅) := by
    have hn : ∀ v ∈ ([] : List GoValue) ++ [.addr (.base ⟨scMsgPtr⟩)],
        normalizeValueForTy (γS (scρA ρ c₅) σ scS13) hhElemTy v = .ok v := by
      intro v hv
      simp only [List.nil_append, List.mem_singleton] at hv
      subst hv
      kernel_rfl
    have hd : defaultValue (γS (scρA ρ c₅) σ scS13) hhElemTy = .ok .nil := by
      kernel_rfl
    have h := GoLean.SliceMem.buildAppendBackingValue_of_norm
      (σ := γS (scρA ρ c₅) σ scS13) (elem := hhElemTy)
      (l₁ := []) (l₂ := [.addr (.base ⟨scMsgPtr⟩)])
      (newCap := appendRealizedCap 0 (0 + 1) (c₅ % 32)) hn hd
      (by simpa using appendRealizedCap_lower 0 (0 + 1) (c₅ % 32))
    simpa [scBackingVal, hhCap] using h
  have htgt : storeLoc { γS (scρA ρ c₅) σ scS13 with
        heap := GoCore.Heap.set (γS (scρA ρ c₅) σ scS13).heap
          (.base ⟨(γS (scρA ρ c₅) σ scS13).nextAddr⟩)
          ⟨some (.array (appendRealizedCap 0 (0 + 1) (c₅ % 32)) hhElemTy),
           scBackingVal c₅⟩,
        nextAddr := (γS (scρA ρ c₅) σ scS13).nextAddr + 1 } (.base ⟨scTgt⟩)
      (.slice ⟨some (.base ⟨(γS (scρA ρ c₅) σ scS13).nextAddr⟩), 0, 0 + 1,
        appendRealizedCap 0 (0 + 1) (c₅ % 32)⟩)
      = .ok (γS (scρA ρ c₅) σ scS14) := by
    kernel_rfl
  rw [scC13_shape]
  exact stepFn_appendSpill_transport (scρA ρ c₅) σ
    (by decide) (by decide) (by with_unfolding_all rfl)
    hvisE hvisO hcons hbuild htgt

/-! ## The composed 4,969-step span. -/

theorem sc_full_span (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (c₁ c₂ c₃ c₄ c₅ : Nat) (ch : Choices) :
    stepFnIter 4969 (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS0)
      (γC (scρ' ρ c₁ c₂ c₃ c₅) scC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: ch)
      = .ok (.next .stop, γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15, ch) := by
  have w1 := fun chx => scWin1 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w2 := fun chx => scWin2 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w3 := fun chx => scWin3 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w4 := fun chx => scWin4 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w5 := fun chx => scWin5 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w6 := fun chx => scWin6 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w7 := fun chx => scWin7 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have w8 := fun chx => scWin8 (scρ' ρ c₁ c₂ c₃ c₅) σ chx hag
  have p1 := scPick1_step (scρA ρ c₅) σ hag (uKey1 c₂) (uKey2 c₂ c₃)
    (uKey3 c₂ c₃) c₁ (c₂ :: c₃ :: c₄ :: c₅ :: ch)
  have p2 := scPick2_step (scρA ρ c₅) σ ((c₁ % 10 : Nat) : Int) (uKey2 c₂ c₃)
    (uKey3 c₂ c₃) c₂ (c₃ :: c₄ :: c₅ :: ch)
  have p3 := scPick3_step (scρA ρ c₅) σ ((c₁ % 10 : Nat) : Int) (uKey3 c₂ c₃)
    c₂ c₃ (c₄ :: c₅ :: ch)
  have p4 := scPick4_step (scρA ρ c₅) σ ((c₁ % 10 : Nat) : Int) c₂ c₃ c₄
    (c₅ :: ch)
  have pstop := scStop_step (scρA ρ c₅) σ ((c₁ % 10 : Nat) : Int) c₂ c₃
    (c₅ :: ch)
  have psort := scSort_step (scρA ρ c₅) σ ((c₁ % 10 : Nat) : Int) c₂ c₃
    (c₅ :: ch)
  have pspill := scSpill_step (uρ' ρ c₁ c₂ c₃) σ c₅ ch
  have hcomm : scρA (uρ' ρ c₁ c₂ c₃) c₅ = scρ' ρ c₁ c₂ c₃ c₅ := by
    with_unfolding_all rfl
  rw [hcomm] at pspill
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
                              (w1 (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: ch))
                              (GoLean.Surface.stepFnIter_one p1))
                            (w2 (c₂ :: c₃ :: c₄ :: c₅ :: ch)))
                          (GoLean.Surface.stepFnIter_one p2))
                        (w3 (c₃ :: c₄ :: c₅ :: ch)))
                      (GoLean.Surface.stepFnIter_one p3))
                    (w4 (c₄ :: c₅ :: ch)))
                  (GoLean.Surface.stepFnIter_one p4))
                (w5 (c₅ :: ch)))
              (GoLean.Surface.stepFnIter_one pstop))
            (w6 (c₅ :: ch)))
          (GoLean.Surface.stepFnIter_one psort))
        (w7 (c₅ :: ch)))
      (GoLean.Surface.stepFnIter_one pspill))
    (w8 ch)
  have hstop : γC (scρ' ρ c₁ c₂ c₃ c₅) (.next .stop) = .next .stop := rfl
  rw [← hstop]
  show stepFnIter 4969 _ _ _ = _
  exact h

/-! ## Projection facts at the literals. -/

theorem sc_pre_absMessage (ρ : Valuation) (σ : ExecState) :
    absMessage (γS ρ σ scS0) (.addr (.base ⟨52⟩))
      = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩ := by
  kernel_rfl

theorem sc_pre_absRaftLog (ρ : Valuation) (σ : ExecState) :
    absRaftLog (γS ρ σ scS0) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem sc_post_absRaftLog (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ : Nat) :
    absRaftLog (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨32⟩ = some hhAbsLog := by
  kernel_rfl

theorem sc_post_er (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    GoCore.Heap.lookup (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15).heap (.base ⟨68⟩)
      = some ⟨some (.interface ⟨"error"⟩), .nil⟩ := by
  kernel_rfl

theorem sc_post_msgs_field (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ : Nat) :
    fieldRead (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ ⟨"raft.raft"⟩ "msgs"
      = some (.slice ⟨some (.base ⟨scBacking⟩), 0, 1, hhCap c₅⟩) := by
  kernel_rfl

theorem sc_post_backing (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    GoCore.Heap.lookup (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15).heap
      (.base ⟨scBacking⟩)
      = some ⟨some (.array (hhCap c₅) hhElemTy), scBackingVal c₅⟩ := by
  kernel_rfl

theorem sc_post_respMsg (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    absMessage (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) (.addr (.base ⟨scMsgPtr⟩))
      = some (specHeartbeatResp 1 2 0) := by
  kernel_rfl

theorem scBackingVal_head (c : Nat) :
    (⟨[GoValue.addr (.base ⟨scMsgPtr⟩)] ++ List.replicate (hhCap c - 1) .nil⟩ :
      Array GoValue)[0]? = some (.addr (.base ⟨scMsgPtr⟩)) := by
  rw [List.cons_append]
  rfl

theorem sc_post_absOutbox (ρ : Valuation) (σ : ExecState)
    (c₁ c₂ c₃ c₅ : Nat) :
    absOutbox (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ "msgs"
      = some [specHeartbeatResp 1 2 0] := by
  rw [absOutbox]
  rw [sc_post_msgs_field ρ σ c₁ c₂ c₃ c₅]
  show sliceRead (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15)
    (.slice ⟨some (.base ⟨scBacking⟩), 0, 1, hhCap c₅⟩) _ = _
  rw [sliceRead]
  rw [sc_post_backing ρ σ c₁ c₂ c₃ c₅]
  show sliceElems (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15)
    ⟨[GoValue.addr (.base ⟨scMsgPtr⟩)] ++ List.replicate (hhCap c₅ - 1) .nil⟩
    (fun σ v => absMessage σ v) 0 1 = _
  rw [sliceElems, scBackingVal_head c₅]
  have hbind : ∀ {α β : Type} (a : α) (f : α → Option β),
      (some a >>= f) = f a := fun a f => rfl
  simp only [hbind]
  rw [sc_post_respMsg ρ σ c₁ c₂ c₃ c₅]
  simp only [hbind]
  rfl

theorem sc_post_maa (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    absOutbox (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ "msgsAfterAppend"
      = some [] := by
  kernel_rfl

/-- THE DEPTH-2 HEADLINE: state 1 → 0 (candidate falls back). -/
theorem sc_post_state (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    fieldReadU64 (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ ⟨"raft.raft"⟩ "state"
      = some 0 := by
  kernel_rfl

theorem sc_post_lead (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    fieldReadU64 (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ ⟨"raft.raft"⟩ "lead"
      = some 2 := by
  kernel_rfl

theorem sc_post_term (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    fieldReadU64 (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ ⟨"raft.raft"⟩ "Term"
      = some 0 := by
  kernel_rfl

/-- Vote rides at wrap depth 14 (probe `SCDepth`; the §4c rule). -/
theorem sc_post_vote (ρ : Valuation) (σ : ExecState) (c₁ c₂ c₃ c₅ : Nat) :
    fieldReadU64 (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) ⟨31⟩ ⟨"raft.raft"⟩ "Vote"
      = some (unrm 14 (ρ.ints 1)) := by
  kernel_rfl

/-! ## THE EQUATION (PRIMARY: allocation-symbolic). -/

/-- **THE stepCandidate × MsgHeartbeat DISPATCH-ARM EQUATION** (the
first DEPTH-2 arm): from the drained `er := stepCandidate(r, m)` call
at ANY placement (FrameSim premise), over EVERY consumed 5-choice
prefix (`c₁..c₅ :: ch` — Intn, three Visit picks, the appendSpill),
the run returns in exactly **4,969 steps** with five choices
consumed, and: the message projects with typ 8; **state 1 → 0 and
lead := m.From = 2** (the candidate falls back to follower — the
depth-2 dispatch-visible transitions); er = nil; the `msgs` outbox
gains exactly the heartbeat response; `msgsAfterAppend` stays empty;
the log view is preserved; Vote and Term read back unchanged. -/
theorem stepCandidate_heartbeat_eq_alloc (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (c₁ c₂ c₃ c₄ c₅ : Nat) (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ scS0) σF) :
    ∃ σFfin,
      stepFnIter 4969 σF (renameConfig r (γC ρ scC0))
        (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: ch)
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15) σFfin
      ∧ absMessage σF (.addr (.base ⟨r 52⟩))
          = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog σF ⟨r 32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σFfin.heap (.base ⟨r 68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σFfin ⟨r 31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σFfin ⟨r 31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σFfin ⟨r 32⟩ = some hhAbsLog
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "state" = some 0
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σFfin ⟨r 31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hpre : γS ρ σ scS0 = γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS0 := by kernel_rfl
  have hpreC : γC ρ scC0 = γC (scρ' ρ c₁ c₂ c₃ c₅) scC0 := by kernel_rfl
  have hrun : stepFnIter 4969 (γS ρ σ scS0) (γC ρ scC0)
      (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: ch)
      = .ok (.next .stop, γS (scρ' ρ c₁ c₂ c₃ c₅) σ scS15, ch) := by
    rw [hpre, hpreC]
    exact sc_full_span ρ σ hag c₁ c₂ c₃ c₄ c₅ ch
  obtain ⟨σFfin, htF, hs⟩ := span_relocate hrun hF
  refine ⟨σFfin, htF, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := sc_pre_absMessage ρ σ
    have h2 := absMessage_ren hF (v := .addr (.base ⟨52⟩)) h
    have hrv : renameValue r (GoValue.addr (.base ⟨52⟩))
        = .addr (.base ⟨r 52⟩) := rfl
    rw [hrv] at h2
    exact h2
  · exact absRaftLog_ren hF (sc_pre_absRaftLog ρ σ)
  · have h := hs.lookup_some (sc_post_er ρ σ c₁ c₂ c₃ c₅)
    have hcell : renameCell r (⟨some (.interface ⟨"error"⟩), .nil⟩ : HeapCell)
        = ⟨some (.interface ⟨"error"⟩), .nil⟩ := rfl
    rw [hcell] at h
    exact h
  · exact absOutbox_ren hs (sc_post_absOutbox ρ σ c₁ c₂ c₃ c₅)
  · exact absOutbox_ren hs (sc_post_maa ρ σ c₁ c₂ c₃ c₅)
  · exact absRaftLog_ren hs (sc_post_absRaftLog ρ σ c₁ c₂ c₃ c₅)
  · exact fieldReadU64_ren hs (sc_post_state ρ σ c₁ c₂ c₃ c₅)
  · exact fieldReadU64_ren hs (sc_post_lead ρ σ c₁ c₂ c₃ c₅)
  · have h := sc_post_vote ρ σ c₁ c₂ c₃ c₅
    rw [unrm_id hvote 14] at h
    exact fieldReadU64_ren hs h
  · exact fieldReadU64_ren hs (sc_post_term ρ σ c₁ c₂ c₃ c₅)

/-- The identity-placement corollary. -/
theorem stepCandidate_heartbeat_eq (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (c₁ c₂ c₃ c₄ c₅ : Nat) (ch : Choices) :
    ∃ σfin,
      stepFnIter 4969 (γS ρ σ scS0) (γC ρ scC0)
        (c₁ :: c₂ :: c₃ :: c₄ :: c₅ :: ch)
        = .ok (.next .stop, σfin, ch)
      ∧ absMessage (γS ρ σ scS0) (.addr (.base ⟨52⟩))
          = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS ρ σ scS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "state" = some 0
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some (ρ.ints 1)
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 := by
  have hF : FrameSim (ρT 69 0) 69 69 [] (γS ρ σ scS0) (γS ρ σ scS0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 69 f.body)
  obtain ⟨σfin, hrun, _, hmsg, hlog0, her, hob, hmaa, hlog1, hst, hl, hv, ht⟩ :=
    stepCandidate_heartbeat_eq_alloc ρ σ hag hvote c₁ c₂ c₃ c₄ c₅ ch hF
  have hcall : renameConfig (ρT 69 0) (γC ρ scC0) = γC ρ scC0 := by
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

/-! ## §3.3 discharge witness (Vote 7, lead 2, ldT 5; the probe's
tuple (3,1,1,0,5)). -/

def scρw : Valuation :=
  { ints := fun i => [0, 7, 2, 0, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

theorem stepCandidate_heartbeat_eq_witness :
    ∃ σfin,
      stepFnIter 4969 (γS scρw wBase scS0) (γC scρw scC0) [3, 1, 1, 0, 5]
        = .ok (.next .stop, σfin, [])
      ∧ absMessage (γS scρw wBase scS0) (.addr (.base ⟨52⟩))
          = some ⟨8, 0, 2, 0, 0, 0, 1, 0, 0, false, [], []⟩
      ∧ absRaftLog (γS scρw wBase scS0) ⟨32⟩ = some hhAbsLog
      ∧ GoCore.Heap.lookup σfin.heap (.base ⟨68⟩)
          = some ⟨some (.interface ⟨"error"⟩), .nil⟩
      ∧ absOutbox σfin ⟨31⟩ "msgs" = some [specHeartbeatResp 1 2 0]
      ∧ absOutbox σfin ⟨31⟩ "msgsAfterAppend" = some []
      ∧ absRaftLog σfin ⟨32⟩ = some hhAbsLog
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "state" = some 0
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "lead" = some 2
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Vote" = some 7
      ∧ fieldReadU64 σfin ⟨31⟩ ⟨"raft.raft"⟩ "Term" = some 0 :=
  stepCandidate_heartbeat_eq scρw wBase ⟨rfl, rfl, rfl, rfl⟩
    (by decide) 3 1 1 0 5 []

end GoLean.RaftSeam
