import GoLeanProofs.Specs.RaftPilot.BfSteps

/-!
# W1 pilot scaffolding (HARVESTED from campaign-arc4d BfSteps2.lean,
2026-08-27; open-tail parameterized). STATUS/retirement per
Specs/RaftPilot/BfLit.lean. Original docstring follows.

# A4-U3: crossing facts, part 2 — Visit picks 2/3, the range STOP,
and the sortSlice COLLAPSE

The 6-leaf case analysis lives here (arc-log proof-shape plan): the
pick-2/3 candidate lists, the stop filter, and the sort inputs depend
on the earlier picked keys, so each fact cases on `c₂ % 3` (and
`c₃ % 2`), rewrites `uKey1/uKey2/uKey3` to leaf literals, and closes
per leaf. The per-site HEAVY facts (`uEntries5/7/9`, the shapes) are
leaf-independent and stated once. The sort apply is the §4(ii)
collapse: for every leaf, the post state is `uS12` — concrete
`[1,2,3]` in the ids array, the dead key cells staying symbolic.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

def uKeyV3 : SymValue := .int (.var 7) .uint64
def uKeyV4 : SymValue := .int (.var 8) .uint64

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## Site 3 — Visit pick 2 (`x₇ = uKey2 c₂ c₃`) -/

theorem uC5_shape (tenv : LocalEnv) (k : SymCont) :
    uC5 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
    uB3 (some (.base ⟨2⟩)) #[uKeyV2] uStart3 uE3 (uK3 tenv k)) := by
  with_unfolding_all rfl

theorem uS6_eq : uS6 = (uS5.alloc uKeyV3 (some uTyK)).2 := by
  unfold uS6 uP6
  rw [uC5_shape [] .stop]
  rfl

theorem uC6_eq (tenv : LocalEnv) (k : SymCont) : uC6 tenv k = .exec uB3
    ((uE3.pushScope).declare "id" (uS5.alloc uKeyV3 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg uB3 (some (.base ⟨2⟩))
      (Array.push #[uKeyV2] uKeyV3) uStart3 uE3 (uK3 tenv k)) := by
  unfold uC6 uP6
  rw [uC5_shape tenv k]
  rfl

theorem uEntries5 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ uS5) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  with_unfolding_all rfl

theorem uPick3_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a d : Int) (c₂ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) σ uS5)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) (uC5 tenv k)) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) (uC6 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) σ uS6, ch.tail) := by
  rw [uC5_shape tenv k, uC6_eq tenv k, uS6_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show ch.headD 0 % 2 = 0 ∨ ch.headD 0 % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 2 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 2, ch.tail) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 3 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 2, ch.tail) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 1 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 2, ch.tail) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 3 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 2, ch.tail) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 1 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 2, ch.tail) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 2 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries5 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 2, ch.tail) = _
      rw [h3]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl

/-! ## Site 4 — Visit pick 3 (`x₈ = uKey3`, the leftover; width 1) -/

theorem uC7_shape (tenv : LocalEnv) (k : SymCont) :
    uC7 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
    uB3 (some (.base ⟨2⟩)) #[uKeyV2, uKeyV3] uStart3 uE3 (uK3 tenv k)) := by
  with_unfolding_all rfl

theorem uS8_eq : uS8 = (uS7.alloc uKeyV4 (some uTyK)).2 := by
  unfold uS8 uP8
  rw [uC7_shape [] .stop]
  rfl

theorem uC8_eq (tenv : LocalEnv) (k : SymCont) : uC8 tenv k = .exec uB3
    ((uE3.pushScope).declare "id" (uS7.alloc uKeyV4 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg uB3 (some (.base ⟨2⟩))
      (Array.push #[uKeyV2, uKeyV3] uKeyV4) uStart3 uE3 (uK3 tenv k)) := by
  unfold uC8 uP8
  rw [uC7_shape tenv k]
  rfl

theorem uEntries7 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ uS7) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  with_unfolding_all rfl

theorem uPick4_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ uS7)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (uC7 tenv k))
      ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (uC8 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ uS8,
          ch.tail) := by
  rw [uC7_shape tenv k, uC8_eq tenv k, uS8_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 1, ch.tail) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 1, ch.tail) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 1, ch.tail) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 1, ch.tail) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 1, ch.tail) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, uEntries7 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    case hne => with_unfolding_all rfl
    case hmand => with_unfolding_all rfl
    case hconsume =>
      simp only [consume_eq]
      change (ch.headD 0 % 1, ch.tail) = _
      rw [Nat.mod_one]
    case hget => with_unfolding_all rfl
    case hkey => with_unfolding_all rfl
    case hnorm => with_unfolding_all rfl

/-! ## Site 5 — the range STOP (candidates exhausted) -/

theorem uC9_shape (tenv : LocalEnv) (k : SymCont) :
    uC9 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
    uB3 (some (.base ⟨2⟩)) #[uKeyV2, uKeyV3, uKeyV4] uStart3 uE3
    (uK3 tenv k)) := by
  with_unfolding_all rfl

theorem uS10_eq : uS10 = uS9 := by
  unfold uS10 uP10
  rw [uC9_shape [] .stop]
  rfl

theorem uC10_eq (tenv : LocalEnv) (k : SymCont) :
    uC10 tenv k = .next (uK3 tenv k) := by
  unfold uC10 uP10
  rw [uC9_shape tenv k]
  rfl

theorem uEntries9 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ uS9) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  with_unfolding_all rfl

theorem uStop_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ uS9)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (uC9 tenv k)) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (uC10 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ uS10,
          ch) := by
  rw [uC9_shape tenv k, uC10_eq tenv k, uS10_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, uEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, uEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, uEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, uEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, uEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, uEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl

/-! ## Site 6 — the sortSlice apply: THE COLLAPSE (§4(ii)) -/

def uE11 : LocalEnv := match uC11 [] .stop with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []
def uK11 (tenv : LocalEnv) (k : SymCont) : GoLean.Sym.Cont symDom :=
  match uC11 tenv k with
  | .retV _ (.stmtOpK _ _ _ _ _ kk) => kk
  | _ => .stop
def uSlice11 : SliceValue :=
  { base := some (.base ⟨45⟩), offset := 0, len := 3, cap := 7 }

theorem uC11_shape (tenv : LocalEnv) (k : SymCont) :
    uC11 tenv k = .retV (.slice uSlice11)
    (.stmtOpK (.sortSlice (.int .uint64)) 0 [] [] uE11 (uK11 tenv k)) := by
  with_unfolding_all rfl

end GoLean.RaftSeam
