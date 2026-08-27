import GoLeanProofs.Specs.RaftPilot.CBfSteps
import GoLeanProofs.Sym.KernelRfl

/-!
# W2 unit 4: the compliant-chain crossing facts, sites 3-6 (the
address-shifted mirror of `BfSteps2`; shared machinery reused by
import). PRIVATE scaffolding per the W1 convention.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## Site 3 — Visit pick 2 (`x₇ = uKey2 c₂ c₃`) -/

theorem cC5_shape (tenv : LocalEnv) (k : SymCont) :
    cC5 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
    cB3 (some (.base ⟨33⟩)) #[uKeyV2] cStart3 cE3 (cK3 tenv k)) := by
  with_unfolding_all rfl

theorem cS6_eq : cS6 = (cS5.alloc uKeyV3 (some uTyK)).2 := by
  unfold cS6 cP6
  rw [cC5_shape [] .stop]
  rfl

theorem cC6_eq (tenv : LocalEnv) (k : SymCont) : cC6 tenv k = .exec cB3
    ((cE3.pushScope).declare "id" (cS5.alloc uKeyV3 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg cB3 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2] uKeyV3) cStart3 cE3 (cK3 tenv k)) := by
  unfold cC6 cP6
  rw [cC5_shape tenv k]
  rfl

theorem cEntries5 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ cS5) (some (.base ⟨33⟩))
      = .ok cCands3 := by
  with_unfolding_all rfl

theorem cPick3_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a d : Int) (c₂ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) σ cS5)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) (cC5 tenv k)) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) (cC6 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ (ch.headD 0)) d) σ cS6, ch.tail) := by
  rw [cC5_shape tenv k, cC6_eq tenv k, cS6_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show ch.headD 0 % 2 = 0 ∨ ch.headD 0 % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ (ch.headD 0) = 2 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, cEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries5 _ σ, Bind.bind, Except.bind]
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

theorem cC7_shape (tenv : LocalEnv) (k : SymCont) :
    cC7 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
    cB3 (some (.base ⟨33⟩)) #[uKeyV2, uKeyV3] cStart3 cE3 (cK3 tenv k)) := by
  with_unfolding_all rfl

theorem cS8_eq : cS8 = (cS7.alloc uKeyV4 (some uTyK)).2 := by
  unfold cS8 cP8
  rw [cC7_shape [] .stop]
  rfl

theorem cC8_eq (tenv : LocalEnv) (k : SymCont) : cC8 tenv k = .exec cB3
    ((cE3.pushScope).declare "id" (cS7.alloc uKeyV4 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg cB3 (some (.base ⟨33⟩))
      (Array.push #[uKeyV2, uKeyV3] uKeyV4) cStart3 cE3 (cK3 tenv k)) := by
  unfold cC8 cP8
  rw [cC7_shape tenv k]
  rfl

theorem cEntries7 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ cS7) (some (.base ⟨33⟩))
      = .ok cCands3 := by
  with_unfolding_all rfl

theorem cPick4_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ cS7)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (cC7 tenv k))
      ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (cC8 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ cS8,
          ch.tail) := by
  rw [cC7_shape tenv k, cC8_eq tenv k, cS8_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, cEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, cEntries7 _ σ, Bind.bind, Except.bind]
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

theorem cC9_shape (tenv : LocalEnv) (k : SymCont) :
    cC9 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
    cB3 (some (.base ⟨33⟩)) #[uKeyV2, uKeyV3, uKeyV4] cStart3 cE3
    (cK3 tenv k)) := by
  with_unfolding_all rfl

theorem cS10_eq : cS10 = cS9 := by
  unfold cS10 cP10
  rw [cC9_shape [] .stop]
  rfl

theorem cC10_eq (tenv : LocalEnv) (k : SymCont) :
    cC10 tenv k = .next (cK3 tenv k) := by
  unfold cC10 cP10
  rw [cC9_shape tenv k]
  rfl

theorem cEntries9 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ cS9) (some (.base ⟨33⟩))
      = .ok cCands3 := by
  with_unfolding_all rfl

theorem cStop_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ cS9)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (cC9 tenv k)) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) (cC10 tenv k),
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ cS10,
          ch) := by
  rw [cC9_shape tenv k, cC10_eq tenv k, cS10_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, cEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, cEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, cEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, cEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, cEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    refine Eq.trans (stepFn_stop_transport ?_) ?_
    · simp only [mapIterCandidates, cEntries9 _ σ, Bind.bind, Except.bind]
      with_unfolding_all rfl
    · rfl

/-! ## Site 6 — the sortSlice apply: THE COLLAPSE (§4(ii)) -/

def cE11 : LocalEnv := match cC11 [] .stop with
  | .retV _ (.stmtOpK _ _ _ _ e _) => e
  | _ => []
def cK11 (tenv : LocalEnv) (k : SymCont) : GoLean.Sym.Cont symDom :=
  match cC11 tenv k with
  | .retV _ (.stmtOpK _ _ _ _ _ kk) => kk
  | _ => .stop
def cSlice11 : SliceValue :=
  { base := some (.base ⟨76⟩), offset := 0, len := 3, cap := 7 }

theorem cC11_shape (tenv : LocalEnv) (k : SymCont) :
    cC11 tenv k = .retV (.slice cSlice11)
    (.stmtOpK (.sortSlice (.int .uint64)) 0 [] [] cE11 (cK11 tenv k)) := by
  with_unfolding_all rfl


end GoLean.RaftSeam
