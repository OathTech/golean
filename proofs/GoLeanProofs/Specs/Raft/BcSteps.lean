import GoLeanProofs.Specs.Raft.BcFixture

/-!
# A4-U4 wave 1: the becomeCandidate crossing facts

The six crossings of the BC chain, in the Bf pattern with the slice-0
simplifications:
- The four PICKS go through `stepFn_pick_transport` (the choice index
  is free, so the step cannot be a closed kernel fact) with the same
  shared machinery as Bf: `uρ`, `uKey1/2/3`, `uCands1`/`uCands3` and
  their get-lemmas, `uKeyV*` — the reset-span reuse, verbatim.
- The range-STOP and the sortSlice COLLAPSE are whole-step
  `kernel_rfl` facts per key-order leaf (six each) behind dispatchers
  — no transport, no shape/heavy-fact ceremony (the U3-era
  `stepFn_stop_transport` route is not needed at literal states; the
  Bf modules keep it as landed history).
Every fact was #eval-validated end-to-end by `BcProbe.lean`'s mirror
walk (γ-image == machine heap) before being stated.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## Site 1 — the Intn pick (map keys 0..9 at base 30, `x₅ = ↑(c₁ % 10)`) -/

def bcB1 : Stmt := match bcC1 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def bcE1 : LocalEnv := match bcC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def bcK1 : GoLean.Sym.Cont symDom := match bcC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def bcStart1 : Array SymValue := match bcC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem bcC1_shape : bcC1 = .next (.mapIterK (some "k") none uTyU uTySt
    bcB1 (some (.base ⟨30⟩)) #[] bcStart1 bcE1 bcK1) := by
  kernel_rfl

theorem bcS2_eq : bcS2 = (bcS1.alloc uKeyV1 (some uTyU)).2 := by
  unfold bcS2 bcP2
  rw [bcC1_shape]
  rfl

theorem bcC2_eq : bcC2 = .exec bcB1
    ((bcE1.pushScope).declare "k" (bcS1.alloc uKeyV1 (some uTyU)).1)
    (.mapIterK (some "k") none uTyU uTySt bcB1 (some (.base ⟨30⟩))
      (Array.push #[] uKeyV1) bcStart1 bcE1 bcK1) := by
  unfold bcC2 bcP2
  rw [bcC1_shape]
  rfl

theorem bcEntries1 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ bcS1) (some (.base ⟨30⟩))
      = .ok uCands1 := by
  kernel_rfl

theorem bcCands1_fact (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) :
    mapIterCandidates (γS ρ σ bcS1) uTyU uTySt (some (.base ⟨30⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok uCands1 := by
  have ht : (γS ρ σ bcS1).types = bfTB.types := hag.1
  simp only [mapIterCandidates, bcEntries1 ρ σ, Bind.bind, Except.bind, ht]
  with_unfolding_all rfl

theorem bcPick1_step (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (b c d : Int) (c₁ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ bcS1)
      (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) bcC1) (c₁ :: rest)
      = .ok (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) bcC2,
          γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ bcS2, rest) := by
  have h10 : c₁ % 10 < 10 := Nat.mod_lt _ (by decide)
  rw [bcC1_shape, bcC2_eq, bcS2_eq]
  refine stepFn_pick_transport _ σ (bcCands1_fact _ σ hag)
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

/-! ## Site 2 — Visit pick 1 (map keys 1..3 at base 2, `x₆ = uKey1 c₂`) -/

def bcB3 : Stmt := match bcC3 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def bcE3 : LocalEnv := match bcC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def bcK3 : GoLean.Sym.Cont symDom := match bcC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def bcStart3 : Array SymValue := match bcC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

theorem bcC3_shape : bcC3 = .next (.mapIterK (some "id") none uTyK uTyProg
    bcB3 (some (.base ⟨2⟩)) #[] bcStart3 bcE3 bcK3) := by
  kernel_rfl

theorem bcS4_eq : bcS4 = (bcS3.alloc uKeyV2 (some uTyK)).2 := by
  unfold bcS4 bcP4
  rw [bcC3_shape]
  rfl

theorem bcC4_eq : bcC4 = .exec bcB3
    ((bcE3.pushScope).declare "id" (bcS3.alloc uKeyV2 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg bcB3 (some (.base ⟨2⟩))
      (Array.push #[] uKeyV2) bcStart3 bcE3 bcK3) := by
  unfold bcC4 bcP4
  rw [bcC3_shape]
  rfl

theorem bcEntries3 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ bcS3) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  kernel_rfl

theorem bcCands3_fact (ρ : Valuation) (σ : ExecState) :
    mapIterCandidates (γS ρ σ bcS3) uTyK uTyProg (some (.base ⟨2⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok uCands3 := by
  simp only [mapIterCandidates, bcEntries3 ρ σ, Bind.bind, Except.bind]
  with_unfolding_all rfl

theorem bcPick2_step (ρ : Valuation) (σ : ExecState)
    (a c d : Int) (c₂ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) c d) σ bcS3)
      (γC (uρ ρ a (uKey1 c₂) c d) bcC3) (c₂ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) c d) bcC4,
          γS (uρ ρ a (uKey1 c₂) c d) σ bcS4, rest) := by
  have h3 : c₂ % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [bcC3_shape, bcC4_eq, bcS4_eq]
  refine stepFn_pick_transport _ σ (bcCands3_fact _ σ)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    ?_ (uCands3_get _ h3) (by with_unfolding_all rfl) ?_
  · show Choices.consume (c₂ :: rest) (uCands3.size + _) = _
    simp only [Choices.consume]
    rfl
  · have hn := normalize_small .uint64 ((c₂ : Int) % 3 + 1)
      (by omega) (by omega)
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [normalizeValueForTyFuel, hn, uTyK]

/-! ## Site 3 — Visit pick 2 (`x₇ = uKey2 c₂ c₃`; 6-leaf case analysis) -/

theorem bcC5_shape : bcC5 = .next (.mapIterK (some "id") none uTyK uTyProg
    bcB3 (some (.base ⟨2⟩)) #[uKeyV2] bcStart3 bcE3 bcK3) := by
  kernel_rfl

theorem bcS6_eq : bcS6 = (bcS5.alloc uKeyV3 (some uTyK)).2 := by
  unfold bcS6 bcP6
  rw [bcC5_shape]
  rfl

theorem bcC6_eq : bcC6 = .exec bcB3
    ((bcE3.pushScope).declare "id" (bcS5.alloc uKeyV3 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg bcB3 (some (.base ⟨2⟩))
      (Array.push #[uKeyV2] uKeyV3) bcStart3 bcE3 bcK3) := by
  unfold bcC6 bcP6
  rw [bcC5_shape]
  rfl

theorem bcEntries5 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ bcS5) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  kernel_rfl

theorem bcPick3_step (ρ : Valuation) (σ : ExecState)
    (a d : Int) (c₂ c₃ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) σ bcS5)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) bcC5) (c₃ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) bcC6,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) d) σ bcS6, rest) := by
  rw [bcC5_shape, bcC6_eq, bcS6_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, bcEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries5 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries5 _ σ, Bind.bind, Except.bind]
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

/-! ## Site 4 — Visit pick 3 (`x₈ = uKey3`, the leftover; width 1) -/

theorem bcC7_shape : bcC7 = .next (.mapIterK (some "id") none uTyK uTyProg
    bcB3 (some (.base ⟨2⟩)) #[uKeyV2, uKeyV3] bcStart3 bcE3 bcK3) := by
  kernel_rfl

theorem bcS8_eq : bcS8 = (bcS7.alloc uKeyV4 (some uTyK)).2 := by
  unfold bcS8 bcP8
  rw [bcC7_shape]
  rfl

theorem bcC8_eq : bcC8 = .exec bcB3
    ((bcE3.pushScope).declare "id" (bcS7.alloc uKeyV4 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg bcB3 (some (.base ⟨2⟩))
      (Array.push #[uKeyV2, uKeyV3] uKeyV4) bcStart3 bcE3 bcK3) := by
  unfold bcC8 bcP8
  rw [bcC7_shape]
  rfl

theorem bcEntries7 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ bcS7) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  kernel_rfl

theorem bcPick4_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ c₄ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ bcS7)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) bcC7)
      (c₄ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) bcC8,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ bcS8,
          rest) := by
  rw [bcC7_shape, bcC8_eq, bcS8_eq]
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    apply stepFn_pick_transport _ σ
    case hcands =>
      simp only [mapIterCandidates, bcEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries7 _ σ, Bind.bind, Except.bind]
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
      simp only [mapIterCandidates, bcEntries7 _ σ, Bind.bind, Except.bind]
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

/-! ## Site 5 — the range STOP: whole-step kernel facts per leaf. -/

theorem bcStop_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ bcS9) (γC (uρ ρ a 1 2 3) bcC9) ch
      = .ok (γC (uρ ρ a 1 2 3) bcC10, γS (uρ ρ a 1 2 3) σ bcS10, ch) := by
  kernel_rfl
theorem bcStop_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ bcS9) (γC (uρ ρ a 1 3 2) bcC9) ch
      = .ok (γC (uρ ρ a 1 3 2) bcC10, γS (uρ ρ a 1 3 2) σ bcS10, ch) := by
  kernel_rfl
theorem bcStop_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ bcS9) (γC (uρ ρ a 2 1 3) bcC9) ch
      = .ok (γC (uρ ρ a 2 1 3) bcC10, γS (uρ ρ a 2 1 3) σ bcS10, ch) := by
  kernel_rfl
theorem bcStop_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ bcS9) (γC (uρ ρ a 2 3 1) bcC9) ch
      = .ok (γC (uρ ρ a 2 3 1) bcC10, γS (uρ ρ a 2 3 1) σ bcS10, ch) := by
  kernel_rfl
theorem bcStop_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ bcS9) (γC (uρ ρ a 3 1 2) bcC9) ch
      = .ok (γC (uρ ρ a 3 1 2) bcC10, γS (uρ ρ a 3 1 2) σ bcS10, ch) := by
  kernel_rfl
theorem bcStop_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ bcS9) (γC (uρ ρ a 3 2 1) bcC9) ch
      = .ok (γC (uρ ρ a 3 2 1) bcC10, γS (uρ ρ a 3 2 1) σ bcS10, ch) := by
  kernel_rfl

theorem bcStop_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ bcS9)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) bcC9) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) bcC10,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ bcS10,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcStop_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcStop_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcStop_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcStop_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcStop_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcStop_leaf_21 ρ σ a ch

/-! ## Site 6 — the sortSlice COLLAPSE (§4(ii)): whole-step kernel
facts per leaf; every leaf's post state is `bcS12` (ids = [1,2,3]). -/

theorem bcSort_leaf_00 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 2 3) σ bcS11) (γC (uρ ρ a 1 2 3) bcC11) ch
      = .ok (γC (uρ ρ a 1 2 3) bcC12, γS (uρ ρ a 1 2 3) σ bcS12, ch) := by
  kernel_rfl
theorem bcSort_leaf_01 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 1 3 2) σ bcS11) (γC (uρ ρ a 1 3 2) bcC11) ch
      = .ok (γC (uρ ρ a 1 3 2) bcC12, γS (uρ ρ a 1 3 2) σ bcS12, ch) := by
  kernel_rfl
theorem bcSort_leaf_10 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 1 3) σ bcS11) (γC (uρ ρ a 2 1 3) bcC11) ch
      = .ok (γC (uρ ρ a 2 1 3) bcC12, γS (uρ ρ a 2 1 3) σ bcS12, ch) := by
  kernel_rfl
theorem bcSort_leaf_11 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 2 3 1) σ bcS11) (γC (uρ ρ a 2 3 1) bcC11) ch
      = .ok (γC (uρ ρ a 2 3 1) bcC12, γS (uρ ρ a 2 3 1) σ bcS12, ch) := by
  kernel_rfl
theorem bcSort_leaf_20 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 1 2) σ bcS11) (γC (uρ ρ a 3 1 2) bcC11) ch
      = .ok (γC (uρ ρ a 3 1 2) bcC12, γS (uρ ρ a 3 1 2) σ bcS12, ch) := by
  kernel_rfl
theorem bcSort_leaf_21 (ρ : Valuation) (σ : ExecState) (a : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a 3 2 1) σ bcS11) (γC (uρ ρ a 3 2 1) bcC11) ch
      = .ok (γC (uρ ρ a 3 2 1) bcC12, γS (uρ ρ a 3 2 1) σ bcS12, ch) := by
  kernel_rfl

theorem bcSort_step (ρ : Valuation) (σ : ExecState)
    (a : Int) (c₂ c₃ : Nat) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ bcS11)
      (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) bcC11) ch
      = .ok (γC (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) bcC12,
          γS (uρ ρ a (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)) σ bcS12,
          ch) := by
  rcases (show c₂ % 3 = 0 ∨ c₂ % 3 = 1 ∨ c₂ % 3 = 2 by omega)
    with h2|h2|h2 <;>
    rcases (show c₃ % 2 = 0 ∨ c₃ % 2 = 1 by omega) with h3|h3
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcSort_leaf_00 ρ σ a ch
  · rw [(show uKey1 c₂ = 1 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcSort_leaf_01 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 3 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcSort_leaf_10 ρ σ a ch
  · rw [(show uKey1 c₂ = 2 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 3 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcSort_leaf_11 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 1 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 2 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcSort_leaf_20 ρ σ a ch
  · rw [(show uKey1 c₂ = 3 by unfold uKey1; rw [h2]; decide),
      (show uKey2 c₂ c₃ = 2 by unfold uKey2; rw [h2, h3]; decide),
      (show uKey3 c₂ c₃ = 1 by unfold uKey3 uKey2 uKey1; rw [h2, h3]; decide)]
    exact bcSort_leaf_21 ρ σ a ch

end GoLean.RaftSeam
