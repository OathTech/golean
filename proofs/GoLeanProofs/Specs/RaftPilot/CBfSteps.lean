import GoLeanProofs.Specs.RaftPilot.CBfFixture
import GoLeanProofs.Specs.RaftPilot.BfSteps2
import GoLeanProofs.Sym.KernelRfl

/-!
# W2 unit 4: the compliant-chain crossing facts, sites 1-2 (the
address-shifted mirror of `BfSteps` sites 1-2; shared machinery —
`uρ'`, the keys, the transports, the type spellings — is REUSED from
`BfSteps`/`BfSteps2` by import; the address-carrying candidate
snapshots are re-laid copies). PRIVATE scaffolding per the W1
convention.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

/-! ## Site 1 — the Intn pick (map keys 0..9, `x₅ = ↑(c₁ % 10)`) -/

def cB1 : Stmt := match cC1 [] .stop with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def cE1 : LocalEnv := match cC1 [] .stop with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def cK1 (tenv : LocalEnv) (k : SymCont) : GoLean.Sym.Cont symDom :=
  match cC1 tenv k with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ kk) => kk
  | _ => .stop

def cStart1 : Array SymValue := match cC1 [] .stop with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]




/-- The Intn candidate snapshot (D-11's 10-entry map, cell order). -/
def cCands1 : Array (GoValue × GoValue) :=
  #[((.int 0 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 1 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 2 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 3 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 4 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 5 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 6 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 7 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 8 .int), .struct ⟨"struct{}"⟩ #[]),
    ((.int 9 .int), .struct ⟨"struct{}"⟩ #[])]

set_option maxRecDepth 8000000
set_option maxHeartbeats 64000000
set_option smartUnfolding false

theorem cC1_shape (tenv : LocalEnv) (k : SymCont) :
    cC1 tenv k = .next (.mapIterK (some "k") none uTyU uTySt
      cB1 (some (.base ⟨63⟩)) #[] cStart1 cE1 (cK1 tenv k)) := by
  kernel_rfl

theorem cS2_eq : cS2 = (cS1.alloc uKeyV1 (some uTyU)).2 := by
  unfold cS2 cP2
  rw [cC1_shape [] .stop]
  rfl

theorem cC2_eq (tenv : LocalEnv) (k : SymCont) : cC2 tenv k = .exec cB1
    ((cE1.pushScope).declare "k" (cS1.alloc uKeyV1 (some uTyU)).1)
    (.mapIterK (some "k") none uTyU uTySt cB1 (some (.base ⟨63⟩))
      (Array.push #[] uKeyV1) cStart1 cE1 (cK1 tenv k)) := by
  unfold cC2 cP2
  rw [cC1_shape tenv k]
  rfl

/-- THE HEAVY FACT for site 1: the live-entry walk at the γ-image
(reduces the window-1 output heap; everything else at this site is
literal-level). -/
theorem cEntries1 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ cS1) (some (.base ⟨63⟩))
      = .ok cCands1 := by
  kernel_rfl

theorem cCands1_fact (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) :
    mapIterCandidates (γS ρ σ cS1) uTyU uTySt (some (.base ⟨63⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok cCands1 := by
  have ht : (γS ρ σ cS1).types = bfTB.types := hag.1
  simp only [mapIterCandidates, cEntries1 ρ σ, Bind.bind, Except.bind, ht]
  with_unfolding_all rfl

theorem cCands1_get (i : Nat) (h : i < 10) :
    cCands1[i]? = some (.int (i : Int) .int, .struct ⟨"struct{}"⟩ #[]) := by
  have hd : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6
      ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases hd with h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem cPick1_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (hag : bfTB.Agrees σ) (b c d : Int) (ch : Choices) :
    stepFn (γS (uρ ρ ((ch.headD 0 % 10 : Nat) : Int) b c d) σ cS1)
      (γC (uρ ρ ((ch.headD 0 % 10 : Nat) : Int) b c d) (cC1 tenv k)) ch
      = .ok (γC (uρ ρ ((ch.headD 0 % 10 : Nat) : Int) b c d) (cC2 tenv k),
          γS (uρ ρ ((ch.headD 0 % 10 : Nat) : Int) b c d) σ cS2,
          ch.tail) := by
  have h10 : ch.headD 0 % 10 < 10 := Nat.mod_lt _ (by decide)
  rw [cC1_shape tenv k, cC2_eq tenv k, cS2_eq]
  refine stepFn_pick_transport _ σ (cCands1_fact _ σ hag)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    ?_ (cCands1_get _ h10) (by with_unfolding_all rfl) ?_
  · show Choices.consume ch (cCands1.size + _) = _
    rw [consume_eq]
    rfl
  · have hn := normalize_small .int ((ch.headD 0 : Int) % 10)
      (by omega) (by omega)
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [normalizeValueForTyFuel, hn, uTyU, ← List.headD_eq_head?_getD]

/-! ## Site 2 — Visit pick 1 (map keys 1..3, `x₆ = uKey1 c₂`) -/

def cB3 : Stmt := match cC3 [] .stop with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def cE3 : LocalEnv := match cC3 [] .stop with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def cK3 (tenv : LocalEnv) (k : SymCont) : GoLean.Sym.Cont symDom :=
  match cC3 tenv k with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ kk) => kk
  | _ => .stop
def cStart3 : Array SymValue := match cC3 [] .stop with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]




def cCands3 : Array (GoValue × GoValue) :=
  #[(.int 1 .uint64, .addr (.base ⟨38⟩)),
    (.int 2 .uint64, .addr (.base ⟨39⟩)),
    (.int 3 .uint64, .addr (.base ⟨40⟩))]

theorem cC3_shape (tenv : LocalEnv) (k : SymCont) :
    cC3 tenv k = .next (.mapIterK (some "id") none uTyK uTyProg
      cB3 (some (.base ⟨33⟩)) #[] cStart3 cE3 (cK3 tenv k)) := by
  kernel_rfl

theorem cS4_eq : cS4 = (cS3.alloc uKeyV2 (some uTyK)).2 := by
  unfold cS4 cP4
  rw [cC3_shape [] .stop]
  rfl

theorem cC4_eq (tenv : LocalEnv) (k : SymCont) : cC4 tenv k = .exec cB3
    ((cE3.pushScope).declare "id" (cS3.alloc uKeyV2 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg cB3 (some (.base ⟨33⟩))
      (Array.push #[] uKeyV2) cStart3 cE3 (cK3 tenv k)) := by
  unfold cC4 cP4
  rw [cC3_shape tenv k]
  rfl

theorem cEntries3 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ cS3) (some (.base ⟨33⟩))
      = .ok cCands3 := by
  kernel_rfl

theorem cCands3_fact (ρ : Valuation) (σ : ExecState) :
    mapIterCandidates (γS ρ σ cS3) uTyK uTyProg (some (.base ⟨33⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok cCands3 := by
  simp only [mapIterCandidates, cEntries3 ρ σ, Bind.bind, Except.bind]
  kernel_rfl

theorem cCands3_get (i : Nat) (h : i < 3) :
    cCands3[i]? = some (.int ((i : Int) + 1) .uint64,
      .addr (.base ⟨38 + i⟩)) := by
  have hd : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hd with h|h|h <;> subst h <;> rfl

theorem cPick2_step (tenv : LocalEnv) (k : SymCont) (ρ : Valuation)
    (σ : ExecState)
    (a c d : Int) (ch : Choices) :
    stepFn (γS (uρ ρ a (uKey1 (ch.headD 0)) c d) σ cS3)
      (γC (uρ ρ a (uKey1 (ch.headD 0)) c d) (cC3 tenv k)) ch
      = .ok (γC (uρ ρ a (uKey1 (ch.headD 0)) c d) (cC4 tenv k),
          γS (uρ ρ a (uKey1 (ch.headD 0)) c d) σ cS4, ch.tail) := by
  have h3 : ch.headD 0 % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [cC3_shape tenv k, cC4_eq tenv k, cS4_eq]
  refine stepFn_pick_transport _ σ (cCands3_fact _ σ)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    ?_ (cCands3_get _ h3) (by with_unfolding_all rfl) ?_
  · show Choices.consume ch (cCands3.size + _) = _
    rw [consume_eq]
    rfl
  · have hn := normalize_small .uint64 ((ch.headD 0 : Int) % 3 + 1)
      (by omega) (by omega)
    simp only [normalizeValueForTy]
    rw [show typeResolutionFuel = 1023 + 1 from rfl]
    simp [normalizeValueForTyFuel, hn, uTyK, ← List.headD_eq_head?_getD]


end GoLean.RaftSeam
