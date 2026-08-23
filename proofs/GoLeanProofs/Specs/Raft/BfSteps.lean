import GoLeanProofs.Specs.Raft.BfFixture
import GoLeanProofs.Sym.KernelRfl

/-!
# A4-U3: the hand crossing facts — checklist items (2) and (4)

The ∀ρ discharges of the six crossings in the becomeFollower chain:
the four PICKS, the Visit range-STOP, and the ONE `sortSlice` apply —
the §4(ii) COLLAPSE point.

Structure (the "one lemma over a fixed γ-image heap" of the U2
handoff, realized): `stepFn_pick_transport` composes
`stepFn_pick_generic` with `alloc_conc`, so a pick fact needs only
(a) ONE heavy γ-heap fact per site (the live-entry walk — the only
premise that reduces the window-output heap), (b) cheap literal-level
candidate/consume/index facts, and (c) a normalize-identity side
lemma for the picked key. The picked keys enter through the valuation
former `uρ` (vars 5–8), derived from the prefix:
`x₅ = ↑(c₁ % 10)`, `x₆ = uKey1 c₂ = ↑(c₂ % 3) + 1`,
`x₇ = uKey2 c₂ c₃`, `x₈ = uKey3 = 6 - x₆ - x₇`. The 6-leaf case
analysis (candidate lists of picks 2/3 + the stop/sort filters depend
on the earlier keys) is confined to CHEAP post-walk reductions —
exactly the arc-log proof-shape plan.

Every fact was `#eval`-validated end-to-end by the BfU3Probe phase-2
walk (γ-image == machine heap at the chain's end) before being
stated.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

/-! ## The pick-absorbing valuation and the derived keys -/

/-- `ρ` with the four pick vars overridden (design §4(ii): the
valuation absorbs the picks; vars 1–4 and 9 ride through). -/
def uρ (ρ : Valuation) (a b c d : Int) : Valuation :=
  { ρ with ints := fun i =>
      if i = 5 then a else if i = 6 then b else if i = 7 then c
      else if i = 8 then d else ρ.ints i }

/-- Visit pick 1: candidate order is mapData order `[1,2,3]`. -/
def uKey1 (c₂ : Nat) : Int := ((c₂ % 3 : Nat) : Int) + 1

/-- Visit pick 2: the two remaining keys, in mapData order. -/
def uKey2 (c₂ c₃ : Nat) : Int :=
  match c₂ % 3, c₃ % 2 with
  | 0, 0 => 2 | 0, 1 => 3
  | 1, 0 => 1 | 1, 1 => 3
  | 2, 0 => 1 | _, _ => 2

/-- Visit pick 3: the leftover key. -/
def uKey3 (c₂ c₃ : Nat) : Int := 6 - uKey1 c₂ - uKey2 c₂ c₃

/-- The full prefix-derived valuation. -/
def uρ' (ρ : Valuation) (c₁ c₂ c₃ : Nat) : Valuation :=
  uρ ρ ((c₁ % 10 : Nat) : Int) (uKey1 c₂) (uKey2 c₂ c₃) (uKey3 c₂ c₃)

/-! ## The transport lemmas (prop-level; no heavy reduction inside) -/

/-- Small-value normalize identity (the picked keys are 0..9 /
1..3 — inside every int kind's range). -/
theorem normalize_small (kind : IntKind) (v : Int) (h0 : 0 ≤ v)
    (h1 : v < 128) : IntKind.normalize kind v = v := by
  unfold IntKind.normalize
  cases kind <;> simp only [IntKind.bits?] <;> (try rfl) <;>
    · split <;> omega

/-- THE PICK TRANSPORT (checklist item 4): a map-range pick at a
γ-image, with the key entering as a symbolic-cell alloc on the mirror
side. `stepFn_pick_generic` + `alloc_conc`; premises are per-site
facts. `vo = none` (both census range sites are key-only). -/
theorem stepFn_pick_transport (ρ : Valuation) (σ : ExecState)
    {S : SymState} {name : String} {kt vt : Ty} {body : Stmt}
    {base : Option Loc} {produced start : Array SymValue}
    {env : LocalEnv} {k : GoLean.Sym.Cont symDom}
    {keyv : SymValue} {cands : Array (GoValue × GoValue)} {mand : Bool}
    {idx : Nat} {ch ch' : Choices} {kv vv : GoValue}
    (hcands : mapIterCandidates (γS ρ σ S) kt vt base
      (produced.map (concV (symInterp ρ))) = .ok cands)
    (hne : cands.isEmpty = false)
    (hmand : mapIterMandatoryRemains (γS ρ σ S) kt cands
      (start.map (concV (symInterp ρ))) = .ok mand)
    (hconsume : Choices.consume ch (cands.size + (if mand then 0 else 1))
      = (idx, ch'))
    (hget : cands[idx]? = some (kv, vv))
    (hkey : concV (symInterp ρ) keyv = kv)
    (hnorm : normalizeValueForTy (γS ρ σ S) kt kv = .ok kv) :
    stepFn (γS ρ σ S)
      (γC ρ (.next (.mapIterK (some name) none kt vt body base produced
        start env k))) ch
      = .ok (γC ρ (.exec body
            ((env.pushScope).declare name (S.alloc keyv (some kt)).1)
            (.mapIterK (some name) none kt vt body base
              (produced.push keyv) start env k)),
          γS ρ σ (S.alloc keyv (some kt)).2, ch') := by
  have halloc := alloc_conc (I := symInterp ρ) σ S keyv (some kt)
  have hbind : bindIterVars env.pushScope (γS ρ σ S) (some name) none kt vt
      kv vv
      = .ok ((env.pushScope).declare name (S.alloc keyv (some kt)).1,
          γS ρ σ (S.alloc keyv (some kt)).2) := by
    simp only [bindIterVars, hnorm, Bind.bind, Except.bind, pure,
      Except.pure]
    rw [← hkey, halloc]
  have hstep := stepFn_pick_generic (body := body)
    (k := concK (symInterp ρ) k) hcands hne hmand hconsume hget hbind
  refine Eq.trans hstep ?_
  simp only [concC, concK, Array.map_push, hkey]

/-! ## Site 1 — the Intn pick (map keys 0..9, `x₅ = ↑(c₁ % 10)`) -/

def uB1 : Stmt := match uC1 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def uE1 : LocalEnv := match uC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def uK1 : GoLean.Sym.Cont symDom := match uC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop

def uStart1 : Array SymValue := match uC1 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

def uTyU : Ty := .int .int
def uTySt : Ty := .defined ⟨"struct{}"⟩
def uKeyV1 : SymValue := .int (.var 5) .int

/-- The Intn candidate snapshot (D-11's 10-entry map, cell order). -/
def uCands1 : Array (GoValue × GoValue) :=
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

theorem uC1_shape : uC1 = .next (.mapIterK (some "k") none uTyU uTySt
    uB1 (some (.base ⟨32⟩)) #[] uStart1 uE1 uK1) := by
  kernel_rfl

theorem uS2_eq : uS2 = (uS1.alloc uKeyV1 (some uTyU)).2 := by
  unfold uS2 uP2
  rw [uC1_shape]
  rfl

theorem uC2_eq : uC2 = .exec uB1
    ((uE1.pushScope).declare "k" (uS1.alloc uKeyV1 (some uTyU)).1)
    (.mapIterK (some "k") none uTyU uTySt uB1 (some (.base ⟨32⟩))
      (Array.push #[] uKeyV1) uStart1 uE1 uK1) := by
  unfold uC2 uP2
  rw [uC1_shape]
  rfl

/-- THE HEAVY FACT for site 1: the live-entry walk at the γ-image
(reduces the window-1 output heap; everything else at this site is
literal-level). -/
theorem uEntries1 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ uS1) (some (.base ⟨32⟩))
      = .ok uCands1 := by
  kernel_rfl

theorem uCands1_fact (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) :
    mapIterCandidates (γS ρ σ uS1) uTyU uTySt (some (.base ⟨32⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok uCands1 := by
  have ht : (γS ρ σ uS1).types = bfTB.types := hag.1
  simp only [mapIterCandidates, uEntries1 ρ σ, Bind.bind, Except.bind, ht]
  with_unfolding_all rfl

theorem uCands1_get (i : Nat) (h : i < 10) :
    uCands1[i]? = some (.int (i : Int) .int, .struct ⟨"struct{}"⟩ #[]) := by
  have hd : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6
      ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases hd with h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

theorem uPick1_step (ρ : Valuation) (σ : ExecState)
    (hag : bfTB.Agrees σ) (b c d : Int) (c₁ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ uS1)
      (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) uC1) (c₁ :: rest)
      = .ok (γC (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) uC2,
          γS (uρ ρ ((c₁ % 10 : Nat) : Int) b c d) σ uS2, rest) := by
  have h10 : c₁ % 10 < 10 := Nat.mod_lt _ (by decide)
  rw [uC1_shape, uC2_eq, uS2_eq]
  refine stepFn_pick_transport _ σ (uCands1_fact _ σ hag)
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

/-! ## Site 2 — Visit pick 1 (map keys 1..3, `x₆ = uKey1 c₂`) -/

def uB3 : Stmt := match uC3 with
  | .next (.mapIterK _ _ _ _ b _ _ _ _ _) => b
  | _ => .seqn #[]
def uE3 : LocalEnv := match uC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ e _) => e
  | _ => []
def uK3 : GoLean.Sym.Cont symDom := match uC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ _ _ k) => k
  | _ => .stop
def uStart3 : Array SymValue := match uC3 with
  | .next (.mapIterK _ _ _ _ _ _ _ st _ _) => st
  | _ => #[]

def uTyK : Ty := .int .uint64
def uTyProg : Ty := .pointer (.defined ⟨"tracker.Progress"⟩)
def uKeyV2 : SymValue := .int (.var 6) .uint64

def uCands3 : Array (GoValue × GoValue) :=
  #[(.int 1 .uint64, .addr (.base ⟨7⟩)),
    (.int 2 .uint64, .addr (.base ⟨8⟩)),
    (.int 3 .uint64, .addr (.base ⟨9⟩))]

theorem uC3_shape : uC3 = .next (.mapIterK (some "id") none uTyK uTyProg
    uB3 (some (.base ⟨2⟩)) #[] uStart3 uE3 uK3) := by
  kernel_rfl

theorem uS4_eq : uS4 = (uS3.alloc uKeyV2 (some uTyK)).2 := by
  unfold uS4 uP4
  rw [uC3_shape]
  rfl

theorem uC4_eq : uC4 = .exec uB3
    ((uE3.pushScope).declare "id" (uS3.alloc uKeyV2 (some uTyK)).1)
    (.mapIterK (some "id") none uTyK uTyProg uB3 (some (.base ⟨2⟩))
      (Array.push #[] uKeyV2) uStart3 uE3 uK3) := by
  unfold uC4 uP4
  rw [uC3_shape]
  rfl

theorem uEntries3 (ρ : Valuation) (σ : ExecState) :
    mapIterLiveEntries (γS ρ σ uS3) (some (.base ⟨2⟩))
      = .ok uCands3 := by
  kernel_rfl

theorem uCands3_fact (ρ : Valuation) (σ : ExecState) :
    mapIterCandidates (γS ρ σ uS3) uTyK uTyProg (some (.base ⟨2⟩))
      (Array.map (concV (symInterp ρ)) #[]) = .ok uCands3 := by
  simp only [mapIterCandidates, uEntries3 ρ σ, Bind.bind, Except.bind]
  kernel_rfl

theorem uCands3_get (i : Nat) (h : i < 3) :
    uCands3[i]? = some (.int ((i : Int) + 1) .uint64,
      .addr (.base ⟨7 + i⟩)) := by
  have hd : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hd with h|h|h <;> subst h <;> rfl

theorem uPick2_step (ρ : Valuation) (σ : ExecState)
    (a c d : Int) (c₂ : Nat) (rest : Choices) :
    stepFn (γS (uρ ρ a (uKey1 c₂) c d) σ uS3)
      (γC (uρ ρ a (uKey1 c₂) c d) uC3) (c₂ :: rest)
      = .ok (γC (uρ ρ a (uKey1 c₂) c d) uC4,
          γS (uρ ρ a (uKey1 c₂) c d) σ uS4, rest) := by
  have h3 : c₂ % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [uC3_shape, uC4_eq, uS4_eq]
  refine stepFn_pick_transport _ σ (uCands3_fact _ σ)
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

/-- The range-STOP transport: candidates exhausted, no consumption. -/
theorem stepFn_stop_transport {σm : ExecState} {ko vo : Option String}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array GoValue} {env : LocalEnv}
    {k : Machine.Cont} {ch : Choices}
    (hcands : mapIterCandidates σm kt vt base produced = .ok #[]) :
    stepFn σm
      (.next (.mapIterK ko vo kt vt body base produced start env k)) ch
      = .ok (.next k, σm, ch) := by
  simp [stepFn, hcands, Bind.bind, Except.bind]

end GoLean.RaftSeam
