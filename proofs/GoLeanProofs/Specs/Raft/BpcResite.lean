import GoLeanProofs.Specs.Raft.AllocEqWave1
import GoLeanProofs.Frame.Relocate

/-!
# A4-U6: the re-sited becomePreCandidate fixture — LIVE allocation-symbolism

**LINEAGE: as `AllocEq.lean`/`Frame/Relocate.lean` (separation-logic
locality; the renaming lemma).**

THE FINDING THIS MODULE ANSWERS (arc log, A4-U6): the twin's function
bodies contain `locLit`s at every static address `0..30`
(`funcListSup = 31`), and the U1–U4 fixtures sit at bases `0..23` ON
that range — so `FrameSim.bodies_inv` + `Agrees` (table equality)
force `r` to fix every fixture address: at the 0-based fixtures the
allocation-symbolic equations' `r`-quantifier is provably
identity-only, and no `FrameSim` can carry a fixture equation to the
twin's real layout (base 389+).

The fix demonstrated here: RE-SITE the fixture off the static range
(every cell shifted `+31`, allocator at 52). At the re-sited fixture
the placement quantifier is LIVE: any `r` fixing the statics `[0,31)`
may permute the footprint and shift the fresh region. Delivered:

* the transported 152-step window at the re-sited fixture (probe
  `Bpc31Probe`: 152 steps, projections exact, γ-image == machine
  heap — re-siting is placement-transparent to the run);
* `becomePreCandidate_handler_eq_alloc31` — the U5 equation at the
  re-sited fixture (same shape, receiver `r 31`);
* the identity corollary; and
* **the NON-identity witness** (`…_witness_shifted`): the handler run
  at a placement where the raft cell has genuinely MOVED (31 ↦ 32,
  the `swap31_32` relocation), the `FrameSim` premise discharged
  concretely by `frameSim_relocate` — the honest gap of U5 closed.

Wave-2 charter consequence (arc log): message-handler fixtures are
BORN re-sited (first cell at ≥ the static sup, never 0-based).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.Frame

set_option maxRecDepth 8000000

/-! ## The re-sited fixture (+31: off the static locLit range) -/

def sh31 : Nat → Nat := (· + 31)

def bpc31SymRaft : SymValue :=
  setSymField (setSymField (setSymField
    (embedGo (renameValue sh31 (uRaftVal 0 0 0 0)))
    "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

def bpc31SymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  (uHeap 0 0 0 0).map (fun (l, c) =>
    if l == .base ⟨0⟩ then (renameLoc sh31 l, .mk c.declaredTy bpc31SymRaft)
    else (renameLoc sh31 l, .mk c.declaredTy (embedGo (renameValue sh31 c.value))))

def bpc31S0 : SymState := { heap := bpc31SymHeap, nextAddr := 52 }

def bpc31C0 : SymConfig :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)

def bpc31S1 : SymState := (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).2.1

theorem bpc31W_n : (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).1 = 152 := by
  kernel_rfl

theorem bpc31C1_stop (ρ : Valuation) :
    γC ρ (symEvalWindowTB bfTB 152 bpc31S0 bpc31C0).2.2 = .next .stop := by
  kernel_rfl

theorem bpc31_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 152 (γS ρ σ bpc31S0) (γC ρ bpc31C0) ch
      = .ok (.next .stop, γS ρ σ bpc31S1, ch) := by
  have h := symEvalWindowTB_refines' bpc31W_n ρ σ ch hag
  rw [bpc31C1_stop ρ] at h
  exact h

theorem bpc31_proj_pre (ρ : Valuation) (σ : ExecState) :
    absRaftNode (γS ρ σ bpc31S0) ⟨31⟩
      = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩ := by
  kernel_rfl

theorem bpc31_proj_post (ρ : Valuation) (σ : ExecState)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1) :
    absRaftNode (γS ρ σ bpc31S1) ⟨31⟩
      = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  have hproj : absRaftNode (γS ρ σ bpc31S1) ⟨31⟩
      = some ⟨0, unrm 5 (ρ.ints 1), 0, 3, 1, 1⟩ := by
    kernel_rfl
  rw [hproj, unrm_id hvote 5]
  with_unfolding_all rfl

/-! ## The allocation-symbolic equation at the re-sited fixture -/

/-- **THE RE-SITED ALLOCATION-SYMBOLIC EQUATION**: same shape as
`becomePreCandidate_handler_eq_alloc`, with a LIVE placement
quantifier — at this fixture, `r` may genuinely move the footprint
(any injection fixing the statics `[0,31)` with the shift law). -/
theorem becomePreCandidate_handler_eq_alloc31
    (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (ch : Choices)
    {r : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σF : ExecState}
    (hF : FrameSim r na₀ na fr (γS ρ σ bpc31S0) σF) :
    ∃ σFfin,
      stepFnIter 152 σF (renameConfig r (γC ρ bpc31C0)) ch
        = .ok (.next .stop, σFfin, ch)
      ∧ FrameSim r na₀ na fr (γS ρ σ bpc31S1) σFfin
      ∧ absRaftNode σF ⟨r 31⟩ = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σFfin ⟨r 31⟩
          = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  have hrun := bpc31_span ρ σ ch hag
  have hsim := stepFnIter_sim (na₀ := na₀) (na := na) 152 hF
    (γC ρ bpc31C0) ch
  obtain ⟨tF, htF, htrip⟩ := hsim.ok_inv hrun
  obtain ⟨cF, σFfin, chF⟩ := tF
  obtain ⟨hc, hs, hch⟩ := htrip
  dsimp only at hc hs hch
  subst hch
  have hcstop : renameConfig r (Machine.Config.next .stop)
      = Machine.Config.next .stop := rfl
  rw [hcstop] at hc
  subst hc
  exact ⟨σFfin, htF, hs, absRaftNode_ren hF (bpc31_proj_pre ρ σ),
    absRaftNode_ren hs (bpc31_proj_post ρ σ hvote)⟩

/-- The identity-placement corollary (the re-sited fixture's concrete
form; there is no shipped predecessor at this placement — this IS its
concrete equation). -/
theorem becomePreCandidate_handler_eq_alloc31_id
    (ρ : Valuation) (σ : ExecState) (hag : bfTB.Agrees σ)
    (hvote : IntKind.normalize .uint64 (ρ.ints 1) = ρ.ints 1)
    (ch : Choices) :
    ∃ σfin,
      stepFnIter 152 (γS ρ σ bpc31S0) (γC ρ bpc31C0) ch
        = .ok (.next .stop, σfin, ch)
      ∧ absRaftNode (γS ρ σ bpc31S0) ⟨31⟩
          = some ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨31⟩
          = some (specBecomePreCandidate ⟨0, ρ.ints 1, ρ.ints 2, 0, 1, 1⟩) := by
  have hF : FrameSim (ρT 52 0) 52 52 [] (γS ρ σ bpc31S0) (γS ρ σ bpc31S0) :=
    frameSim_seed rfl (fun f _ => renameStmt_ρT_zero 52 f.body)
  obtain ⟨σfin, hrun, _, hpre, hpost⟩ :=
    becomePreCandidate_handler_eq_alloc31 ρ σ hag hvote ch hF
  have hcall : renameConfig (ρT 52 0) (γC ρ bpc31C0) = γC ρ bpc31C0 := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have haddr : (⟨ρT 52 0 31⟩ : Addr) = ⟨31⟩ := rfl
  rw [haddr] at hpre hpost
  exact ⟨σfin, hrun, hpre, hpost⟩

/-! ## The NON-identity witness (U5's honest gap, closed) -/

/-- The twin program's loc support, computed once: every body `locLit`
sits below 31 (`#eval`-checked first, probe `LocSupProbe`). -/
theorem wBase_funcSup : funcListSup wBase.functions.toList = 31 := by
  kernel_rfl

/-- Any renaming fixing the static range `[0,31)` leaves every twin
function body invariant — the generic `bodies_inv` discharge for
re-sited fixtures. -/
theorem wBase_bodies_inv {r : Nat → Nat} (hid : ∀ x < 31, r x = x) :
    ∀ f ∈ wBase.functions.toList, renameStmt r f.body = f.body := by
  intro f hf
  refine renameStmt_id (n := 31) hid f.body ?_
  have h1 := funcListSup_mem hf
  rw [wBase_funcSup] at h1
  exact h1

/-- The relocation: swap the raft cell's address with its neighbor
(31 ↔ 32), fix everything else — injective, shift-law at 33. -/
def swap31_32 : Nat → Nat := fun x =>
  if x = 31 then 32 else if x = 32 then 31 else x

theorem swap31_32_spec : ShiftSpec swap31_32 33 33 := by
  constructor
  · intro x y h
    simp only [swap31_32] at h
    by_cases hx1 : x = 31 <;> by_cases hx2 : x = 32 <;>
      by_cases hy1 : y = 31 <;> by_cases hy2 : y = 32 <;>
      simp [hx1, hx2, hy1, hy2] at h <;> omega
  · intro k
    show swap31_32 (33 + k) = 33 + k
    simp only [swap31_32]
    rw [if_neg (by omega), if_neg (by omega)]

/-- The concretely relocated placement: the witness fixture's
rename-image under the swap (raft cell now at base 32). -/
def bpc31σF : ExecState := renameState swap31_32 (γS bpcρw wBase bpc31S0)

theorem bpc31_relocSim :
    FrameSim swap31_32 33 33 [] (γS bpcρw wBase bpc31S0) bpc31σF :=
  frameSim_relocate swap31_32_spec (by show 33 ≤ 52; decide)
    (wBase_bodies_inv (fun x hx => by
      simp only [swap31_32]
      rw [if_neg (by omega), if_neg (by omega)]))

/-- **THE NON-IDENTITY WITNESS**: the handler run at a placement
where the raft cell has MOVED (base 32, not the fixture's 31) — every
premise of the allocation-symbolic equation discharged concretely,
the `FrameSim` premise by `frameSim_relocate` at a genuinely
non-identity relocation. This is the liveness demonstration U5
recorded as its honest gap. -/
theorem becomePreCandidate_handler_eq_alloc31_witness_shifted :
    ∃ σfin,
      stepFnIter 152 bpc31σF
        (.retV (.addr (.base ⟨32⟩))
          (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop)) []
        = .ok (.next .stop, σfin, [])
      ∧ absRaftNode bpc31σF ⟨32⟩ = some ⟨0, 7, 2, 0, 1, 1⟩
      ∧ absRaftNode σfin ⟨32⟩
          = some (specBecomePreCandidate ⟨0, 7, 2, 0, 1, 1⟩) := by
  obtain ⟨σfin, hrun, _, hpre, hpost⟩ :=
    becomePreCandidate_handler_eq_alloc31 bpcρw wBase ⟨rfl, rfl, rfl, rfl⟩
      (by decide) [] bpc31_relocSim
  have hcall : renameConfig swap31_32 (γC bpcρw bpc31C0)
      = .retV (.addr (.base ⟨32⟩))
          (.callArgsK ⟨"raft.raft.becomePreCandidate"⟩ [] [] [] [] .stop) := by
    with_unfolding_all rfl
  rw [hcall] at hrun
  have haddr : (⟨swap31_32 31⟩ : Addr) = ⟨32⟩ := by
    simp [swap31_32]
  rw [haddr] at hpre hpost
  exact ⟨σfin, hrun, hpre, hpost⟩

end GoLean.RaftSeam
