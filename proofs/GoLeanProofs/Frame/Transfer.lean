import GoLeanProofs.Frame.StepSim
import GoLeanProofs.FuelMeasure

/-!
# The executable frame theorem: iterated simulation and the transfer
corollaries (design §1)

* `stepFnIter_sim` — the per-step simulation, iterated.
* `execStmtLoop_ren` — success-run transfer at the driver: a canonical
  completion transfers to the framed placement at the SAME fuel and the
  SAME choice stream, with the terminal states `FrameSim`-related and
  the outcome tag preserved.
* `completesIn_ren` / completion transfer — the fuel-measure segments
  proved at the canonical placement reach every admissible framed
  placement (the headline's completion half).
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

set_option linter.unusedSimpArgs false

/-- `renameCont` reaches `.stop` only from `.stop`. -/
theorem renameCont_eq_stop_iff {ρ : Nat → Nat} {k : Cont} :
    renameCont ρ k = .stop ↔ k = .stop := by
  cases k <;> simp [renameCont]

theorem stepFnIter_sim {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} :
    ∀ (n : Nat) {σ σF : ExecState} (_ : FrameSim ρ na₀ na fr σ σF)
      (c : Config) (ch : Choices),
      ExSim (TripSim ρ na₀ na fr)
        (stepFnIter n σ c ch) (stepFnIter n σF (renameConfig ρ c) ch) := by
  intro n
  induction n with
  | zero =>
      intro σ σF hS c ch
      exact ExSim.ok ⟨rfl, hS, rfl⟩
  | succ m ih =>
      intro σ σF hS c ch
      simp only [stepFnIter]
      refine ExSim.bind (stepFn_sim hS c ch) ?_
      intro r rF hr
      obtain ⟨c', σ', ch'⟩ := r
      obtain ⟨cF', σF', chF'⟩ := rF
      obtain ⟨h1, h2, h3⟩ := hr
      dsimp only at h1 h2 h3
      subst h1 h3
      exact ih h2 c' _

/-- The outcome relation at the driver's terminals: same tag, related
states. -/
def OutSim (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    ExecOutcome × Choices → ExecOutcome × Choices → Prop
  | (.normal σ', ch), (.normal σF', chF) =>
      FrameSim ρ na₀ na fr σ' σF' ∧ chF = ch
  | (.returned σ', ch), (.returned σF', chF) =>
      FrameSim ρ na₀ na fr σ' σF' ∧ chF = ch
  | (.broke σ', ch), (.broke σF', chF) =>
      FrameSim ρ na₀ na fr σ' σF' ∧ chF = ch
  | (.continued σ', ch), (.continued σF', chF) =>
      FrameSim ρ na₀ na fr σ' σF' ∧ chF = ch
  | _, _ => False

/-- **Success-run transfer at the driver**: a canonical `execStmtLoop`
completion transfers to the framed run at the same fuel, the same
stream, the same outcome tag, and `FrameSim`-related terminal states. -/
theorem execStmtLoop_ren {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} :
    ∀ (fuel : Nat) {σ σF : ExecState} (_ : FrameSim ρ na₀ na fr σ σF)
      {c : Config} {ch : Choices} {out : ExecOutcome} {ch' : Choices},
      execStmtLoop fuel σ c ch = .ok (out, ch') →
      ∃ outF, execStmtLoop fuel σF (renameConfig ρ c) ch = .ok (outF, ch')
        ∧ OutSim ρ na₀ na fr (out, ch') (outF, ch') := by
  intro fuel
  induction fuel with
  | zero =>
      intro σ σF hS c ch out ch' h
      cases c <;> first
        | (simp [execStmtLoop] at h)
        | skip
      case next k =>
          cases k
          case stop =>
            simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
            exact ⟨.normal σF, by simp [execStmtLoop, renameConfig, renameCont],
              hS, rfl⟩
          all_goals simp [execStmtLoop] at h
      case returning k =>
          cases k
          case stop =>
            simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
            exact ⟨.returned σF, by simp [execStmtLoop, renameConfig, renameCont],
              hS, rfl⟩
          all_goals simp [execStmtLoop] at h
      case breaking k =>
          cases k
          case stop =>
            simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
            exact ⟨.broke σF, by simp [execStmtLoop, renameConfig, renameCont],
              hS, rfl⟩
          all_goals simp [execStmtLoop] at h
      case continuing k =>
          cases k
          case stop =>
            simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
            exact ⟨.continued σF, by simp [execStmtLoop, renameConfig, renameCont],
              hS, rfl⟩
          all_goals simp [execStmtLoop] at h
  | succ m ih =>
      intro σ σF hS c ch out ch' h
      have hstep_tac : ∀ {c₀ : Config},
          execStmtLoop (m + 1) σ c₀ ch = .ok (out, ch') →
          (∀ (r : Config × ExecState × Choices),
            stepFn σ c₀ ch = .ok r →
            execStmtLoop (m + 1) σ c₀ ch
              = execStmtLoop m r.2.1 r.1 r.2.2) →
          True := fun _ _ => trivial
      cases c <;> first
        | (simp [execStmtLoop] at h)
        | skip
      case next k =>
          cases hk : k
          case stop =>
              subst hk
              simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1, ← h.2]
              exact ⟨.normal σF, by simp [execStmtLoop, renameConfig, renameCont],
                hS, rfl⟩
          all_goals
            subst hk
            simp only [execStmtLoop, bind_eq_ok] at h
            obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
            obtain ⟨rF, hstepF, htrip⟩ := (stepFn_sim hS _ ch).ok_inv hstep
            obtain ⟨cF₁, σF₁, chF₁⟩ := rF
            obtain ⟨h1, h2, h3⟩ := htrip
            dsimp only at h1 h2 h3
            subst h1
            subst h3
            obtain ⟨outF, hloopF, hout⟩ := ih h2 hrest
            refine ⟨outF, ?_, hout⟩
            simp only [execStmtLoop, renameConfig, renameCont]
            rw [bind_eq_ok]
            exact ⟨_, hstepF, hloopF⟩
      case returning k =>
          cases hk : k
          case stop =>
              subst hk
              simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1, ← h.2]
              exact ⟨.returned σF, by simp [execStmtLoop, renameConfig, renameCont],
                hS, rfl⟩
          all_goals
            subst hk
            simp only [execStmtLoop, bind_eq_ok] at h
            obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
            obtain ⟨rF, hstepF, htrip⟩ := (stepFn_sim hS _ ch).ok_inv hstep
            obtain ⟨cF₁, σF₁, chF₁⟩ := rF
            obtain ⟨h1, h2, h3⟩ := htrip
            dsimp only at h1 h2 h3
            subst h1
            subst h3
            obtain ⟨outF, hloopF, hout⟩ := ih h2 hrest
            refine ⟨outF, ?_, hout⟩
            simp only [execStmtLoop, renameConfig, renameCont]
            rw [bind_eq_ok]
            exact ⟨_, hstepF, hloopF⟩
      case breaking k =>
          cases hk : k
          case stop =>
              subst hk
              simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1, ← h.2]
              exact ⟨.broke σF, by simp [execStmtLoop, renameConfig, renameCont],
                hS, rfl⟩
          all_goals
            subst hk
            simp only [execStmtLoop, bind_eq_ok] at h
            obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
            obtain ⟨rF, hstepF, htrip⟩ := (stepFn_sim hS _ ch).ok_inv hstep
            obtain ⟨cF₁, σF₁, chF₁⟩ := rF
            obtain ⟨h1, h2, h3⟩ := htrip
            dsimp only at h1 h2 h3
            subst h1
            subst h3
            obtain ⟨outF, hloopF, hout⟩ := ih h2 hrest
            refine ⟨outF, ?_, hout⟩
            simp only [execStmtLoop, renameConfig, renameCont]
            rw [bind_eq_ok]
            exact ⟨_, hstepF, hloopF⟩
      case continuing k =>
          cases hk : k
          case stop =>
              subst hk
              simp only [execStmtLoop, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.1, ← h.2]
              exact ⟨.continued σF, by simp [execStmtLoop, renameConfig, renameCont],
                hS, rfl⟩
          all_goals
            subst hk
            simp only [execStmtLoop, bind_eq_ok] at h
            obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
            obtain ⟨rF, hstepF, htrip⟩ := (stepFn_sim hS _ ch).ok_inv hstep
            obtain ⟨cF₁, σF₁, chF₁⟩ := rF
            obtain ⟨h1, h2, h3⟩ := htrip
            dsimp only at h1 h2 h3
            subst h1
            subst h3
            obtain ⟨outF, hloopF, hout⟩ := ih h2 hrest
            refine ⟨outF, ?_, hout⟩
            simp only [execStmtLoop, renameConfig, renameCont]
            rw [bind_eq_ok]
            exact ⟨_, hstepF, hloopF⟩
      all_goals
        simp only [execStmtLoop, bind_eq_ok] at h
        obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hrest⟩ := h
        obtain ⟨rF, hstepF, htrip⟩ := (stepFn_sim hS _ ch).ok_inv hstep
        obtain ⟨cF₁, σF₁, chF₁⟩ := rF
        obtain ⟨h1, h2, h3⟩ := htrip
        dsimp only at h1 h2 h3
        subst h1
        subst h3
        obtain ⟨outF, hloopF, hout⟩ := ih h2 hrest
        refine ⟨outF, ?_, hout⟩
        simp only [execStmtLoop, renameConfig, renameCont]
        rw [bind_eq_ok]
        exact ⟨_, hstepF, hloopF⟩

/-- **Completion transfer** (design §1): `CompletesIn` at the canonical
placement reaches every `FrameSim`-related framed placement — same
fuel, every stream. -/
theorem completesIn_ren {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hS : FrameSim ρ na₀ na fr σ σF)
    {f : Nat} {c : Config} (h : CompletesIn f σ c) :
    CompletesIn f σF (renameConfig ρ c) := by
  intro ch
  obtain ⟨out, ch', hrun⟩ := h ch
  obtain ⟨outF, hrunF, _⟩ := execStmtLoop_ren f hS hrun
  exact ⟨outF, ch', hrunF⟩

end GoLean.Frame
