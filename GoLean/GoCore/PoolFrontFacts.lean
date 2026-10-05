import GoLean.GoCore.PoolStatement

/-! The driver's pre-fuel classifications. [AGENT Codex, pool grind] 2026-10-05. -/
namespace GoLean.GoCore.PoolFrontFacts
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics.Pool

variable {ctx : ProgramCtx} {m : MultiConfig} {r : RaceState} {ch ch' : Choices}

theorem continue_iff :
    (∃ rec, Continue ctx m ch ch' rec) ↔
      m.panicMsg? = none ∧ runnableIdxs ctx m.shared m.threads ≠ [] ∧
        ((m.mainOutcome? = none ∧ ch = ch') ∨
          ∃ s, m.mainOutcome? = some s ∧ Choices.consumeAt .l5ExitWindow 2 ch = (1, ch')) := by
  constructor
  · rintro ⟨rec, h⟩
    cases h with
    | running hp hm hr => exact ⟨hp, hr, .inl ⟨hm, rfl⟩⟩
    | window hp hm hr hc => exact ⟨hp, hr, .inr ⟨_, hm, (Choices.consumeAtE_inv hc).2⟩⟩
  · rintro ⟨hp, hr, ⟨hm, rfl⟩ | ⟨s, hm, hc⟩⟩
    · exact ⟨[], .running hp hm hr⟩
    · refine ⟨PickRecord.ofPick .l5ExitWindow 2 1, .window hp hm hr ?_⟩
      simp only [Choices.consumeAtE_eq, hc]

theorem normal_iff {s : Store} :
    (∃ rec, PoolFinish ctx m r ch rec (.normal s ch') 0) ↔
      m.panicMsg? = none ∧ m.mainOutcome? = some s ∧
        ((runnableIdxs ctx m.shared m.threads = [] ∧ ch = ch') ∨
          (runnableIdxs ctx m.shared m.threads ≠ [] ∧
            Choices.consumeAt .l5ExitWindow 2 ch = (0, ch'))) := by
  constructor
  · rintro ⟨rec, h⟩
    cases h with
    | normal hp hm hr => exact ⟨hp, hm, .inl ⟨hr, rfl⟩⟩
    | exitWindow hp hm hr hc => exact ⟨hp, hm, .inr ⟨hr, (Choices.consumeAtE_inv hc).2⟩⟩
  · rintro ⟨hp, hm, ⟨hr, rfl⟩ | ⟨hr, hc⟩⟩
    · exact ⟨[], .normal hp hm hr⟩
    · refine ⟨PickRecord.ofPick .l5ExitWindow 2 0, .exitWindow hp hm hr ?_⟩
      simp only [Choices.consumeAtE_eq, hc]

theorem aborted_iff {msg : String} :
    PoolFinish ctx m r ch [] (.aborted msg ch) 0 ↔ m.panicMsg? = some msg := by
  constructor
  · intro h; cases h; assumption
  · exact PoolFinish.aborted

theorem deadlock_iff :
    PoolFinish ctx m r ch [] (.deadlock ch) 0 ↔ PoolDeadlock ctx m := by
  constructor
  · intro h; cases h; assumption
  · exact PoolFinish.deadlock

-- Shared simp sets apply across the complete front case tree.
set_option linter.unusedSimpArgs false in
theorem front_continue  :
    front ctx m ch = .ok (.inr ch') ↔ ∃ rec, Continue ctx m ch ch' rec := by
  by_cases he : m.threads.isEmpty = true
  · have ht := Array.empty_of_isEmpty he
    simp [front, he, ht, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
      runnableIdxs, PoolDeadlock, eq_comm, continue_iff]
  · rcases hc : Choices.consumeAt .l5ExitWindow 2 ch with ⟨pick, tail⟩
    have hb := Choices.consumeAt_fst_lt (site := ChoiceSite.l5ExitWindow) (ch := ch)
      (bound := 2) (by omega)
    rw [hc] at hb
    have hp : pick = 0 ∨ pick = 1 := by omega
    rcases hp with rfl | rfl <;>
      cases hpanic : m.panicMsg? <;>
      cases hmain : m.mainOutcome? <;>
      cases hrun : runnableIdxs ctx m.shared m.threads <;>
      simp [front, he, hpanic, hmain, hrun, hc, PoolDeadlock, eq_comm, continue_iff]

-- Shared simp sets apply across the complete front case tree.
set_option linter.unusedSimpArgs false in
theorem front_normal {s : Store} :
    front ctx m ch = .ok (.inl (s, ch')) ↔ ∃ rec, PoolFinish ctx m r ch rec (.normal s ch') 0 := by
  by_cases he : m.threads.isEmpty = true
  · have ht := Array.empty_of_isEmpty he
    simp [front, he, ht, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
      runnableIdxs, PoolDeadlock, eq_comm, normal_iff]
  · rcases hc : Choices.consumeAt .l5ExitWindow 2 ch with ⟨pick, tail⟩
    have hb := Choices.consumeAt_fst_lt (site := ChoiceSite.l5ExitWindow) (ch := ch)
      (bound := 2) (by omega)
    rw [hc] at hb
    have hp : pick = 0 ∨ pick = 1 := by omega
    rcases hp with rfl | rfl <;>
      cases hpanic : m.panicMsg? <;>
      cases hmain : m.mainOutcome? <;>
      cases hrun : runnableIdxs ctx m.shared m.threads <;>
      simp [front, he, hpanic, hmain, hrun, hc, PoolDeadlock, eq_comm, normal_iff]

-- Shared simp sets apply across the complete front case tree.
set_option linter.unusedSimpArgs false in
theorem front_aborted {msg : String} :
    front ctx m ch = .error (.panic msg) ↔ PoolFinish ctx m r ch [] (.aborted msg ch) 0 := by
  by_cases he : m.threads.isEmpty = true
  · have ht := Array.empty_of_isEmpty he
    simp [front, he, ht, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
      runnableIdxs, PoolDeadlock, eq_comm, aborted_iff]
  · rcases hc : Choices.consumeAt .l5ExitWindow 2 ch with ⟨pick, tail⟩
    have hb := Choices.consumeAt_fst_lt (site := ChoiceSite.l5ExitWindow) (ch := ch)
      (bound := 2) (by omega)
    rw [hc] at hb
    have hp : pick = 0 ∨ pick = 1 := by omega
    rcases hp with rfl | rfl <;>
      cases hpanic : m.panicMsg? <;>
      cases hmain : m.mainOutcome? <;>
      cases hrun : runnableIdxs ctx m.shared m.threads <;>
      simp [front, he, hpanic, hmain, hrun, hc, PoolDeadlock, eq_comm, aborted_iff]

-- Shared simp sets apply across the complete front case tree.
set_option linter.unusedSimpArgs false in
theorem front_deadlock  :
    front ctx m ch = .error .deadlock ↔ PoolFinish ctx m r ch [] (.deadlock ch) 0 := by
  by_cases he : m.threads.isEmpty = true
  · have ht := Array.empty_of_isEmpty he
    simp [front, he, ht, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
      runnableIdxs, PoolDeadlock, eq_comm, deadlock_iff]
  · rcases hc : Choices.consumeAt .l5ExitWindow 2 ch with ⟨pick, tail⟩
    have hb := Choices.consumeAt_fst_lt (site := ChoiceSite.l5ExitWindow) (ch := ch)
      (bound := 2) (by omega)
    rw [hc] at hb
    have hp : pick = 0 ∨ pick = 1 := by omega
    rcases hp with rfl | rfl <;>
      cases hpanic : m.panicMsg? <;>
      cases hmain : m.mainOutcome? <;>
      cases hrun : runnableIdxs ctx m.shared m.threads <;>
      simp [front, he, hpanic, hmain, hrun, hc, PoolDeadlock, eq_comm, deadlock_iff]

-- Shared simp sets apply across the complete front case tree.
set_option linter.unusedSimpArgs false in
theorem front_refusal {rr : Refusal} :
    front ctx m ch = .error (.refusal rr) ↔ m.threads.isEmpty = true ∧ rr = .internal "thread pool without a main goroutine" := by
  by_cases he : m.threads.isEmpty = true
  · have ht := Array.empty_of_isEmpty he
    simp [front, he, ht, MultiConfig.panicMsg?, MultiConfig.mainOutcome?,
      runnableIdxs, PoolDeadlock, eq_comm]
  · rcases hc : Choices.consumeAt .l5ExitWindow 2 ch with ⟨pick, tail⟩
    have hb := Choices.consumeAt_fst_lt (site := ChoiceSite.l5ExitWindow) (ch := ch)
      (bound := 2) (by omega)
    rw [hc] at hb
    have hp : pick = 0 ∨ pick = 1 := by omega
    rcases hp with rfl | rfl <;>
      cases hpanic : m.panicMsg? <;>
      cases hmain : m.mainOutcome? <;>
      cases hrun : runnableIdxs ctx m.shared m.threads <;>
      simp [front, he, hpanic, hmain, hrun, hc, PoolDeadlock, eq_comm]

end GoLean.GoCore.PoolFrontFacts
