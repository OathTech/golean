import GoLean.GoCore.RelationalOutcome
import GoLean.GoCore.RelationalSound

namespace GoLean.GoCore.Relational

open Machine ExecutionStatement

/-- The two sequential loop entry points implement the same classification,
including errors and fuel boundaries. -/
theorem runConfig_eq_loop (ctx : ProgramCtx) (fuel : Nat) (s : Store) (c : Config)
    (ch : Choices) : runConfig ctx fuel s c ch = execStmtLoop ctx fuel s c ch := by
  fun_induction runConfig ctx fuel s c ch <;>
    rw [execStmtLoop_unfold] <;> simp_all

/-- Every semantic pick is realized while leaving an arbitrary suffix. -/
theorem Selection.realize {site : ChoiceSite} {bound pick : Nat} {records : List PickRecord}
    (h : Selection site bound pick records) (tail : Choices) :
    ∃ ch, Choices.consumeAtE site bound ch = (pick, tail, records) := by
  obtain ⟨hp, rfl⟩ := h
  by_cases hb : bound ≤ 1
  · have hz : pick = 0 := by omega
    subst pick
    exact ⟨tail, by simp [Choices.consumeAtE_le_one hb, PickRecord.ofPick, hb]⟩
  · refine ⟨pick :: tail, ?_⟩
    rw [Choices.consumeAtE_eq, Choices.consumeAt_of_lt (by omega)]
    simp only [Choices.consume, show max 1 bound = bound by omega, Nat.mod_eq_of_lt (by omega : pick < bound)]

theorem selection_of_consume {site : ChoiceSite} {bound pick : Nat} {records : List PickRecord}
    {ch tail : Choices} (h : Choices.consumeAtE site bound ch = (pick, tail, records)) :
    Selection site bound pick records := by
  obtain ⟨hr, hc⟩ := Choices.consumeAtE_inv h
  refine ⟨?_, hr⟩
  by_cases hb : bound ≤ 1
  · rw [Choices.consumeAt_le_one hb] at hc
    cases hc
    omega
  · have hp : (Choices.consumeAt site bound ch).1 < bound := Choices.consumeAt_fst_lt (by omega)
    rw [hc] at hp
    exact Nat.lt_of_lt_of_le hp (Nat.le_max_right _ _)

def Ending.asFinish (s : Store) (ch : Choices) : Ending → FinishOutcome
  | .normal => .normal s ch
  | .deadlock => .deadlock s ch
  | .panic _ _ text => .aborted text s ch
  | .renderingRefusal _ _ reason => .refused reason s ch

/-- Terminal boundary realization preserves its records and may leave any
residual tape, including after panic rendering. -/
theorem Boundary.realize {ctx : ProgramCtx} {a : State} {records : List PickRecord}
    {ending : Ending} {cost : Nat} (h : Boundary ctx a records ending cost) (tail : Choices) :
    ∃ ch, Finish ctx a.store a.control ch records (ending.asFinish a.store tail) cost := by
  cases h with
  | normal => exact ⟨tail, .normal⟩
  | send => exact ⟨tail, .blocked (.inl ⟨_, _, _, rfl⟩)⟩
  | recv => exact ⟨tail, .blocked (.inr (.inl ⟨_, _, _, _, _, rfl⟩))⟩
  | select => exact ⟨tail, .blocked (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))⟩
  | sync => exact ⟨tail, .blocked (.inr (.inr (.inr ⟨_, _, _, _, rfl⟩)))⟩
  | panic ha hp hm =>
    obtain ⟨ch, hc⟩ := hp.realize tail
    exact ⟨ch, .aborted ha hc hm⟩
  | renderingRefusal ha hp hm =>
    obtain ⟨ch, hc⟩ := hp.realize tail
    exact ⟨ch, .abortRefused ha hc hm⟩

/-- The finishing consultation is stitched to the same tape as the run. -/
theorem Completed.realize {ctx : ProgramCtx} {a b : State} {ls : List StepLabel}
    {records : List PickRecord} {ending : Ending} {cost : Nat}
    (h : Completed ctx a ls b records ending cost) (tail : Choices) :
    ∃ ch middle finishCost,
      Prefix ctx ls.length a.store a.control ch ls b.store b.control middle ∧
      Finish ctx b.store b.control middle records (ending.asFinish b.store tail) finishCost ∧
      cost = ls.length + finishCost := by
  obtain ⟨fc, hr, hf, hc⟩ := h
  obtain ⟨middle, hm⟩ := hf.realize tail
  obtain ⟨ch, hp⟩ := hr.realize middle
  exact ⟨ch, middle, fc, hp, hm, hc⟩

/-- The normal subset has an exact fuel-bounded correspondence, with no
domain premise. Fatal/refusing runs are not claimed to be normal runs. -/
theorem normal_run_iff {ctx : ProgramCtx} {a : State} {s : Store} {fuel : Nat} :
    (∃ ch tail, execStmtLoop ctx fuel a.store a.control ch = .ok (s, tail)) ↔
    ∃ ls, ls.length ≤ fuel ∧ Run ctx a ls ⟨.next .stop, s⟩ := by
  constructor
  · rintro ⟨ch, tail, h⟩
    obtain ⟨n, hn, ls, hp⟩ := (ExecutionStatement.run_ok_iff ctx fuel _ _ _ _ _).mp h
    exact ⟨ls, by rwa [prefix_length hp], of_prefix hp⟩
  · rintro ⟨ls, hn, h⟩
    obtain ⟨ch, hp⟩ := h.realize []
    exact ⟨ch, [], (ExecutionStatement.run_ok_iff ctx fuel _ _ _ _ _).mpr
      ⟨ls.length, hn, ls, hp⟩⟩

theorem Boundary.zero_cost_iff {ctx : ProgramCtx} {a : State} :
    (∃ ending, Boundary ctx a [] ending 0) ↔ ZeroCost a.control := by
  constructor
  · rintro ⟨ending, h⟩
    cases h <;> simp [ZeroCost, Blocked]
  · rcases a with ⟨c, s⟩
    rintro (hc | hb)
    · change c = .next .stop at hc
      subst c; exact ⟨.normal, .normal⟩
    · change Blocked c at hb
      rcases hb with ⟨ch, v, k, rfl⟩ | ⟨ch, targets, elem, env, k, rfl⟩ |
          ⟨clauses, env, k, rfl⟩ | ⟨op, loc, env, k, rfl⟩
      · exact ⟨.deadlock, .send⟩
      · exact ⟨.deadlock, .recv⟩
      · exact ⟨.deadlock, .select⟩
      · exact ⟨.deadlock, .sync⟩

/-- Exact budget exhaustion in both directions, with no refusal-freedom
premise. A different choice may finish earlier. -/
theorem exhaustion_iff {ctx : ProgramCtx} {a : State} {fuel : Nat} :
    (∃ ch, execStmtLoop ctx fuel a.store a.control ch = .error .fuelOut) ↔
    ∃ ls b, Exhausted ctx a ls b fuel := by
  constructor
  · rintro ⟨ch, h⟩
    obtain ⟨ls, s, c, tail, hp, hz⟩ := (run_fuelOut_iff ctx fuel _ _ ch).mp h
    exact ⟨ls, ⟨c, s⟩, of_prefix hp, prefix_length hp,
      fun h => hz (Boundary.zero_cost_iff.mp h)⟩
  · rintro ⟨ls, b, hr, hn, hz⟩
    obtain ⟨ch, hp⟩ := hr.realize []
    rw [hn] at hp
    exact ⟨ch, (run_fuelOut_iff ctx fuel _ _ ch).mpr
      ⟨ls, b.store, b.control, [], hp, fun h => hz (Boundary.zero_cost_iff.mpr h)⟩⟩

/-- Every successful panic rendering, retaining the payload chain and final
consultation, corresponds to the actual sequential panic outcome. -/
theorem panic_run_iff {ctx : ProgramCtx} {a : State} {fuel : Nat} {text : String} :
    (∃ ch, execStmtLoop ctx fuel a.store a.control ch = .error (.terminal (.panic text))) ↔
    ∃ ls b records first rest cost,
      Completed ctx a ls b records (.panic first rest text) cost ∧ cost ≤ fuel := by
  constructor
  · rintro ⟨ch, h⟩
    obtain ⟨n, ls, s, c, middle, tail, records, hn, hp, hf⟩ :=
      (run_panic_iff ctx fuel _ _ ch text).mp h
    cases hf with
    | aborted ha hc hm =>
      exact ⟨ls, ⟨c, s⟩, records, _, _, n + 1,
        ⟨1, of_prefix hp, .panic ha (selection_of_consume hc) hm,
          by rw [prefix_length hp]⟩, hn⟩
  · rintro ⟨ls, b, records, first, rest, cost, h, hn⟩
    obtain ⟨ch, middle, finishCost, hp, hf, hc⟩ := h.realize []
    simp only [Ending.asFinish] at hf
    have he : finishCost = 1 := (finish_aborted_stepFn hf).1
    subst finishCost
    exact ⟨ch, (run_panic_iff ctx fuel _ _ ch text).mpr
      ⟨ls.length, ls, b.store, b.control, middle, [], records, by omega, hp, hf⟩⟩

/-- A blocked endpoint finishes at zero extra cost, even with no fuel left. -/
theorem deadlock_run_iff {ctx : ProgramCtx} {a : State} {fuel : Nat} :
    (∃ ch, execStmtLoop ctx fuel a.store a.control ch = .error (.terminal .deadlock)) ↔
    ∃ ls b cost, Completed ctx a ls b [] .deadlock cost ∧ cost ≤ fuel := by
  constructor
  · rintro ⟨ch, h⟩
    obtain ⟨n, hn, ls, s, c, middle, hp, hf⟩ := (run_deadlock_iff ctx fuel _ _ ch).mp h
    cases hf with
    | blocked hb =>
      have boundary : Boundary ctx ⟨c, s⟩ [] .deadlock 0 := by
        rcases hb with ⟨ch, v, k, rfl⟩ | ⟨ch, targets, elem, env, k, rfl⟩ |
            ⟨clauses, env, k, rfl⟩ | ⟨op, loc, env, k, rfl⟩
        · exact .send
        · exact .recv
        · exact .select
        · exact .sync
      exact ⟨ls, ⟨c, s⟩, n,
        ⟨0, of_prefix hp, boundary, by simp [prefix_length hp]⟩, hn⟩
  · rintro ⟨ls, b, cost, h, hn⟩
    obtain ⟨ch, middle, finishCost, hp, hf, hc⟩ := h.realize []
    simp only [Ending.asFinish] at hf
    have he : finishCost = 0 := by
      generalize hctrl : b.control = c at hf
      cases hf
      rfl
    subst finishCost
    have ht : middle = [] := by
      generalize hctrl : b.control = c at hf
      cases hf
      rfl
    subst middle
    exact ⟨ch, (run_deadlock_iff ctx fuel _ _ ch).mpr
      ⟨ls.length, by omega, ls, b.store, b.control, [], hp, hf⟩⟩

/-- Rendering refusal remains an actual driver error. This is deliberately
one-way: other operations can refuse with the same reason. -/
theorem Completed.rendering_refusal {ctx : ProgramCtx} {a b : State}
    {ls : List StepLabel} {records : List PickRecord} {first : PanicEntry}
    {rest : List PanicEntry} {reason : Refusal} {cost fuel : Nat}
    (h : Completed ctx a ls b records (.renderingRefusal first rest reason) cost)
    (enough : cost ≤ fuel) :
    ∃ ch, execStmtLoop ctx fuel a.store a.control ch = .error (.refusal reason) := by
  obtain ⟨ch, middle, finishCost, hp, hf, hc⟩ := h.realize []
  simp only [Ending.asFinish] at hf
  obtain ⟨fc, _, boundary, _⟩ := h
  have ha : b.control.abort? = some (first, rest) := by cases boundary; assumption
  have hfCost : finishCost = 1 := by
    generalize hctrl : b.control = c at hf
    cases hf
    rfl
  subst finishCost
  have stepError := (finish_refused_step ctx b.store b.control middle first rest reason ha).mp
    ⟨records, [], hf⟩
  have hz : ¬ ZeroCost b.control := by
    rw [(abort?_some ha).1]
    simp [ZeroCost, Blocked]
  refine ⟨ch, ?_⟩
  rw [hp.run_le (by omega), execStmtLoop_nonZero hz]
  obtain ⟨n, hn⟩ : ∃ n, fuel - ls.length = n + 1 := ⟨fuel - ls.length - 1, by omega⟩
  rw [hn]
  simp [stepError, Except.bind]

end GoLean.GoCore.Relational
