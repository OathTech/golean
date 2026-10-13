import GoLean.GoCore.RelationalPhase
import GoLean.GoCore.RelationalSound

namespace GoLean.GoCore.Relational

open Machine ExecutionStatement

private theorem init_nonzero {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config}
    {ch : Choices} (hz : ¬ ZeroCost c) :
    runInitConfig ctx fuel s c ch =
      (match initPrintRefusal? c with
       | some e => .error e
       | none => match fuel with
         | 0 => .error .fuelOut
         | f + 1 => (stepFn ctx s c ch).bind fun r => runInitConfig ctx f r.2.1 r.1 r.2.2.1) := by
  rw [runInitConfig.eq_def]
  cases c <;> simp_all [ZeroCost, Blocked]
  all_goals rfl

/-- A print guard wins even at zero fuel. The semantic guard is stated in
terms of output, not an assumption about every hypothetical execution. -/
theorem init_print_at_zero {ctx : ProgramCtx} {a : State}
    (h : InitPrintRefusal a) (ch : Choices) :
    ∃ r, runInitConfig ctx 0 a.store a.control ch = .error (.refusal r) := by
  obtain ⟨bytes, hp⟩ := h
  have hz : ¬ ZeroCost a.control := by
    rintro (hn | ⟨_, _, _, hn⟩ | ⟨_, _, _, _, _, hn⟩ | ⟨_, _, _, hn⟩ | ⟨_, _, _, _, hn⟩) <;>
      rw [hn] at hp <;> cases hp
  rw [init_nonzero hz]
  simp [initPrintRefusal?, hp, Stop.unsupported]

theorem Initializes.realize {ctx : ProgramCtx} {a : State} {ls : List StepLabel} {s : Store}
    (h : Initializes ctx a ls s) (fuel : Nat) (enough : ls.length ≤ fuel) (tail : Choices) :
    ∃ ch, runInitConfig ctx fuel a.store a.control ch = .ok (s, tail) := by
  induction h generalizing fuel with
  | done => exact ⟨tail, by rw [runInitConfig.eq_def]; rfl⟩
  | step hp hs _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      obtain ⟨mid, hr⟩ := ih fuel (by simpa using enough)
      obtain ⟨ch₀, tail₀, he⟩ := step_complete hs
      obtain ⟨ch, hc⟩ := stepFn_any_residual he mid
      refine ⟨ch, ?_⟩
      rw [init_nonzero (stepFn_zeroCost_not_ok hc)]
      simp [initPrintRefusal?, hp, hc, hr, Except.bind]

/-- Soundness for every actual successful initialization run. -/
theorem initializes_of_run {ctx : ProgramCtx} {fuel : Nat} {s t : Store} {c : Config}
    {ch tail : Choices} (h : runInitConfig ctx fuel s c ch = .ok (t, tail)) :
    ∃ ls, ls.length ≤ fuel ∧ Initializes ctx ⟨c, s⟩ ls t := by
  fun_induction runInitConfig ctx fuel s c ch with
  | case1 =>
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], Nat.zero_le _, .done⟩
  | case2 | case3 | case4 | case5 | case6 | case7 =>
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | case8 =>
    rename_i hp _ ih
    rw [bind_eq_ok] at h
    obtain ⟨⟨d, u, mid, l⟩, hs, hr⟩ := h
    obtain ⟨ls, hn, hh⟩ := ih _ _ _ hr
    have noPrint {c : Config} (hg : initPrintRefusal? c = none) : printOut? c = none := by
      unfold initPrintRefusal? at hg
      split at hg
      · cases hg
      · assumption
    have hp' := noPrint hp
    exact ⟨l :: ls, Nat.succ_le_succ hn, .step hp' (stepFn_sound hs) hh⟩

theorem initializes_iff {ctx : ProgramCtx} {fuel : Nat} {a : State} {t : Store} :
    (∃ ch tail, runInitConfig ctx fuel a.store a.control ch = .ok (t, tail)) ↔
    ∃ ls, ls.length ≤ fuel ∧ Initializes ctx a ls t := by
  constructor
  · rintro ⟨ch, tail, h⟩
    exact initializes_of_run h
  · rintro ⟨ls, hn, h⟩
    obtain ⟨ch, hc⟩ := h.realize fuel hn []
    exact ⟨ch, [], hc⟩

end GoLean.GoCore.Relational
