import GoLean.GoCore.RecoveryPool

/-! Choice independence for this profile's STEPS. Absence of methods excludes
the nil-receiver wrapper text choice; the control grammar excludes every
other sequential consultation site — EXCEPT the abort (landing chunk L3):
an admitted recovery program CAN reach an abort whose head is a recovered
entry re-panicked with an equal payload (`Tests/RecoveryTyping.lean`'s
`repanicProgram`), and there the abort draws the `repanicCollapse` pick.
That draw is the `panic` terminal's, never a successful step's, so every
SUCCESSFUL execution still retains its stream verbatim
(`Inv.loop_all_choices`), while the terminal text is genuinely two-valued
on that shape (`RecoveryTerminal`). -/
namespace GoLean.GoCore.RecoveryRuntime
open Machine

theorem entryConsult_no_methods {s : ExecState} (hm : s.methods = #[])
    (fid : FuncId) (args : List GoValue) : entryConsult? s fid args = none := by
  have hn : nilValueMethodText? s fid args = none := by
    unfold nilValueMethodText?
    cases findFunctionIn? s.functions fid <;> simp [methodInfoByFuncId?, hm]
  simp [entryConsult?, nilValueMethodWidth, hn]

theorem entryConsult_match_no_methods {s : ExecState} (hm : s.methods = #[])
    (c : Config) :
    (match entryCallSite? c with
      | some (fid, args) => entryConsult? s fid args
      | none => none) = none := by
  cases entryCallSite? c with
  | none => rfl
  | some pair => exact entryConsult_no_methods hm pair.1 pair.2

theorem ValueCont.no_seq_consumption {world fs kind k} (h : ValueCont world fs kind k)
    {s : ExecState} (hm : s.methods = #[]) (v : GoValue) :
    seqConsumption s (.retV v k) = none := by
  induction h <;> (first | assumption | rfl |
    (simp only [seqConsumption, Config.applyPos]; exact entryConsult_match_no_methods hm _) | skip)
  case strict =>
    rename_i Γ env op ds kind ps out done pending k he hp hd hes hk ih
    cases pending <;> rfl
  case rhs =>
    rename_i Γ env p before after refs done pending k he hr hd ha hk
    cases pending <;> rfl

/-- An unwinding configuration consults nothing — except at the ABORT
(`.stop` under a nonempty chain), the one place the `repanicCollapse` pick
may be drawn. -/
theorem UnwindCont.no_seq_consumption {world fs k} (h : UnwindCont world fs k)
    {s : ExecState} (hm : s.methods = #[]) (chain : List PanicEntry) :
    seqConsumption s (.panicking chain k) = none ∨ (Config.panicking chain k).abort?.isSome := by
  cases h with
  | exit h =>
    cases h with
    | stop =>
      cases chain with
      | nil => exact .inl rfl
      | cons first rest => exact .inr rfl
    | stmt h => cases h <;> first | exact .inl rfl | exact .inl (entryConsult_match_no_methods hm _)
    | resume => exact .inl rfl
  | value h =>
    left
    induction h <;> first | assumption | rfl

/-- Every configuration of the control grammar consults nothing — except an
abort, where the `repanicCollapse` pick may be drawn (the profile's
`repanicProgram` realizes that shape). -/
theorem Control.no_seq_consumption {world fs c} (h : Control world fs c)
    {s : ExecState} (hm : s.methods = #[]) :
    seqConsumption s c = none ∨ c.abort?.isSome := by
  cases h <;> try exact .inl rfl
  case next hk =>
    cases hk with
    | stop => exact .inl rfl
    | stmt hk => cases hk <;> first | exact .inl rfl | exact .inl (entryConsult_match_no_methods hm _)
    | resume => exact .inl rfl
  case ret hv hk => exact .inl (hk.no_seq_consumption hm _)
  case execNeutral he hs hn hk =>
    exact .inl (entryConsult_match_no_methods hm _)
  case execFrame he hs hk =>
    exact .inl (entryConsult_match_no_methods hm _)
  case execSeq he hs ht hk =>
    exact .inl (entryConsult_match_no_methods hm _)
  case returning hk =>
    exact .inl (entryConsult_match_no_methods hm _)
  case panicking hc hk => exact hk.no_seq_consumption hm _

theorem Inv.no_seq_consumption {p ps roots s c} (inv : Inv p ps roots s c) :
    seqConsumption s c = none ∨ c.abort?.isSome := by
  obtain ⟨world, heap, control, pins⟩ := inv.typed
  apply control.no_seq_consumption
  exact (congrArg ExecState.methods inv.sameContext).symm.trans
    (Array.eq_empty_of_size_eq_zero inv.program.2.1)

/-- A SUCCESSFUL step of the profile consults nothing: the only consulting
configuration is the abort, whose step is never `.ok`
(`stepFn_success_no_abort`). -/
theorem Inv.step_no_seq_consumption {p ps roots s c ch next t residual}
    (inv : Inv p ps roots s c) (step : stepFn s c ch = .ok (next, t, residual)) :
    seqConsumption s c = none := by
  rcases inv.no_seq_consumption with h | h
  · exact h
  · rw [stepFn_success_no_abort step] at h
    cases h

/-- A successful execution on one supplied stream executes to the same
state on every other stream, preserving the latter stream verbatim. -/
theorem Inv.loop_all_choices {p ps roots s c fuel initial final residual}
    (inv : Inv p ps roots s c)
    (run : execStmtLoop fuel s c initial = .ok (final, residual)) (ch : Choices) :
    execStmtLoop fuel s c ch = .ok (final, ch) := by
  revert inv
  fun_induction execStmtLoop fuel s c initial with
  | case1 => cases run; intro _; simp [execStmtLoop]
  | case2 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case3 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case4 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case5 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case6 => simp [throw, throwThe, MonadExceptOf.throw] at run
  | case7 =>
    rename_i ih
    rw [bind_eq_ok] at run
    obtain ⟨⟨next, t, nextCh⟩, step, run⟩ := run
    intro inv
    have uniform := (stepFn_consumption_none (inv.step_no_seq_consumption step) step).2
    rw [execStmtLoop_step (uniform ch)]
    exact ih _ _ _ run (inv.step (stepFn_sound step))

end GoLean.GoCore.RecoveryRuntime
