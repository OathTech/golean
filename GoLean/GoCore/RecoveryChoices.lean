import GoLean.GoCore.RecoveryPool

/-! Choice independence for this profile. Absence of methods excludes the
nil-receiver wrapper text choice; the control grammar excludes every other
sequential consultation site. -/
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

theorem UnwindCont.no_seq_consumption {world fs k} (h : UnwindCont world fs k)
    {s : ExecState} (hm : s.methods = #[]) (chain : List PanicEntry) :
    seqConsumption s (.panicking chain k) = none := by
  cases h with
  | exit h =>
    cases h with
    | stop => rfl
    | stmt h => cases h <;> first | rfl | exact entryConsult_match_no_methods hm _
    | resume => rfl
  | value h =>
    induction h <;> first | assumption | rfl

theorem Control.no_seq_consumption {world fs c} (h : Control world fs c)
    {s : ExecState} (hm : s.methods = #[]) : seqConsumption s c = none := by
  cases h <;> try rfl
  case next hk =>
    cases hk with
    | stop => rfl
    | stmt hk => cases hk <;> first | rfl | exact entryConsult_match_no_methods hm _
    | resume => rfl
  case ret hv hk => exact hk.no_seq_consumption hm _
  case execNeutral he hs hn hk =>
    exact entryConsult_match_no_methods hm _
  case execFrame he hs hk =>
    exact entryConsult_match_no_methods hm _
  case execSeq he hs ht hk =>
    exact entryConsult_match_no_methods hm _
  case returning hk =>
    exact entryConsult_match_no_methods hm _
  case panicking hc hk => exact hk.no_seq_consumption hm _

theorem Inv.no_seq_consumption {p ps roots s c} (inv : Inv p ps roots s c) :
    seqConsumption s c = none := by
  obtain ⟨world, heap, control, pins⟩ := inv.typed
  apply control.no_seq_consumption
  exact (congrArg ExecState.methods inv.sameContext).symm.trans
    (Array.eq_empty_of_size_eq_zero inv.program.2.1)

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
    have uniform := (stepFn_consumption_none inv.no_seq_consumption step).2
    rw [execStmtLoop_step (uniform ch)]
    exact ih _ _ _ run (inv.step (stepFn_sound step))

end GoLean.GoCore.RecoveryRuntime
