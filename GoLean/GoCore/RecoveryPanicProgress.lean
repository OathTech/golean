import GoLean.GoCore.RecoveryFrameProgress

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem panic_value_advances {world fs s kind k chain}
    (heap : HeapTyped world s) (hchain : ChainTyped chain)
    (hk : ValueCont world fs kind k) : Advances world fs s (.panicking chain k) := by
  induction hk with
  | coerce _ _ ih => exact ih
  | strict _ _ _ _ hk _ =>
    exact advances_same heap (.panicking hchain (.value hk)) (fun _ => rfl)
  | and _ _ hk _ => exact advances_same heap (.panicking hchain (.value hk)) (fun _ => rfl)
  | or _ _ hk _ => exact advances_same heap (.panicking hchain (.value hk)) (fun _ => rfl)
  | bool hk _ => exact advances_same heap (.panicking hchain (.value hk)) (fun _ => rfl)
  | branch _ _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | target _ _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | rhs _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | callArgs _ _ _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | callCallee _ _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | callValueArgs _ _ _ _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | deferCallee _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | deferArgs _ _ _ _ _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | panic hk => exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)

theorem panic_return_advances {p : Program} {world s k chain}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hchain : ChainTyped chain)
    (hk : ReturnCont world p.funcs k) : Advances world p.funcs s (.panicking chain k) := by
  cases hk with
  | seq _ _ hk =>
    exact advances_same heap (.panicking hchain (.exit (.stmt hk))) (fun _ => rfl)
  | @frame Γ plans ps env results ds k he ht hr hd hk wb =>
    cases ds with
    | nil => exact advances_same heap (.panicking hchain (.exit hk)) (fun _ => rfl)
    | cons d ds =>
      have pending := hd d (by simp)
      have tail : DefersTyped world p.funcs ds := fun d hd' => hd d (by simp [hd'])
      have outer := ReturnCont.frame he ht hr tail hk wb
      intro ch
      obtain ⟨fid, caps, f, next, env', roots, t, hcallee, run, ext, hw, control⟩ :=
        deferred_entry_control hp hc heap pending (.resume hchain outer) ch
      rcases d with ⟨callee, args⟩
      dsimp only at hcallee
      subst callee
      exact ⟨next, _, t, by
        simp only [stepFn, run]
        simp [deliverS, hw, Bind.bind, Except.bind, Pure.pure, Except.pure], ext, control⟩

theorem panic_progress {p : Program} {world s k chain}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hchain : ChainTyped chain)
    (hk : UnwindCont world p.funcs k) :
    k = .stop ∨ Advances world p.funcs s (.panicking chain k) := by
  cases hk with
  | value hk => exact .inr (panic_value_advances heap hchain hk)
  | exit hk =>
    cases hk with
    | stop => exact .inl rfl
    | stmt hk => exact .inr (panic_return_advances hp hc heap hchain hk)
    | resume suspended hk =>
      exact .inr (advances_same heap (.panicking (suspended.append hchain) (.exit (.stmt hk)))
        (fun _ => rfl))

/-- Normal termination and semantic abort are classified before asking for
a relational successor. The abort renderer is a separate driver obligation. -/
def Progress (world : World) (fs : Array Func) (s : ExecState) (c : Config) : Prop :=
  c = .next .stop ∨ (∃ first rest, c = .panicking (first :: rest) .stop) ∨ Advances world fs s c

theorem control_progress {p : Program} {world s c}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (control : Control world p.funcs c) :
    Progress world p.funcs s c := by
  cases control with
  | next hk =>
    rcases exit_next_progress hp hc heap hk with rfl | h
    · exact .inl rfl
    · exact .inr (.inr h)
  | execNeutral he hs hn hk => exact .inr (.inr (exec_neutral_advances hp hc heap he hs hn hk))
  | execFrame he hs hk => exact .inr (.inr (exec_frame_advances hp hc heap he hs hk))
  | execSeq he hs hrest hk => exact .inr (.inr (exec_seq_advances hp hc heap he hs hrest hk))
  | eval he ht hk => exact .inr (.inr (expression_advances heap he ht hk))
  | ret hv hk => exact .inr (.inr (value_advances hp hc heap hk hv))
  | store he hr hv hk => exact .inr (.inr (store_advances heap he hr hv hk))
  | returning hk => exact .inr (.inr (returning_advances hp hc heap hk))
  | @panicking chain k hchain hk =>
    rcases panic_progress hp hc heap hchain hk with rfl | h
    · rcases List.exists_cons_of_ne_nil hchain.1 with ⟨first, rest, rfl⟩
      exact .inr (.inl ⟨first, rest, rfl⟩)
    · exact .inr (.inr h)

end GoLean.GoCore.RecoveryRuntime
