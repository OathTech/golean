import GoLean.GoCore.RecoveryStatementProgress

namespace GoLean.GoCore.RecoveryRuntime
open RecoveryTyping Machine

theorem frame_exit_progress {p : Program} {world s plans env results ds k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s)
    (frame : ReturnCont world p.funcs (.frame plans env results ds k false)) :
    ∀ ch, ∃ next c' t, stepFrameExit s plans env results ds k false ch = .ok (c', t, ch) ∧
      StoreExtension world next s t ∧ Control next p.funcs c' := by
  cases frame with
  | frame he ht hr hd hk wb =>
    cases ds with
    | nil =>
      cases ht with
      | nil =>
        cases hr
        exact fun ch => ⟨world, _, s, rfl, .refl heap, .next hk⟩
      | cons ht hts =>
        cases ht with
        | root hty hx =>
          obtain ⟨vs, run, hv⟩ := hr.load heap
          exact fun ch => ⟨world, _, s, by simp [stepFrameExit, run]; rfl,
            .refl heap, .eval he hx
              (.target (before := []) he hty .nil hts (.values hv) (wb (by simp)))⟩
    | cons d ds =>
      have pending := hd d (by simp)
      have tail : DefersTyped world p.funcs ds := fun d hd' => hd d (by simp [hd'])
      have outer := ReturnCont.frame he ht hr tail hk wb
      intro ch
      obtain ⟨fid, caps, f, next, env', roots, t, hcallee, run, ext, hw, control⟩ :=
        deferred_entry_control hp hc heap pending (.stmt outer) ch
      rcases d with ⟨callee, args⟩
      dsimp only at hcallee
      subst callee
      exact ⟨next, _, t, by
        simp only [stepFrameExit, run]
        simp [deliverS, hw, Bind.bind, Except.bind, Pure.pure, Except.pure], ext, control⟩

theorem frame_next_advances {p : Program} {world s plans env results ds k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s)
    (frame : ReturnCont world p.funcs (.frame plans env results ds k false)) :
    Advances world p.funcs s (.next (.frame plans env results ds k false)) :=
  frame_exit_progress hp hc heap frame

theorem frame_return_advances {p : Program} {world s plans env results ds k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s)
    (frame : ReturnCont world p.funcs (.frame plans env results ds k false)) :
    Advances world p.funcs s (.signal .ret (.frame plans env results ds k false)) :=
  frame_exit_progress hp hc heap frame

theorem returning_advances {p : Program} {world s k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hk : ReturnCont world p.funcs k) :
    Advances world p.funcs s (.signal .ret k) := by
  cases hk with
  | seq _ _ hk => exact advances_same heap (.returning hk) (fun _ => rfl)
  | frame he ht hr hd hk wb => exact frame_return_advances hp hc heap (.frame he ht hr hd hk wb)

theorem return_next_advances {p : Program} {world s k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hk : ReturnCont world p.funcs k) :
    Advances world p.funcs s (.next k) := by
  cases hk with
  | seq he hs hk =>
    cases hs with
    | nil => exact advances_same heap (.next (.stmt hk)) (fun _ => rfl)
    | cons hs hss => exact advances_same heap (.execSeq he hs hss hk) (fun _ => rfl)
  | frame he ht hr hd hk wb => exact frame_next_advances hp hc heap (.frame he ht hr hd hk wb)

theorem exit_next_progress {p : Program} {world s k}
    (hp : ProgramTyped p)
    (hc : BooleanRuntime.SameContext (BooleanRuntime.programState p) s)
    (heap : HeapTyped world s) (hk : ExitCont world p.funcs k) :
    k = .stop ∨ Advances world p.funcs s (.next k) := by
  cases hk with
  | stop => exact .inl rfl
  | stmt hk => exact .inr (return_next_advances hp hc heap hk)
  | @resume chain k hchain hk =>
    right
    cases hrec : chainNewestRecovered chain with
    | false =>
      exact advances_same heap (.panicking hchain (.exit (.stmt hk)))
        (fun _ => by simp [stepFn, hrec])
    | true => exact advances_same heap (.next (.stmt hk)) (fun _ => by simp [stepFn, hrec])

end GoLean.GoCore.RecoveryRuntime
