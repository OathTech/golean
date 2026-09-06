import GoLean.GoCore.BooleanInvariant

/-! Preservation for every relational successor of the Boolean machine.
The local executable equations are uniform in the choice stream. Completeness
of `stepFn` for `Step` then covers all successors, not only one selected run. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

def Advances (s : ExecState) (c : Config) : Prop :=
  ∀ ch, ∃ c' t, stepFn s c ch = .ok (c', t, ch) ∧
    Extension s t ∧ TypedControl t c'

theorem expression_advances {Γ e env k s} (hc : Covers Γ env)
    (he : EnvRoots s env) (hh : BoolHeap s) (ht : ExprTyped Γ e)
    (hk : BoolCont (BoolRoot s) (EnvRoots s) k) : Advances s (.evalE e env k) := by
  intro ch
  cases ht with
  | var hx =>
      obtain ⟨loc, hl⟩ := hc _ hx
      obtain ⟨b, hb⟩ := (he.lookup hl).load
      exact ⟨.retV (.bool b) k, s,
        by simp [stepFn, hl, hb, Bind.bind, Except.bind], .refl hh, .retBool hk⟩
  | literal b => exact ⟨_, s, rfl, .refl hh, .retBool hk⟩
  | not ht => exact ⟨_, s, rfl, .refl hh, .evalBool hc he ht (.not he hk)⟩
  | and hl hr => exact ⟨_, s, rfl, .refl hh, .evalBool hc he hl (.and hc he hr hk)⟩
  | or hl hr => exact ⟨_, s, rfl, .refl hh, .evalBool hc he hl (.or hc he hr hk)⟩

theorem statement_advances {Γ stmt env k s} (hc : Covers Γ env)
    (he : EnvRoots s env) (hh : BoolHeap s) (ht : ControlStmt false Γ stmt)
    (hk : ReturnCont (EnvRoots s) k) : Advances s (.exec stmt env k) := by
  intro ch
  cases ht with
  | seqn hs => exact ⟨_, s, rfl, .refl hh, control_seqCont hc he hs hk⟩
  | block ht hs =>
      obtain ⟨env', t, ha, hc', he', hex⟩ := block_setup hc he hh ht
      exact ⟨_, t, by simp [stepFn, ha, Bind.bind, Except.bind], hex,
        .next (.seq hc' he' hs (hk.mono (fun _ => hex.env)))⟩
  | assign hx ht => exact ⟨_, s, rfl, .refl hh,
      .evalRef hc he hx (.target hc he ht hk)⟩
  | branch ht htrue hfalse => exact ⟨_, s, rfl, .refl hh,
      .evalBool hc he ht (.branch hc he htrue hfalse hk)⟩
  | ret => exact ⟨_, s, rfl, .refl hh, .returning hk⟩

theorem sequence_head_advances {Γ stmt rest env k s} (hc : Covers Γ env)
    (he : EnvRoots s env) (hh : BoolHeap s) (ht : ControlStmt true Γ stmt)
    (hrest : ControlStmts (afterStmt Γ stmt) rest) (hk : ReturnCont (EnvRoots s) k) :
    Advances s (.exec stmt env (.seq rest env k)) := by
  cases ht with
  | seqn hs =>
      intro ch
      refine ⟨_, s, ?_, .refl hh, .next (.seq hc he
        ((controlStmts_append_iff _ _ _).mpr ⟨hs, hrest⟩) hk)⟩
      simp [stepFn, seqCont]
  | block ht hs => exact statement_advances hc he hh (.block ht hs) (.seq hc he hrest hk)
  | @initialization Γ p ht =>
      intro ch
      let t := (s.alloc (.bool false) .bool).2
      let loc := (s.alloc (.bool false) .bool).1
      have hex : Extension s t := Extension.alloc hh false
      have hl : BoolRoot t loc := BoolRoot.alloc_new s false
      refine ⟨_, t, ?_, hex, .next (.seq (hc.declare p.id loc)
        ((hex.env he).declare hl p.id) hrest (hk.mono (fun _ => hex.env)))⟩
      simp [stepFn, ht, default_bool, t, loc, Bind.bind, Except.bind]
  | assign hx ht => exact statement_advances hc he hh (.assign hx ht) (.seq hc he hrest hk)
  | branch ht htrue hfalse =>
      exact statement_advances hc he hh (.branch ht htrue hfalse) (.seq hc he hrest hk)
  | ret => exact statement_advances hc he hh .ret (.seq hc he hrest hk)

theorem bool_return_advances {k s} (hh : BoolHeap s)
    (h : BoolCont (BoolRoot s) (EnvRoots s) k) (b : Bool) :
    Advances s (.retV (.bool b) k) := by
  intro ch
  cases h with
  | not he hk => exact ⟨_, s, rfl, .refl hh, .retBool hk⟩
  | and hc he ht hk =>
      cases b
      · exact ⟨_, s, rfl, .refl hh, .retBool hk⟩
      · exact ⟨_, s, rfl, .refl hh, .evalBool hc he ht (.coerce hk)⟩
  | or hc he ht hk =>
      cases b
      · exact ⟨_, s, rfl, .refl hh, .evalBool hc he ht (.coerce hk)⟩
      · exact ⟨_, s, rfl, .refl hh, .retBool hk⟩
  | coerce hk => exact ⟨_, s, rfl, .refl hh, .retBool hk⟩
  | branch hc he ht hf hk =>
      cases b
      · exact ⟨_, s, rfl, .refl hh, .exec hc he hf hk⟩
      · exact ⟨_, s, rfl, .refl hh, .exec hc he ht hk⟩
  | rhs hl he hk => exact ⟨_, s, rfl, .refl hh, .store hl he hk⟩

theorem control_advances {s c} (hh : BoolHeap s) (h : TypedControl s c) :
    c = .next .stop ∨ Advances s c := by
  cases h with
  | terminal => exact .inl rfl
  | next hk =>
      apply Or.inr
      intro ch
      cases hk with
      | barrier => exact ⟨_, s, rfl, .refl hh, .terminal⟩
      | @seq Γ env ss k hc he ht hk =>
          cases ht with
          | nil => exact ⟨_, s, rfl, .refl hh, .next hk⟩
          | cons hs ht => exact ⟨_, s, rfl, .refl hh, .execSeq hc he hs ht hk⟩
  | exec hc he ht hk => exact .inr (statement_advances hc he hh ht hk)
  | execSeq hc he ht hrest hk => exact .inr (sequence_head_advances hc he hh ht hrest hk)
  | evalBool hc he ht hk => exact .inr (expression_advances hc he hh ht hk)
  | evalRef hc he hx hk =>
      apply Or.inr
      intro ch
      obtain ⟨loc, hl⟩ := hc _ hx
      exact ⟨_, s, by simp [stepFn, hl], .refl hh, .retAddr (he.lookup hl) hk⟩
  | @retBool b k hk => exact .inr (bool_return_advances hh hk b)
  | retAddr hl hk =>
      apply Or.inr
      intro ch
      cases hk with
      | target hc he ht hk => exact ⟨_, s, rfl, .refl hh,
          .evalBool hc he ht (.rhs hl he hk)⟩
  | @store loc b env k hl he hk =>
      apply Or.inr
      intro ch
      obtain ⟨t, ht, hex⟩ := store_extension hh hl b
      have hs : storeTarget s (.chain (.addr loc) [] []) (.bool b) = .ok t := ht
      exact ⟨_, t, by simp [stepFn, hs, toResult, Bind.bind, Except.bind], hex,
        .storeDone (hex.env he) (hk.mono (fun _ => hex.env))⟩
  | storeDone he hk =>
      exact .inr (fun _ => ⟨_, s, rfl, .refl hh, .exec (Covers.empty _) he (.seqn .nil) hk⟩)
  | returning hk =>
      apply Or.inr
      intro ch
      cases hk with
      | barrier => exact ⟨_, s, rfl, .refl hh, .terminal⟩
      | seq hc he ht hk => exact ⟨_, s, rfl, .refl hh, .returning hk⟩

theorem control_stepFn {s c ch c' t ch'} (hh : BoolHeap s) (hc : TypedControl s c)
    (hstep : stepFn s c ch = .ok (c', t, ch')) :
    Extension s t ∧ TypedControl t c' ∧ ch' = ch := by
  rcases control_advances hh hc with rfl | ha
  · simp [stepFn] at hstep
  · obtain ⟨d, u, hu, hex, hd⟩ := ha ch
    rw [hu] at hstep
    cases hstep
    exact ⟨hex, hd, rfl⟩

theorem control_step {s c c' t} (hh : BoolHeap s) (hc : TypedControl s c)
    (hstep : Step c s c' t) : Extension s t ∧ TypedControl t c' := by
  obtain ⟨ch, ch', h⟩ := step_complete hstep
  obtain ⟨hex, hc', _⟩ := control_stepFn hh hc h
  exact ⟨hex, hc'⟩

theorem Inv.step {context results s c t c'} (h : Inv context results s c)
    (hstep : Step c s c' t) : Inv context results t c' := by
  obtain ⟨hex, hc⟩ := control_step h.heap h.control hstep
  exact ⟨h.sameContext.trans hex.context, hex.heap,
    fun loc hl => hex.root (h.pinned loc hl), hc, hstep.preserves_wf h.machineWf⟩

end GoLean.GoCore.BooleanRuntime
