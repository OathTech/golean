import GoLeanProofs.FastEval.Ops

/-!
# FastEval — the one-directional loop simulation (campaign Arc 2, U4)

The semantic core's `for i in [:n]` loops elaborate to
`Std.Legacy.Range.forIn`, whose implementation is a PRIVATE
well-founded `loop` — unnameable and kernel-hostile. The kit's landed
bridge (`SliceMem.lean` precedent) is
`Std.Legacy.Range.forIn_eq_forIn_range'`: Range-forIn equals
`List.forIn` over `List.range' …`, which is STRUCTURAL on both axes —
inductable in proofs and kernel-reducible in fast mirrors. So:

- FAST mirrors write their loops as `List.forIn (List.range' …)`
  (or plain recursion) — never Range-forIn;
- sims convert the SLOW side by the bridge lemma and close with
  `list_forIn_sim` below — the one-directional relational transport
  through a list fold, proved once.

UNTRUSTED METHOD — never in any statement closure.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore

/-- Transport of `ForInStep` along a relation. -/
def stepRel (R : β' → β → Prop) : ForInStep β' → ForInStep β → Prop
  | .done r', .done r => R r' r
  | .yield r', .yield r => R r' r
  | _, _ => False

/-- **The one-directional list-fold simulation**: if the fast body's
`.ok` answers are matched by the slow body's up to `R` (constructor
included), a completed fast fold transports. -/
theorem list_forIn_sim {α β β' : Type} {R : β' → β → Prop}
    {bodyF : α → β' → Except GoError (ForInStep β')}
    {body : α → β → Except GoError (ForInStep β)}
    (hbody : ∀ x b' b, R b' b → ∀ s', bodyF x b' = .ok s' →
      ∃ s, body x b = .ok s ∧ stepRel R s' s) :
    ∀ (l : List α) {init' : β'} {init : β}, R init' init →
    ∀ {res' : β'}, forIn l init' bodyF = .ok res' →
    ∃ res, forIn l init body = .ok res ∧ R res' res := by
  intro l
  induction l with
  | nil =>
      intro init' init hR res' hrun
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hrun
      exact ⟨init, by simpa [List.forIn_nil, pure, Except.pure] using rfl,
        hrun ▸ hR⟩
  | cons x xs ih =>
      intro init' init hR res' hrun
      rw [List.forIn_cons] at hrun
      cases hstep : bodyF x init' with
      | error e => rw [hstep] at hrun; simp [Bind.bind, Except.bind] at hrun
      | ok s' =>
          rw [hstep] at hrun
          obtain ⟨s, hs, hrel⟩ := hbody x init' init hR s' hstep
          rw [List.forIn_cons, hs]
          cases s' with
          | done r' =>
              cases s with
              | done r =>
                  simp only [Bind.bind, Except.bind, pure, Except.pure,
                    Except.ok.injEq] at hrun ⊢
                  exact ⟨r, rfl, hrun ▸ hrel⟩
              | yield r => exact absurd hrel (by simp [stepRel])
          | yield r' =>
              cases s with
              | done r => exact absurd hrel (by simp [stepRel])
              | yield r =>
                  simp only [Bind.bind, Except.bind] at hrun ⊢
                  exact ih hrel hrun

end GoLean.FastEval
