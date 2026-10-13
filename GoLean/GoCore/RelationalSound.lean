import GoLean.GoCore.Relational
import GoLean.GoCore.Prefix

/-! # Executable correspondence for the labelled relational surface

Evaluator/tape names belong in this bridge, not in the relational carriers.
Finite realization uses residual-tape stitching already proved in `Prefix`;
it makes no claim about infinite runs or fairness.
-/

namespace GoLean.GoCore.Relational

open Machine ExecutionStatement

theorem prefix_length {ctx : ProgramCtx} {n : Nat} {s t : Store} {c d : Config}
    {ch tail : Choices} {ls : List StepLabel}
    (h : Prefix ctx n s c ch ls t d tail) : ls.length = n := by
  induction h with
  | done => rfl
  | step _ _ ih => simp [ih]

theorem of_prefix {ctx : ProgramCtx} {n : Nat} {s t : Store} {c d : Config}
    {ch tail : Choices} {ls : List StepLabel}
    (h : Prefix ctx n s c ch ls t d tail) : Run ctx ⟨c, s⟩ ls ⟨d, t⟩ := by
  induction h with
  | done => exact .refl
  | step hs _ ih => exact .cons (stepFn_sound hs) ih

/-- Every finite relational run can leave any prescribed residual tape. -/
theorem Run.realize {ctx : ProgramCtx} {a b : State} {ls : List StepLabel}
    (h : Run ctx a ls b) (tail : Choices) :
    ∃ ch, Prefix ctx ls.length a.store a.control ch ls b.store b.control tail := by
  induction h with
  | refl => exact ⟨tail, .done⟩
  | cons hs _ ih =>
    obtain ⟨ch, ht⟩ := ih
    obtain ⟨ch₀, ch₀', he⟩ := step_complete hs
    obtain ⟨start, hh⟩ := stepFn_any_residual he ch
    exact ⟨start, .step hh ht⟩

theorem run_iff_prefix {ctx : ProgramCtx} {a b : State} {ls : List StepLabel}
    (tail : Choices) : Run ctx a ls b ↔
      ∃ ch, Prefix ctx ls.length a.store a.control ch ls b.store b.control tail := by
  constructor
  · exact fun h => h.realize tail
  · rintro ⟨ch, h⟩
    exact of_prefix h

/-- Soundness, not completeness, transfers universally quantified semantic
properties to each actual executable prefix. -/
theorem Invariant.on_prefix {ctx : ProgramCtx} {a : State} {P : State → Prop}
    (h : Invariant ctx a P) {n : Nat} {b : State} {ch tail : Choices} {ls : List StepLabel}
    (hp : Prefix ctx n a.store a.control ch ls b.store b.control tail) : P b :=
  h ls b (of_prefix hp)

/-- The records emitted by a successful step replay on its own tape. -/
private theorem records_replay {ctx : ProgramCtx} {s t : Store} {c d : Config}
    {ch tail : Choices} {l : StepLabel}
    (h : stepFn ctx s c ch = .ok (d, t, tail, l)) : replays l.picks ch tail := by
  cases hc : seqConsumption ctx s c with
  | none =>
    rw [stepFn_picks_none (ch₀ := ch) hc _ h]
    exact (stepFn_consumption_none hc h).1
  | some pair =>
    obtain ⟨site, bound⟩ := pair
    rw [stepFn_picks_some (ch₀ := ch) hc _ h]
    have ht := (stepFn_consumption_some hc h).1
    by_cases hb : bound ≤ 1
    · simp only [PickRecord.ofPick, if_pos hb, replays]
      simpa [Choices.consumeAt_le_one hb] using ht
    · simp only [PickRecord.ofPick, if_neg hb, replays]
      refine ⟨tail, ?_, rfl⟩
      rw [Choices.consumeAtE]
      simp only [ht, if_neg hb]

/-- Equal recorded choices determine the complete successful transition.
No well-formedness assumption and no claim that all choices succeed. -/
theorem Transition.deterministic_by_picks {ctx : ProgramCtx} {a b d : State}
    {l m : StepLabel} (h : Transition ctx a l b) (k : Transition ctx a m d)
    (picks : l.picks = m.picks) : b = d ∧ l = m := by
  obtain ⟨ch, tail, he⟩ := step_complete h
  obtain ⟨ch₂, tail₂, hk⟩ := step_complete k
  have hr := records_replay hk
  rw [← picks] at hr
  have hh := replay_coverage ctx a.store b.store a.control b.control ch tail l he ch₂ tail₂ hr
  rw [hk] at hh
  have hx := Except.ok.inj hh
  cases b; cases d
  simp_all

/-- Pick-free successful steps work on every tape and leave it untouched. -/
theorem Transition.on_any_tape {ctx : ProgramCtx} {a b : State} {l : StepLabel}
    (h : Transition ctx a l b) (silent : l.picks = []) (ch : Choices) :
    stepFn ctx a.store a.control ch = .ok (b.control, b.store, ch, l) := by
  obtain ⟨ch₀, tail, he⟩ := step_complete h
  apply replay_coverage ctx _ _ _ _ _ _ _ he ch ch
  simp [silent, replays]

/-- One pick-free success determines every successful successor, including
the label. Store preservation is a separate property. -/
theorem Transition.unique_of_no_picks {ctx : ProgramCtx} {a b d : State}
    {l m : StepLabel} (h : Transition ctx a l b) (silent : l.picks = [])
    (k : Transition ctx a m d) : b = d ∧ l = m := by
  obtain ⟨ch, tail, hk⟩ := step_complete k
  have hh := h.on_any_tape silent ch
  rw [hk] at hh
  have hx := Except.ok.inj hh
  cases b; cases d
  simp_all

/-- Run determinism requires the sequence of per-step records. It does not
equate arbitrary permutations of the ordered labels. -/
theorem Run.deterministic_by_picks {ctx : ProgramCtx} {a b c : State}
    {ls ms : List StepLabel} (h : Run ctx a ls b) (k : Run ctx a ms c)
    (records : ls.map (·.picks) = ms.map (·.picks)) : b = c ∧ ls = ms := by
  induction h generalizing ms c with
  | refl =>
    have hm : ms = [] := by simpa using records.symm
    subst ms
    cases k
    exact ⟨rfl, rfl⟩
  | cons hs _ ih =>
    cases k with
    | refl => simp at records
    | cons ks kt =>
      simp only [List.map_cons, List.cons.injEq] at records
      obtain ⟨rfl, rfl⟩ := hs.deterministic_by_picks ks records.1
      obtain ⟨rfl, rfl⟩ := ih kt records.2
      exact ⟨rfl, rfl⟩

/-- Address validity and heap normalization, not typing or refusal freedom. -/
def WellFormed (ctx : ProgramCtx) (a : State) : Prop :=
  MachineWf ctx a.store a.control

theorem Transition.preserves_wellFormed {ctx : ProgramCtx} {a b : State} {l : StepLabel}
    (h : Transition ctx a l b) (hw : WellFormed ctx a) : WellFormed ctx b :=
  Step.preserves_wf h hw

theorem Run.preserves_wellFormed {ctx : ProgramCtx} {a b : State} {ls : List StepLabel}
    (h : Run ctx a ls b) (hw : WellFormed ctx a) : WellFormed ctx b :=
  invariant_of_preserved hw (fun hp hs => hs.preserves_wellFormed hp) _ _ h

theorem Run.heap_size_mono {ctx : ProgramCtx} {a b : State} {ls : List StepLabel}
    (h : Run ctx a ls b) (hw : WellFormed ctx a) : a.store.heap.size ≤ b.store.heap.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | cons hs _ ih =>
    exact Nat.le_trans (Machine.heap_size_mono hs hw.1 hw.2) (ih (hs.preserves_wellFormed hw))

end GoLean.GoCore.Relational
