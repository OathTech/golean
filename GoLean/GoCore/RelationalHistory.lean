import GoLean.GoCore.RelationalEvent

/-! Finite chronological observation histories. These carriers describe
successful prefixes, including unfinished ones, with no terminal, safety
or fuel premise. An observer may inspect each event's pre-store. -/
namespace GoLean.GoCore.Relational.Boundary
open Machine ExecutionStatement

inductive History {Ev : Type} (observe : BoundaryEvent → List Ev) (ctx : ProgramCtx) :
    State → List StepLabel → List Ev → State → Prop where
  | refl {a} : History observe ctx a [] [] a
  | cons {a b c l ls es} : Transition ctx a l b → History observe ctx b ls es c →
      History observe ctx a (l :: ls) (project observe ctx a ++ es) c

namespace History
variable {Ev : Type} {observe : BoundaryEvent → List Ev} {ctx : ProgramCtx}

theorem erase {a b ls es} (h : History observe ctx a ls es b) : Run ctx a ls b := by
  induction h with
  | refl => exact .refl
  | cons hs _ ih => exact .cons hs ih

theorem coverage {a b ls} (h : Run ctx a ls b) : ∃ es, History observe ctx a ls es b := by
  induction h with
  | refl => exact ⟨[], .refl⟩
  | cons hs _ ih =>
    obtain ⟨es, he⟩ := ih
    exact ⟨_, .cons hs he⟩

theorem append {a b c xs ys es fs}
    (h : History observe ctx a xs es b) (k : History observe ctx b ys fs c) :
    History observe ctx a (xs ++ ys) (es ++ fs) c := by
  induction h with
  | refl => exact k
  | cons hs _ ih => simpa only [List.cons_append, List.append_assoc] using History.cons hs (ih k)

theorem split {a c xs ys es} (h : History observe ctx a (xs ++ ys) es c) :
    ∃ b left right, es = left ++ right ∧
      History observe ctx a xs left b ∧ History observe ctx b ys right c := by
  induction xs generalizing a es with
  | nil =>
    cases h with
    | refl => exact ⟨_, [], [], rfl, .refl, .refl⟩
    | cons hs ht => exact ⟨_, [], _, rfl, .refl, .cons hs ht⟩
  | cons l ls ih =>
    cases h with
    | cons hs ht =>
      obtain ⟨b, left, right, rfl, hl, hr⟩ := ih ht
      exact ⟨b, _, right, (List.append_assoc _ _ _).symm, .cons hs hl, hr⟩

/-- The complete labels determine the intermediate states and history.
No transition-proof or realizing-tape choice can alter the projection. -/
theorem unique {a b c ls es fs} (h : History observe ctx a ls es b)
    (k : History observe ctx a ls fs c) : b = c ∧ es = fs := by
  induction h generalizing fs c with
  | refl => cases k; exact ⟨rfl, rfl⟩
  | cons hs _ ih =>
    cases k with
    | cons hs' ht' =>
      obtain ⟨rfl, _⟩ := hs.deterministic_by_picks hs' rfl
      obtain ⟨rfl, rfl⟩ := ih ht'
      exact ⟨rfl, rfl⟩

/-- Composition is exact in both directions, including zero-length and
unfinished pieces. No final-state classification is used. -/
theorem append_iff {a c xs ys es} : History observe ctx a (xs ++ ys) es c ↔
    ∃ b left right, es = left ++ right ∧
      History observe ctx a xs left b ∧ History observe ctx b ys right c := by
  constructor
  · exact split
  · rintro ⟨b, left, right, rfl, hl, hr⟩
    exact hl.append hr

/-- Any supplied residual tape can realize the same labels and history. -/
theorem realize {a b ls es} (h : History observe ctx a ls es b) (tail : Choices) :
    ∃ ch, Prefix ctx ls.length a.store a.control ch ls b.store b.control tail :=
  h.erase.realize tail

/-- Every actual executable prefix has a unique projected semantic history. -/
theorem on_prefix {n a b ch tail ls}
    (h : Prefix ctx n a.store a.control ch ls b.store b.control tail) :
    ∃ es, History observe ctx a ls es b ∧
      ∀ fs, History observe ctx a ls fs b → fs = es := by
  obtain ⟨es, he⟩ := coverage (observe := observe) (of_prefix h)
  exact ⟨es, he, fun _ hf => (hf.unique he).2⟩

end History
end GoLean.GoCore.Relational.Boundary
