import GoLean.GoCore.RelationalOutcomeSound

/-! Compositional operation checks. A passed check is deliberately not a
successful machine transition: it only says that this check did not reject.
The failure relation records semantic selections without a choice tape.
Executable interpretation is confined to the correspondence namespace. -/
namespace GoLean.GoCore.Relational.Local
open Machine

inductive OperationCheck where
  | passed
  | failed (cause : Stop)
  | consult (site : ChoiceSite) (bound : Nat) (next : Nat → OperationCheck)

namespace OperationCheck

def after {α : Type} (operation : Except Stop α) (next : α → OperationCheck) :
    OperationCheck :=
  match operation with
  | .error cause => .failed cause
  | .ok value => next value

def validate {α : Type} (operation : Except Stop α) : OperationCheck :=
  after operation fun _ => .passed

/-- Recoverable panics are successful unwind transitions, not failed operations. -/
def delivered {α : Type} (operation : Except Stop α) : OperationCheck :=
  validate (toResult operation)

def afterDelivered {α : Type} (operation : Except Stop α)
    (next : α → OperationCheck) : OperationCheck :=
  after (toResult operation) fun result =>
    match result with
    | .panic _ => .passed
    | .ok value => next value

/-- Validation and commit are distinct fallible operations. Commit errors keep
the existing exact diagnostic, including a forbidden commit-time panic. -/
def committed {α : Type} (store : Store) (plan : Except Stop (Commit α)) :
    OperationCheck :=
  after (toResult plan) fun result =>
    match result with
    | .panic _ => .passed
    | .ok commit => validate (runCommit commit store)

inductive Rejects : OperationCheck → List PickRecord → Stop → Prop where
  | failed {cause} : Rejects (.failed cause) [] cause
  | consult {site bound next pick records tail cause} :
      Selection site bound pick records → Rejects (next pick) tail cause →
      Rejects (.consult site bound next) (records ++ tail) cause

namespace Correspondence
open ExecutionStatement

/-- The tape interpreter belongs to the bridge, not to `Rejects`. It retains
consultations even on a failed check; these are witnesses, not error returns
of the machine. -/
def run : OperationCheck → Choices → Option Stop × Choices × List PickRecord
  | .passed, ch => (none, ch, [])
  | .failed cause, ch => (some cause, ch, [])
  | .consult site bound next, ch =>
      let (pick, middle, records) := Choices.consumeAtE site bound ch
      let (result, tail, rest) := run (next pick) middle
      (result, tail, records ++ rest)

theorem replays_append {xs ys : List PickRecord} {start middle tail : Choices}
    (hx : replays xs start middle) (hy : replays ys middle tail) :
    replays (xs ++ ys) start tail := by
  induction xs generalizing start with
  | nil => simp only [replays] at hx; subst middle; exact hy
  | cons x xs ih =>
    obtain ⟨next, hp, hr⟩ := hx
    exact ⟨next, hp, ih hr⟩

theorem replays_append_inv {xs ys : List PickRecord} {start tail : Choices}
    (h : replays (xs ++ ys) start tail) :
    ∃ middle, replays xs start middle ∧ replays ys middle tail := by
  induction xs generalizing start with
  | nil => exact ⟨start, rfl, h⟩
  | cons x xs ih =>
    obtain ⟨next, hp, hr⟩ := h
    obtain ⟨middle, hx, hy⟩ := ih hr
    exact ⟨middle, ⟨next, hp, hx⟩, hy⟩

theorem consume_replays {site bound ch pick middle records}
    (h : Choices.consumeAtE site bound ch = (pick, middle, records)) :
    replays records ch middle := by
  have hs := selection_of_consume h
  obtain ⟨_, rfl⟩ := hs
  by_cases hb : bound ≤ 1
  · simp [Choices.consumeAtE, Choices.consumeAt_le_one hb] at h
    simp_all [PickRecord.ofPick, replays]
  · simp only [PickRecord.ofPick, if_neg hb]
    exact ⟨middle, by simpa [PickRecord.ofPick, hb] using h, rfl⟩

theorem run_coverage (check : OperationCheck) (ch : Choices) {cause : Stop}
    (h : (run check ch).1 = some cause) :
    Rejects check (run check ch).2.2 cause ∧
      replays (run check ch).2.2 ch (run check ch).2.1 := by
  induction check generalizing ch with
  | passed => cases h
  | failed e => cases h; exact ⟨.failed, rfl⟩
  | consult site bound next ih =>
    obtain ⟨pick, middle, records, hc⟩ : ∃ pick middle records,
        Choices.consumeAtE site bound ch = (pick, middle, records) := ⟨_, _, _, rfl⟩
    simp only [run, hc] at h ⊢
    obtain ⟨hr, ht⟩ := ih pick middle h
    exact ⟨.consult (selection_of_consume hc) hr,
      replays_append (consume_replays hc) ht⟩

theorem selection_replay {site bound pick records ch tail}
    (hs : Selection site bound pick records) (hr : replays records ch tail) :
    Choices.consumeAtE site bound ch = (pick, tail, records) := by
  obtain ⟨hp, rfl⟩ := hs
  by_cases hb : bound ≤ 1
  · have hz : pick = 0 := by omega
    subst pick
    simp only [PickRecord.ofPick, if_pos hb, replays] at hr
    subst tail
    simp [Choices.consumeAtE, Choices.consumeAt_le_one hb, PickRecord.ofPick, hb]
  · simp only [PickRecord.ofPick, if_neg hb, replays] at hr
    obtain ⟨middle, hc, rfl⟩ := hr
    simpa [PickRecord.ofPick, hb] using hc

theorem replay_exact {check records cause} (h : Rejects check records cause)
    {ch tail} (hr : replays records ch tail) : run check ch = (some cause, tail, records) := by
  induction h generalizing ch tail with
  | failed => cases hr; rfl
  | consult hs _ ih =>
    obtain ⟨middle, hx, hy⟩ := replays_append_inv hr
    simp only [run, selection_replay hs hx, ih hy]

theorem replay {check records cause} (h : Rejects check records cause)
    {ch tail} (hr : replays records ch tail) : (run check ch).1 = some cause := by
  rw [replay_exact h hr]

theorem selections {check records cause} (h : Rejects check records cause)
    (tail : Choices) : ∃ ch, replays records ch tail := by
  induction h with
  | failed => exact ⟨tail, rfl⟩
  | consult hs _ ih =>
    obtain ⟨middle, hr⟩ := ih
    obtain ⟨ch, hc⟩ := hs.realize middle
    exact ⟨ch, replays_append (consume_replays hc) hr⟩

end Correspondence
end OperationCheck
end GoLean.GoCore.Relational.Local
