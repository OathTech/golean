import GoLean.GoCore.RelationalObservation
import GoLean.GoCore.RelationalEventFrame

/-! Semantic body-entry and normal-return events, independently projected
from the supplied pre-state. Operational completeness is the call-stack
effect theorem, not agreement between two copies of an entry inventory. -/
namespace GoLean.GoCore.Relational
open Machine

inductive BoundaryEvent where
  | entry : EntryEvent → BoundaryEvent
  | returned : ReturnEvent → BoundaryEvent

namespace Boundary

/-- Candidate sequential invocation with the arguments supplied to entry.
This projection includes admission of direct-call target plans and excludes
pool spawn; its completeness is proved against actual successful steps. -/
def invocation? : Config → Option (FuncId × List GoValue)
  | .exec (.call targets fid args) _ _ =>
      match targetsPlan targets.toList, args.toList with
      | some _, [] => some (fid, [])
      | _, _ => none
  | .retV v (.callArgsK fid _ done [] _ _) => some (fid, done ++ [v])
  | .retV (.funcVal fid caps) (.callValCalleeK _ [] _ _) => some (fid, caps)
  | .retV v (.callValArgsK (.funcVal fid caps) _ done [] _ _) => some (fid, caps ++ done ++ [v])
  | .next (.frame _ _ _ ((.funcVal fid caps, args) :: _) _ _) => some (fid, caps ++ args)
  | .signal .ret (.frame _ _ _ ((.funcVal fid caps, args) :: _) _ _) => some (fid, caps ++ args)
  | .panicking _ (.frame _ _ _ ((.funcVal fid caps, args) :: _) _ _) => some (fid, caps ++ args)
  | _ => none

theorem invocation?_iff {fid args c} : invocation? c = some (fid, args) ↔
    ∃ frame, EntrySite fid args c frame := by
  constructor
  · intro h
    unfold invocation? at h
    split at h
    · split at h
      · cases h; exact ⟨_, .direct (by assumption) (by assumption)⟩
      · cases h
    · cases h; exact ⟨_, .arguments⟩
    · cases h; exact ⟨_, .closure⟩
    · cases h; exact ⟨_, .closureArguments⟩
    · cases h; exact ⟨_, .deferFall⟩
    · cases h; exact ⟨_, .deferReturn⟩
    · cases h; exact ⟨_, .deferPanic⟩
    · cases h
  · rintro ⟨_, site⟩
    cases site <;> simp_all [invocation?]

/-- Resolved identity, original supplied arguments and pre-store. A requeued
promotion/dispatch and a delivered entry panic do not enter a body. -/
def entry? (ctx : ProgramCtx) (a : State) : Option EntryEvent := do
  let (fid, args) ← invocation? a.control
  match enterFrame ctx a.store fid args with
  | .ok (.run f _ _, _, _) => some ⟨f.id, args, a.store⟩
  | _ => none

/-- Exact payload and continuation introduction/elimination. The independent
stack-effect theorem supplies operational completeness of this projection. -/
theorem entry?_iff {ctx a event} : entry? ctx a = some event ↔
    ∃ b l, Enters ctx a b l event := by
  constructor
  · intro h
    unfold entry? at h
    cases hi : invocation? a.control with
    | none => simp [hi] at h
    | some pair =>
      obtain ⟨fid, args⟩ := pair
      simp only [hi] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · rename_i f env roots t tr he
        cases h
        obtain ⟨frame, site⟩ := invocation?_iff.mp hi
        exact ⟨⟨.exec f.body env (frame roots f.id), t⟩, ⟨tr, [], []⟩,
          fid, frame, f, env, roots, tr, site, he, rfl, rfl, rfl, rfl⟩
      · cases h
  · rintro ⟨b, l, fid, frame, f, env, roots, tr, site, he, _, hf, hs, _⟩
    have hi := invocation?_iff.mpr ⟨frame, site⟩
    cases event
    simp_all [entry?]

/-- On an actual successful step, the projection reports precisely its
entry, including the actual successor and complete label. -/
theorem entry?_on_transition {ctx a b l event} (h : Transition ctx a l b) :
    entry? ctx a = some event ↔ Enters ctx a b l event := by
  constructor
  · intro he
    obtain ⟨b', l', entry⟩ := entry?_iff.mp he
    obtain ⟨rfl, rfl⟩ := entry.all_successors h
    exact entry
  · intro he
    exact entry?_iff.mpr ⟨b, l, he⟩

/-- Snapshot at normal exit, before subsequent target evaluation/writeback.
Discarded results are [] even when the function signature has results. -/
def exitValues? (ctx : ProgramCtx) (s : Store) :
    List (TargetShape × List Expr) → List Loc → Cont → Option (List GoValue)
  | [], [], _ => some []
  | [], [rl], .preprintK _ _ _ _ => (loadResults ctx s [rl]).toOption.map Prod.fst
  | (_, _ :: _) :: _, roots, _ => (loadResults ctx s roots).toOption.map Prod.fst
  | _, _, _ => none

/-- Normal exits only: panic frame unwinding and driver readback are distinct. -/
def return? (ctx : ProgramCtx) (a : State) : Option ReturnEvent :=
  match a.control with
  | .next (.frame plans _ roots [] k fid)
  | .signal .ret (.frame plans _ roots [] k fid) =>
      (exitValues? ctx a.store plans roots k).map fun vs => ⟨fid, vs, a.store⟩
  | _ => none

/-- The two normal ways of leaving a drained function frame. -/
inductive ReturnMode where
  | falling | explicit

def ReturnMode.control : ReturnMode → Cont → Config
  | .falling, k => .next k
  | .explicit, k => .signal .ret k

/-- The operation at the exit boundary, before caller target evaluation.
No premise asserts that later evaluation or delivery succeeds. -/
inductive ExitSite (ctx : ProgramCtx) (s : Store) :
    List (TargetShape × List Expr) → List Loc → Cont → LocalEnv →
    Config → List GoValue → AccessTrace → Prop where
  | discarded {k env} : ExitSite ctx s [] [] k env (.next k) [] []
  | targets {sh e ops rest roots k env vs tr} :
      loadResults ctx s roots = .ok (vs, tr) →
      ExitSite ctx s ((sh, e :: ops) :: rest) roots k env
        (.evalE e env (.tgtOpK sh [] ops [] rest .vals [] vs (.seqn #[]) env k)) vs tr
  | preprint {rl older entry newer k env v tr} :
      Mem.loadBinding ctx s rl = .ok (v, tr) →
      ExitSite ctx s [] [rl] (.preprintK older entry newer k) env
        (.retV v (.preprintK older entry newer k)) [v] tr

/-- Exact normal-exit descriptor, including successor, label and pre-store. -/
inductive Returns (ctx : ProgramCtx) : State → State → StepLabel → ReturnEvent → Prop where
  | intro {mode : ReturnMode} {plans roots k env c vs tr s fid} : ExitSite ctx s plans roots k env c vs tr →
      Returns ctx ⟨mode.control (.frame plans env roots [] k fid), s⟩
        ⟨c, s⟩ ⟨tr, [], []⟩ ⟨fid, vs, s⟩

theorem Returns.transition {ctx a b l event} (h : Returns ctx a b l event) :
    Transition ctx a l b := by
  cases h with
  | @intro mode plans roots k env c vs tr s fid site =>
    cases mode <;> cases site
    · exact Step.frameFall
    · exact Step.frameFallTargets (by assumption)
    · exact Step.preprintFall (by assumption)
    · exact Step.frameReturn
    · exact Step.frameReturnTargets (by assumption)
    · exact Step.preprintReturn (by assumption)

theorem Returns.all_successors {ctx a b d l m event} (h : Returns ctx a b l event)
    (hs : Transition ctx a m d) : b = d ∧ l = m := by
  have hp : l.picks = [] := by cases h; rfl
  exact h.transition.unique_of_no_picks hp hs

theorem ExitSite.values {ctx s plans roots k env c vs tr}
    (h : ExitSite ctx s plans roots k env c vs tr) : exitValues? ctx s plans roots k = some vs := by
  cases h with
  | discarded => rfl
  | targets he => simp [exitValues?, he, Except.toOption]
  | preprint he => simp [exitValues?, loadResults, he, Except.toOption, Bind.bind, Except.bind]

theorem exitValues?_iff {ctx s plans roots k env vs} :
    exitValues? ctx s plans roots k = some vs ↔ ∃ c tr, ExitSite ctx s plans roots k env c vs tr := by
  constructor
  · intro h
    unfold exitValues? at h
    split at h
    · cases h; exact ⟨_, _, .discarded⟩
    · rename_i rl older entry newer tail
      cases he : Mem.loadBinding ctx s rl with
      | error e => simp [loadResults, he, Except.toOption, Bind.bind, Except.bind] at h
      | ok pair =>
        obtain ⟨v, tr⟩ := pair
        simp [loadResults, he, Except.toOption, Bind.bind, Except.bind] at h
        subst vs
        exact ⟨_, _, .preprint he⟩
    · cases he : loadResults ctx s roots with
      | error e => simp [he, Except.toOption] at h
      | ok pair =>
        obtain ⟨vals, tr⟩ := pair
        simp [he, Except.toOption] at h
        subst vs
        exact ⟨_, _, .targets he⟩
    · cases h
  · rintro ⟨_, _, h⟩
    exact h.values

theorem return?_iff {ctx a event} : return? ctx a = some event ↔
    ∃ b l, Returns ctx a b l event := by
  constructor
  · intro h
    obtain ⟨c, s⟩ := a
    unfold return? at h
    split at h
    · rename_i plans env roots fid k hc
      change c = _ at hc
      subst c
      cases hv : exitValues? ctx s plans roots k with
      | none => simp [hv] at h
      | some vs =>
        simp [hv] at h
        subst event
        obtain ⟨d, tr, site⟩ := (exitValues?_iff (env := env)).mp hv
        exact ⟨_, _, .intro (mode := .falling) site⟩
    · rename_i plans env roots fid k hc
      change c = _ at hc
      subst c
      cases hv : exitValues? ctx s plans roots k with
      | none => simp [hv] at h
      | some vs =>
        simp [hv] at h
        subst event
        obtain ⟨d, tr, site⟩ := (exitValues?_iff (env := env)).mp hv
        exact ⟨_, _, .intro (mode := .explicit) site⟩
    · cases h
  · rintro ⟨b, l, h⟩
    cases h with
    | @intro mode plans roots k env c vs tr s fid site =>
      cases mode <;> simpa only [return?, ReturnMode.control, Option.map_some] using
        congrArg (Option.map fun vs => ReturnEvent.mk fid vs s) site.values

theorem return?_on_transition {ctx a b l event} (h : Transition ctx a l b) :
    return? ctx a = some event ↔ Returns ctx a b l event := by
  constructor
  · intro he
    obtain ⟨b', l', ret⟩ := return?_iff.mp he
    obtain ⟨rfl, rfl⟩ := ret.all_successors h
    exact ret
  · intro he
    exact return?_iff.mpr ⟨b, l, he⟩

/-- Semantic events of a successful step from this pre-state. On arbitrary
failed attempts this is only a projection, not evidence of an executed event. -/
def events (ctx : ProgramCtx) (a : State) : List BoundaryEvent :=
  (entry? ctx a).toList.map .entry ++ (return? ctx a).toList.map .returned

theorem entry_excludes_return {ctx a e} (h : entry? ctx a = some e) : return? ctx a = none := by
  obtain ⟨c, s⟩ := a
  obtain ⟨fn, args, pre⟩ := e
  obtain ⟨b, l, fid, frame, f, env, roots, tr, site, _⟩ := entry?_iff.mp h
  cases site <;> rfl

theorem events_cases (ctx : ProgramCtx) (a : State) :
    events ctx a = [] ∨ (∃ e, events ctx a = [.entry e]) ∨ ∃ e, events ctx a = [.returned e] := by
  cases he : entry? ctx a with
  | none =>
    cases hr : return? ctx a with
    | none => exact Or.inl (by simp [events, he, hr])
    | some e => exact Or.inr (Or.inr ⟨e, by simp [events, he, hr]⟩)
  | some e =>
    exact Or.inr (Or.inl ⟨e, by simp [events, he, entry_excludes_return he]⟩)

theorem events_entry_iff {ctx a e} : events ctx a = [.entry e] ↔ entry? ctx a = some e := by
  cases he : entry? ctx a with
  | none => cases hr : return? ctx a <;> simp [events, he, hr]
  | some v => simp [events, he, entry_excludes_return he]

theorem events_return_iff {ctx a e} : events ctx a = [.returned e] ↔ return? ctx a = some e := by
  cases he : entry? ctx a with
  | none => cases hr : return? ctx a <;> simp [events, he, hr]
  | some v => simp [events, he, entry_excludes_return he]

/-- Clients select/project semantic events; projections may inspect pre-store. -/
def project {Ev : Type} (observe : BoundaryEvent → List Ev) (ctx : ProgramCtx)
    (a : State) : List Ev := (events ctx a).flatMap observe

/-- The control is currently propagating a panic, rather than returning. -/
def unwinding : Config → Bool
  | .panicking _ _ => true
  | _ => false

/-- The separately classified removal of a panic-unwound frame. -/
def Unwinds (a b : State) : Prop :=
  ∃ chain plans env roots k fid,
    a.control = .panicking chain (.frame plans env roots [] k fid) ∧
    b.control = .panicking chain k ∧ b.store = a.store

/-- An independent structural meaning for the event classifier. Empty
observations preserve activations except for the explicit panic-unwind pop;
entry pushes and normal return pops the reported function identity. -/
def Effect (a b : State) : List BoundaryEvent → Prop
  | [] => activeCalls b.control = activeCalls a.control ∨ Unwinds a b
  | [.entry e] => activeCalls b.control = e.function :: activeCalls a.control
  | [.returned e] => activeCalls a.control = e.function :: activeCalls b.control ∧
      unwinding a.control = false
  | _ => False

end Boundary

theorem ReturnsDiscarded.observed {ctx a b event} (h : ReturnsDiscarded a b event) :
    Boundary.Returns ctx a b ⟨[], [], []⟩ event := by
  cases h
  · exact .intro (mode := .explicit) .discarded
  · exact .intro (mode := .falling) .discarded

end GoLean.GoCore.Relational
