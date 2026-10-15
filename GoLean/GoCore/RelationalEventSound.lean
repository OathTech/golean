import GoLean.GoCore.RelationalEvent

namespace GoLean.GoCore.Relational
open Machine Boundary ObservationImplementation
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

local macro "boundary_simp" : tactic => `(tactic|
  simp_all [Boundary.Effect, Boundary.events, Boundary.entry?,
    Boundary.invocation?, Boundary.return?, Boundary.exitValues?, Except.toOption,
    activeCalls, callFrames, Boundary.unwinding, Entry.callConfig, Entry.drainConfig])

theorem step_boundary_effect {ctx c s d t l} (h : Step ctx c s d t l) :
    Boundary.Effect ⟨c, s⟩ ⟨d, t⟩ (Boundary.events ctx ⟨c, s⟩) := by
  cases h
  case evalRecover =>
    rename_i env k v k' he
    have hh := recoverResult_calls k
    rw [he] at hh
    boundary_simp
  case seqn =>
    rename_i ss env k
    have hh := seqCont_calls ss.toList env k
    boundary_simp
  case signal =>
    rename_i sg k he
    unfold signalStep at he
    repeat' split at he
    all_goals cases he <;> boundary_simp
  case signalStmt =>
    rename_i stmt sg env k he
    cases stmt <;> simp_all [Stmt.signal?] <;> boundary_simp
  case stmtOpFirst =>
    rename_i stmt op nt e rest env k he
    cases stmt <;> simp_all [stmtPlan] <;> boundary_simp
  case chanStFirst =>
    rename_i stmt op e rest env k he
    cases stmt <;> simp_all [chanPlan] <;> boundary_simp
  case syncStFirst =>
    rename_i stmt op e rest env k he
    cases stmt <;> simp_all [syncPlan] <;> boundary_simp
  case atomicStFirst =>
    rename_i stmt op e rest env k he
    cases stmt <;> simp_all [atomicPlan] <;> boundary_simp
  case deferCalleeNoArgs =>
    rename_i cv env k k' hc he
    have hh := pushDefer_calls he
    boundary_simp
  case deferArgsDone =>
    rename_i v cv vals env k k' he
    have hh := pushDefer_calls he
    boundary_simp
  case panicUnwind =>
    rename_i chain k k' he
    have hh := panicPassthrough_calls he
    unfold panicPassthrough at he
    split at he
    · cases k with
      | nil => cases he
      | cons f k =>
        cases f <;> boundary_simp
        all_goals simp_all [Cont.isGlue, Cont.class, Frame.class]
    · cases he
  case panicFrameEmpty =>
    boundary_simp
    exact ⟨_, _, _, _, _, _, rfl, rfl, rfl⟩
  case preprintReturn =>
    rename_i tenv rl older entry newer k fr v tr he
    have hl : loadResults ctx s [rl] = .ok ([v], tr) := by
      simp [loadResults, he, bind_eq_ok]
    boundary_simp
  case preprintFall =>
    rename_i tenv rl older entry newer k fr v tr he
    have hl : loadResults ctx s [rl] = .ok ([v], tr) := by
      simp [loadResults, he, bind_eq_ok]
    boundary_simp
  case callImmediate =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case callArgsDoneEnter =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case callValCalleeEnter =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case callValArgsEnter =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case frameDeferFall =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case frameDeferReturn =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case panicFrameDefer =>
    rename_i he hd
    rcases enterFramePick_cases he with ⟨e, t, tr, rfl, hx, rfl, rfl⟩ | ⟨msg, rfl, hx, _, _⟩
    · cases e <;> cases hd <;> boundary_simp
    · cases hd
      boundary_simp
  case evalStrictNullary =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case strictApply =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case stmtOpShiftTarget =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case stmtOpApply =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case rhsStores =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case storeStep =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case unseqRunLoad =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case preprintResolve =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, _⟩ | ⟨msg, rfl, _⟩
    all_goals cases hd <;> boundary_simp
  case chanStApply =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, hx⟩ | ⟨msg, rfl, _⟩
    · cases hd
      have hh := applyChanOp_calls hx
      boundary_simp
    · cases hd
      boundary_simp
  case syncStApply =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, hx⟩ | ⟨msg, rfl, _⟩
    · cases hd
      have hh := applySyncOp_calls hx
      boundary_simp
    · cases hd
      boundary_simp
  case atomicStApply =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, hx⟩ | ⟨msg, rfl, _⟩
    · cases hd
      have hh := applyAtomicOp_calls hx
      boundary_simp
    · cases hd
      boundary_simp
  case selectApply =>
    rename_i he hd
    rcases toResult_cases he with ⟨x, rfl, hx⟩ | ⟨msg, rfl, _⟩
    · cases hd
      have hh := applySelect_calls hx
      boundary_simp
    · cases hd
      boundary_simp
  all_goals boundary_simp

/-- Exhaustive successful-step classification. The structural clauses follow
from eliminating the original operational rules, including every generic
configuration-producing helper; they are independent of the event inventory. -/
theorem Transition.boundary_cases {ctx a b l} (h : Transition ctx a l b) :
    (events ctx a = [] ∧ (activeCalls b.control = activeCalls a.control ∨ Unwinds a b)) ∨
    (∃ e, events ctx a = [.entry e] ∧ Enters ctx a b l e ∧
      activeCalls b.control = e.function :: activeCalls a.control) ∨
    (∃ e, events ctx a = [.returned e] ∧ Returns ctx a b l e ∧
      activeCalls a.control = e.function :: activeCalls b.control ∧ unwinding a.control = false) := by
  have effect := step_boundary_effect h
  rcases events_cases ctx a with hn | ⟨e, he⟩ | ⟨e, he⟩
  · rw [hn] at effect
    exact Or.inl ⟨hn, effect⟩
  · rw [he] at effect
    exact Or.inr (Or.inl ⟨e, he, (entry?_on_transition h).mp (events_entry_iff.mp he), effect⟩)
  · rw [he] at effect
    exact Or.inr (Or.inr ⟨e, he, (return?_on_transition h).mp (events_return_iff.mp he), effect⟩)

namespace Boundary

theorem Unwinds.depth {a b} (h : Unwinds a b) :
    (activeCalls a.control).length = (activeCalls b.control).length + 1 ∧ unwinding a.control = true := by
  obtain ⟨chain, plans, env, roots, k, fid, ha, hb, _⟩ := h
  simp [ha, hb, activeCalls, callFrames, unwinding]

/-- Every actual activation push is reported, and every reported entry pushes
one activation. This criterion does not mention the proposed site inventory. -/
theorem entry_iff_depth {ctx a b l} (h : Transition ctx a l b) :
    (∃ e, Enters ctx a b l e) ↔ (activeCalls b.control).length = (activeCalls a.control).length + 1 := by
  constructor
  · rintro ⟨e, he⟩
    have hp := step_boundary_effect h
    rw [events_entry_iff.mpr ((entry?_on_transition h).mpr he)] at hp
    change activeCalls b.control = _ at hp
    simp [hp]
  · intro depth
    rcases h.boundary_cases with ⟨_, eq | uw⟩ | ⟨e, _, entry, _⟩ | ⟨e, _, _, eq, _⟩
    · rw [eq] at depth; omega
    · have hd := uw.depth; omega
    · exact ⟨e, entry⟩
    · have hd := congrArg List.length eq; simp only [List.length_cons] at hd; omega

/-- Every normal activation pop is reported, with panic propagation separated.
No well-formedness, safety, termination or realizing-tape premise is required. -/
theorem return_iff_depth {ctx a b l} (h : Transition ctx a l b) :
    (∃ e, Returns ctx a b l e) ↔
      (activeCalls a.control).length = (activeCalls b.control).length + 1 ∧ unwinding a.control = false := by
  constructor
  · rintro ⟨e, he⟩
    have hp := step_boundary_effect h
    rw [events_return_iff.mpr ((return?_on_transition h).mpr he)] at hp
    obtain ⟨eq, hn⟩ := hp
    exact ⟨by simp [eq], hn⟩
  · rintro ⟨depth, normal⟩
    rcases h.boundary_cases with ⟨_, eq | uw⟩ | ⟨e, _, _, eq⟩ | ⟨e, _, ret, _⟩
    · rw [eq] at depth; omega
    · have hd := uw.depth; simp_all
    · have hd := congrArg List.length eq; simp only [List.length_cons] at hd; omega
    · exact ⟨e, ret⟩

end Boundary
end GoLean.GoCore.Relational
