import GoLean.GoCore.StateWf

/-! Structural call-frame effects used to establish the complete event census.
The stack is extracted independently of any entry/exit site table. -/
namespace GoLean.GoCore.Relational
open Machine

/-- The active function identities, innermost first. Administrative frames
and suspended panic chains are not function activations. -/
def callFrames : Cont → List FuncId
  | [] => []
  | .frame _ _ _ _ fid :: k => fid :: callFrames k
  | _ :: k => callFrames k

/-- Function activations in the actual supplied control, without reachability
or well-formedness assumptions. -/
def activeCalls : Config → List FuncId
  | .exec _ _ k | .evalE _ _ k | .retV _ k | .next k | .signal _ k
  | .panicking _ k | .blockedSend _ _ k | .blockedRecv _ _ _ _ k
  | .blockedSelect _ _ k | .blockedSync _ _ _ k => callFrames k

namespace ObservationImplementation
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem rebuild_calls {β : Type} {descend : Cont → Bool}
    {act : Cont → Option (β × Cont)}
    (preserves : ∀ k b t, act k = some (b, t) → callFrames t = callFrames k)
    {k : Cont} {b : β} {t : Cont} (h : Cont.rebuild descend act k = some (b, t)) :
    callFrames t = callFrames k := by
  induction k generalizing t with
  | nil => exact preserves _ _ _ h
  | cons f k ih =>
    rw [Cont.rebuild_cons] at h
    split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨b', t'⟩, ht, rfl, rfl⟩ := h
      have he := ih ht
      cases f <;> simp_all [callFrames]
    · exact preserves _ _ _ h

 theorem pushDefer_calls {d k t} (h : pushDefer d k = some t) :
    callFrames t = callFrames k := by
  simp only [pushDefer, Option.map_eq_some_iff] at h
  obtain ⟨⟨b, t'⟩, he, rfl⟩ := h
  apply rebuild_calls (h := he)
  intro k b t h
  split at h
  · cases h; rfl
  · cases h

 theorem recoverAtDeferred_calls {k v t} (h : recoverAtDeferred k = some (v, t)) :
    callFrames t = callFrames k := by
  unfold recoverAtDeferred at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨v', chain⟩, _, rfl, rfl⟩ := h
    rfl
  · cases h

 theorem recoverResult_calls (k : Cont) : callFrames (recoverResult k).2 = callFrames k := by
  unfold recoverResult
  generalize he : Cont.rebuild _ _ k = result
  cases result with
  | none => rfl
  | some p =>
    exact rebuild_calls (h := he) (by
      intro k v t h
      split at h
      · split at h
        · cases h
          simpa [callFrames] using recoverAtDeferred_calls (by assumption)
        · cases h; rfl
      · cases h; rfl)

 theorem seqCont_calls (ss env k) : callFrames (seqCont ss env k) = callFrames k := by
  unfold seqCont
  split
  · split <;> rfl
  · rfl

 theorem signalStep_calls {sg k d} (h : signalStep sg k = some d) :
    activeCalls d = callFrames k := by
  unfold signalStep at h
  repeat' split at h
  all_goals cases h <;> rfl

 theorem panicPassthrough_calls {k t} (h : panicPassthrough k = some t) :
    callFrames t = callFrames k := by
  cases k with
  | nil => simp [panicPassthrough, Cont.isGlue, Cont.class] at h
  | cons f k =>
    cases f <;> simp_all [panicPassthrough, Cont.isGlue, Cont.class, Frame.class,
      Cont.tail, callFrames]

 theorem enterRecvTargets_calls {s targets vals body env k d t}
    (h : enterRecvTargets s targets vals body env k = .ok (d, t)) :
    activeCalls d = callFrames k := by
  unfold enterRecvTargets at h
  split at h
  · cases h; rfl
  · cases h

 theorem applyAtomicOp_calls {ctx s op vs env k d t tr}
    (h : applyAtomicOp ctx s op vs env k = .ok (d, t, tr)) :
    activeCalls d = callFrames k := by
  rw [applyAtomicOp.eq_def] at h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨loc, _, value, _, h⟩ := h
    split at h
    · split at h
      · cases h
      · simp only [bind_eq_ok] at h
        obtain ⟨⟨newValue, result⟩, _, s', _, h⟩ := h
        split at h
        · cases h; rfl
        · simp only [bind_eq_ok] at h
          obtain ⟨⟨c', s''⟩, he, h⟩ := h
          cases h
          exact enterRecvTargets_calls he
    · cases h
  · cases h



 theorem applyChanOp_calls {ctx s op vs env k d t tr}
    (h : applyChanOp ctx s op vs env k = .ok (d, t, tr)) :
    activeCalls d = callFrames k := by
  rw [applyChanOp.eq_def] at h
  repeat' first
    | (guard_hyp h : (Except.error _ : Except Stop _) = .ok _; cases h)
    | (guard_hyp h : (pure _ : Except _ _) = .ok _
       simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       first
         | obtain ⟨rfl, rfl, rfl⟩ := h
         | obtain ⟨rfl, rfl⟩ := h
       first | rfl | exact enterRecvTargets_calls (by assumption))
    | (try simp only [bind_eq_ok] at h
       guard_hyp h : ∃ _, _
       obtain ⟨x, hx, h⟩ := h)
    | split at h
  all_goals cases h

 theorem applySyncOpCore_calls {ctx s op vs env k d t tr}
    (h : applySyncOpCore ctx s op vs env k = .ok (d, t, tr)) :
    activeCalls d = callFrames k := by
  rw [applySyncOpCore.eq_def] at h
  repeat' first
    | (guard_hyp h : (Except.error _ : Except Stop _) = .ok _; cases h)
    | (guard_hyp h : (pure _ : Except _ _) = .ok _
       simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       first
         | obtain ⟨rfl, rfl, rfl⟩ := h
         | obtain ⟨rfl, rfl⟩ := h
       first | rfl | exact enterRecvTargets_calls (by assumption))
    | (try simp only [bind_eq_ok] at h
       guard_hyp h : ∃ _, _
       obtain ⟨x, hx, h⟩ := h)
    | split at h
  all_goals cases h

 theorem tryDeliver_calls {b s targets env k d t}
    (h : tryDeliver b s targets env k = .ok (d, t)) :
    activeCalls d = callFrames k := by
  rw [tryDeliver.eq_def] at h
  repeat' first
    | (guard_hyp h : (Except.error _ : Except Stop _) = .ok _; cases h)
    | (guard_hyp h : (pure _ : Except _ _) = .ok _
       simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       first
         | obtain ⟨rfl, rfl, rfl⟩ := h
         | obtain ⟨rfl, rfl⟩ := h
       first | rfl | exact enterRecvTargets_calls (by assumption))
    | (try simp only [bind_eq_ok] at h
       guard_hyp h : ∃ _, _
       obtain ⟨x, hx, h⟩ := h)
    | split at h
  all_goals cases h

 theorem applyTryLock_calls {ctx s op loc pre spurious targets env k d t tr}
    (h : applyTryLock ctx s op loc pre spurious targets env k = .ok (d, t, tr)) :
    activeCalls d = callFrames k := by
  rw [applyTryLock.eq_def] at h
  repeat' first
    | (guard_hyp h : (pure _ : Except _ _) = .ok _
       simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       exact tryDeliver_calls (by assumption))
    | (try simp only [bind_eq_ok] at h
       guard_hyp h : ∃ _, _
       obtain ⟨x, hx, h⟩ := h)
    | split at h
  all_goals cases h

 theorem applySyncOp_calls {ctx s ch op vs env k d t tail ps tr}
    (h : applySyncOp ctx s ch op vs env k = .ok (d, t, tail, ps, tr)) :
    activeCalls d = callFrames k := by
  rw [applySyncOp.eq_def] at h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨loc, _, pre, _, ⟨d', t', tr'⟩, he, h⟩ := h
    cases h
    exact applyTryLock_calls he
  · cases h
  · simp only [bind_eq_ok] at h
    obtain ⟨⟨d', t', tr'⟩, he, h⟩ := h
    cases h
    exact applySyncOpCore_calls he

 theorem commitClause_calls {ctx s env k cl d t tr}
    (h : commitClause ctx s env k cl = .ok (d, t, tr)) :
    activeCalls d = callFrames k := by
  rw [commitClause.eq_def] at h
  repeat' first
    | (guard_hyp h : (Except.error _ : Except Stop _) = .ok _; cases h)
    | (guard_hyp h : (pure _ : Except _ _) = .ok _
       simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
       first
         | obtain ⟨rfl, rfl, rfl⟩ := h
         | obtain ⟨rfl, rfl⟩ := h
       first | rfl | exact enterRecvTargets_calls (by assumption))
    | (try simp only [bind_eq_ok] at h
       guard_hyp h : ∃ _, _
       obtain ⟨x, hx, h⟩ := h)
    | split at h
  all_goals cases h

/-- Every chosen select outcome retains the supplied call stack. This follows
all precommitted branches, including the defensive picked-panic branch. -/
theorem applySelect_calls {ctx s clauses default vs env k ch d t tail ps cl tr}
    (h : applySelect ctx s clauses default vs env k ch = .ok (d, t, tail, ps, cl, tr)) :
    activeCalls d = callFrames k := by
  rw [applySelect.eq_def] at h
  simp only [bind_eq_ok] at h
  obtain ⟨outcome, hc, h⟩ := h
  rw [applySelectCore.eq_def] at hc
  simp only [bind_eq_ok] at hc
  obtain ⟨evs, _, ready, _, hc⟩ := hc
  split at h
  · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    split at hc
    · split at hc <;> cases hc <;> rfl
    · simp only [bind_eq_ok] at hc
      obtain ⟨⟨d', t', tr'⟩, he, hc⟩ := hc
      cases hc
      exact commitClause_calls he
    · simp only [bind_eq_ok] at hc
      obtain ⟨_, _, hc⟩ := hc
      cases hc
  · split at h
    · rename_i clp dc tc trc hget
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      split at hc
      · split at hc <;> cases hc
      · simp only [bind_eq_ok] at hc
        obtain ⟨⟨_, _, _⟩, _, hc⟩ := hc
        cases hc
      · simp only [bind_eq_ok] at hc
        obtain ⟨commits, hm, hc⟩ := hc
        cases hc
        obtain ⟨clause, _, he⟩ := mapM_getElem?_mem hm hget
        have hcommit : commitClause ctx s env k clause = .ok (dc, tc, trc) := by
          cases heq : commitClause ctx s env k clause with
          | ok r => rw [heq] at he; simp_all
          | error e =>
            rw [heq] at he
            rcases e with _ | term | _
            · simp_all
            · cases term <;> simp_all
            · simp_all
        exact commitClause_calls hcommit
    · cases h; rfl
    · cases h

end ObservationImplementation
end GoLean.GoCore.Relational
