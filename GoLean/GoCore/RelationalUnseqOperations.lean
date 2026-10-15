import GoLean.GoCore.RelationalUnseq

namespace GoLean.GoCore.Relational.Unseq
open Machine ExecutionStatement

/-- The exact tape consumed by a successful step replays its own record. -/
theorem successful_replay {ctx s t c d ch tail l}
    (h : stepFn ctx s c ch = .ok (d,t,tail,l)) : replays l.picks ch tail := by
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

/-- Store-uniform all-tape scheduler coverage with actual labels and records. -/
theorem scheduler_cover {ctx g st env body tail}
    (binary : Binary g st) (pending : g.allSettled st = false) (ready : g.ready st ≠ [])
    (s : Store) (ch : Choices) :
    ∃ i, i ∈ g.ready st ∧ ∃ l residual,
      Transition ctx (atPick g body st env tail s) l
        ⟨.next (.unseqK g body st [] env (.run i) tail.toMachine),s⟩ ∧
      replays l.picks ch residual := by
  obtain ⟨⟨c,t⟩, residual, l, he⟩ := scheduler_total (ctx := ctx) (env := env)
    (body := body) (tail := tail) (s := s) binary pending ready ch
  have hr := successful_replay he
  have hs := stepFn_sound he
  change Step ctx (.next (.unseqK g body st [] env .pick tail.toMachine)) s c t l at hs
  cases hs with
  | unseqComplete _ done _ _ => simp [pending] at done
  | unseqPick skip pick =>
    exact ⟨_, List.mem_of_getElem? pick, _, residual, Step.unseqPick skip pick, hr⟩

/-- A binder return is an actual single owned-root update. This law does not
mention a resource representation or assume facts about unrelated cells. -/
theorem binder_effect {ctx g st env body tail i o id head slot ty old v new}
    (get : g.occs[i]? = some o) (body_eq : o.body = .eval id head)
    (lookup : env.lookup id = some (.base ⟨slot⟩))
    (normal : normalizeValueForTy ctx ty v = .ok new) :
    StoreEffect ctx (fun s t => ∃ h : s.heap[slot]? = some (.value ty old),
      t = {s with heap := s.heap.set slot (.value ty new) (Array.getElem?_eq_some_iff.mp h).1})
      (.retV v (.unseqK g body st [] env (.wait i) tail))
      (.next (.unseqK g body (st.set i .done) [] env .pick tail)) := by
  refine ⟨⟨(by intro h; cases h), rfl⟩, ?_⟩
  intro s t h
  obtain ⟨cell, rfl⟩ := h
  have write := write_root (ctx := ctx) cell normal
  have loc : unseqCellLoc env id = .ok (.base ⟨slot⟩) := by
    simp [unseqCellLoc, lookup, pure, Except.pure]
  refine ⟨⟨[.access .write (.data (.base ⟨slot⟩))], [], []⟩,
    Step.unseqValue get body_eq loc ?_, rfl⟩
  simp [Mem.store, write, Loc.canon, Bind.bind, Except.bind, pure, Except.pure]

theorem completion_path {ctx g st env body tail fact policy}
    (ranked : Ranked g) (binary : Binary g st) (settled : g.allSettled st = true)
    (stores : g.stores = [])
    (pick_policy : policy (.next (.unseqK g body st [] env .pick tail)))
    (store_policy : policy (.next (.storeK [] [] body env tail))) :
    StorePathFor ctx fact policy (.next (.unseqK g body st [] env .pick tail))
      (.exec body env tail) := by
  refine .step (d := .next (.storeK [] [] body env tail)) ?_
    ⟨(by intro h; cases h), rfl⟩ pick_policy ?_
  · intro s _
    exact ⟨_, Step.unseqComplete binary.no_skipped_dependencies settled
      (ranked.completion_produced binary settled stores body)
      (by simp [stores, unseqStorePlan, pure, Except.pure]), rfl⟩
  exact .step (fun _ _ => ⟨_, Step.storeDone, rfl⟩)
    ⟨(by intro h; cases h), rfl⟩ store_policy .refl

end GoLean.GoCore.Relational.Unseq
