import GoLean.GoCore.PoolStatement

/-! Replay helper proofs for the pool. [AGENT Codex, pool grind] 2026-10-05. -/

namespace GoLean.GoCore.PoolReplayFacts

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

theorem replays_append {xs ys : List PickRecord} {ch ch' : Choices} :
    replays (xs ++ ys) ch ch' ↔ ∃ mid, replays xs ch mid ∧ replays ys mid ch' := by
  induction xs generalizing ch with
  | nil => simp [replays]
  | cons x xs ih =>
      simp only [List.cons_append, replays, ih]
      constructor
      · rintro ⟨mid, hc, last, hx, hy⟩
        exact ⟨last, ⟨mid, hc, hx⟩, hy⟩
      · rintro ⟨last, ⟨mid, hc, hx⟩, hy⟩
        exact ⟨mid, hc, last, hx, hy⟩

theorem consult_replay {site : ChoiceSite} {bound pick : Nat} {ch ch' : Choices}
    {ps : List PickRecord} (h : Choices.consumeAtE site bound ch = (pick, ch', ps))
    {other rest : Choices} (hr : replays ps other rest) :
    Choices.consumeAtE site bound other = (pick, rest, ps) := by
  by_cases hb : bound ≤ 1
  · rw [Choices.consumeAtE_le_one hb] at h
    cases h
    cases hr
    exact Choices.consumeAtE_le_one hb
  · have hp := (Choices.consumeAtE_inv h).1
    rw [hp, PickRecord.ofPick, if_neg hb] at hr ⊢
    obtain ⟨mid, hm, hr⟩ := hr
    cases hr
    exact hm

theorem consult_of_replays {site : ChoiceSite} {bound pick : Nat}
    (hp : pick < bound) {ch rest : Choices}
    (hr : replays (PickRecord.ofPick site bound pick) ch rest) :
    Choices.consumeAtE site bound ch = (pick, rest, PickRecord.ofPick site bound pick) := by
  by_cases hb : bound ≤ 1
  · have h0 : pick = 0 := by omega
    subst pick
    simp only [PickRecord.ofPick, if_pos hb, replays] at hr
    subst rest
    simp only [Choices.consumeAtE_le_one hb, PickRecord.ofPick, if_pos hb]
  · simp only [PickRecord.ofPick, if_neg hb, replays] at hr
    obtain ⟨mid, hm, rfl⟩ := hr
    simpa only [PickRecord.ofPick, if_neg hb] using hm

theorem applySelect_replay {ctx : ProgramCtx} {s s' : Store}
    {clauses : List (SelectClauseHead × Stmt)} {default : Option Stmt} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {ch ch' : Choices} {c' : Config}
    {ps : List PickRecord} {cl : Option EvClause} {tr : AccessTrace}
    (h : applySelect ctx s clauses default vs env k ch = .ok (c', s', ch', ps, cl, tr))
    {other rest : Choices} (hr : replays ps other rest) :
    applySelect ctx s clauses default vs env k other = .ok (c', s', rest, ps, cl, tr) := by
  unfold applySelect at h ⊢
  cases hc : applySelectCore ctx s clauses default vs env k with
  | error e => rw [hc] at h; cases h
  | ok res =>
      rw [hc] at h
      cases res with
      | done c s cl tr =>
          cases h
          cases hr
          rfl
      | picks poll commits =>
          simp only [Bind.bind, Except.bind] at h ⊢
          rcases hd : Choices.consumeAtE .l2Entry commits.length ch with ⟨pick, mid, recs⟩
          rw [hd] at h
          cases hg : commits[pick]? with
          | none => rw [hg] at h; cases h
          | some r =>
              obtain ⟨cl, r⟩ := r
              cases r with
              | inl r =>
                  obtain ⟨c, s, tr⟩ := r
                  rw [hg] at h
                  cases h
                  rw [consult_replay hd hr, hg]
                  rfl
              | inr msg =>
                  rw [hg] at h
                  cases h
                  rw [consult_replay hd hr, hg]
                  rfl

theorem applySelect_panic_replay {ctx : ProgramCtx} {s : Store}
    {clauses : List (SelectClauseHead × Stmt)} {default : Option Stmt} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} {ch : Choices} {msg : String}
    (h : applySelect ctx s clauses default vs env k ch = .error (.panic msg)) (other : Choices) :
    applySelect ctx s clauses default vs env k other = .error (.panic msg) := by
  unfold applySelect at h ⊢
  cases hc : applySelectCore ctx s clauses default vs env k with
  | error e => rw [hc] at h; exact h
  | ok res =>
      rw [hc] at h
      cases res with
      | done c s cl tr => cases h
      | picks poll commits =>
          simp only [Bind.bind, Except.bind] at h
          split at h <;> cases h

theorem enterFramePickV_replay {ctx : ProgramCtx} {s : Store} {fid : FuncId} {args : List GoValue}
    {ch ch' : Choices} {r : Result (Commit (Entry × Store × AccessTrace))} {ps : List PickRecord}
    (h : enterFramePickV ctx s fid args ch = .ok (r, ch', ps))
    {other rest : Choices} (hr : replays ps other rest) :
    enterFramePickV ctx s fid args other = .ok (r, rest, ps) := by
  unfold enterFramePickV at h ⊢
  cases he : toResult (enterFrame.plan ctx s fid args) with
  | error e => rw [he] at h; cases h
  | ok v =>
      rw [he] at h
      cases v with
      | ok c => cases h; cases hr; rfl
      | panic msg =>
          rcases hd : Choices.consumeAtE .nilValueMethodText (nilValueMethodWidth ctx fid args) ch
            with ⟨pick, mid, recs⟩
          rw [hd] at h
          cases h
          rw [consult_replay hd hr]

theorem spawnStep_replay {ctx : ProgramCtx} {s s' : Store} {cv : GoValue} {args : List GoValue}
    {k : Cont} {ch ch' : Choices} {parent child : Config} {ps : List PickRecord} {tr : AccessTrace}
    (h : spawnStep ctx s cv args k ch = .ok (parent, child, s', ch', ps, tr))
    {other rest : Choices} (hr : replays ps other rest) :
    spawnStep ctx s cv args k other = .ok (parent, child, s', rest, ps, tr) := by
  unfold spawnStep at h ⊢
  split at h
  · rename_i fid captured
    rcases he : enterFramePickV ctx s fid (captured ++ args) ch with e | ⟨r, mid, recs⟩
    · rw [he] at h; cases h
    · rw [he] at h
      simp only [Bind.bind, Except.bind] at h
      cases r with
      | ok c =>
          dsimp only at h
          cases hc : runCommit c s with
          | error e => rw [hc] at h; cases h
          | ok result =>
              obtain ⟨entry, s₁, tr₁⟩ := result
              rw [hc] at h
              cases h
              rw [enterFramePickV_replay he hr]
              simp only [Bind.bind, Except.bind, hc]
              rfl
      | panic msg =>
          cases h
          rw [enterFramePickV_replay he hr]
          rfl
  · cases h
  · cases h

end GoLean.GoCore.PoolReplayFacts
