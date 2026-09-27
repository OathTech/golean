import GoLean.GoCore.ExecutionStatement
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.GoCore.ExecutionStatement

/-! Re-verification at `09c7fb0a` ([AGENT] auditor, 2026-09-27). -/

/-! ### F1: the old witness on the fixed interpreter -/
def ctx0 : ProgramCtx := ProgramCtx.ofTables #[] #[]
def s0 : Store := { heap := #[.value (.array 0 .int) (.array #[])] }
def c0 : Config := .evalE (.var "x") [[("x", .index (.base ⟨0⟩) 5)]] .stop

#eval match stepFn ctx0 s0 c0 [] with | .ok _ => "ok" | .error e => s!"{repr e}"
#eval match execStmtLoop ctx0 1 s0 c0 [] with | .ok _ => "ok" | .error e => s!"{repr e}"

theorem step0_refuses (ch : Choices) : ∃ r, stepFn ctx0 s0 c0 ch = .error (.refusal r) := ⟨_, rfl⟩

/-- The old refutation's key fact is now FALSE: no panic terminal at the witness. -/
theorem step0_not_panic (ch : Choices) (m : String) :
    stepFn ctx0 s0 c0 ch ≠ .error (.terminal (.panic m)) := by
  obtain ⟨r, h⟩ := step0_refuses ch; rw [h]; intro h'; cases h'

/-! ### F2: the corrected `NoRefusal` is SOUND — it excludes every refusing run -/

theorem prefix_snoc {ctx : ProgramCtx} {n : Nat} {s s' s'' : Store} {c c' c'' : Config}
    {ch ch' ch'' : Choices} {ls : List AccessTrace} {l : AccessTrace}
    (h : Prefix ctx n s c ch ls s' c' ch') (hs : stepFn ctx s' c' ch' = .ok (c'', s'', ch'', l)) :
    Prefix ctx (n + 1) s c ch (ls ++ [l]) s'' c'' ch'' := by
  induction h with
  | done => exact .step hs .done
  | step h1 _ ih => exact .step h1 (ih hs)

theorem loop_nonzero {ctx : ProgramCtx} {f : Nat} {s : Store} {c : Config} {ch : Choices}
    (hz : ¬ ZeroCost c) :
    execStmtLoop ctx (f + 1) s c ch =
      (do let (c', σ', ch', _) ← stepFn ctx s c ch; execStmtLoop ctx f σ' c' ch') := by
  rw [execStmtLoop_unfold]
  split
  · exact absurd (Or.inl rfl) hz
  · exact absurd (Or.inr (Or.inl ⟨_, _, _, rfl⟩)) hz
  · exact absurd (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl⟩))) hz
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩)))) hz
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩)))) hz
  · rfl

theorem loop_zeroCost {ctx : ProgramCtx} {f : Nat} {s : Store} {c : Config} {ch : Choices}
    (hz : ZeroCost c) (r : Refusal) : execStmtLoop ctx f s c ch ≠ .error (.refusal r) := by
  rcases hz with rfl | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    simp [execStmtLoop_unfold, throw, throwThe, MonadExceptOf.throw]

/-- Soundness of the corrected premise: under `NoRefusal`, NO run from `(s, c)` — at any fuel,
from any prefix endpoint — ends in a refusal. (The renderer clause is not needed: an abort
configuration is non-zero-cost, so the first clause already covers its refusal.) -/
theorem loop_noRefusal {ctx : ProgramCtx} {s : Store} {c : Config} {ch : Choices}
    (hN : NoRefusal ctx s c) :
    ∀ (fuel n : Nat) (ls : List AccessTrace) (s' : Store) (c' : Config) (ch' : Choices),
      Prefix ctx n s c ch ls s' c' ch' → ∀ r, execStmtLoop ctx fuel s' c' ch' ≠ .error (.refusal r) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n ls s' c' ch' hp r
    rw [execStmtLoop_unfold]
    split <;> simp [throw, throwThe, MonadExceptOf.throw]
  | succ fuel ih =>
    intro n ls s' c' ch' hp r
    by_cases hz : ZeroCost c'
    · exact loop_zeroCost hz r
    · rw [loop_nonzero hz]
      cases hst : stepFn ctx s' c' ch' with
      | error e =>
        simp only [bind, Except.bind]
        intro he; cases he
        exact (hN n ch ls s' c' ch' hp).1 hz r hst
      | ok v =>
        obtain ⟨c'', s'', ch'', l⟩ := v
        simp only [bind, Except.bind]
        exact ih _ _ _ _ _ (prefix_snoc hp hst) r

theorem noRefusal_sound {ctx : ProgramCtx} {s : Store} {c : Config} (hN : NoRefusal ctx s c)
    (fuel : Nat) (ch : Choices) (r : Refusal) : execStmtLoop ctx fuel s c ch ≠ .error (.refusal r) :=
  loop_noRefusal (ch := ch) hN fuel 0 [] s c ch .done r

/-! ### F3: `finish_replay_stmt` is TRUE -/

theorem pick_of_rec {site : ChoiceSite} {b : Nat} {ch ch₂ x : Choices} {p : Nat}
    {rec : List PickRecord} (h : Choices.consumeAtE site b ch = (p, x, rec))
    (h2 : (Choices.consumeAtE site b ch₂).2.2 = rec) : (Choices.consumeAtE site b ch₂).1 = p := by
  by_cases hb : b ≤ 1
  · simp [Choices.consumeAtE, Choices.consumeAt, hb] at h ⊢
    exact h.1
  · simp only [Choices.consumeAtE, hb, if_false] at h h2 ⊢
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    simp only [List.cons.injEq, PickRecord.mk.injEq] at h2
    exact h2.1.2.2

theorem finish_replay : finish_replay_stmt := by
  intro ctx s c ch ch₂ first rest rec habort hrec
  have key : ∀ {pick : Nat} {ch'' : Choices},
      Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch = (pick, ch'', rec) →
      Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂ =
        (pick, (Choices.consumeAtE .repanicCollapse (repanicCollapseWidth first rest) ch₂).2.1, rec) := by
    intro pick ch'' hc
    exact Prod.ext (pick_of_rec hc hrec) (Prod.ext rfl hrec)
  constructor
  · intro t ch'' hf
    cases hf with
    | aborted ha hc hm =>
      rw [habort] at ha; cases ha
      exact .aborted habort (key hc) hm
  · intro r ch'' hf
    cases hf with
    | abortRefused ha hc hm =>
      rw [habort] at ha; cases ha
      exact .abortRefused habort (key hc) hm

#print axioms noRefusal_sound
#print axioms finish_replay
