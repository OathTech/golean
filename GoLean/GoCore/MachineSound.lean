import GoLean.GoCore.StepFn

/-!
# Per-rule soundness of the executable step (reshape S5)

`stepFn_sound`: every `.ok` step the executable takes is a step of the
relation. With `step_complete` (the other direction), this replaces the
old T1/T2 big-step/small-step correspondence inductions: because `stepFn`
and the `Step` rules share their premise functions verbatim, the proof is
case analysis on the definition tree (`fun_cases`), not simulation
induction.
-/

namespace GoLean.GoCore.Machine

open GoLean

/-! ### Except-monad reduction helpers (the house idiom, formerly in
`Correspondence.lean`) -/

@[simp] theorem pure_eq_ok {ε α : Type} (a : α) :
    (pure a : Except ε α) = .ok a := rfl
@[simp] theorem stuck_def {α : Type} (m : String) :
    (GoCore.stuck m : Except GoError α) = .error (.stuck m) := rfl
@[simp] theorem panic_def {α : Type} (m : String) :
    (GoCore.panic m : Except GoError α) = .error (.panic m) := rfl
@[simp] theorem unsupported_def {α : Type} (m : String) :
    (GoCore.unsupported m : Except GoError α) = .error (.unsupported m) := rfl

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- Inverting a successful bool coercion: only `.bool` values pass. -/
theorem valueAsBool_ok {v : GoValue} {b : Bool} (h : valueAsBool v = .ok b) :
    v = .bool b := by
  cases v <;> simp_all [valueAsBool]

/-- The choice consumed at a nondeterministic point is in bounds (for a
positive bound) — `consume` reduces modulo the bound. -/
theorem consume_fst_lt {ch : Choices} {bound : Nat} (hb : 0 < bound) :
    (Choices.consume ch bound).1 < bound := by
  cases ch with
  | nil => simpa [Choices.consume] using hb
  | cons c rest =>
      have h := Nat.mod_lt c (y := max 1 bound) (by omega)
      simp only [Choices.consume]
      omega

/-! ### Soundness -/

-- The unused-simp-arg linter misfires on the shared multi-goal combinator
-- (an argument unused in one goal is load-bearing in another).
set_option linter.unusedSimpArgs false in
theorem stepFn_sound {s : ExecState} {c : Config} {ch : Choices}
    {c' : Config} {s' : ExecState} {ch' : Choices}
    (h : stepFn s c ch = .ok (c', s', ch')) : Step c s c' s' := by
  fun_cases stepFn s c ch
  all_goals
    (first
      | (simp_all [stepFn]; done)
      | (simp_all only [stepFn, Prod.mk.injEq]
         (try obtain ⟨rfl, rfl, rfl⟩ := h)
         constructor <;> first | assumption | rfl | omega)
      | skip)
  case case3 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.block hd
  case case4 =>
    simp_all only [stepFn, reduceIte, bind_eq_ok, pure_eq_ok, Except.ok.injEq,
      Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.initialization hd rfl
  case case23 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.callImmediate ‹_› ‹_› hd
  case case28 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨s₂, ch₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.stmtOpNullary ‹_› hd
  case case32 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.evalVar ‹_› hd
  case case52 =>
    simp_all only [stepFn, bind_eq_ok]
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b
    · simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.andFalse
    · simp only [reduceIte, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.andTrue
  case case53 =>
    simp_all only [stepFn, bind_eq_ok]
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b
    · simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.orFalse
    · simp only [reduceIte, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.orTrue
  case case54 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    obtain rfl := valueAsBool_ok hb
    exact Step.boolCoerce
  case case55 =>
    simp_all only [stepFn, bind_eq_ok]
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b
    · simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.ifFalse
    · simp only [reduceIte, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.ifTrue
  case case56 =>
    simp_all only [stepFn, bind_eq_ok]
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b
    · simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.whileFalse
    · simp only [reduceIte, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.whileTrue
  case case67 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.callTargetsDoneEnter ‹_› hd
  case case69 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.callArgsDoneEnter hd
  case case73 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.stmtOpShiftPlain (Nat.le_of_not_lt ‹_›)
  case case81 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.callValCalleeEnter hd
  case case87 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.callValArgsEnter hd
  case case97 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨entries, hd, rfl, rfl, rfl⟩ := h
    exact Step.mapRangeSnapshot hd
  case case104 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, s₂, hstore, rfl, rfl, rfl⟩ := h
    exact Step.frameFall hload hstore
  case case105 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.frameDeferFall hd
  case case132 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨func, frameEnv, resultLocs, s₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.frameDeferReturn hd
  case case109 =>
    rename_i hempty
    obtain rfl : _ = (#[] : Array (GoValue × GoValue)) := Array.isEmpty_iff.mp hempty
    simp_all only [stepFn, Array.isEmpty_empty, reduceIte, Except.ok.injEq,
      Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.mapIterDone
  case case110 =>
    rename_i keyVar valVar keyTy valTy body remaining env k' hne idx choices₂
      hcons hidx
    exfalso
    rw [Array.getElem?_eq_none_iff] at hidx
    have hsz : 0 < remaining.size := by
      simp [Array.isEmpty] at hne
      exact Array.size_pos_iff.mpr hne
    have hlt : idx < remaining.size := by
      simpa [hcons] using consume_fst_lt (ch := ch) hsz
    omega
  case case111 =>
    rename_i keyVar valVar keyTy valTy body remaining env k' hne idx choices₂
      hcons key value hidx hlt
    simp only [stepFn, hcons] at h
    rw [if_neg hne] at h
    have hfst : (Choices.consume ch remaining.size).fst = idx := by rw [hcons]
    split at h
    · rename_i heq
      rw [hfst, hidx] at heq
      cases heq
    · rename_i key' value' heq
      rw [hfst] at heq
      obtain ⟨rfl, rfl⟩ : key = key' ∧ value = value' := by
        simpa using hidx.symm.trans heq
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
      obtain ⟨_, hw⟩ := Array.getElem?_eq_some_iff.mp hidx
      exact Step.mapIterNext hlt (by rw [hw]; exact hd)
  case case131 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, s₂, hstore, rfl, rfl, rfl⟩ := h
    exact Step.frameReturn hload hstore

/-! ### Completeness -/

set_option linter.unusedSimpArgs false in
/-- Every relation step is realized by the executable under some choice
stream (deterministic rules under any stream; the two nondeterministic
step classes — `mapIterNext`'s pick and `stmtOpApply`'s capacity choice —
under the stream that encodes the rule's choice). -/
theorem step_complete {c : Config} {s : ExecState} {c' : Config} {s' : ExecState}
    (h : Step c s c' s') :
    ∃ ch ch' : Choices, stepFn s c ch = .ok (c', s', ch') := by
  cases h
  -- The strict-form and wide-statement entry rules hold the expression /
  -- statement abstract with only its plan known; stepFn's match needs the
  -- constructor, so case on it (the `Option` payloads of `slice` /
  -- `makeSlice` / `makeMap` split once more).
  case evalStrict =>
    rename_i e op e₁ rest env k hplan
    refine ⟨[], [], ?_⟩
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan])
  case evalStrictNullary =>
    rename_i e op v env k hplan happly
    refine ⟨[], [], ?_⟩
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan])
  case evalStrictNullaryPanic =>
    rename_i e op msg env k hplan happly
    refine ⟨[], [], ?_⟩
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan])
  case stmtOpFirst =>
    rename_i stmt op nt e rest env k hplan
    refine ⟨[], [], ?_⟩
    cases stmt <;>
      first
        | (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done))
  case stmtOpNullary =>
    rename_i stmt op nt env k ch₀ ch₁ hplan happly
    refine ⟨ch₀, ch₁, ?_⟩
    cases stmt <;>
      first
        | (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done))
  -- The choice-carrying apply rules: the witness stream is the rule's own.
  case stmtOpApply =>
    rename_i op nt done v env k ch₀ ch₁ happly
    exact ⟨ch₀, ch₁, by simp_all [stepFn]⟩
  case stmtOpApplyPanic =>
    rename_i op nt done v msg env k ch₀ happly
    exact ⟨ch₀, ch₀, by simp_all [stepFn]⟩
  case stmtOpShiftPlain =>
    rename_i op nt done v e rest env k hle
    refine ⟨[], [], ?_⟩
    simp only [stepFn]
    rw [if_neg (Nat.not_lt.mpr hle)]
    rfl
  -- The nondeterministic pick: the witness stream encodes the rule's index.
  case mapIterNext =>
    rename_i keyVar valVar keyTy valTy body remaining idx env env' k
      hidx hbind
    refine ⟨[idx], [], ?_⟩
    simp only [stepFn]
    rw [if_neg (by
      simp only [Array.isEmpty_iff]
      rintro rfl
      simp at hidx)]
    have hcons : Choices.consume [idx] remaining.size = (idx, []) := by
      simp [Choices.consume, Nat.mod_eq_of_lt
        (show idx < max 1 remaining.size by omega)]
    split
    · rename_i heq
      rw [hcons] at heq
      simp [Array.getElem?_eq_getElem hidx] at heq
    · rename_i key' value' heq
      rw [hcons] at heq
      simp only [Array.getElem?_eq_getElem hidx, Option.some.injEq] at heq
      simp only [heq] at hbind
      simp [hbind, hcons, Bind.bind, Except.bind]
  all_goals
    exact ⟨[], [], by simp_all [stepFn, Bind.bind, Except.bind, valueAsBool]⟩

/-! ### Driver-level soundness -/

/-- A terminating `runConfig` execution is a reachable relation trace
ending at the sequential terminal — the machine analogue of the old
`interpreterSound_frag`, but total over the full fragment and by simple
iteration over `stepFn_sound` instead of a simulation induction. -/
theorem runConfig_sound {fuel : Nat} {s : ExecState} {c : Config}
    {ch : Choices} {sF : ExecState} {chF : Choices}
    (h : runConfig fuel s c ch = .ok (sF, chF)) :
    Steps c s (.next .stop) sF := by
  fun_induction runConfig fuel s c ch with
  | case1 =>
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Steps.refl _ _
  | case2 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case3 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case4 =>
      rename_i ih
      rw [bind_eq_ok] at h
      obtain ⟨⟨c', s', ch'⟩, hstep, hrun⟩ := h
      exact (Steps.single (stepFn_sound hstep)).trans (ih _ _ _ hrun)

set_option linter.unusedSimpArgs false in
/-- Wrapper-level soundness for normal completion: a terminating
`execStmt` run (the F4 §2 Surface wrapper) is a reachable relation trace
to the sequential terminal. Total — the old fragment-scoped
side-conditions (`HeapFrag`, `StInv`) are retired. -/
theorem execStmtLoop_sound_normal {fuel : Nat} {σ : ExecState} {c : Config}
    {ch : Choices} {σf : ExecState} {chf : Choices}
    (h : execStmtLoop fuel σ c ch = .ok (.normal σf, chf)) :
    Steps c σ (.next .stop) σf := by
  fun_induction execStmtLoop fuel σ c ch with
  | case1 =>
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq,
        ExecOutcome.normal.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Steps.refl _ _
  | case2 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case3 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case4 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case5 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case6 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case7 =>
      rename_i ih
      rw [bind_eq_ok] at h
      obtain ⟨⟨c', s', ch'⟩, hstep, hrun⟩ := h
      exact (Steps.single (stepFn_sound hstep)).trans (ih _ _ _ hrun)

theorem execStmt_sound_normal {fuel : Nat} {env : LocalEnv} {σ : ExecState}
    {ch : Choices} {prog : Stmt} {σf : ExecState} {chf : Choices}
    (h : execStmt fuel env σ ch prog = .ok (.normal σf, chf)) :
    Steps (.exec prog env .stop) σ (.next .stop) σf :=
  execStmtLoop_sound_normal h

end GoLean.GoCore.Machine
