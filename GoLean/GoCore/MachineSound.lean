import GoLean.GoCore.StepFn
import GoLean.GoCore.StateWf

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

/-! The Except-monad reduction helpers (`pure_eq_ok`, `stuck_def`,
`panic_def`, `unsupported_def`, `bind_eq_ok`) moved upstream to
`StateWf.lean` (sem-adequacy slice 3) — same names, same namespace. -/

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
  case case2 =>
    simp_all only [stepFn, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.panicFrameEmpty
  case case3 =>
    simp_all only [stepFn, enterFrameDeferPanicking]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.panicFrameDefer hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.panicFrameDeferEnterPanic hd
    · simp at h
  case case158 =>
    rename_i hrec
    simp_all only [stepFn, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.panicResumeContinue (Bool.eq_false_iff.mpr hrec)
  case case13 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.block hd
  case case14 =>
    simp_all [stepFn, bind_eq_ok]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.initialization hd rfl
  case case37 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callImmediate ‹_› ‹_› hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callImmediatePanic ‹_› ‹_› hd
    · simp at h
  case case56 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨s₂, ch₂⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.stmtOpNullary ‹_› hd
  case case58 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.evalVar ‹_› hd
  case case79 =>
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
  case case80 =>
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
  case case81 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    obtain rfl := valueAsBool_ok hb
    exact Step.boolCoerce
  case case82 =>
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
  case case83 =>
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
  case case94 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callTargetsDoneEnter ‹_› hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callTargetsDoneEnterPanic ‹_› hd
    · simp at h
  case case96 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callArgsDoneEnter hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callArgsDoneEnterPanic hd
    · simp at h
  case case100 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.stmtOpShiftPlain (Nat.le_of_not_lt ‹_›)
  case case108 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callValCalleeEnter hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callValCalleeEnterPanic hd
    · simp at h
  case case114 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callValArgsEnter hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.callValArgsEnterPanic hd
    · simp at h
  case case124 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨entries, hd, rfl, rfl, rfl⟩ := h
    exact Step.mapRangeSnapshot hd
  case case153 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, s₂, hstore, rfl, rfl, rfl⟩ := h
    exact Step.frameFall hload hstore
  case case154 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.frameDeferFall hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.frameDeferFallEnterPanic hd
    · simp at h
  case case192 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.frameDeferReturn hd
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.frameDeferReturnEnterPanic hd
    · simp at h
  case case161 =>
    rename_i hempty
    obtain rfl : _ = (#[] : Array (GoValue × GoValue)) := Array.isEmpty_iff.mp hempty
    simp_all only [stepFn, Array.isEmpty_empty, reduceIte, Except.ok.injEq,
      Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.mapIterDone
  case case162 =>
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
  case case163 =>
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
  case case191 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, s₂, hstore, rfl, rfl, rfl⟩ := h
    exact Step.frameReturn hload hstore
  -- Channel statements (channels arc slice 1).
  case case42 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.chanStFirst hplan
  case case43 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case44 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_pos hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case45 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_neg hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case128 =>
    rename_i happly
    simp only [stepFn] at h
    rw [happly] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.chanStApplyPanic happly
  case case132 =>
    rename_i happly
    simp only [stepFn] at h
    rw [happly] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.selectApplyPanic happly

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
  case panicUnwind =>
    rename_i chain k k' hpass
    refine ⟨[], [], ?_⟩
    cases k <;> simp_all [stepFn, panicPassthrough]
  -- Channel statements (channels arc slice 1): entry holds the statement
  -- abstract behind its plan (case on it, like stmtOpFirst); the plain
  -- shift needs its `if_neg`, like stmtOpShiftPlain.
  case chanStFirst =>
    rename_i stmt op e rest env k hplan
    refine ⟨[], [], ?_⟩
    cases stmt <;>
      first
        | (simp_all [stepFn, chanPlan]; done)
        | (simp only [stepFn]; rw [hplan]; rfl)
  -- The select apply rules carry their own stream (the L2 pick, slice
  -- 4): realize under exactly it.
  case selectApply =>
    rename_i ch₀ ch₀' happly
    simp only [List.reverse_cons] at happly
    exact ⟨ch₀, ch₀', by simp [stepFn, happly]⟩
  case selectApplyPanic =>
    rename_i ch₀ happly
    simp only [List.reverse_cons] at happly
    exact ⟨ch₀, ch₀, by simp [stepFn, happly]⟩
  all_goals
    exact ⟨[], [], by simp_all [stepFn, enterFrameStep, enterFrameDeferPanicking, Bind.bind, Except.bind, valueAsBool]⟩

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
  | case4 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case5 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case6 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case7 =>
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
  | case7 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case8 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case9 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case10 =>
      rename_i ih
      rw [bind_eq_ok] at h
      obtain ⟨⟨c', s', ch'⟩, hstep, hrun⟩ := h
      exact (Steps.single (stepFn_sound hstep)).trans (ih _ _ _ hrun)

theorem execStmt_sound_normal {fuel : Nat} {env : LocalEnv} {σ : ExecState}
    {ch : Choices} {prog : Stmt} {σf : ExecState} {chf : Choices}
    (h : execStmt fuel env σ ch prog = .ok (.normal σf, chf)) :
    Steps (.exec prog env .stop) σ (.next .stop) σf :=
  execStmtLoop_sound_normal h

/-- **Executable reachability is relation reachability** (sem-adequacy
arc slice 4): a successful `stepFnIter` prefix is a `Steps` trace —
`stepFn_sound` chained. This is the transport the interpreter-level
invariance judgment (`Surface.GoInvariant` over `Surface.ReachableExec`)
rides to consume relation-side discharges: every `stepFnIter`-reachable
configuration is `Steps`-reachable. The CONVERSE (every `Steps`-reachable
configuration is `stepFnIter`-reachable under some stream) is true on
paper — `step_complete` realizes each rule at some stream — but chaining
its per-step witness streams into ONE `stepFnIter` stream needs a
stream-stitching lemma that is not built; it is not needed for any
current discharge and is recorded in the arc doc, not claimed. -/
theorem stepFnIter_sound :
    ∀ {n : Nat} {σ₀ : ExecState} {c₀ : Config} {ch : Choices}
      {c : Config} {σ : ExecState} {ch' : Choices},
    stepFnIter n σ₀ c₀ ch = .ok (c, σ, ch') → Steps c₀ σ₀ c σ := by
  intro n
  induction n with
  | zero =>
    intro σ₀ c₀ ch c σ ch' h
    simp only [stepFnIter, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Steps.refl _ _
  | succ n ih =>
    intro σ₀ c₀ ch c σ ch' h
    simp only [stepFnIter, bind_eq_ok] at h
    obtain ⟨⟨c₁, σ₁, ch₁⟩, hstep, hiter⟩ := h
    exact (Steps.single (stepFn_sound hstep)).trans (ih hiter)


/-! ### The sem() correspondence kit (sem-adequacy arc slice 3, 2026-08-03)

Interpreter-level `Terminates`/`ProgressExec` (`Surface.lean`) rest on
three machine facts: fuel monotonicity of completed runs, choices-
obliviousness of step SUCCESS (the machine consumes the stream at exactly
two sites, both total — `applyStmtOpCore` makes this structural), and the
transport from relation-Progress to per-run non-stuckness.

**Slice-3 obstruction (2026-08-03, machine-checked): step SUCCESS is NOT
choices-oblivious over arbitrary states.** `applyStmtOp`'s appendSlice
spill path allocates the new backing at `s.nextAddr` and THEN stores the
result slice through the target address; a target `Loc` that aliases into
that fresh cell (base id = `s.nextAddr` — a dangling address no reachable
well-formed state contains, but nothing in these theorems' hypotheses
excludes) makes the outcome depend on the consumed capacity choice:
`extra` sizes the fresh backing array, so an index along the target path
can be in range at one stream and out of range (panic) — or land on a
non-array element (stuck) — at another. Concrete witness (state: heap
`{0 ↦ array[4], 1 ↦ array[1]}`, `nextAddr = 2`, spill `4+1 > cap 4`,
growth base `appendGrowthCap 4 5 = 8`, target `.index (.base 2) 8`):
`.ok` under stream `[1]` (newCap 9) vs `.error (.panic "index out of
range")` under `[0]` (newCap 8); with target `.index (.index (.base 2) 8)
0` it is panic-vs-STUCK. So `applyStmtOp`-ok-at-one-stream →
ok-at-every-stream is FALSE, and with it per-rule completeness-at-every-
stream and the unconditioned relation-Progress → `ProgressExec`
transport. `buildAppendBackingValue` itself is NOT the obstruction (its
cap-check never fires for the caps this arm passes, and its padding
`defaultValue` is derivable from the arm's normalize successes); the
final aliasing store is. The transport needs a dangling-loc
well-formedness side condition (locs below `nextAddr`, preserved by
`Step`) — a design decision recorded for the arc doc, not forced here. -/

/-- A completed bounded run is stable under more fuel: the loop stops at
the terminal before consulting the surplus. -/
theorem execStmtLoop_mono :
    ∀ (fuel fuel' : Nat) (σ : ExecState) (c : Config) (ch : Choices)
      (r : ExecOutcome × Choices),
    fuel ≤ fuel' → execStmtLoop fuel σ c ch = .ok r →
    execStmtLoop fuel' σ c ch = .ok r := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' σ c ch r _ h
    unfold execStmtLoop at h ⊢
    split at h <;> simp_all
  | succ n ih =>
    intro fuel' σ c ch r hle h
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := ⟨fuel' - 1, by omega⟩
    unfold execStmtLoop at h ⊢
    split at h <;> try simp_all
    -- the non-terminal arm: one step then recurse at smaller fuel
    simp only [Bind.bind] at h ⊢
    cases hstep : stepFn σ c ch with
    | error e => rw [hstep] at h; simp [Except.bind] at h
    | ok trip =>
      obtain ⟨c', σ', ch'⟩ := trip
      rw [hstep] at h
      simp only [Except.bind] at h ⊢
      exact ih _ _ _ _ _ _ (by omega) h

@[inherit_doc execStmtLoop_mono]
theorem execStmt_mono {fuel fuel' : Nat} {env : LocalEnv} {σ : ExecState}
    {ch : Choices} {prog : Stmt} {r : ExecOutcome × Choices}
    (hle : fuel ≤ fuel')
    (h : execStmt fuel env σ ch prog = .ok r) :
    execStmt fuel' env σ ch prog = .ok r :=
  execStmtLoop_mono fuel fuel' _ _ _ _ hle h

/-- `.panicked` is genuinely terminal for the relation, not just for the
driver: no rule's source configuration is `.panicked` (every conclusion
starts from an eval/ret/exec/unwind shape), so a reachable `.panicked`
can never be discharged by "it still steps" in a progress hypothesis. -/
theorem step_panicked_elim {msg : String} {σ : ExecState} {c' : Config}
    {σ' : ExecState} : ¬ Step (.panicked msg) σ c' σ' := by
  intro h
  cases h

/-! The three unwound-`.stop` terminals are ALSO genuinely terminal for
the relation (audit response 2026-08-04): every `.returning`/`.breaking`/
`.continuing`-source rule matches a specific non-`.stop` continuation
constructor (`.seq`/`.loop`/`.breakableK`/`.mapIterK`/`.frame`), so none
applies at `.stop`. With `step_panicked_elim` these pin
`execStmtLoop_ok_or_fuelOut`'s success disjunct to the `.normal`
terminal: under a relation-Progress hypothesis (every reachable
configuration is `.next .stop` or steps), a reachable unwound-`.stop`
configuration is a CONTRADICTION, not a successful completion. -/

@[inherit_doc step_panicked_elim]
theorem step_returning_stop_elim {σ : ExecState} {c' : Config}
    {σ' : ExecState} : ¬ Step (.returning .stop) σ c' σ' := by
  intro h
  cases h

@[inherit_doc step_panicked_elim]
theorem step_breaking_stop_elim {σ : ExecState} {c' : Config}
    {σ' : ExecState} : ¬ Step (.breaking .stop) σ c' σ' := by
  intro h
  cases h

@[inherit_doc step_panicked_elim]
theorem step_continuing_stop_elim {σ : ExecState} {c' : Config}
    {σ' : ExecState} : ¬ Step (.continuing .stop) σ c' σ' := by
  intro h
  cases h

/-! Blocked configurations (channels arc slice 1) are relation-TERMINAL:
no rule steps a blocked goroutine — pairing is the slice-2 pool's job.
Under a relation-Progress hypothesis a reachable blocked configuration
is therefore a contradiction, which keeps
`execStmtLoop_ok_or_fuelOut`'s meaning intact: a proven sequential
Progress still implies the run never deadlocks. -/

@[inherit_doc step_panicked_elim]
theorem step_blockedSend_elim {chl : Option Loc} {v : GoValue} {k : Cont}
    {σ : ExecState} {c' : Config} {σ' : ExecState} :
    ¬ Step (.blockedSend chl v k) σ c' σ' := by
  intro h
  cases h

@[inherit_doc step_panicked_elim]
theorem step_blockedRecv_elim {chl : Option Loc} {targets : List Assignee}
    {elem : Ty} {env : LocalEnv} {k : Cont} {σ : ExecState} {c' : Config}
    {σ' : ExecState} :
    ¬ Step (.blockedRecv chl targets elem env k) σ c' σ' := by
  intro h
  cases h

@[inherit_doc step_panicked_elim]
theorem step_blockedSelect_elim {clauses : List EvClause} {env : LocalEnv}
    {k : Cont} {σ : ExecState} {c' : Config} {σ' : ExecState} :
    ¬ Step (.blockedSelect clauses env k) σ c' σ' := by
  intro h
  cases h

/-! ### Well-formedness preservation at the machine level (StateWf arc,
2026-08-04; `GoLean/GoCore/StateWf.lean`)

The dangling-loc side condition the slice-3 obstruction note above asked
for now EXISTS: `MachineWf` (state + configuration location-boundedness)
is preserved by every rule, and the executable inherits it through
`stepFn_sound`.

**Status of the ∀-choices kit under wf — CLOSED (history preserved):**
* `appendSlice` resolved exactly as predicted: under bounded operands the
  spill target's root base addresses an EXISTING cell, so ok-ness cannot
  depend on the consumed capacity choice (`applyStmtOp_ok_any_ch_wf`
  below).
* A SECOND obstruction was machine-checked mid-slice
  (`.tmp/probe_mapiter.lean`): `mapIterNext` resisted ∀-streams even
  under loc-wf — an ill-TYPED `mapIterK` snapshot (`#[(int,_),(bool,_)]`
  at `keyTy = int`) is loc-free, the relation steps by picking the good
  entry, but a stream picking the bad one fails `bindIterVars`'
  normalization. Loc-wf structurally cannot exclude it. RESOLVED (user
  decision, arc doc slice-3 entry): the mapRange SNAPSHOT step now
  fail-closes unless every snapshot key AND value is self-normalized at
  the range types (`mapRangeSnapshotEntries`), and `MachineWf` carries
  the matching `itersNormalized` typing component for in-flight
  snapshots — so `step_complete_any_wf`, `execStmtLoop_ok_or_fuelOut`,
  and `progressExec_of_progress` (Surface) hold as stated below; the old
  witness now fails `MachineWf` and its snapshot is rejected identically
  at every stream (`.tmp/probe_mapiter2.lean`). -/

@[inherit_doc step_preserves_wf]
theorem Step.preserves_wf {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} (h : Step c σ c' σ') (hwf : MachineWf σ c) :
    MachineWf σ' c' :=
  step_preserves_wf h hwf

/-- Executable-side preservation: an `.ok` step of `stepFn` keeps the
machine well-formed (`stepFn_sound` + `step_preserves_wf`). This is the
fact `execStmtLoop`-level inductions thread along a run. -/
theorem stepFn_preserves_wf {s : ExecState} {c : Config} {ch : Choices}
    {c' : Config} {s' : ExecState} {ch' : Choices}
    (h : stepFn s c ch = .ok (c', s', ch')) (hwf : MachineWf s c) :
    MachineWf s' c' :=
  step_preserves_wf (stepFn_sound h) hwf

/-- Every wide op that dispatches through the choices-free core succeeds
identically under EVERY stream (the stream passes through untouched):
the non-`appendSlice` half of the ∀-choices kit, true by construction
since the `applyStmtOpCore` refactor. -/
theorem applyStmtOp_ok_any_ch_core {σ : ExecState} {ch : Choices}
    {op : StmtOp} {nt : Nat} {vs : List GoValue} {σ' : ExecState}
    {ch' : Choices} (hop : ∀ elem, op ≠ .appendSlice elem)
    (h : applyStmtOp σ ch op nt vs = .ok (σ', ch')) :
    ∀ ch₂ : Choices, applyStmtOp σ ch₂ op nt vs = .ok (σ', ch₂) := by
  intro ch₂
  cases op <;>
    first
    | exact absurd rfl (hop _)
    | (simp only [applyStmtOp, bind_eq_ok, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h ⊢
       obtain ⟨σ₂, hcore, rfl, rfl⟩ := h
       exact ⟨σ₂, hcore, rfl, trivial⟩)

/-! ### The appendSlice half of the ∀-choices kit (sem-adequacy slice 3,
2026-08-04)

The spill path's outcome CLASS (ok / panic / neither) is independent of
the consumed capacity choice, under `StateWf` + bounded operands. The
three previously-recorded missing lemmas are here:
`defaultValueFuel_ok_of_normalize_ok` (padding defaults derivable from
any element's normalize success), `Heap.lookup_set_ne` +
`loadLoc_root_congr` (load/store agreement below `nextAddr` across the
fresh-backing alloc), and the `capCong` congruence family (normalize-ok
uniformity: store success cannot depend on the stored slice's CAP, the
only value component the choice reaches). -/

/-- The root `.base` location of an access path — the only heap KEY
`loadLoc`/`storeLoc` ever look up along the path. -/
def Loc.rootLoc (l : Loc) : Loc := .base ⟨Loc.rootBase l⟩

theorem Heap.lookup_set_ne {h : Heap} {k l : Loc} {c : HeapCell}
    (hne : k ≠ l) :
    Heap.lookup (Heap.set h k c) l = Heap.lookup h l := by
  induction h with
  | nil => simp [Heap.set, Heap.lookup, beq_eq_false_iff_ne.mpr hne]
  | cons p rest ih =>
    obtain ⟨loc, old⟩ := p
    simp only [Heap.set]
    cases hb : (loc == k) with
    | true =>
      obtain rfl := eq_of_beq hb
      simp [Heap.lookup, beq_eq_false_iff_ne.mpr hne]
    | false => simp [Heap.lookup, ih]

/-- `loadLoc` is determined by the ROOT cell: two states agreeing on the
path's root cell load identically along the whole path. -/
theorem loadLoc_root_congr {σ₁ σ₂ : ExecState} :
    ∀ {l : Loc},
      Heap.lookup σ₂.heap (Loc.rootLoc l) = Heap.lookup σ₁.heap (Loc.rootLoc l) →
      loadLoc σ₂ l = loadLoc σ₁ l := by
  intro l
  induction l with
  | base a =>
    intro hl
    have hl' : Heap.lookup σ₂.heap (.base a) = Heap.lookup σ₁.heap (.base a) := hl
    simp only [loadLoc]
    rw [hl']
  | field b t f ih =>
    intro hl
    simp only [loadLoc]
    rw [ih hl]
  | index b i ih =>
    intro hl
    simp only [loadLoc]
    rw [ih hl]

/-! #### `capCong`: values congruent up to slice capacity -/

mutual

/-- Values identical except that SLICE values may differ in their `cap`
(base, offset, and len must agree). The capacity choice reaches exactly
one value component — the result slice's `cap` — so this is the
congruence the spill path's store transports along. -/
def GoValue.capCong : GoValue → GoValue → Prop
  | .slice a, .slice b => a.base = b.base ∧ a.offset = b.offset ∧ a.len = b.len
  | .struct t fs, .struct t' gs => t = t' ∧ capCongFields fs.toList gs.toList
  | .array vs, .array ws => capCongList vs.toList ws.toList
  | v, w => v = w

def capCongList : List GoValue → List GoValue → Prop
  | [], [] => True
  | v :: vs, w :: ws => GoValue.capCong v w ∧ capCongList vs ws
  | _, _ => False

def capCongFields : List (String × GoValue) → List (String × GoValue) → Prop
  | [], [] => True
  | (n, v) :: vs, (m, w) :: ws => n = m ∧ GoValue.capCong v w ∧ capCongFields vs ws
  | _, _ => False

end

mutual

theorem GoValue.capCong_refl : ∀ v : GoValue, GoValue.capCong v v
  | .unit => rfl
  | .bool _ => rfl
  | .int _ _ => rfl
  | .string _ => rfl
  | .addr _ => rfl
  | .nil => rfl
  | .interface _ _ => rfl
  | .map _ => rfl
  | .mapData _ => rfl
  | .chan _ => rfl
  | .chanData _ _ _ => rfl
  | .funcVal _ _ => rfl
  | .float _ _ => rfl
  | .slice _ => ⟨rfl, rfl, rfl⟩
  | .struct _ fs => ⟨rfl, capCongFields_refl fs.toList⟩
  | .array vs => capCongList_refl vs.toList

theorem capCongList_refl : ∀ l : List GoValue, capCongList l l
  | [] => trivial
  | v :: vs => ⟨GoValue.capCong_refl v, capCongList_refl vs⟩

theorem capCongFields_refl : ∀ l : List (String × GoValue), capCongFields l l
  | [] => trivial
  | (_, v) :: vs => ⟨rfl, GoValue.capCong_refl v, capCongFields_refl vs⟩

end

theorem capCongList_length :
    ∀ {l₁ l₂ : List GoValue}, capCongList l₁ l₂ → l₁.length = l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ <;> simp_all [capCongList]
  | cons v vs ih =>
    intro l₂ h
    cases l₂ with
    | nil => exact absurd h (by simp [capCongList])
    | cons w ws => simpa using ih h.2

theorem capCongFields_length :
    ∀ {l₁ l₂ : List (String × GoValue)}, capCongFields l₁ l₂ →
      l₁.length = l₂.length := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ <;> simp_all [capCongFields]
  | cons p vs ih =>
    intro l₂ h
    obtain ⟨n, v⟩ := p
    cases l₂ with
    | nil => exact absurd h (by simp [capCongFields])
    | cons q ws =>
      obtain ⟨m, w⟩ := q
      simpa using ih h.2.2

theorem capCongList_set :
    ∀ {l : List GoValue} {i : Nat} {a b : GoValue}, GoValue.capCong a b →
      capCongList (l.set i a) (l.set i b) := by
  intro l
  induction l with
  | nil => intro i a b _; simp [capCongList]
  | cons v vs ih =>
    intro i a b hab
    cases i with
    | zero => exact ⟨hab, capCongList_refl vs⟩
    | succ n => exact ⟨GoValue.capCong_refl v, ih hab⟩

theorem capCongFields_append :
    ∀ {l₁ l₂ r₁ r₂ : List (String × GoValue)}, capCongFields l₁ l₂ →
      capCongFields r₁ r₂ → capCongFields (l₁ ++ r₁) (l₂ ++ r₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ h hr
    cases l₂ <;> simp_all [capCongFields]
  | cons p vs ih =>
    intro l₂ r₁ r₂ h hr
    obtain ⟨n, v⟩ := p
    cases l₂ with
    | nil => exact absurd h (by simp [capCongFields])
    | cons q ws =>
      obtain ⟨m, w⟩ := q
      obtain ⟨rfl, hvw, hrest⟩ := h
      exact ⟨rfl, hvw, ih hrest hr⟩

/-- The constructors `capCong` treats specially (everything else is
related only to itself). -/
def GoValue.isCapStructural : GoValue → Bool
  | .slice _ | .struct _ _ | .array _ => true
  | _ => false

set_option maxHeartbeats 1600000 in
/-- Non-slice/struct/array values are `capCong`-related only to
themselves. -/
theorem GoValue.capCong_eq {v w : GoValue} (h : GoValue.capCong v w)
    (hv : GoValue.isCapStructural v = false) :
    v = w := by
  cases v <;> cases w <;>
    first
    | rfl
    | exact h
    | exact GoValue.noConfusion h
    | exact Bool.noConfusion hv

theorem GoValue.capCong_slice_left {a : SliceValue} {w : GoValue}
    (h : GoValue.capCong (.slice a) w) :
    ∃ b, w = .slice b ∧ a.base = b.base ∧ a.offset = b.offset ∧ a.len = b.len := by
  cases w <;>
    first
    | exact ⟨_, rfl, h.1, h.2.1, h.2.2⟩
    | exact GoValue.noConfusion h

theorem GoValue.capCong_struct_left {t : TypeId} {fs : Array (String × GoValue)}
    {w : GoValue} (h : GoValue.capCong (.struct t fs) w) :
    ∃ gs, w = .struct t gs ∧ capCongFields fs.toList gs.toList := by
  cases w <;>
    first
    | (obtain ⟨rfl, hf⟩ := h; exact ⟨_, rfl, hf⟩)
    | exact GoValue.noConfusion h

theorem GoValue.capCong_array_left {vs : Array GoValue} {w : GoValue}
    (h : GoValue.capCong (.array vs) w) :
    ∃ ws, w = .array ws ∧ capCongList vs.toList ws.toList := by
  cases w <;>
    first
    | exact ⟨_, rfl, h⟩
    | exact GoValue.noConfusion h

/-! #### Outcome-class congruence: `exceptCong` -/

def _root_.GoLean.GoError.isPanic : GoError → Bool
  | .panic _ => true
  | _ => false

/-- Two results agree up to `R` on success and up to PANIC-CLASS on
error (`stepFn` turns a `.panic` into a legal `.panicking` step and
throws on everything else, so panic-vs-not is the only error distinction
the completeness kit needs; error MESSAGES may differ — `repr` of a
slice prints its cap). -/
def exceptCong {α β : Type} (R : α → β → Prop) :
    Except GoError α → Except GoError β → Prop
  | .ok a, .ok b => R a b
  | .error e₁, .error e₂ => e₁.isPanic = e₂.isPanic
  | _, _ => False

theorem exceptCong.bind_congr {α β γ δ : Type} {R : α → β → Prop}
    {S : γ → δ → Prop} {x : Except GoError α} {y : Except GoError β}
    {f : α → Except GoError γ} {g : β → Except GoError δ}
    (hxy : exceptCong R x y)
    (hfg : ∀ a b, R a b → exceptCong S (f a) (g b)) :
    exceptCong S (x >>= f) (y >>= g) := by
  cases x with
  | error e₁ =>
    cases y with
    | error e₂ => exact hxy
    | ok b => exact hxy.elim
  | ok a =>
    cases y with
    | error e₂ => exact hxy.elim
    | ok b => exact hfg a b hxy

theorem exceptCong.map_congr {α β γ δ : Type} {R : α → β → Prop}
    {S : γ → δ → Prop} {x : Except GoError α} {y : Except GoError β}
    {f : α → γ} {g : β → δ}
    (hxy : exceptCong R x y) (hfg : ∀ a b, R a b → S (f a) (g b)) :
    exceptCong S (f <$> x) (g <$> y) := by
  cases x with
  | error e₁ =>
    cases y with
    | error e₂ => exact hxy
    | ok b => exact hxy.elim
  | ok a =>
    cases y with
    | error e₂ => exact hxy.elim
    | ok b => exact hfg a b hxy

theorem exceptCong.self {α : Type} {R : α → α → Prop} {x : Except GoError α}
    (h : ∀ a, R a a) : exceptCong R x x := by
  cases x with
  | ok a => exact h a
  | error e => rfl

theorem exceptCong.ok_left {α β : Type} {R : α → β → Prop}
    {x : Except GoError α} {y : Except GoError β} {a : α}
    (h : exceptCong R x y) (hx : x = .ok a) : ∃ b, y = .ok b ∧ R a b := by
  subst hx
  cases y with
  | ok b => exact ⟨b, rfl, h⟩
  | error e => exact h.elim

theorem exceptCong.panic_left {α β : Type} {R : α → β → Prop}
    {x : Except GoError α} {y : Except GoError β} {m : String}
    (h : exceptCong R x y) (hx : x = .error (.panic m)) :
    ∃ m', y = .error (.panic m') := by
  subst hx
  cases y with
  | ok b => exact h.elim
  | error e =>
    cases e <;>
      first
      | exact ⟨_, rfl⟩
      | exact Bool.noConfusion (h : true = false)

theorem exceptCong.of_ok_bind {α₁ α₂ β₁ β₂ : Type} {S : β₁ → β₂ → Prop}
    {x₁ : α₁} {x₂ : α₂} {f : α₁ → Except GoError β₁}
    {g : α₂ → Except GoError β₂}
    (h : exceptCong S (f x₁) (g x₂)) :
    exceptCong S (Except.ok x₁ >>= f) (Except.ok x₂ >>= g) := h

theorem exceptCong.ite_congr {α β : Type} {R : α → β → Prop} {c : Prop}
    [Decidable c] {x₁ y₁ : Except GoError α} {x₂ y₂ : Except GoError β}
    (ht : c → exceptCong R x₁ x₂) (he : ¬c → exceptCong R y₁ y₂) :
    exceptCong R (if c then x₁ else y₁) (if c then x₂ else y₂) := by
  by_cases h : c
  · simp only [if_pos h]
    exact ht h
  · simp only [if_neg h]
    exact he h

/-! #### Congruence of the value walks along `capCong` -/

theorem normalizeListWith_congr {f g : GoValue → Except GoError GoValue}
    (hfg : ∀ v w, GoValue.capCong v w → exceptCong GoValue.capCong (f v) (g w)) :
    ∀ {l₁ l₂ : List GoValue}, capCongList l₁ l₂ →
      exceptCong (fun a b : Array GoValue => capCongList a.toList b.toList)
        (normalizeListWith f l₁) (normalizeListWith g l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => exact trivial
    | cons w ws => exact h.elim
  | cons v vs ih =>
    intro l₂ h
    cases l₂ with
    | nil => exact h.elim
    | cons w ws =>
      obtain ⟨hvw, hrest⟩ := h
      simp only [normalizeListWith]
      refine exceptCong.bind_congr (hfg v w hvw) fun a b hab => ?_
      refine exceptCong.bind_congr (ih hrest) fun as bs habs => ?_
      show capCongList (#[a] ++ as).toList (#[b] ++ bs).toList
      rw [Array.toList_append, Array.toList_append]
      exact ⟨hab, habs⟩

theorem normalizeFieldsWith_congr {f g : Ty → GoValue → Except GoError GoValue}
    (hfg : ∀ ty v w, GoValue.capCong v w →
      exceptCong GoValue.capCong (f ty v) (g ty w)) :
    ∀ (fds : List FieldDef) {l₁ l₂ : List (String × GoValue)},
      capCongFields l₁ l₂ →
      exceptCong (fun a b : Array (String × GoValue) =>
          capCongFields a.toList b.toList)
        (normalizeFieldsWith f fds l₁) (normalizeFieldsWith g fds l₂) := by
  intro fds
  induction fds with
  | nil =>
    intro l₁ l₂ h
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil => exact trivial
      | cons q ws => exact h.elim
    | cons p vs =>
      cases l₂ with
      | nil =>
        obtain ⟨n, v⟩ := p
        exact h.elim
      | cons q ws => exact trivial
  | cons fd rest ih =>
    intro l₁ l₂ h
    cases l₁ with
    | nil =>
      cases l₂ with
      | nil => exact trivial
      | cons q ws =>
        obtain ⟨m, w⟩ := q
        exact h.elim
    | cons p vs =>
      obtain ⟨n, v⟩ := p
      cases l₂ with
      | nil => exact h.elim
      | cons q ws =>
        obtain ⟨m, w⟩ := q
        obtain ⟨rfl, hvw, hrest⟩ := h
        simp only [normalizeFieldsWith]
        refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
        refine exceptCong.bind_congr
          (R := fun (_ : PUnit) (_ : PUnit) => True)
          (exceptCong.self fun _ => trivial) fun _ _ _ => ?_
        refine exceptCong.bind_congr (hfg _ v w hvw) fun a b hab => ?_
        refine exceptCong.bind_congr (ih hrest) fun as bs habs => ?_
        show capCongFields (#[(fd.name, a)] ++ as).toList
          (#[(fd.name, b)] ++ bs).toList
        rw [Array.toList_append, Array.toList_append]
        exact ⟨rfl, hab, habs⟩

set_option maxHeartbeats 3200000 in
/-- Normalization congruence: along `capCong` values AND states agreeing
on `types`, normalization results agree up to `capCong` (successes) or
panic-class (errors — normalization never panics, but the statement does
not need that fact). -/
theorem normalizeValueForTyFuel_congr {σ₁ σ₂ : ExecState}
    (htypes : σ₂.types = σ₁.types) :
    ∀ (fuel : Nat) (ty : Ty) (v w : GoValue), GoValue.capCong v w →
      exceptCong GoValue.capCong (normalizeValueForTyFuel fuel σ₁ ty v)
        (normalizeValueForTyFuel fuel σ₂ ty w) := by
  intro fuel
  induction fuel with
  | zero =>
    intro ty v w hcc
    simp [normalizeValueForTyFuel, exceptCong, GoError.isPanic]
  | succ f ih =>
    intro ty v w hcc
    cases ty with
    | int kind =>
      cases v <;>
        first
        | (obtain ⟨b, rfl, _, _, _⟩ := GoValue.capCong_slice_left hcc
           exact rfl)
        | (obtain ⟨gs, rfl, _⟩ := GoValue.capCong_struct_left hcc
           exact rfl)
        | (obtain ⟨ws, rfl, _⟩ := GoValue.capCong_array_left hcc
           exact rfl)
        | (obtain rfl := GoValue.capCong_eq hcc rfl
           exact exceptCong.self fun a => GoValue.capCong_refl a)
    | float kind =>
      cases v <;>
        first
        | (obtain ⟨b, rfl, _, _, _⟩ := GoValue.capCong_slice_left hcc
           exact rfl)
        | (obtain ⟨gs, rfl, _⟩ := GoValue.capCong_struct_left hcc
           exact rfl)
        | (obtain ⟨ws, rfl, _⟩ := GoValue.capCong_array_left hcc
           exact rfl)
        | (obtain rfl := GoValue.capCong_eq hcc rfl
           exact exceptCong.self fun a => GoValue.capCong_refl a)
    | array length elem =>
      cases v <;>
        first
        | (obtain ⟨b, rfl, _, _, _⟩ := GoValue.capCong_slice_left hcc
           exact rfl)
        | (obtain ⟨gs, rfl, _⟩ := GoValue.capCong_struct_left hcc
           exact rfl)
        | (obtain rfl := GoValue.capCong_eq hcc rfl
           exact exceptCong.self fun a => GoValue.capCong_refl a)
        | skip
      case array vs =>
        obtain ⟨ws, rfl, hl⟩ := GoValue.capCong_array_left hcc
        have hlen : ws.size = vs.size := (capCongList_length hl).symm
        simp only [normalizeValueForTyFuel, hlen]
        refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
        refine exceptCong.bind_congr
          (R := fun (_ : PUnit) (_ : PUnit) => True)
          (exceptCong.self fun _ => trivial) fun _ _ _ => ?_
        refine exceptCong.map_congr
          (normalizeListWith_congr (fun a b hab => ih elem a b hab) hl)
          fun as bs habs => ?_
        exact habs
    | interface _ =>
      cases v <;>
        first
        | (obtain ⟨b, rfl, hb, ho, hle⟩ := GoValue.capCong_slice_left hcc
           exact hcc)
        | (obtain ⟨gs, rfl, hf⟩ := GoValue.capCong_struct_left hcc
           exact hcc)
        | (obtain ⟨ws, rfl, hl⟩ := GoValue.capCong_array_left hcc
           exact hcc)
        | (obtain rfl := GoValue.capCong_eq hcc rfl
           exact exceptCong.self fun a => GoValue.capCong_refl a)
    | funcType params results =>
      cases v <;>
        first
        | (obtain ⟨b, rfl, _, _, _⟩ := GoValue.capCong_slice_left hcc
           exact rfl)
        | (obtain ⟨gs, rfl, _⟩ := GoValue.capCong_struct_left hcc
           exact rfl)
        | (obtain ⟨ws, rfl, _⟩ := GoValue.capCong_array_left hcc
           exact rfl)
        | (obtain rfl := GoValue.capCong_eq hcc rfl
           exact exceptCong.self fun a => GoValue.capCong_refl a)
    | defined name =>
      simp only [normalizeValueForTyFuel, htypes]
      cases hlook : TypeEnv.lookup σ₁.types name with
      | none => exact rfl
      | some td =>
        cases td with
        | alias target => exact ih target v w hcc
        | defined target => exact ih target v w hcc
        | unsupported _ => exact rfl
        | interfaceDef _ => exact rfl
        | struct fields =>
          cases v <;>
            first
            | (obtain ⟨b, rfl, _, _, _⟩ := GoValue.capCong_slice_left hcc
               exact rfl)
            | (obtain ⟨ws, rfl, _⟩ := GoValue.capCong_array_left hcc
               exact rfl)
            | (obtain rfl := GoValue.capCong_eq hcc rfl
               exact exceptCong.self fun a => GoValue.capCong_refl a)
            | skip
          case struct t fs =>
            obtain ⟨gs, rfl, hf⟩ := GoValue.capCong_struct_left hcc
            have hlen : gs.size = fs.size := (capCongFields_length hf).symm
            simp only [normalizeStructValueWith, emptyStructAssignable,
              Array.isEmpty, hlen]
            refine exceptCong.ite_congr (fun _ => ?_) fun _ => ?_
            · -- Tag mismatch: after rewriting the sizes equal, the
              -- assignability-escape condition is the SAME on both sides;
              -- its ok arm returns the identical retagged empty struct and
              -- its stuck arm the identical error.
              refine exceptCong.ite_congr (fun _ => ?_) fun _ => rfl
              exact exceptCong.self fun a => GoValue.capCong_refl a
            refine exceptCong.bind_congr
              (R := fun (_ : PUnit) (_ : PUnit) => True)
              (exceptCong.self fun _ => trivial) fun _ _ _ => ?_
            refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
            refine exceptCong.bind_congr
              (R := fun (_ : PUnit) (_ : PUnit) => True)
              (exceptCong.self fun _ => trivial) fun _ _ _ => ?_
            refine exceptCong.map_congr
              (normalizeFieldsWith_congr
                (fun ty a b hab => ih ty a b hab) fields.toList hf)
              fun as bs habs => ?_
            exact ⟨rfl, habs⟩
    | unsupported _ => exact rfl
    | bool => exact hcc
    | string => exact hcc
    | slice _ => exact hcc
    | map _ _ => exact hcc
    | chan _ _ =>
      -- Chan-typed normalization is state-independent and canonicalizes
      -- nil; capCong on channel values is equality (the catch-all), and
      -- the cap-divergent shapes (slice/struct/array values at a chan
      -- type) fail closed on BOTH sides with the same error class.
      cases v <;> cases w <;>
        simp_all [GoValue.capCong, normalizeValueForTyFuel, exceptCong,
          GoError.isPanic]
    | pointer _ => exact hcc

theorem normalizeValueForTy_congr {σ₁ σ₂ : ExecState}
    (htypes : σ₂.types = σ₁.types) {ty : Ty} {v w : GoValue}
    (hcc : GoValue.capCong v w) :
    exceptCong GoValue.capCong (normalizeValueForTy σ₁ ty v)
      (normalizeValueForTy σ₂ ty w) := by
  unfold normalizeValueForTy
  exact normalizeValueForTyFuel_congr htypes _ ty v w hcc

/-! Right-sided inversions (the catch-all arms of `coerceStoredValue`
case on the OLD/NEW pair, so the third value's constructor must be read
off from the right). -/

theorem GoValue.capCong_eq_right {v w : GoValue} (h : GoValue.capCong v w)
    (hw : GoValue.isCapStructural w = false) : v = w := by
  cases v <;> cases w <;>
    first
    | rfl
    | exact h
    | exact GoValue.noConfusion h
    | exact Bool.noConfusion hw

theorem GoValue.capCong_struct_right {t : TypeId} {gs : Array (String × GoValue)}
    {v : GoValue} (h : GoValue.capCong v (.struct t gs)) :
    ∃ fs, v = .struct t fs ∧ capCongFields fs.toList gs.toList := by
  cases v <;>
    first
    | (obtain ⟨rfl, hf⟩ := h; exact ⟨_, rfl, hf⟩)
    | exact GoValue.noConfusion h

theorem GoValue.capCong_array_right {ws : Array GoValue} {v : GoValue}
    (h : GoValue.capCong v (.array ws)) :
    ∃ vs, v = .array vs ∧ capCongList vs.toList ws.toList := by
  cases v <;>
    first
    | exact ⟨_, rfl, h⟩
    | exact GoValue.noConfusion h

set_option maxHeartbeats 1600000 in
/-- Stored-value coercion congruence along `capCong` (the OLD cell value
is fixed — both runs read the same cell below `nextAddr`). -/
theorem coerceStoredValue_congr :
    ∀ (old v : GoValue) {w : GoValue}, GoValue.capCong v w →
      exceptCong GoValue.capCong (coerceStoredValue old v)
        (coerceStoredValue old w) := by
  refine fun old v => coerceStoredValue.induct
    (motive_1 := fun old v => ∀ {w}, GoValue.capCong v w →
      exceptCong GoValue.capCong (coerceStoredValue old v)
        (coerceStoredValue old w))
    (motive_2 := fun oldFs vFs => ∀ {wFs}, capCongFields vFs wFs →
      exceptCong (fun a b : Array (String × GoValue) =>
          capCongFields a.toList b.toList)
        (coerceStruct oldFs vFs) (coerceStruct oldFs wFs))
    (motive_3 := fun oldL vL => ∀ {wL}, capCongList vL wL →
      exceptCong (fun a b : Array GoValue => capCongList a.toList b.toList)
        (coerceArray oldL vL) (coerceArray oldL wL))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ old v
  · -- int / int
    intro iv k v' k' w hcc
    obtain rfl := GoValue.capCong_eq hcc rfl
    exact rfl
  · -- float / float, kinds equal (capCong on scalars is equality)
    intro ob kind bits k hk w hcc
    obtain rfl := GoValue.capCong_eq hcc rfl
    exact exceptCong.self fun a => GoValue.capCong_refl a
  · -- float / float, kind mismatch
    intro ob kind bits k hk w hcc
    obtain rfl := GoValue.capCong_eq hcc rfl
    exact exceptCong.self fun a => GoValue.capCong_refl a
  · -- array / array, size mismatch
    intro o n hne w hcc
    obtain ⟨ws, rfl, hl⟩ := GoValue.capCong_array_left hcc
    have hlen : ws.size = n.size := (capCongList_length hl).symm
    simp only [coerceStoredValue, hlen]
    exact exceptCong.ite_congr (fun _ => rfl) fun hno => absurd hne hno
  · -- array / array, sizes agree
    intro o n hne ih w hcc
    obtain ⟨ws, rfl, hl⟩ := GoValue.capCong_array_left hcc
    have hlen : ws.size = n.size := (capCongList_length hl).symm
    simp only [coerceStoredValue, hlen]
    refine exceptCong.ite_congr (fun hyes => absurd hyes hne) fun _ => ?_
    exact exceptCong.map_congr (ih hl) fun as bs habs => habs
  · -- struct / struct, type mismatch
    intro ot ofs nt nfs hne w hcc
    obtain ⟨gs, rfl, hf⟩ := GoValue.capCong_struct_left hcc
    simp only [coerceStoredValue]
    exact exceptCong.ite_congr (fun _ => rfl) fun hno => absurd hne hno
  · -- struct / struct, field-count mismatch
    intro ot ofs nt nfs hne hsz w hcc
    obtain ⟨gs, rfl, hf⟩ := GoValue.capCong_struct_left hcc
    have hlen : gs.size = nfs.size := (capCongFields_length hf).symm
    simp only [coerceStoredValue, hlen]
    refine exceptCong.ite_congr (fun hyes => absurd hyes hne) fun _ => ?_
    exact exceptCong.ite_congr (fun _ => rfl) fun hno => absurd hsz hno
  · -- struct / struct, aligned
    intro ot ofs nt nfs hne hsz ih w hcc
    obtain ⟨gs, rfl, hf⟩ := GoValue.capCong_struct_left hcc
    have hlen : gs.size = nfs.size := (capCongFields_length hf).symm
    simp only [coerceStoredValue, hlen]
    refine exceptCong.ite_congr (fun hyes => absurd hyes hne) fun _ => ?_
    refine exceptCong.ite_congr (fun hyes => absurd hyes hsz) fun _ => ?_
    refine exceptCong.map_congr (ih hf) fun as bs habs => ?_
    exact ⟨rfl, habs⟩
  · -- catch-all: the value passes through
    intro t x hint hfloat harr hstruct w hcc
    have hx : coerceStoredValue t x = pure x := by
      rw [coerceStoredValue.eq_def]
      split
      · exact (hint _ _ _ _ rfl rfl).elim
      · exact (hfloat _ _ _ _ rfl rfl).elim
      · exact (harr _ _ rfl rfl).elim
      · exact (hstruct _ _ _ _ rfl rfl).elim
      · rfl
    have hw : coerceStoredValue t w = pure w := by
      rw [coerceStoredValue.eq_def]
      split
      · obtain rfl := GoValue.capCong_eq_right hcc rfl
        exact (hint _ _ _ _ rfl rfl).elim
      · obtain rfl := GoValue.capCong_eq_right hcc rfl
        exact (hfloat _ _ _ _ rfl rfl).elim
      · obtain ⟨vs, rfl, _⟩ := GoValue.capCong_array_right hcc
        exact (harr _ _ rfl rfl).elim
      · obtain ⟨fs, rfl, _⟩ := GoValue.capCong_struct_right hcc
        exact (hstruct _ _ _ _ rfl rfl).elim
      · rfl
    rw [hx, hw]
    exact hcc
  · -- coerceArray cons
    intro ov orest nv nrest ih1 ih3 wL hl
    cases wL with
    | nil => exact hl.elim
    | cons wv wrest =>
      obtain ⟨hvw, hrest⟩ := hl
      simp only [coerceArray]
      refine exceptCong.bind_congr (ih1 hvw) fun a b hab => ?_
      refine exceptCong.bind_congr (ih3 hrest) fun as bs habs => ?_
      show capCongList (#[a] ++ as).toList (#[b] ++ bs).toList
      rw [Array.toList_append, Array.toList_append]
      exact ⟨hab, habs⟩
  · -- coerceArray catch-all
    intro t x hnc wL hl
    have hx : coerceArray t x = pure #[] := by
      rw [coerceArray.eq_def]
      split
      · exact (hnc _ _ _ _ rfl rfl).elim
      · rfl
    have hw : coerceArray t wL = pure #[] := by
      rw [coerceArray.eq_def]
      split
      · rename_i ov orest nv nrest
        cases x with
        | nil => exact hl.elim
        | cons a as => exact (hnc _ _ _ _ rfl rfl).elim
      · rfl
    rw [hx, hw]
    exact trivial
  · -- coerceStruct cons, name mismatch
    intro on ov orest nn nv nrest hname _ih1 _ih2 wFs hf
    cases wFs with
    | nil => exact hf.elim
    | cons q wrest =>
      obtain ⟨m, wv⟩ := q
      obtain ⟨rfl, hvw, hrest⟩ := hf
      simp only [coerceStruct]
      exact exceptCong.ite_congr (fun _ => rfl) fun hno => absurd hname hno
  · -- coerceStruct cons, names equal
    intro on ov orest nn nv nrest hname ih1 ih2 wFs hf
    cases wFs with
    | nil => exact hf.elim
    | cons q wrest =>
      obtain ⟨m, wv⟩ := q
      obtain ⟨rfl, hvw, hrest⟩ := hf
      simp only [coerceStruct]
      refine exceptCong.ite_congr (fun hyes => absurd hyes hname) fun _ => ?_
      refine exceptCong.bind_congr
        (R := fun (_ : PUnit) (_ : PUnit) => True)
        (exceptCong.self fun _ => trivial) fun _ _ _ => ?_
      refine exceptCong.bind_congr (ih1 hvw) fun a b hab => ?_
      refine exceptCong.bind_congr (ih2 hrest) fun as bs habs => ?_
      show capCongFields (#[(on, a)] ++ as).toList (#[(on, b)] ++ bs).toList
      rw [Array.toList_append, Array.toList_append]
      exact ⟨rfl, hab, habs⟩
  · -- coerceStruct catch-all
    intro t x hnc wFs hf
    have hx : coerceStruct t x = pure #[] := by
      rw [coerceStruct.eq_def]
      split
      · exact (hnc _ _ _ _ _ _ rfl rfl).elim
      · rfl
    have hw : coerceStruct t wFs = pure #[] := by
      rw [coerceStruct.eq_def]
      split
      · rename_i on ov orest nn nv nrest
        cases x with
        | nil => exact hf.elim
        | cons a as =>
          obtain ⟨an, av⟩ := a
          exact (hnc _ _ _ _ _ _ rfl rfl).elim
      · rfl
    rw [hx, hw]
    exact trivial

/-! #### Store congruence: the final spill store cannot depend on the cap -/

/-- `ForInStep` congruence: same step kind, related payloads. -/
def forInStepCong {β₁ β₂ : Type} (R : β₁ → β₂ → Prop) :
    ForInStep β₁ → ForInStep β₂ → Prop
  | .yield y₁, .yield y₂ => R y₁ y₂
  | .done y₁, .done y₂ => R y₁ y₂
  | _, _ => False

/-- Generic `forIn` congruence over `Except` for related loop states. -/
theorem forIn_congr_except {α β₁ β₂ : Type} {R : β₁ → β₂ → Prop}
    {body₁ : α → β₁ → Except GoError (ForInStep β₁)}
    {body₂ : α → β₂ → Except GoError (ForInStep β₂)}
    (hbody : ∀ a b₁ b₂, R b₁ b₂ →
      exceptCong (forInStepCong R) (body₁ a b₁) (body₂ a b₂)) :
    ∀ (l : List α) {b₁ b₂}, R b₁ b₂ →
      exceptCong R (forIn l b₁ body₁) (forIn l b₂ body₂) := by
  intro l
  induction l with
  | nil =>
    intro b₁ b₂ hb
    rw [List.forIn_nil, List.forIn_nil]
    exact hb
  | cons a as ih =>
    intro b₁ b₂ hb
    rw [List.forIn_cons, List.forIn_cons]
    refine exceptCong.bind_congr (hbody a b₁ b₂ hb) fun s₁ s₂ hs => ?_
    cases s₁ with
    | done y₁ =>
      cases s₂ with
      | done y₂ => exact hs
      | yield y₂ => exact hs.elim
    | yield y₁ =>
      cases s₂ with
      | done y₂ => exact hs.elim
      | yield y₂ => exact ih hs

@[inherit_doc forIn_congr_except]
theorem forIn_congr_except_array {α β₁ β₂ : Type} {R : β₁ → β₂ → Prop}
    {body₁ : α → β₁ → Except GoError (ForInStep β₁)}
    {body₂ : α → β₂ → Except GoError (ForInStep β₂)}
    (hbody : ∀ a b₁ b₂, R b₁ b₂ →
      exceptCong (forInStepCong R) (body₁ a b₁) (body₂ a b₂))
    (l : Array α) {b₁ b₂ : _} (hb : R b₁ b₂) :
    exceptCong R (forIn l b₁ body₁) (forIn l b₂ body₂) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact forIn_congr_except hbody l.toList hb

set_option maxHeartbeats 800000 in
/-- `StructFields.set` congruence: the fields are fixed (loaded from the
shared cell), only the inserted value varies up to `capCong`. -/
theorem StructFields.set_congr {fields : Array (String × GoValue)}
    {needle : String} {v w : GoValue} (hcc : GoValue.capCong v w) :
    exceptCong (fun a b : Array (String × GoValue) =>
        capCongFields a.toList b.toList)
      (StructFields.set fields needle v) (StructFields.set fields needle w) := by
  unfold StructFields.set
  refine exceptCong.bind_congr
    (R := fun (r₁ r₂ : MProd Bool (Array (String × GoValue))) =>
      r₁.fst = r₂.fst ∧ capCongFields r₁.snd.toList r₂.snd.toList)
    (forIn_congr_except_array ?_ fields ⟨rfl, trivial⟩) fun r₁ r₂ hr => ?_
  · intro p r₁ r₂ hr
    obtain ⟨hfnd, hout⟩ := hr
    obtain ⟨name, old⟩ := p
    dsimp only
    by_cases hn : (name == needle) = true
    · rw [if_pos hn, if_pos hn]
      have hpush : capCongFields (r₁.snd.push (name, v)).toList
          (r₂.snd.push (name, w)).toList := by
        rw [Array.toList_push, Array.toList_push]
        exact capCongFields_append hout ⟨rfl, hcc, trivial⟩
      exact ⟨rfl, hpush⟩
    · rw [if_neg hn, if_neg hn]
      have hpush : capCongFields (r₁.snd.push (name, old)).toList
          (r₂.snd.push (name, old)).toList := by
        rw [Array.toList_push, Array.toList_push]
        exact capCongFields_append hout ⟨rfl, GoValue.capCong_refl old, trivial⟩
      exact ⟨hfnd, hpush⟩
  · obtain ⟨f₁, o₁⟩ := r₁
    obtain ⟨f₂, o₂⟩ := r₂
    obtain ⟨hfnd, hout⟩ := hr
    dsimp only at hfnd hout ⊢
    subst hfnd
    by_cases hf : f₁ = true
    · rw [if_pos hf, if_pos hf]
      exact hout
    · rw [if_neg hf, if_neg hf]
      exact rfl

theorem arraySet_congr {values : Array GoValue} {i : Int} {v w : GoValue}
    (hcc : GoValue.capCong v w) :
    exceptCong (fun a b : Array GoValue => capCongList a.toList b.toList)
      (arraySet values i v) (arraySet values i w) := by
  unfold arraySet
  refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
    fun n n' hn => ?_
  subst hn
  cases hidx : values[n]? with
  | none =>
    show exceptCong _ (indexOutOfRangePanic i values.size)
      (indexOutOfRangePanic i values.size)
    exact exceptCong.self fun a => capCongList_refl a.toList
  | some old =>
    refine exceptCong.bind_congr (coerceStoredValue_congr old v hcc)
      fun a b hab => ?_
    show capCongList (values.set! n a).toList (values.set! n b).toList
    rw [Array.set!, Array.set!, Array.toList_setIfInBounds,
      Array.toList_setIfInBounds]
    exact capCongList_set hab

set_option maxHeartbeats 1600000 in
/-- **Store class-congruence**: two states agreeing on `types` and on the
target path's root cell, storing `capCong`-related values, succeed
together, panic together, or fail (non-panic) together. This is the fact
that makes the spill store's outcome class independent of the fresh
backing (which lives at `nextAddr`, above every well-formed target) and
of the result slice's capacity. -/
theorem storeLoc_congr {σ₁ σ₂ : ExecState} (htypes : σ₂.types = σ₁.types) :
    ∀ {l : Loc} {v w : GoValue},
      Heap.lookup σ₂.heap (Loc.rootLoc l) = Heap.lookup σ₁.heap (Loc.rootLoc l) →
      GoValue.capCong v w →
      exceptCong (fun _ _ : ExecState => True) (storeLoc σ₁ l v)
        (storeLoc σ₂ l w) := by
  intro l
  induction l with
  | base a =>
    intro v w hl hcc
    have hl' : Heap.lookup σ₂.heap (.base a) = Heap.lookup σ₁.heap (.base a) := hl
    simp only [storeLoc]
    rw [hl']
    cases hlook : Heap.lookup σ₁.heap (.base a) with
    | none => exact trivial
    | some cell =>
      dsimp only
      cases hdt : cell.declaredTy with
      | some ty =>
        dsimp only
        refine exceptCong.bind_congr (normalizeValueForTy_congr htypes hcc)
          fun _ _ _ => ?_
        exact trivial
      | none =>
        dsimp only
        refine exceptCong.bind_congr (coerceStoredValue_congr _ _ hcc)
          fun _ _ _ => ?_
        exact trivial
  | field b tid fname ih =>
    intro v w hl hcc
    simp only [storeLoc]
    rw [loadLoc_root_congr (l := b) hl]
    cases hload : loadLoc σ₁ b with
    | error e => exact rfl
    | ok bv =>
      cases bv <;> try exact rfl
      case struct actual fields =>
        refine exceptCong.of_ok_bind ?_
        refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
        refine exceptCong.bind_congr
          (R := fun (_ : PUnit) (_ : PUnit) => True)
          (exceptCong.self fun _ => trivial) fun _ _ _ => ?_
        refine exceptCong.bind_congr (StructFields.set_congr hcc)
          fun u₁ u₂ hu => ?_
        exact ih hl ⟨rfl, hu⟩
  | index b i ih =>
    intro v w hl hcc
    simp only [storeLoc]
    rw [loadLoc_root_congr (l := b) hl]
    cases hload : loadLoc σ₁ b with
    | error e => exact rfl
    | ok bv =>
      cases bv <;> try exact rfl
      case array values =>
        refine exceptCong.of_ok_bind ?_
        refine exceptCong.bind_congr (arraySet_congr hcc) fun a₁ a₂ ha => ?_
        exact ih hl ha

/-! #### Loop-shape facts for the spill path -/

/-- A loop whose every successful step yields a one-element push grows
the accumulator by exactly the list length. -/
theorem forIn_yield_push_size {α : Type}
    {body : α → Array GoValue → Except GoError (ForInStep (Array GoValue))}
    (hshape : ∀ a r out, body a r = .ok out → ∃ v, out = .yield (r.push v)) :
    ∀ (l : List α) {acc out : Array GoValue},
      forIn l acc body = .ok out → out.size = acc.size + l.length := by
  intro l
  induction l with
  | nil =>
    intro acc out h
    rw [List.forIn_nil] at h
    obtain rfl : acc = out := by simpa [pure_eq_ok] using h
    simp
  | cons a as ih =>
    intro acc out h
    rw [List.forIn_cons, bind_eq_ok] at h
    obtain ⟨s, hs, hrest⟩ := h
    obtain ⟨v, rfl⟩ := hshape a acc s hs
    cases (rfl : ForInStep.yield (acc.push v) = .yield (acc.push v)) with
    | _ =>
      simp only at hrest
      have := ih hrest
      simp only [Array.size_push] at this
      simp [this, List.length_cons]
      omega

/-- A loop whose body always succeeds (with a yield) succeeds. -/
theorem forIn_ok_of_body_ok {α β : Type}
    {body : α → β → Except GoError (ForInStep β)}
    (hok : ∀ a b, ∃ r, body a b = .ok (.yield r)) :
    ∀ (l : List α) (acc : β), ∃ out, forIn l acc body = .ok out := by
  intro l
  induction l with
  | nil => intro acc; exact ⟨acc, by rw [List.forIn_nil]; rfl⟩
  | cons a as ih =>
    intro acc
    obtain ⟨r, hr⟩ := hok a acc
    obtain ⟨out, hout⟩ := ih r
    refine ⟨out, ?_⟩
    rw [List.forIn_cons, hr]
    exact hout

/-- A successful nonempty loop's first step succeeded. -/
theorem forIn_head_ok {α β : Type}
    {body : α → β → Except GoError (ForInStep β)} {a : α} {l : List α}
    {acc : β} {out : β} (h : forIn (a :: l) acc body = .ok out) :
    ∃ r, body a acc = .ok r := by
  rw [List.forIn_cons, bind_eq_ok] at h
  obtain ⟨r, hr, _⟩ := h
  exact ⟨r, hr⟩

/-- Padding defaults are derivable from any normalization success: if
SOME value normalizes at `ty` (at the same fuel), `ty` has a default.
The two walks refuse the same type shapes (`unsupported`/unknown
defined/interface-def), so a normalizable type is defaultable. -/
theorem defaultValueFuel_ok_of_normalize_ok {σ : ExecState} :
    ∀ (fuel : Nat) (ty : Ty) (v r : GoValue),
      normalizeValueForTyFuel fuel σ ty v = .ok r →
      ∃ d, defaultValueFuel fuel σ ty = .ok d := by
  intro fuel
  induction fuel with
  | zero => intro ty v r h; simp [normalizeValueForTyFuel] at h
  | succ f ih =>
    intro ty v r h
    cases ty with
    | int kind =>
      exact ⟨.int 0 kind, by simp [defaultValueFuel, pure, Except.pure]⟩
    | float kind =>
      exact ⟨.float 0 kind, by simp [defaultValueFuel, pure, Except.pure]⟩
    | bool =>
      exact ⟨.bool false, by simp [defaultValueFuel, pure, Except.pure]⟩
    | string =>
      exact ⟨.string GoString.empty, by
        simp [defaultValueFuel, pure, Except.pure]⟩
    | slice elem =>
      exact ⟨.slice { base := none, offset := 0, len := 0, cap := 0 }, by
        simp [defaultValueFuel, pure, Except.pure]⟩
    | chan _ _ =>
      exact ⟨.chan { base := none }, by
        simp [defaultValueFuel, pure, Except.pure]⟩
    | map kt vt =>
      exact ⟨.map { base := none }, by
        simp [defaultValueFuel, pure, Except.pure]⟩
    | pointer _ =>
      exact ⟨.nil, by simp [defaultValueFuel, pure, Except.pure]⟩
    | funcType _ _ =>
      exact ⟨.nil, by simp [defaultValueFuel, pure, Except.pure]⟩
    | interface _ =>
      exact ⟨.nil, by simp [defaultValueFuel, pure, Except.pure]⟩
    | unsupported _ => simp [normalizeValueForTyFuel] at h
    | array length elem =>
      by_cases hlen : length = 0
      · exact ⟨.array #[], by
          simp [defaultValueFuel, hlen, pure, Except.pure]⟩
      · cases v
        case array values =>
          simp only [normalizeValueForTyFuel] at h
          by_cases hsz : (values.size != length) = true
          · rw [if_pos hsz] at h
            simp [Bind.bind, Except.bind, stuck_def] at h
          · rw [if_neg hsz] at h
            have h' : GoValue.array <$> normalizeListWith
                (normalizeValueForTyFuel f σ elem) values.toList = .ok r := h
            have hsz' : values.size = length := by simpa [bne_iff_ne] using hsz
            cases hvl : values.toList with
            | nil =>
              exfalso
              have h0 : values.size = 0 := congrArg List.length hvl
              omega
            | cons v₀ rest =>
              rw [hvl] at h'
              rw [map_eq_ok] at h'
              obtain ⟨arr, harr, _⟩ := h'
              simp only [normalizeListWith, bind_eq_ok] at harr
              obtain ⟨head, hhead, _⟩ := harr
              obtain ⟨d, hd⟩ := ih elem v₀ head hhead
              exact ⟨.array (Array.replicate length d), by
                simp [defaultValueFuel, hlen, hd, Bind.bind, Except.bind, pure,
                  Except.pure]⟩
        all_goals simp [normalizeValueForTyFuel] at h
    | defined name =>
      simp only [normalizeValueForTyFuel] at h
      cases hlook : TypeEnv.lookup σ.types name with
      | none => rw [hlook] at h; simp at h
      | some td =>
        rw [hlook] at h
        cases td with
        | alias target =>
          obtain ⟨d, hd⟩ := ih target v r h
          exact ⟨d, by simp [defaultValueFuel, hlook, hd]⟩
        | defined target =>
          obtain ⟨d, hd⟩ := ih target v r h
          exact ⟨d, by simp [defaultValueFuel, hlook, hd]⟩
        | unsupported _ => simp at h
        | interfaceDef _ => simp at h
        | struct fields =>
          have h' : normalizeStructValueWith (normalizeValueForTyFuel f σ)
              name fields v = .ok r := h
          clear h
          cases v
          case struct actual fieldsValue =>
            simp only [normalizeStructValueWith] at h'
            by_cases hty : (actual != name) = true
            · rw [if_pos hty] at h'
              -- Tag mismatch: only the empty-struct assignability escape
              -- succeeds, and it forces the TARGET field list empty, so the
              -- default value exists trivially.
              by_cases hesc :
                  emptyStructAssignable actual name fields fieldsValue = true
              · have h3 : fields = #[] := by
                  simp [emptyStructAssignable, Array.isEmpty] at hesc
                  exact hesc.1.2
                exact ⟨.struct name #[], by
                  simp [defaultValueFuel, hlook, h3, defaultFieldsWith,
                    pure, Except.pure, Functor.map, Except.map]⟩
              · rw [if_neg hesc] at h'
                simp [Bind.bind, Except.bind, stuck_def] at h'
            · rw [if_neg hty] at h'
              by_cases hsz : (fieldsValue.size != fields.size) = true
              · rw [if_pos hsz] at h'
                simp [Bind.bind, Except.bind, stuck_def] at h'
              · rw [if_neg hsz] at h'
                have h'' : GoValue.struct name <$> normalizeFieldsWith
                    (normalizeValueForTyFuel f σ) fields.toList
                    fieldsValue.toList = .ok r := h'
                rw [map_eq_ok] at h''
                obtain ⟨arr, harr, _⟩ := h''
                suffices haux : ∀ (fds : List FieldDef)
                    (vals : List (String × GoValue))
                    (out : Array (String × GoValue)),
                    normalizeFieldsWith (normalizeValueForTyFuel f σ) fds vals
                      = .ok out →
                    vals.length = fds.length →
                    ∃ ds, defaultFieldsWith (defaultValueFuel f σ) fds = .ok ds by
                  have hlen : fieldsValue.toList.length = fields.toList.length :=
                    (by simpa [bne_iff_ne] using hsz :
                      fieldsValue.size = fields.size)
                  obtain ⟨ds, hds⟩ := haux fields.toList fieldsValue.toList arr
                    harr hlen
                  exact ⟨.struct name ds, by
                    simp [defaultValueFuel, hlook, hds, map_eq_ok]⟩
                intro fds
                induction fds with
                | nil =>
                  intro vals out _ _
                  exact ⟨#[], by simp [defaultFieldsWith, pure, Except.pure]⟩
                | cons fd fdRest ihf =>
                  intro vals out hnorm hlen
                  cases vals with
                  | nil => simp at hlen
                  | cons p valRest =>
                    obtain ⟨pn, pv⟩ := p
                    simp only [normalizeFieldsWith] at hnorm
                    by_cases hname : (pn != fd.name) = true
                    · rw [if_pos hname] at hnorm
                      simp [Bind.bind, Except.bind, stuck_def] at hnorm
                    · rw [if_neg hname] at hnorm
                      have hnorm' : (normalizeValueForTyFuel f σ fd.typ pv >>=
                          fun head =>
                            normalizeFieldsWith (normalizeValueForTyFuel f σ)
                                fdRest valRest >>= fun tail =>
                              pure (#[(fd.name, head)] ++ tail)) = .ok out := hnorm
                      rw [bind_eq_ok] at hnorm'
                      obtain ⟨head, hhead, hrest⟩ := hnorm'
                      rw [bind_eq_ok] at hrest
                      obtain ⟨tail, htail, _⟩ := hrest
                      obtain ⟨d, hd⟩ := ih fd.typ pv head hhead
                      obtain ⟨ds, hds⟩ := ihf valRest tail htail
                        (by simpa using hlen)
                      exact ⟨#[(fd.name, d)] ++ ds, by
                        simp [defaultFieldsWith, hd, hds, Bind.bind, Except.bind,
                          pure, Except.pure]⟩
          all_goals exact absurd h' (by simp [normalizeStructValueWith])

/-- The growth policy never shrinks below the requested length. -/
theorem appendGrowthCap_ge {oldCap newLen : Nat} (h : oldCap < newLen) :
    newLen ≤ appendGrowthCap oldCap newLen := by
  unfold appendGrowthCap
  rw [if_neg (by omega)]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · have hloop : ∀ cap, newLen ≤ appendGrowthCap.loop newLen cap := by
          intro cap
          fun_induction appendGrowthCap.loop with
          | case1 c hge => simpa using hge
          | case2 c hlt ih => exact ih
        exact hloop oldCap

/-- A valid slice's visible length is below its capacity. -/
theorem validateSlice_le {sl : SliceValue} {u : Unit}
    (h : validateSlice sl = .ok u) : sl.len ≤ sl.cap := by
  unfold validateSlice at h
  by_cases hlc : sl.len ≤ sl.cap
  · exact hlc
  · rw [if_pos (by simpa using Nat.lt_of_not_le hlc)] at h
    split at h <;> simp_all [Bind.bind, Except.bind, stuck_def] <;>
      split at h <;> simp_all

/-- The visible-values read returns exactly `len` values. -/
theorem sliceVisibleValues_size {σ : ExecState} {sl : SliceValue}
    {vs : Array GoValue} (h : sliceVisibleValues σ sl = .ok vs) :
    vs.size = sl.len := by
  unfold sliceVisibleValues at h
  rw [bind_eq_ok] at h
  obtain ⟨u, hu, h⟩ := h
  rw [bind_eq_ok] at h
  obtain ⟨out, hout, hpure⟩ := h
  obtain rfl : out = vs := by simpa [pure_eq_ok] using hpure
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hout
  have hsz := forIn_yield_push_size (body := _)
    (fun a r o hbody => by
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, true_and] at hbody
      obtain ⟨l, hl, v, hv, hs⟩ := hbody
      obtain ⟨_, hs⟩ := hs
      exact ⟨v, hs.symm⟩) _ hout
  simpa [List.length_range'] using hsz

/-- `exceptCong.self` strengthened with a success postcondition. -/
theorem exceptCong.self_post {α : Type} {P : α → Prop} {x : Except GoError α}
    (h : ∀ a, x = .ok a → P a) :
    exceptCong (fun a b : α => a = b ∧ P a) x x := by
  cases x with
  | ok a => exact ⟨rfl, h a rfl⟩
  | error e => rfl

/-- Two successes are trivially outcome-congruent. -/
theorem exceptCong.of_oks {α β : Type} {x : Except GoError α}
    {y : Except GoError β} (hx : ∃ a, x = .ok a) (hy : ∃ b, y = .ok b) :
    exceptCong (fun _ _ => True) x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact trivial

theorem bind_isOk {α β : Type} {x : Except GoError α}
    {f : α → Except GoError β} (hx : ∃ a, x = .ok a)
    (hf : ∀ a, ∃ b, f a = .ok b) : ∃ b, x >>= f = .ok b := by
  obtain ⟨a, rfl⟩ := hx
  simpa [Bind.bind, Except.bind] using hf a

set_option maxHeartbeats 1600000 in
/-- The backing build succeeds/fails in the same class at ANY sufficient
capacity: the normalize loop is capacity-independent, the capacity check
passes at both (both ≥ the element count), and the padding default is
derivable from any element's normalize success (`e` is nonempty on the
spill path). -/
theorem buildAppendBackingValue_congr {σ : ExecState} {elem : Ty}
    {o e : Array GoValue} {cap₁ cap₂ : Nat}
    (h₁ : o.size + e.size ≤ cap₁) (h₂ : o.size + e.size ≤ cap₂)
    (hne : e.size ≠ 0) :
    exceptCong (fun _ _ : GoValue => True)
      (buildAppendBackingValue σ elem o e cap₁)
      (buildAppendBackingValue σ elem o e cap₂) := by
  unfold buildAppendBackingValue
  refine exceptCong.bind_congr
    (exceptCong.self_post (P := fun out : Array GoValue =>
      out.size = o.size + e.size ∧ ∃ d, defaultValue σ elem = .ok d) ?_)
    fun values values' hv => ?_
  · intro out hout
    rw [← Array.forIn_toList] at hout
    constructor
    · have hsz := forIn_yield_push_size (body := _)
        (fun a r s hbody => by
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, true_and] at hbody
          obtain ⟨v, hv, hs⟩ := hbody
          obtain ⟨_, hs⟩ := hs
          exact ⟨v, hs.symm⟩) _ hout
      have h' : out.size = 0 + (o ++ e).size := hsz
      rw [Array.size_append] at h'
      omega
    · have hnil : (o ++ e).toList ≠ [] := by
        intro hcontra
        have hz : (o ++ e).size = 0 := congrArg List.length hcontra
        rw [Array.size_append] at hz
        omega
      obtain ⟨v₀, rest, hcons⟩ := List.exists_cons_of_ne_nil hnil
      rw [hcons] at hout
      obtain ⟨r, hr⟩ := forIn_head_ok hout
      simp only [bind_eq_ok, pure_eq_ok] at hr
      obtain ⟨nv, hnv, _⟩ := hr
      unfold normalizeValueForTy at hnv
      obtain ⟨d, hd⟩ := defaultValueFuel_ok_of_normalize_ok _ _ _ _ hnv
      exact ⟨d, by unfold defaultValue; exact hd⟩
  · obtain ⟨rfl, hsz, d, hd⟩ := hv
    rw [if_neg (by omega), if_neg (by omega)]
    refine exceptCong.of_oks ?_ ?_ <;>
      · refine bind_isOk ⟨PUnit.unit, rfl⟩ fun _ => ?_
        refine bind_isOk ?_ fun vs => ⟨.array vs, rfl⟩
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        exact forIn_ok_of_body_ok
          (fun a b => ⟨b.push d, by
            simp [hd, Bind.bind, Except.bind, pure, Except.pure]⟩) _ _

set_option maxHeartbeats 3200000 in
/-- **The appendSlice ∀-choices lemma** (spill obstruction resolved):
under bounded OPERANDS the outcome CLASS of the appendSlice apply step is
the same under every choice stream — operand boundedness alone suffices
(audit correction 2026-08-04: an earlier draft also took `StateWf σ` and
credited it, but the proof never uses it; the fresh backing is allocated
above every OPERAND-reachable location, which is what the store transport
needs). The choice only sizes the fresh backing and the result slice's
`cap` — `storeLoc_congr` transports the final store across both. -/
theorem applyStmtOp_appendSlice_congr {σ : ExecState} {elem : Ty} {nt : Nat}
    {vs : List GoValue} (hb : goValueListSup vs ≤ σ.nextAddr)
    (ch₁ ch₂ : Choices) :
    exceptCong (fun _ _ : ExecState × Choices => True)
      (applyStmtOp σ ch₁ (.appendSlice elem) nt vs)
      (applyStmtOp σ ch₂ (.appendSlice elem) nt vs) := by
  match vs, hb with
  | [], _ => exact rfl
  | [_], _ => exact rfl
  | [_, _], _ => exact rfl
  | _ :: _ :: _ :: _ :: _, _ => exact rfl
  | [tv, sliceV, elemsV], hb =>
    have htv : GoValue.locSup tv ≤ σ.nextAddr := by
      simp only [goValueListSup] at hb
      omega
    simp only [applyStmtOp]
    refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
      fun slice slice' hs => ?_
    subst hs
    refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
      fun elems elems' hs => ?_
    subst hs
    refine exceptCong.bind_congr
      (exceptCong.self_post (P := fun _ : Unit => slice.len ≤ slice.cap)
        (fun u hu => validateSlice_le hu)) fun _ _ hvs => ?_
    obtain ⟨_, hslice_le⟩ := hvs
    refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
      fun _ _ _ => ?_
    refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
      fun elemValues elemValues' hs => ?_
    subst hs
    refine exceptCong.bind_congr
      (exceptCong.self_post (P := fun l : Loc => Loc.locSup l ≤ σ.nextAddr)
        (fun l hl => Nat.le_trans (valueAsLoc_locSup hl) htv))
      fun tloc tloc' htl => ?_
    obtain ⟨heq, htloc⟩ := htl
    subst heq
    refine exceptCong.ite_congr (fun _ => ?_) (fun hspill => ?_)
    · -- in-place: choice-free, streams pass through untouched
      refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
        fun st st' hs => ?_
      subst hs
      refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
        fun σ' σ'' hs => ?_
      subst hs
      exact trivial
    · -- spill
      refine exceptCong.bind_congr
        (exceptCong.self_post (P := fun o : Array GoValue => o.size = slice.len)
          (fun o ho => sliceVisibleValues_size ho))
        fun oldValues oldValues' ho => ?_
      obtain ⟨heq, holdsz⟩ := ho
      subst heq
      rcases hc1 : Choices.consume ch₁ 8 with ⟨e₁, r₁⟩
      rcases hc2 : Choices.consume ch₂ 8 with ⟨e₂, r₂⟩
      have hgrow : slice.len + elemValues.size
          ≤ appendGrowthCap slice.cap (slice.len + elemValues.size) :=
        appendGrowthCap_ge (by omega)
      have hne : elemValues.size ≠ 0 := by omega
      refine exceptCong.bind_congr
        (buildAppendBackingValue_congr (by omega) (by omega) hne)
        fun b₁ b₂ _ => ?_
      have hkey : (Loc.base ⟨σ.nextAddr⟩ : Loc) ≠ Loc.rootLoc tloc := by
        intro hkeq
        have hroot := congrArg Loc.rootBase hkeq
        simp only [Loc.rootBase, Loc.rootLoc] at hroot
        simp only [Loc.locSup] at htloc
        omega
      refine exceptCong.bind_congr
        (storeLoc_congr ?_ (l := tloc) ?_ ?_)
        fun _ _ _ => ?_
      · exact rfl
      · show Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
            (Loc.rootLoc tloc)
          = Heap.lookup (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) _)
            (Loc.rootLoc tloc)
        rw [Heap.lookup_set_ne hkey, Heap.lookup_set_ne hkey]
      · exact ⟨rfl, rfl, rfl⟩
      · exact trivial

/-- The full wide-op table's outcome class is choice-independent given
bounded operands: everything but appendSlice is choices-free by
construction, and appendSlice is the lemma above (which needs only the
operand bound — audit correction 2026-08-04, `StateWf` dropped here
too). -/
theorem applyStmtOp_congr_any_ch {σ : ExecState} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} (hb : goValueListSup vs ≤ σ.nextAddr)
    (ch₁ ch₂ : Choices) :
    exceptCong (fun _ _ : ExecState × Choices => True)
      (applyStmtOp σ ch₁ op nt vs) (applyStmtOp σ ch₂ op nt vs) := by
  cases op
  case appendSlice elem => exact applyStmtOp_appendSlice_congr hb ch₁ ch₂
  all_goals
    refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
      fun a a' ha => ?_
  all_goals exact trivial

/-- The recorded missing lemma, closed: a wide op that succeeds under one
stream succeeds under EVERY stream, given bounded operands (audit
correction 2026-08-04: `StateWf` dropped — the operand bound is the whole
requirement). -/
theorem applyStmtOp_ok_any_ch_wf {σ : ExecState} {ch₀ : Choices}
    {op : StmtOp} {nt : Nat} {vs : List GoValue} {r : ExecState × Choices}
    (hb : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStmtOp σ ch₀ op nt vs = .ok r) :
    ∀ ch : Choices, ∃ r', applyStmtOp σ ch op nt vs = .ok r' := by
  intro ch
  obtain ⟨r', hr', _⟩ :=
    exceptCong.ok_left (applyStmtOp_congr_any_ch hb ch₀ ch) h
  exact ⟨r', hr'⟩

/-- Panic twin: a wide op that panics under one stream panics under every
stream. -/
theorem applyStmtOp_panic_any_ch_wf {σ : ExecState} {ch₀ : Choices}
    {op : StmtOp} {nt : Nat} {vs : List GoValue} {m : String}
    (hb : goValueListSup vs ≤ σ.nextAddr)
    (h : applyStmtOp σ ch₀ op nt vs = .error (.panic m)) :
    ∀ ch : Choices, ∃ m', applyStmtOp σ ch op nt vs = .error (.panic m') :=
  fun ch => exceptCong.panic_left (applyStmtOp_congr_any_ch hb ch₀ ch) h

/-! ### Completeness at EVERY stream, under `MachineWf` -/

/-- Under the wf typing component, a snapshot entry's variables always
bind: the keys/values are self-normalized, so `bindIterVars`' per-pick
normalization succeeds (returning them unchanged) at every pick. -/
theorem bindIterVars_ok_of_normal {env : LocalEnv} {σ : ExecState}
    {kv vv : Option String} {kt vt : Ty} {key value : GoValue}
    (hk : isNormalForTy σ.types kt key = true)
    (hv : isNormalForTy σ.types vt value = true) :
    ∃ env' σ', bindIterVars env σ kv vv kt vt key value = .ok (env', σ') := by
  unfold bindIterVars
  cases kv with
  | none =>
    cases vv with
    | none => exact ⟨env, σ, rfl⟩
    | some nv =>
      refine ⟨env.declare nv (.base ⟨σ.nextAddr⟩),
        { σ with
          heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            { declaredTy := some vt, value := value },
          nextAddr := σ.nextAddr + 1 }, ?_⟩
      simp [isNormalForTy_sound hv, Bind.bind, Except.bind, ExecState.alloc,
        ExecState.freshLoc, pure, Except.pure]
  | some nk =>
    cases vv with
    | none =>
      refine ⟨env.declare nk (.base ⟨σ.nextAddr⟩),
        { σ with
          heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
            { declaredTy := some kt, value := key },
          nextAddr := σ.nextAddr + 1 }, ?_⟩
      simp [isNormalForTy_sound hk, Bind.bind, Except.bind, ExecState.alloc,
        ExecState.freshLoc, pure, Except.pure]
    | some nv =>
      have hv' : normalizeValueForTy
          { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              { declaredTy := some kt, value := key },
            nextAddr := σ.nextAddr + 1 } vt value = .ok value :=
        isNormalForTy_sound hv
      refine ⟨(env.declare nk (.base ⟨σ.nextAddr⟩)).declare nv
          (.base ⟨σ.nextAddr + 1⟩),
        { σ with
          heap := Heap.set
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              { declaredTy := some kt, value := key })
            (.base ⟨σ.nextAddr + 1⟩)
            { declaredTy := some vt, value := value },
          nextAddr := σ.nextAddr + 1 + 1 }, ?_⟩
      simp [isNormalForTy_sound hk, hv', Bind.bind, Except.bind,
        ExecState.alloc, ExecState.freshLoc, pure, Except.pure]

/-- `mapM` over `Except` preserves length on success. -/
theorem mapM_ok_length {α β : Type} {f : α → Except GoError β}
    {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil, pure_eq_ok, Except.ok.injEq] at h
      subst h
      rfl
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
      obtain ⟨y, hy, ys', hys', rfl⟩ := h
      simp [ih hys']

/-- `applySelect`'s apply-SUCCESS is pick-independent (the ∀-choices
kit's discipline; the mapIterNext-snapshot precedent): if the apply
returns `.ok` or a panic under one stream, it does under EVERY stream
— `applySelectCore` is stream-free and pre-commits every ready clause,
so a fail-closed commit error fires identically on every stream, and
per-pick variation is confined to WHICH `.ok` configuration or panic
surfaces. -/
theorem applySelect_ok_or_panic_any_ch {σ : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {ch₀ : Choices}
    (h : (∃ out, applySelect σ clauses default? vs env k ch₀ = .ok out)
      ∨ (∃ msg, applySelect σ clauses default? vs env k ch₀
          = .error (.panic msg))) :
    ∀ ch : Choices,
      (∃ out, applySelect σ clauses default? vs env k ch = .ok out)
      ∨ (∃ msg, applySelect σ clauses default? vs env k ch
          = .error (.panic msg)) := by
  intro ch
  rw [applySelect.eq_def] at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hcore : applySelectCore σ clauses default? vs env k with
  | error e =>
      rw [hcore] at h
      rcases h with ⟨out, h⟩ | ⟨msg, h⟩
      · cases h
      · cases h
        exact .inr ⟨_, rfl⟩
  | ok outc =>
      rw [hcore] at h
      cases outc with
      | done c' s' => exact .inl ⟨_, rfl⟩
      | picks commits =>
          dsimp only at h ⊢
          cases commits with
          | nil =>
              rcases h with ⟨out, h⟩ | ⟨msg, h⟩ <;>
                simp [throw, throwThe, MonadExceptOf.throw] at h
          | cons b rest =>
              rcases hcons : Choices.consume ch (b :: rest).length
                with ⟨idx, ch'⟩
              have hlt : idx < (b :: rest).length := by
                have := consume_fst_lt (ch := ch)
                  (show 0 < (b :: rest).length by simp)
                rw [hcons] at this
                simpa using this
              dsimp only
              rw [List.getElem?_eq_getElem hlt]
              cases hb : (b :: rest)[idx] with
              | inl r => exact .inl ⟨_, rfl⟩
              | inr msg => exact .inr ⟨_, rfl⟩

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- `step_complete_any_wf`, ∃-packaged (the per-case scripts close a
single existential over the whole result). -/
theorem step_complete_any_wf_aux {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} (h : Step c σ c' σ') (hwf : MachineWf σ c) :
    ∀ ch : Choices, ∃ out, stepFn σ c ch = .ok out := by
  obtain ⟨hs, hc, hi⟩ := hwf
  intro ch
  cases h
  case evalStrict e op e₁ rest env k hplan =>
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan])
  case evalStrictNullary e op v env k hplan happly =>
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan])
  case evalStrictNullaryPanic e op msg env k hplan happly =>
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan])
  case stmtOpFirst stmt op nt e rest env k hplan =>
    cases stmt <;>
      first
        | (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;>
            (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done))
  case stmtOpNullary stmt op nt env k ch₀ ch₁ hplan happly =>
    obtain ⟨⟨σ₂, ch₂⟩, hr⟩ := applyStmtOp_ok_any_ch_wf
      (by simp [goValueListSup]) happly ch
    cases stmt <;>
      first
        | (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;>
            (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done))
  case stmtOpApply op nt done v env k ch₀ ch₁ happly =>
    have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
        exprListSup, Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    obtain ⟨⟨σ₂, ch₂⟩, hr⟩ := applyStmtOp_ok_any_ch_wf hop happly ch
    simp only [List.reverse_cons] at hr
    simp [stepFn, hr]
  case stmtOpApplyPanic op nt done v msg env k ch₀ happly =>
    have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
        exprListSup, Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    obtain ⟨m', hm'⟩ := applyStmtOp_panic_any_ch_wf hop happly ch
    simp only [List.reverse_cons] at hm'
    simp [stepFn, hm']
  case stmtOpShiftPlain op nt done v e rest env k hle =>
    simp only [stepFn]
    rw [if_neg (Nat.not_lt.mpr hle)]
    exact ⟨_, rfl⟩
  case mapIterNext keyVar valVar keyTy valTy body remaining idx env env' k
      hidx hbind =>
    have hne : ¬remaining.isEmpty = true := by
      simp only [Array.isEmpty_iff]
      rintro rfl
      simp at hidx
    have hsnap : snapshotEntriesSelfNormalized σ.types keyTy valTy remaining
        = true := by
      simp only [Config.itersNormalized, Cont.itersNormalized,
        Bool.and_eq_true] at hi
      exact hi.1
    simp only [stepFn]
    rw [if_neg hne]
    rcases hcons : Choices.consume ch remaining.size with ⟨idx', rest'⟩
    have hlt : idx' < remaining.size := by
      have hpos : 0 < remaining.size := by
        have hne' := hne
        simp only [Array.isEmpty_iff] at hne'
        exact Array.size_pos_iff.mpr hne'
      have hb := consume_fst_lt (ch := ch) hpos
      rw [hcons] at hb
      exact hb
    split
    · rename_i heq
      rw [Array.getElem?_eq_getElem hlt] at heq
      cases heq
    · rename_i key' value' heq
      rw [Array.getElem?_eq_getElem hlt] at heq
      have hkv : remaining[idx'] = (key', value') := by simpa using heq
      have hmem := snapshotEntriesSelfNormalizedList_mem
        (types := σ.types) (kt := keyTy) (vt := valTy)
        (l := remaining.toList) hsnap
        (e := remaining[idx'])
        (List.mem_of_getElem? (by
          rw [Array.getElem?_toList]
          exact Array.getElem?_eq_getElem hlt))
      rw [hkv] at hmem
      obtain ⟨env₂, σ₂, hbind₂⟩ := bindIterVars_ok_of_normal
        (env := env.pushScope) (kv := keyVar) (vv := valVar)
        hmem.1 hmem.2
      simp [hbind₂, Bind.bind, Except.bind]
  case panicUnwind chain k k' hpass =>
    cases k <;> simp_all [stepFn, panicPassthrough]
  case chanStFirst stmt op e rest env k hplan =>
    cases stmt <;>
      first
        | (simp_all [stepFn, chanPlan]; done)
        | (simp only [stepFn]; rw [hplan]; exact ⟨_, rfl⟩)
  -- The select apply is pick-independent in apply-SUCCESS (slice 4;
  -- `applySelect_ok_or_panic_any_ch`): under any stream it lands `.ok`
  -- or a panic, and `stepFn` maps both to `.ok` configurations.
  case selectApply clauses default? done v env k ch₀ ch₁ happly =>
    rcases applySelect_ok_or_panic_any_ch (.inl ⟨_, happly⟩) ch with
      ⟨⟨c₂, σ₂, ch₂⟩, hap⟩ | ⟨msg, hap⟩ <;>
      simp only [List.reverse_cons] at hap
    · exact ⟨(c₂, σ₂, ch₂), by simp [stepFn, hap]⟩
    · exact ⟨(.panicking [⟨runtimeErrorValue msg, false⟩] k, σ, ch),
        by simp [stepFn, hap]⟩
  case selectApplyPanic clauses default? done v msg env k ch₀ happly =>
    rcases applySelect_ok_or_panic_any_ch (.inr ⟨_, happly⟩) ch with
      ⟨⟨c₂, σ₂, ch₂⟩, hap⟩ | ⟨msg', hap⟩ <;>
      simp only [List.reverse_cons] at hap
    · exact ⟨(c₂, σ₂, ch₂), by simp [stepFn, hap]⟩
    · exact ⟨(.panicking [⟨runtimeErrorValue msg', false⟩] k, σ, ch),
        by simp [stepFn, hap]⟩
  all_goals simp_all [stepFn, enterFrameStep, enterFrameDeferPanicking, Bind.bind, Except.bind, valueAsBool]

/-- **Completeness at every stream** (the recorded kit obligation): a
configuration the relation can step from is one the executable steps
from under EVERY choice stream, provided the machine is well-formed. -/
theorem step_complete_any_wf {c : Config} {σ : ExecState} {c' : Config}
    {σ' : ExecState} (h : Step c σ c' σ') (hwf : MachineWf σ c) :
    ∀ ch : Choices, ∃ (c₂ : Config) (σ₂ : ExecState) (ch₂ : Choices),
      stepFn σ c ch = .ok (c₂, σ₂, ch₂) := by
  intro ch
  obtain ⟨⟨c₂, σ₂, ch₂⟩, hout⟩ := step_complete_any_wf_aux h hwf ch
  exact ⟨c₂, σ₂, ch₂, hout⟩

/-- **Interpreter-side safety from relation-Progress + well-formedness**:
if every relation-reachable configuration from a well-formed start is
the sequential terminal or can step, then every bounded `execStmtLoop`
run — under EVERY choice stream — returns `.ok (.normal …)` or
`.error .fuelOut`; never stuck, never an unrecovered panic, never
unsupported/internal, and never a completion at a non-`.normal`
terminal. Fuel induction carrying reachability (to keep the progress
hypothesis applicable) and `MachineWf` (via `stepFn_preserves_wf`);
`.panicked` is excluded by progress + `step_panicked_elim`, and the
three non-`.stop` unwound terminals are excluded the same way
(`step_returning_stop_elim` and siblings — audit response 2026-08-04:
they used to return `.ok` with the outcome unconstrained, which silently
weakened `ProgressExec`-based statements to accepting top-level
`.returned`/`.broke`/`.continued` completions the relation-Progress
hypothesis actually rules out). -/
theorem execStmtLoop_ok_or_fuelOut {σ₀ : ExecState} {c₀ : Config}
    (hprog : ∀ (c' : Config) (σ' : ExecState), Steps c₀ σ₀ c' σ' →
      c' = .next .stop ∨ ∃ (c'' : Config) (σ'' : ExecState), Step c' σ' c'' σ'')
    (hwf : MachineWf σ₀ c₀) :
    ∀ (fuel : Nat) (ch : Choices),
      (∃ (σf : ExecState) (ch' : Choices),
        execStmtLoop fuel σ₀ c₀ ch = .ok (.normal σf, ch'))
      ∨ execStmtLoop fuel σ₀ c₀ ch = .error .fuelOut := by
  suffices haux : ∀ (fuel : Nat) (c : Config) (σ : ExecState),
      Steps c₀ σ₀ c σ → MachineWf σ c → ∀ ch : Choices,
      (∃ (σf : ExecState) (ch' : Choices),
        execStmtLoop fuel σ c ch = .ok (.normal σf, ch'))
        ∨ execStmtLoop fuel σ c ch = .error .fuelOut by
    intro fuel ch
    exact haux fuel c₀ σ₀ (Steps.refl _ _) hwf ch
  intro fuel
  induction fuel with
  | zero =>
    intro c σ hreach hwfc ch
    unfold execStmtLoop
    split
    · exact .inl ⟨_, _, rfl⟩
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_returning_stop_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_breaking_stop_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_continuing_stop_elim
    · rename_i msg
      rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_panicked_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedSend_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedRecv_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedSelect_elim
    · exact .inr rfl
  | succ n ih =>
    intro c σ hreach hwfc ch
    unfold execStmtLoop
    split
    · exact .inl ⟨_, _, rfl⟩
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_returning_stop_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_breaking_stop_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_continuing_stop_elim
    · rename_i msg
      rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_panicked_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedSend_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedRecv_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedSelect_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · rename_i harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8
        first
          | exact absurd hstop harm1
          | exact absurd hstop.symm harm1
          | exact (harm1 hstop).elim
          | exact (harm1 hstop.symm).elim
      · obtain ⟨c₂, σ₂, ch₂, hstepFn⟩ := step_complete_any_wf hstep hwfc ch
        rw [hstepFn]
        simp only [Bind.bind, Except.bind]
        exact ih c₂ σ₂
          (hreach.trans (Steps.single (stepFn_sound hstepFn)))
          (stepFn_preserves_wf hstepFn hwfc) ch₂

/-! ### The ∀-streams termination checker (sem-adequacy arc slice 5,
2026-08-04)

`Terminates` (Surface) quantifies EVERY choice stream at one uniform fuel
bound, but a kernel evaluation exhibits one stream. The bridge is the
machine's choices discipline (structural since `applyStmtOpCore`): the
stream is consumed at exactly TWO sites — the `mapIterK` pick (bound =
snapshot size, part of the CONFIGURATION) and `applyStmtOp`'s
`appendSlice` spill (bound = `appendSpillWidth oldCap newLen` ≥ 32,
derived from the operand slice — F2's envelope widening, arc-final
audit 2026-08-06; BOTH sites' bounds are configuration-dependent, not
constants) — and every other arm both ignores the
stream and computes a stream-independent successor. So a single
kernel-checked exploration certifies the ∀-streams claim:
`allStreamsOk` walks the run, treating every non-consuming step as the
oblivious step it provably is (`stepFn_oblivious`), BRANCHING over every
possible pick at a nonempty `mapIterK` (the choice is `head % size` —
finitely many), and FAILING CLOSED (false) at any `appendSlice` apply
position (a genuinely stream-sized allocation; no pinned program hits
one, and a future one turns the checker false, never unsound).
`execStmtLoop_ok_of_allStreamsOk` is the soundness theorem: checker true
at fuel `N` ⇒ every stream's run completes within `N`. -/

/-- Is this configuration about to dispatch `applyStmtOp` with an
`appendSlice` op (the one stream-consuming wide op)? Conservative
shape check on the two `applyStmtOp` call sites in `stepFn`: the
`stmtOpK` apply position and the nullary wide-statement arm. -/
def consumesAppendSlice : Config → Bool
  | .retV _ (.stmtOpK op _ _ [] _ _) =>
      match op with
      | .appendSlice _ => true
      | _ => false
  | .exec stmt _ _ =>
      match stmtPlan stmt with
      | some (op, _, []) =>
          match op with
          | .appendSlice _ => true
          | _ => false
      | _ => false
  | _ => false

/-- Is this configuration the select APPLY position (whose
`applySelect` may consume the L2 clause pick — slice 4)? Conservative,
like `consumesAppendSlice`: flags every select apply, including the
stream-oblivious single-ready/default ones — the checker fails closed
there rather than reasoning about readiness. -/
def consumesSelect : Config → Bool
  | .retV _ (.selectOpsK _ _ _ [] _ _) => true
  | _ => false

/-- The kernel-evaluable ∀-streams run explorer (docstring above). At a
nonempty `mapIterK` it checks EVERY pick; elsewhere it probes one step
at the canonical stream `[0]` and relies on `stepFn_oblivious`. `false`
is always safe (fail closed): at fuel 0, at any error, at any
`appendSlice` apply position. -/
def allStreamsOk : Nat → ExecState → Config → Bool
  | 0, _, _ => false
  | fuel + 1, σ, c =>
      match c with
      | .next .stop => true
      | .returning .stop => true
      | .breaking .stop => true
      | .continuing .stop => true
      | .next (.mapIterK keyVar valVar keyTy valTy body remaining env k) =>
          if remaining.isEmpty then
            match stepFn σ (.next (.mapIterK keyVar valVar keyTy valTy body
                remaining env k)) [0] with
            | .ok (c', σ', _) => allStreamsOk fuel σ' c'
            | .error _ => false
          else
            (List.range remaining.size).all fun i =>
              match stepFn σ (.next (.mapIterK keyVar valVar keyTy valTy body
                  remaining env k)) [i] with
              | .ok (c', σ', _) => allStreamsOk fuel σ' c'
              | .error _ => false
      | c =>
          if consumesAppendSlice c || consumesSelect c then false
          else
            match stepFn σ c [0] with
            | .ok (c', σ', _) => allStreamsOk fuel σ' c'
            | .error _ => false

/-- Non-`appendSlice` wide ops dispatch through the choices-free core:
the result is the core's, with the stream threaded through untouched —
on success AND on error. -/
theorem applyStmtOp_eq_core {σ : ExecState} {ch : Choices} {op : StmtOp}
    {nt : Nat} {vs : List GoValue} (hop : ∀ e, op ≠ .appendSlice e) :
    applyStmtOp σ ch op nt vs
      = (fun σ₂ => (σ₂, ch)) <$> applyStmtOpCore σ op nt vs := by
  cases op <;>
    first
    | exact absurd rfl (hop _)
    | (simp only [applyStmtOp, Bind.bind, Except.bind, Functor.map, Except.map,
         pure, Except.pure]
       all_goals (cases applyStmtOpCore σ _ nt vs <;> rfl))

/-- Mapping cannot manufacture or change an error. -/
theorem map_eq_error {ε α β : Type} {g : α → β} {x : Except ε α} {e : ε} :
    g <$> x = .error e ↔ x = .error e := by
  cases x <;> simp [Functor.map, Except.map]

/-- The `stmtOpK` apply-position shape flag transfers to the op. -/
theorem consumesAppendSlice_stmtOpK {v : GoValue} {op : StmtOp} {nt : Nat}
    {done : List GoValue} {env : LocalEnv} {k : Cont}
    (h : consumesAppendSlice (.retV v (.stmtOpK op nt done [] env k)) = false) :
    ∀ e, op ≠ .appendSlice e := by
  intro e he
  subst he
  simp [consumesAppendSlice] at h

/-- The nullary wide-statement shape flag transfers to the planned op. -/
theorem consumesAppendSlice_execPlan {stmt : Stmt} {env : LocalEnv} {k : Cont}
    {op : StmtOp} {nt : Nat}
    (hplan : stmtPlan stmt = some (op, nt, []))
    (h : consumesAppendSlice (.exec stmt env k) = false) :
    ∀ e, op ≠ .appendSlice e := by
  intro e he
  subst he
  simp [consumesAppendSlice, hplan] at h

/-- The `stepFn` equation at a nullary wide-statement configuration: with
the plan pinned (`some (op, nt, [])`), the arm is exactly the immediate
`applyStmtOp` dispatch. Proved by statement cases: non-wide constructors
refute the plan hypothesis; wide constructors reduce and rewrite. -/
theorem stepFn_exec_plan_nullary {σ : ExecState} {stmt : Stmt}
    {env : LocalEnv} {k : Cont} {op : StmtOp} {nt : Nat} {ch : Choices}
    (hplan : stmtPlan stmt = some (op, nt, [])) :
    stepFn σ (.exec stmt env k) ch
      = (do
          let (s', choices') ← applyStmtOp σ ch op nt []
          pure (.next k, s', choices')) := by
  cases stmt <;>
    first
    | (simp [stmtPlan] at hplan; done)
    | (simp only [stepFn]
       rw [hplan])

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- **Stream obliviousness of the non-consuming arms**: away from the
three consuming shapes (a `mapIterK` at the `.next` position — excluded
by `hmi` — an `appendSlice` apply position — excluded by `hnc` — and a
select apply position, whose `applySelect` may draw the L2 clause pick
— excluded by `hns`, slice 4), a step
that succeeds under one stream succeeds under EVERY stream, with the SAME
successor and the stream returned untouched. Sweep over `stepFn`'s case
tree; a newly added stream-consuming arm breaks this proof loudly rather
than silently unsounding the checker. -/
theorem stepFn_oblivious {σ : ExecState} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (hmi : ∀ (kv vv : Option String) (kt vt : Ty) (body : Stmt)
      (rem : Array (GoValue × GoValue)) (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body rem env k))
    (hnc : consumesAppendSlice c = false)
    (hns : consumesSelect c = false)
    (h : stepFn σ c ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepFn σ c ch = .ok (c', σ', ch) := by
  fun_cases stepFn σ c ch₀
  all_goals first
    | exact absurd rfl (hmi _ _ _ _ _ _ _ _)
    | (simp [consumesSelect] at hns; done)
    | (refine ⟨?_, fun ch => ?_⟩ <;> (simp_all [stepFn]; done))
    | skip
  -- 23 arms remain: every one binds through a choices-free helper
  -- (enterFrame / allocDecls / defaultValue / loadLoc / valueAsBool /
  -- mapRangeSnapshotEntries / loadMany+storeMany) or dispatches a
  -- non-appendSlice applyStmtOp (`hnc`). Uniform recipe: reduce the probe
  -- equation, invert its bind, replay the same bind at the arbitrary
  -- stream (the helpers never see the stream).
  case case3 =>
    simp_all only [stepFn, enterFrameDeferPanicking]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameDeferPanicking, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameDeferPanicking, hd]
    · simp at h
  case case13 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨⟨env', s₁⟩, hd, ?_⟩
    simp
  -- Channel receive entry (channels arc slice 1): the plan match needs
  -- its hypothesis rewritten in; both arms are stream-oblivious.
  case case42 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case43 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case44 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_pos hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case45 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_neg hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case14 =>
    simp_all [stepFn, bind_eq_ok]
    obtain ⟨v, hd, h1, h2, h3⟩ := h
    exact ⟨h3.symm, v, hd, h1, h2⟩

  case case37 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h
  case case56 =>
    rename_i op nt hplan
    have hop := consumesAppendSlice_execPlan hplan hnc
    rw [stepFn_exec_plan_nullary hplan, applyStmtOp_eq_core hop] at h
    simp only [bind_eq_ok, map_eq_ok] at h
    obtain ⟨a, ⟨σ₂, hcore, rfl⟩, hrest⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at hrest
    obtain ⟨rfl, rfl, rfl⟩ := hrest
    refine ⟨by simp, fun ch => ?_⟩
    rw [stepFn_exec_plan_nullary hplan, applyStmtOp_eq_core hop, hcore]
    rfl
  case case58 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨v, hd, ?_⟩
    simp
  case case79 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case80 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case81 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨b, hb, ?_⟩
    simp
  case case82 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case83 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case94 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h
  case case96 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h
  case case100 =>
    rename_i hlt
    simp only [stepFn, if_neg hlt, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, if_neg hlt]
    rfl
  case case101 =>
    rename_i s₂ ch₂ happly
    have hop := consumesAppendSlice_stmtOpK hnc
    simp only [stepFn, happly, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [applyStmtOp_eq_core hop, map_eq_ok] at happly
    obtain ⟨σ₂, hcore, heq⟩ := happly
    injection heq with h1 h2
    subst h1
    subst h2
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn]
    rw [applyStmtOp_eq_core hop, hcore]
    rfl
  case case102 =>
    rename_i msg happly
    have hop := consumesAppendSlice_stmtOpK hnc
    simp only [stepFn, happly, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [applyStmtOp_eq_core hop, map_eq_error] at happly
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn]
    rw [applyStmtOp_eq_core hop, happly]
    rfl
  case case108 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h
  case case114 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h
  case case124 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨entries, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨entries, hd, ?_⟩
    simp
  case case153 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, s₂, hstore, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨vs, hload, ?_⟩
    simp [hstore, Bind.bind, Except.bind]
  case case154 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h
  case case191 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, s₂, hstore, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨vs, hload, ?_⟩
    simp [hstore, Bind.bind, Except.bind]
  case case192 =>
    simp_all only [stepFn, enterFrameStep]
    split at h
    · rename_i func frameEnv resultLocs s₂ hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · rename_i msg hd
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp only [stepFn, enterFrameStep, hd]
    · simp at h

/-- The empty-snapshot `mapIterK` step is oblivious: it pops the
continuation at every stream. -/
theorem stepFn_mapIter_empty {σ : ExecState} {kv vv : Option String}
    {kt vt : Ty} {body : Stmt} {remaining : Array (GoValue × GoValue)}
    {env : LocalEnv} {k : Cont} (hemp : remaining.isEmpty = true) :
    ∀ ch : Choices,
      stepFn σ (.next (.mapIterK kv vv kt vt body remaining env k)) ch
        = .ok (.next k, σ, ch) := by
  intro ch
  simp [stepFn, hemp]

set_option linter.unusedSimpArgs false in
/-- The nonempty `mapIterK` step, factored through the consumed choice:
the successor is a function of the PICK INDEX alone (`bindIterVars` never
sees the stream), and the stream moves to the consume's tail. This is the
equation that lets one probe per index cover every stream whose choice
reduces to that index. -/
theorem stepFn_mapIter_pick {σ : ExecState} {kv vv : Option String}
    {kt vt : Ty} {body : Stmt} {remaining : Array (GoValue × GoValue)}
    {env : LocalEnv} {k : Cont} {ch : Choices} {idx : Nat} {tail : Choices}
    (hne : ¬ remaining.isEmpty = true)
    (hcons : Choices.consume ch remaining.size = (idx, tail))
    (hlt : idx < remaining.size) :
    stepFn σ (.next (.mapIterK kv vv kt vt body remaining env k)) ch
      = ((bindIterVars env.pushScope σ kv vv kt vt
            remaining[idx].1 remaining[idx].2).map
          fun p => (.exec body p.1
            (.mapIterK kv vv kt vt body (remaining.eraseIdx idx hlt) env k),
            p.2, tail)) := by
  simp only [stepFn]
  rw [if_neg hne]
  split
  · rename_i heq
    rw [hcons] at heq
    simp only at heq
    rw [Array.getElem?_eq_getElem hlt] at heq
    cases heq
  · rename_i key value heq
    rw [hcons] at heq
    simp only at heq
    rw [Array.getElem?_eq_getElem hlt] at heq
    injection heq with heq
    have h1 : remaining[idx].1 = key := congrArg Prod.fst heq
    have h2 : remaining[idx].2 = value := congrArg Prod.snd heq
    subst h1
    subst h2
    simp only [hcons]
    cases hbind : bindIterVars env.pushScope σ kv vv kt vt
        remaining[idx].1 remaining[idx].2 <;>
      simp [hbind, Except.map, Bind.bind, Except.bind]

/-- The one-layer unfolding of `execStmtLoop`, as an EQUATION (the loop
is fuel-structural, so the definitional unfolding needs the fuel
constructor exposed — `cases fuel` then `rfl`). -/
theorem execStmtLoop_unfold (fuel : Nat) (σ : ExecState) (c : Config)
    (ch : Choices) :
    execStmtLoop fuel σ c ch
      = (match c with
         | .next .stop => .ok (.normal σ, ch)
         | .returning .stop => .ok (.returned σ, ch)
         | .breaking .stop => .ok (.broke σ, ch)
         | .continuing .stop => .ok (.continued σ, ch)
         | .panicked msg => throw (.panic msg)
         | .blockedSend _ _ _ => throw .deadlock
         | .blockedRecv _ _ _ _ _ => throw .deadlock
         | .blockedSelect _ _ _ => throw .deadlock
         | c =>
             match fuel with
             | 0 => throw .fuelOut
             | fuel + 1 => do
                 let (c', σ', choices') ← stepFn σ c ch
                 execStmtLoop fuel σ' c' choices') := by
  rw [execStmtLoop.eq_def]
  rfl

/-- One non-terminal step folds into the loop: `stepFn` throws on every
terminal shape, so a successful step means the loop at `fuel + 1` is
exactly the step followed by the loop at `fuel`. -/
theorem execStmtLoop_step {fuel : Nat} {σ : ExecState} {c : Config}
    {ch : Choices} {c₁ : Config} {σ₁ : ExecState} {ch₁ : Choices}
    (h : stepFn σ c ch = .ok (c₁, σ₁, ch₁)) :
    execStmtLoop (fuel + 1) σ c ch = execStmtLoop fuel σ₁ c₁ ch₁ := by
  rw [execStmtLoop_unfold (fuel + 1) σ c ch]
  split
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp [stepFn, throw, throwThe, MonadExceptOf.throw] at h
  · simp only [Bind.bind]
    rw [h]
    rfl

/-- **Checker soundness**: `allStreamsOk fuel σ c = true` certifies that
EVERY choice stream's run from `(σ, c)` completes `.ok` within `fuel`.
One kernel evaluation of the checker plus `execStmt_mono` therefore
discharges `Surface.Terminates` — ∀-streams quantifier included — at a
concrete seeded program. -/
theorem execStmtLoop_ok_of_allStreamsOk :
    ∀ {fuel : Nat} {σ : ExecState} {c : Config},
      allStreamsOk fuel σ c = true →
      ∀ ch : Choices, ∃ (out : ExecOutcome) (ch' : Choices),
        execStmtLoop fuel σ c ch = .ok (out, ch') := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ c hall ch
    simp [allStreamsOk] at hall
  | succ n ih =>
    intro σ c hall ch
    unfold allStreamsOk at hall
    split at hall
    · exact ⟨.normal σ, ch, rfl⟩
    · exact ⟨.returned σ, ch, rfl⟩
    · exact ⟨.broke σ, ch, rfl⟩
    · exact ⟨.continued σ, ch, rfl⟩
    · -- the mapIterK pick point
      rename_i keyVar valVar keyTy valTy body remaining env k
      split at hall
      · -- empty snapshot: oblivious pop
        rename_i hemp
        split at hall
        · rename_i c₁ σ₁ ch₁ hprobe
          rw [stepFn_mapIter_empty hemp [0]] at hprobe
          obtain ⟨rfl, rfl, rfl⟩ :
              c₁ = .next k ∧ σ₁ = σ ∧ ch₁ = [0] := by
            have h1 := congrArg (fun r => match r with
              | Except.ok (c, _, _) => c | _ => c₁) hprobe
            have h2 := congrArg (fun r => match r with
              | Except.ok (_, s, _) => s | _ => σ₁) hprobe
            have h3 := congrArg (fun r => match r with
              | Except.ok (_, _, l) => l | _ => ch₁) hprobe
            simp only at h1 h2 h3
            exact ⟨h1.symm, h2.symm, h3.symm⟩
          obtain ⟨out, ch', hrun⟩ := ih hall ch
          exact ⟨out, ch',
            by rw [execStmtLoop_step (stepFn_mapIter_empty hemp ch)]; exact hrun⟩
        · exact absurd hall (by simp)
      · -- nonempty: every pick was checked; the stream's choice is one
        rename_i hne
        rw [List.all_eq_true] at hall
        rcases hcons : Choices.consume ch remaining.size with ⟨idx, tail⟩
        have hpos : 0 < remaining.size := by
          rcases Nat.eq_zero_or_pos remaining.size with hz | hp
          · exact absurd (by simpa [Array.isEmpty_iff, Array.size_eq_zero_iff]
              using hz) hne
          · exact hp
        have hlt : idx < remaining.size := by
          have hb := consume_fst_lt (ch := ch) hpos
          rw [hcons] at hb
          exact hb
        have hidx := hall idx (by simpa using List.mem_range.mpr hlt)
        have hconsi : Choices.consume [idx] remaining.size = (idx, []) := by
          simp [Choices.consume,
            Nat.mod_eq_of_lt (show idx < max 1 remaining.size by omega)]
        rw [stepFn_mapIter_pick hne hconsi hlt] at hidx
        cases hbind : bindIterVars env.pushScope σ keyVar valVar keyTy valTy
            remaining[idx].1 remaining[idx].2 with
        | error e =>
          rw [hbind] at hidx
          simp [Except.map] at hidx
        | ok p =>
          rw [hbind] at hidx
          simp only [Except.map] at hidx
          obtain ⟨out, ch', hrun⟩ := ih hidx tail
          refine ⟨out, ch', ?_⟩
          rw [execStmtLoop_step
            (by rw [stepFn_mapIter_pick hne hcons hlt, hbind]; rfl)]
          exact hrun
    · -- the oblivious catch-all
      rename_i hx1 hx2 hx3 hx4 hx5
      cases hnc : (consumesAppendSlice c || consumesSelect c) with
      | true =>
        rw [hnc] at hall
        simp at hall
      | false =>
        rw [hnc] at hall
        simp only [Bool.false_eq_true, if_false] at hall
        obtain ⟨hnc1, hnc2⟩ : consumesAppendSlice c = false
            ∧ consumesSelect c = false := by
          simpa using hnc
        split at hall
        · rename_i c₁ σ₁ ch₁ hprobe
          obtain ⟨-, hobl⟩ := stepFn_oblivious
            (fun kv vv kt vt b r e kk heq => hx5 kv vv kt vt b r e kk heq)
            hnc1 hnc2 hprobe
          obtain ⟨out, ch', hrun⟩ := ih hall ch
          exact ⟨out, ch', by rw [execStmtLoop_step (hobl ch)]; exact hrun⟩
        · exact absurd hall (by simp)
