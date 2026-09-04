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


/-- B2 APPLY arm of `stepFn_sound`: the arm is `do let r ← toResult X;
pure (deliverS …)`. Split the bind, case the classified result, and hand
the rule its two premises (the classification and the delivery — the
latter by `rfl`, `deliver` reducing on the constructor). -/
macro "deliver_arm " h:ident rule:term : tactic =>
  `(tactic| (
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok]
    obtain ⟨r, hres, $h:ident⟩ := $h:ident
    cases r with
    | ok a =>
      simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3⟩ := $h:ident
      subst h1; subst h2; subst h3
      exact $rule hres (by first | rfl | simp only [deliver_ok])
    | panic msg =>
      simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3⟩ := $h:ident
      subst h1; subst h2; subst h3
      exact $rule hres rfl))

/-- B2 frame-ENTRY arm of `stepFn_sound`: the arm is `do let (r, ch') ←
enterFramePick …; pure (deliverS …)`. -/
macro "entry_arm " h:ident rule:term : tactic =>
  `(tactic| (
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok]
    obtain ⟨⟨r, ch₁⟩, hpick, $h:ident⟩ := $h:ident
    (try simp only at $h:ident)
    cases r with
    | ok a =>
      simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3⟩ := $h:ident
      subst h1; subst h2; subst h3
      exact $rule hpick (by first | rfl | simp only [deliver_ok])
    | panic msg =>
      simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3⟩ := $h:ident
      subst h1; subst h2; subst h3
      exact $rule hpick rfl))

/-- B2 stream-free APPLY arm of `stepFn_oblivious`: the apply never sees
the stream, so the classified result — value or panic — is the same at
every stream and `deliverS` returns the arm's own stream untouched. -/
macro "oblivious_apply " h:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok]
    obtain ⟨r, hres, $h:ident⟩ := $h:ident
    (try simp only [List.reverse_cons] at hres)
    cases r with
    | ok a =>
      simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3⟩ := $h:ident
      subst h1; subst h2; subst h3
      exact ⟨rfl, fun ch => by simp [stepFn, hres, Bind.bind, Except.bind]⟩
    | panic msg =>
      simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3⟩ := $h:ident
      subst h1; subst h2; subst h3
      exact ⟨rfl, fun ch => by simp [stepFn, hres, Bind.bind, Except.bind]⟩))

/-- B2 frame-ENTRY arm of `stepFn_oblivious`: outside the wrapper family
(`hnv`) the entry's site consult is inert (`enterFramePick_of_isSome_false`),
so the entry is the stream-free `enterFrame` classification. -/
macro "oblivious_entry " h:ident hnv:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, consumesNilValueMethod, entryCallSite?]
    rw [enterFramePick_of_isSome_false $hnv] at $h:ident
    cases hx : toResult (enterFrame _ _ _) with
    | error e =>
      rw [hx] at $h:ident
      simp [Except.map, Bind.bind, Except.bind] at $h:ident
    | ok r =>
      rw [hx] at $h:ident
      cases r with
      | ok a =>
        simp only [Except.map, Bind.bind, Except.bind, pure_eq_ok, Pure.pure, Except.pure,
          deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at $h:ident
        obtain ⟨h1, h2, h3⟩ := $h:ident
        subst h1; subst h2; subst h3
        (try simp only [List.append_assoc] at hx $hnv:ident)
        exact ⟨rfl, fun ch => by
          simp [stepFn, enterFramePick_of_isSome_false $hnv, hx, Except.map, Bind.bind, Except.bind]⟩
      | panic msg =>
        simp only [Except.map, Bind.bind, Except.bind, pure_eq_ok, Pure.pure, Except.pure,
          deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
        obtain ⟨h1, h2, h3⟩ := $h:ident
        subst h1; subst h2; subst h3
        (try simp only [List.append_assoc] at hx $hnv:ident)
        exact ⟨rfl, fun ch => by
          simp [stepFn, enterFramePick_of_isSome_false $hnv, hx, Except.map, Bind.bind, Except.bind]⟩))

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
  case case77 =>
    -- A4: a global past the heap REFUSES (`.stuck`); no step is produced.
    rename_i hgid
    simp only [stepFn] at h
    rw [if_neg hgid] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case2 =>
    simp_all only [stepFn, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.panicFrameEmpty
  case case3 =>
    entry_arm h Step.panicFrameDefer
  case case150 =>
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
  case case36 =>
    entry_arm h (Step.callImmediate ‹_› ‹_›)
  case case69 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.evalVar ‹_› hd
  case case78 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.evalAnd
  case case79 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.evalOr
  case case80 =>
    simp only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.evalRecover rfl
  case case83 =>
    deliver_arm h (Step.evalStrictNullary ‹_›)
  case case86 =>
    deliver_arm h Step.strictApply
  case case87 =>
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
  case case88 =>
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
  case case89 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    obtain rfl := valueAsBool_ok hb
    exact Step.boolCoerce
  case case90 =>
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
  case case91 =>
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
  case case93 =>
    entry_arm h Step.callArgsDoneEnter
  case case94 =>
    -- The target-check arm sits under `if done.length < nt`: split the
    -- classified `valueAsLoc` result by hand.
    rename_i hlt
    simp only [stepFn, if_pos hlt] at h
    (try simp only [Bind.bind, Except.bind] at h)
    split at h
    · simp at h
    · rename_i r hres
      cases r with
      | ok a =>
        simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact Step.stmtOpShiftTarget ‹_› hres rfl
      | panic msg =>
        simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact Step.stmtOpShiftTarget ‹_› hres rfl
  case case95 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.stmtOpShiftPlain (Nat.le_of_not_lt ‹_›)
  case case96 =>
    deliver_arm h Step.stmtOpApply
  case case97 =>
    entry_arm h Step.callValCalleeEnter
  case case103 =>
    entry_arm h Step.callValArgsEnter
  case case113 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨bs, hd, rfl, rfl, rfl⟩ := h
    exact Step.mapRangeStart (base := bs.1) (start := bs.2) hd
  case case116 =>
    deliver_arm h Step.chanStApply
  case case118 =>
    deliver_arm h Step.selectApply
  case case126 =>
    deliver_arm h Step.rhsStores
  case case133 =>
    deliver_arm h Step.syncStApply
  case case135 =>
    deliver_arm h Step.atomicStApply
  case case143 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case144 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, rfl, rfl, rfl⟩ := h
    exact Step.frameFallTargets hload
  case case146 =>
    entry_arm h Step.frameDeferFall
  case case183 =>
    entry_arm h Step.frameDeferReturn
  case case153 =>
    -- BUG-005 (L): the pick arm is ONE fun_cases equation now (the
    -- candidates load precedes every split), so done/stop/pick are
    -- separated manually here.
    rename_i keyVar valVar keyTy valTy body base produced start env k'
    simp only [stepFn, Choices.consumeAt_mapIter, bind_eq_ok] at h
    obtain ⟨cands, hcands, h⟩ := h
    by_cases hemp : cands.isEmpty
    · rw [if_pos hemp] at h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Step.mapIterDone (by rwa [Array.isEmpty_iff.mp hemp] at hcands)
    · rw [if_neg hemp] at h
      -- The mandatory test is pure (B1 stamps); name its value.
      generalize hmand : mapIterMandatoryRemains cands start = mand at h
      have hsz : 0 < cands.size := by
        simp only [Array.isEmpty_iff] at hemp
        exact Array.size_pos_iff.mpr hemp
      rcases hcons : ch.consume (cands.size + (if mand then 0 else 1))
        with ⟨idx, ch₂⟩
      rw [hcons] at h
      simp only at h
      split at h
      · -- the STOP slot: cands[idx]? = none, only reachable mand-free
        rename_i hidxnone
        rw [Array.getElem?_eq_none_iff] at hidxnone
        cases mand
        · -- mand = false: a legal stop
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact Step.mapIterStop hcands (by omega) hmand
        · -- mand = true: width = size, so idx < size — no stop slot
          exfalso
          have hb := consume_fst_lt
            (ch := ch) (bound := cands.size + if true = true then 0 else 1)
            (by simp; omega)
          rw [hcons] at hb
          simp at hb
          omega
      · -- a PICK: cands[idx]? = some (id, key, value)
        rename_i id key value hidx
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
        obtain ⟨hlt, hw⟩ := Array.getElem?_eq_some_iff.mp hidx
        have hi : id = cands[idx].1 := by rw [hw]
        have hk : key = cands[idx].2.1 := by rw [hw]
        have hv : value = cands[idx].2.2 := by rw [hw]
        subst hi
        subst hk
        subst hv
        exact Step.mapIterNext hlt hcands hd
  case case154 =>
    deliver_arm h Step.storeStep
  case case180 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case181 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, rfl, rfl, rfl⟩ := h
    exact Step.frameReturnTargets hload
  -- (The stmtOpK apply's ok path — formerly `case102`, threaded through
  -- the delete-prune bind — is closed by the generic pass since the B1
  -- stamps: the arm is a plain `return`.)
  -- Channel statements (channels arc slice 1).
  case case41 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.chanStFirst hplan
  case case42 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case43 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_pos hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case44 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_neg hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- Sync statements (spec-parity slice 2): the chan handlers' shapes.
  case case60 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.syncStFirst hplan
  case case61 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case62 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- sync/atomic statements (atomics arc wave 1): the sync handlers'
  -- shapes verbatim (entry / two throws / the apply's panic arm).
  case case63 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.atomicStFirst hplan
  case case64 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case65 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### Completeness -/

/-- B2 APPLY rule of `step_complete`: realize the rule's classified
result under the witness stream `ws` — a value by the same apply, a
panic by the same panic (`deliver` and `deliverS` agree by
construction). -/
macro "complete_apply " hres:ident hdel:ident ws:term : tactic =>
  `(tactic| (
    rcases toResult_cases $hres:ident with ⟨a, ha, hX⟩ | ⟨msg, ha, hX⟩
    · subst ha
      (try simp only [List.reverse_cons] at hX)
      simp only [deliver_ok, Prod.mk.injEq] at $hdel:ident
      obtain ⟨h1, h2⟩ := $hdel:ident
      subst h1; subst h2
      exact ⟨$ws, $ws, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
    · subst ha
      (try simp only [List.reverse_cons] at hX)
      obtain ⟨h1, h2⟩ := deliver_panic_eq $hdel:ident
      subst h1; subst h2
      exact ⟨$ws, $ws, by simp [stepFn, hX, Bind.bind, Except.bind]⟩))

/-- B2 frame-ENTRY rule of `step_complete`: the rule carries its own
stream (`ch`/`ch'`); realize under exactly it. -/
macro "complete_entry " hpick:ident hdel:ident ch:term:max ch':term:max : tactic =>
  `(tactic| (
    (try simp only [List.append_assoc] at $hpick:ident)
    rcases enterFramePick_cases $hpick:ident with ⟨func, frameEnv, resultLocs, s₂, ha, hX, -⟩ | ⟨msg, ha, hX, -⟩
    · subst ha
      simp only [deliver_ok, Prod.mk.injEq] at $hdel:ident
      obtain ⟨h1, h2⟩ := $hdel:ident
      subst h1; subst h2
      exact ⟨$ch, $ch', by simp [stepFn, $hpick:ident, Bind.bind, Except.bind]⟩
    · subst ha
      obtain ⟨h1, h2⟩ := deliver_panic_eq $hdel:ident
      subst h1; subst h2
      exact ⟨$ch, $ch', by simp [stepFn, $hpick:ident, Bind.bind, Except.bind]⟩))

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
    rename_i e op r env k hplan hres hdel
    -- The nullary strict form: `stepFn` dispatches on the expression's
    -- constructor with only its plan known — split it, then the B2
    -- apply/deliver recipe under the empty stream.
    rcases toResult_cases hres with ⟨⟨v, s₂⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      refine ⟨[], [], ?_⟩
      cases e <;>
        first
          | (simp_all [stepFn, strictPlan, Bind.bind, Except.bind]; done)
          | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan, Bind.bind, Except.bind]; done))
          | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
             obtain ⟨rfl, hargs⟩ := hplan
             simp_all [stepFn, strictPlan, Bind.bind, Except.bind])
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      refine ⟨[], [], ?_⟩
      cases e <;>
        first
          | (simp_all [stepFn, strictPlan, Bind.bind, Except.bind]; done)
          | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan, Bind.bind, Except.bind]; done))
          | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
             obtain ⟨rfl, hargs⟩ := hplan
             simp_all [stepFn, strictPlan, Bind.bind, Except.bind])
  case stmtOpFirst =>
    rename_i stmt op nt e rest env k hplan
    refine ⟨[], [], ?_⟩
    cases stmt <;>
      first
        | (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done))
  case stmtOpApply =>
    rename_i op nt done v r env k ch₀ hres hdel
    rcases toResult_cases hres with ⟨⟨s₂, ch₁⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩ <;>
      simp only [List.reverse_cons] at hX
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨ch₀, ch₁, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨ch₀, ch₀, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
  case stmtOpShiftTarget =>
    rename_i op nt done v r e rest env k hlt hres hdel
    rcases toResult_cases hres with ⟨loc, rfl, hX⟩ | ⟨msg, rfl, hX⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨[], [], by simp [stepFn, hlt, hX, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨[], [], by simp [stepFn, hlt, hX, Bind.bind, Except.bind]⟩
  case strictApply =>
    rename_i op done v r env k hres hdel
    complete_apply hres hdel []
  case chanStApply =>
    rename_i op done v r env k hres hdel
    rcases toResult_cases hres with ⟨⟨c₂, s₂⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩ <;>
      simp only [List.reverse_cons] at hX
    · simp only [deliver_ok, id, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨[], [], by simp [stepFn, hX, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨[], [], by simp [stepFn, hX, Bind.bind, Except.bind]⟩
  case atomicStApply =>
    rename_i op done v r env k hres hdel
    rcases toResult_cases hres with ⟨⟨c₂, s₂⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩ <;>
      simp only [List.reverse_cons] at hX
    · simp only [deliver_ok, id, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨[], [], by simp [stepFn, hX, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨[], [], by simp [stepFn, hX, Bind.bind, Except.bind]⟩
  case rhsStores =>
    rename_i rop refs done v r body env k hres hdel
    complete_apply hres hdel []
  case storeStep =>
    rename_i ref rs val vals r body env k hres hdel
    complete_apply hres hdel []
  -- The frame-entry rules carry their own stream (BUG-087's text pick
  -- is drawn from it on the panic path): realize under exactly it.
  case callImmediate =>
    rename_i targets fid args plans r env k ch₀ ch₁ hplan hargs hpick hdel
    rcases enterFramePick_cases hpick with ⟨func, frameEnv, resultLocs, s₂, rfl, hX, -⟩ | ⟨msg, rfl, hX, -⟩
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨ch₀, ch₁, by simp [stepFn, hplan, hargs, hpick, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨ch₀, ch₁, by simp [stepFn, hplan, hargs, hpick, Bind.bind, Except.bind]⟩
  case callArgsDoneEnter =>
    rename_i v fid plans vals r env k ch₀ ch₁ hpick hdel
    complete_entry hpick hdel ch₀ ch₁
  case callValCalleeEnter =>
    rename_i fid captured plans r env k ch₀ ch₁ hpick hdel
    complete_entry hpick hdel ch₀ ch₁
  case callValArgsEnter =>
    rename_i v fid captured plans vals r env k ch₀ ch₁ hpick hdel
    complete_entry hpick hdel ch₀ ch₁
  case frameDeferFall =>
    rename_i targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel
    complete_entry hpick hdel ch₀ ch₁
  case frameDeferReturn =>
    rename_i targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel
    complete_entry hpick hdel ch₀ ch₁
  case panicFrameDefer =>
    rename_i chain targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel
    complete_entry hpick hdel ch₀ ch₁
  case stmtOpShiftPlain =>
    rename_i op nt done v e rest env k hle
    refine ⟨[], [], ?_⟩
    simp only [stepFn]
    rw [if_neg (Nat.not_lt.mpr hle)]
    rfl
  -- The nondeterministic pick: the witness stream encodes the rule's index.
  case mapIterNext =>
    rename_i keyVar valVar keyTy valTy body base produced start cands idx
      env env' k hidx hcands hbind
    refine ⟨[idx], [], ?_⟩
    -- The mandatory test is pure (B1 stamps); name its value.
    obtain ⟨mand, hmand⟩ : ∃ m, mapIterMandatoryRemains cands start = m := ⟨_, rfl⟩
    have hwidth : idx < max 1 (cands.size + (if mand then 0 else 1)) := by
      cases mand <;> simp <;> omega
    have hcons : Choices.consume [idx]
        (cands.size + (if mand then 0 else 1)) = (idx, []) := by
      simp [Choices.consume, Nat.mod_eq_of_lt hwidth]
    simp only [stepFn, Choices.consumeAt_mapIter, hcands, hmand, bind_eq_ok]
    refine ⟨cands, rfl, ?_⟩
    rw [if_neg (by
      simp only [Array.isEmpty_iff]
      rintro rfl
      simp at hidx)]
    rw [hmand, hcons]
    dsimp only
    split
    · rename_i heq
      simp [Array.getElem?_eq_getElem hidx] at heq
    · rename_i id' key' value' heq
      simp only [Array.getElem?_eq_getElem hidx, Option.some.injEq] at heq
      have hi : cands[idx].fst = id' := by rw [heq]
      have hk : cands[idx].snd.fst = key' := by rw [heq]
      have hv : cands[idx].snd.snd = value' := by rw [heq]
      rw [hk, hv] at hbind
      rw [hi]
      simp [hbind, Bind.bind, Except.bind]
  case mapIterStop =>
    rename_i keyVar valVar keyTy valTy body base produced start cands env k
      hne hmand hcands
    refine ⟨[cands.size], [], ?_⟩
    have hcons : Choices.consume [cands.size] (cands.size + 1)
        = (cands.size, []) := by
      simp [Choices.consume, Nat.mod_eq_of_lt
        (show cands.size < max 1 (cands.size + 1) by omega)]
    simp only [stepFn, Choices.consumeAt_mapIter, hcands, hmand, bind_eq_ok]
    refine ⟨cands, rfl, ?_⟩
    rw [if_neg (by simp only [Array.isEmpty_iff, ← Array.size_eq_zero_iff]; exact hne)]
    have hred : (cands.size + if false = true then 0 else 1)
        = cands.size + 1 := by simp
    rw [hmand, hred, hcons]
    dsimp only
    split
    · rename_i heq
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
      try exact ⟨rfl, rfl, rfl⟩
    · rename_i id' key' value' heq
      exfalso
      have := (Array.getElem?_eq_some_iff.mp heq).1
      omega
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
    rename_i clauses default? done v r env k ch₀ hres hdel
    rcases toResult_cases hres with ⟨⟨c₂, s₂, ch₁, cl⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩ <;>
      simp only [List.reverse_cons] at hX
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨ch₀, ch₁, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨ch₀, ch₀, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
  -- The sync apply rules carry their own stream (the TRY heads' pick,
  -- Q-TRYLOCK): realize under exactly it — the select recipe.
  case syncStApply =>
    rename_i op done v r env k ch₀ hres hdel
    rcases toResult_cases hres with ⟨⟨c₂, s₂, ch₁⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩ <;>
      simp only [List.reverse_cons] at hX
    · simp only [deliver_ok, Prod.mk.injEq] at hdel
      obtain ⟨rfl, rfl⟩ := hdel
      exact ⟨ch₀, ch₁, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
    · obtain ⟨rfl, rfl⟩ := deliver_panic_eq hdel
      exact ⟨ch₀, ch₀, by simp [stepFn, hX, Bind.bind, Except.bind]⟩
  -- Sync statements (spec-parity slice 2): entry holds the statement
  -- abstract behind its plan — the chanStFirst recipe.
  case syncStFirst =>
    rename_i stmt op e rest env k hplan
    refine ⟨[], [], ?_⟩
    cases stmt <;>
      first
        | (simp_all [stepFn, syncPlan]; done)
        | (simp only [stepFn]; rw [hplan]; rfl)
  case atomicStFirst =>
    rename_i stmt op e rest env k hplan
    refine ⟨[], [], ?_⟩
    cases stmt <;>
      first
        | (simp_all [stepFn, atomicPlan]; done)
        | (simp only [stepFn]; rw [hplan]; rfl)
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
  | case4 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case5 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case6 => simp [throw, throwThe, MonadExceptOf.throw] at h
  -- blockedSync (spec-parity slice 2): one more deadlock-classified arm.
  | case7 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case8 =>
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
  -- blockedSync (spec-parity slice 2): one more deadlock-classified arm.
  | case10 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case11 =>
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

/-- The sync-parked shape is relation-silent (spec-parity slice 2): the
pool wakes it; the sequential driver classifies it as the deadlocked
run. -/
theorem step_blockedSync_elim {op : SyncOp} {loc : Loc} {env : LocalEnv}
    {k : Cont} {σ : ExecState} {c' : Config} {σ' : ExecState} :
    ¬ Step (.blockedSync op loc env k) σ c' σ' := by
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

/-- Allocation does not touch any other root cell (dense heap: `push` is
invisible below the old size). -/
theorem Heap.lookup_push_ne {h : Heap} {l : Loc} {c : HeapCell}
    (hne : (Loc.base ⟨h.size⟩ : Loc) ≠ l) :
    Heap.lookup (h.push c) l = Heap.lookup h l := by
  cases l with
  | base a =>
    obtain ⟨j⟩ := a
    have hj : j ≠ h.size := fun hj => hne (by subst hj; rfl)
    simp [Heap.lookup, Array.getElem?_push, hj]
  | field _ _ _ => rfl
  | index _ _ => rfl

/-- An in-range overwrite does not touch any other root cell. -/
theorem Heap.lookup_set_ne {h : Heap} {i : Nat} {l : Loc} {c : HeapCell}
    {hi : i < h.size} (hne : (Loc.base ⟨i⟩ : Loc) ≠ l) :
    Heap.lookup (h.set i c hi) l = Heap.lookup h l := by
  cases l with
  | base a =>
    obtain ⟨j⟩ := a
    have hj : i ≠ j := fun hj => hne (by subst hj; rfl)
    simp [Heap.lookup, Array.getElem?_set_ne hi hj]
  | field _ _ _ => rfl
  | index _ _ => rfl

/-- A root-cell update touches no other root cell (A3: the one write path). -/
theorem ExecState.updateCell_lookup_ne {σ σ' : ExecState} {a : Addr}
    {f : HeapCell → Except Stop HeapCell} {l : Loc}
    (h : σ.updateCell a f = .ok σ') (hne : (Loc.base a : Loc) ≠ l) :
    Heap.lookup σ'.heap l = Heap.lookup σ.heap l := by
  obtain ⟨i⟩ := a
  unfold ExecState.updateCell at h
  split at h
  · rename_i hi
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨cell', _, hσ⟩ := h
    subst hσ
    exact Heap.lookup_set_ne (hi := hi) hne
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The tag-compatibility check reads only the types map (triage L7). -/
theorem structTagCompatible_congr {σ₁ σ₂ : ExecState}
    (htypes : σ₂.types = σ₁.types) :
    structTagCompatible σ₂ = structTagCompatible σ₁ := by
  funext a b
  simp [structTagCompatible, htypes]

/-- `loadLoc` is determined by the ROOT cell and the types map (the
latter entering only through the field arm's tag-compatibility check,
triage L7): two states agreeing on both load identically along the
whole path. -/
theorem loadLoc_root_congr {σ₁ σ₂ : ExecState}
    (htypes : σ₂.types = σ₁.types) :
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
    rw [ih hl, structTagCompatible_congr htypes]
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
  | .chan _ => rfl
  | .funcVal _ _ => rfl
  | .float _ _ => rfl
  | .syncData _ => rfl
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

def _root_.GoLean.Stop.isPanic : Stop → Bool
  | .panic _ => true
  | _ => false

/-- Two results agree up to `R` on success and up to PANIC-CLASS on
error (`stepFn` turns a `.panic` into a legal `.panicking` step and
throws on everything else, so panic-vs-not is the only error distinction
the completeness kit needs; error MESSAGES may differ — `repr` of a
slice prints its cap). -/
def exceptCong {α β : Type} (R : α → β → Prop) :
    Except Stop α → Except Stop β → Prop
  | .ok a, .ok b => R a b
  | .error e₁, .error e₂ => e₁.isPanic = e₂.isPanic
  | _, _ => False

theorem exceptCong.bind_congr {α β γ δ : Type} {R : α → β → Prop}
    {S : γ → δ → Prop} {x : Except Stop α} {y : Except Stop β}
    {f : α → Except Stop γ} {g : β → Except Stop δ}
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
    {S : γ → δ → Prop} {x : Except Stop α} {y : Except Stop β}
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

theorem exceptCong.self {α : Type} {R : α → α → Prop} {x : Except Stop α}
    (h : ∀ a, R a a) : exceptCong R x x := by
  cases x with
  | ok a => exact h a
  | error e => rfl

theorem exceptCong.ok_left {α β : Type} {R : α → β → Prop}
    {x : Except Stop α} {y : Except Stop β} {a : α}
    (h : exceptCong R x y) (hx : x = .ok a) : ∃ b, y = .ok b ∧ R a b := by
  subst hx
  cases y with
  | ok b => exact ⟨b, rfl, h⟩
  | error e => exact h.elim

theorem exceptCong.panic_left {α β : Type} {R : α → β → Prop}
    {x : Except Stop α} {y : Except Stop β} {m : String}
    (h : exceptCong R x y) (hx : x = .error (.panic m)) :
    ∃ m', y = .error (.panic m') := by
  subst hx
  cases y with
  | ok b => exact h.elim
  | error e =>
    -- A1 stop grammar: only the terminal class can hold a panic.
    rcases e with r | t | _
    · cases r <;> exact Bool.noConfusion (h : true = false)
    · cases t <;>
        first
        | exact ⟨_, rfl⟩
        | exact Bool.noConfusion (h : true = false)
    · exact Bool.noConfusion (h : true = false)

theorem exceptCong.of_ok_bind {α₁ α₂ β₁ β₂ : Type} {S : β₁ → β₂ → Prop}
    {x₁ : α₁} {x₂ : α₂} {f : α₁ → Except Stop β₁}
    {g : α₂ → Except Stop β₂}
    (h : exceptCong S (f x₁) (g x₂)) :
    exceptCong S (Except.ok x₁ >>= f) (Except.ok x₂ >>= g) := h

theorem exceptCong.ite_congr {α β : Type} {R : α → β → Prop} {c : Prop}
    [Decidable c] {x₁ y₁ : Except Stop α} {x₂ y₂ : Except Stop β}
    (ht : c → exceptCong R x₁ x₂) (he : ¬c → exceptCong R y₁ y₂) :
    exceptCong R (if c then x₁ else y₁) (if c then x₂ else y₂) := by
  by_cases h : c
  · simp only [if_pos h]
    exact ht h
  · simp only [if_neg h]
    exact he h

/-! #### Congruence of the value walks along `capCong` -/

theorem normalizeListWith_congr {f g : GoValue → Except Stop GoValue}
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

theorem normalizeFieldsWith_congr {f g : Ty → GoValue → Except Stop GoValue}
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
    simp [normalizeValueForTyFuel, exceptCong, Stop.isPanic]
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
    | sync kind =>
      -- Sync cells (spec-parity slice 2): the scalar recipe — capCong
      -- on a non-slice/struct/array value is equality.
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
    | funcType params results _ =>
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
        | opaqueDecl _ => exact rfl
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
            refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
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
          Stop.isPanic]
    | pointer _ => exact hcc

theorem normalizeValueForTy_congr {σ₁ σ₂ : ExecState}
    (htypes : σ₂.types = σ₁.types) {ty : Ty} {v w : GoValue}
    (hcc : GoValue.capCong v w) :
    exceptCong GoValue.capCong (normalizeValueForTy σ₁ ty v)
      (normalizeValueForTy σ₂ ty w) := by
  unfold normalizeValueForTy
  exact normalizeValueForTyFuel_congr htypes _ ty v w hcc

/-! #### Store congruence: the final spill store cannot depend on the cap -/

/-- `ForInStep` congruence: same step kind, related payloads. -/
def forInStepCong {β₁ β₂ : Type} (R : β₁ → β₂ → Prop) :
    ForInStep β₁ → ForInStep β₂ → Prop
  | .yield y₁, .yield y₂ => R y₁ y₂
  | .done y₁, .done y₂ => R y₁ y₂
  | _, _ => False

/-- Generic `forIn` congruence over `Except` for related loop states. -/
theorem forIn_congr_except {α β₁ β₂ : Type} {R : β₁ → β₂ → Prop}
    {body₁ : α → β₁ → Except Stop (ForInStep β₁)}
    {body₂ : α → β₂ → Except Stop (ForInStep β₂)}
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
    {body₁ : α → β₁ → Except Stop (ForInStep β₁)}
    {body₂ : α → β₂ → Except Stop (ForInStep β₂)}
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
  -- 4.32.2: the loop state is now `(array, flag) : _ × Bool` (was
  -- `MProd Bool (Array _)`); the R conjunct order is preserved (flag eq
  -- first) — only the projections move.
  refine exceptCong.bind_congr
    (R := fun (r₁ r₂ : Array (String × GoValue) × Bool) =>
      r₁.2 = r₂.2 ∧ capCongFields r₁.1.toList r₂.1.toList)
    (forIn_congr_except_array ?_ fields ⟨rfl, trivial⟩) fun r₁ r₂ hr => ?_
  · intro p r₁ r₂ hr
    obtain ⟨hfnd, hout⟩ := hr
    obtain ⟨name, old⟩ := p
    dsimp only
    by_cases hn : (name == needle) = true
    · rw [if_pos hn, if_pos hn]
      have hpush : capCongFields (r₁.1.push (name, v)).toList
          (r₂.1.push (name, w)).toList := by
        rw [Array.toList_push, Array.toList_push]
        exact capCongFields_append hout ⟨rfl, hcc, trivial⟩
      exact ⟨rfl, hpush⟩
    · rw [if_neg hn, if_neg hn]
      have hpush : capCongFields (r₁.1.push (name, old)).toList
          (r₂.1.push (name, old)).toList := by
        rw [Array.toList_push, Array.toList_push]
        exact capCongFields_append hout ⟨rfl, GoValue.capCong_refl old, trivial⟩
      exact ⟨hfnd, hpush⟩
  · obtain ⟨o₁, f₁⟩ := r₁
    obtain ⟨o₂, f₂⟩ := r₂
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
    show capCongList (values.set! n v).toList (values.set! n w).toList
    rw [Array.set!, Array.set!, Array.toList_setIfInBounds,
      Array.toList_setIfInBounds]
    exact capCongList_set hcc

/-- Root-cell updates agree in outcome CLASS when the two heaps agree at the
root and the two update functions agree in class on every cell (A3; the
congruence behind `storeLoc_congr`). -/
theorem ExecState.updateCell_congr {σ₁ σ₂ : ExecState} {a : Addr}
    {f₁ f₂ : HeapCell → Except Stop HeapCell}
    (hl : Heap.lookup σ₂.heap (.base a) = Heap.lookup σ₁.heap (.base a))
    (hf : ∀ c, exceptCong (fun _ _ : HeapCell => True) (f₁ c) (f₂ c)) :
    exceptCong (fun _ _ : ExecState => True)
      (σ₁.updateCell a f₁) (σ₂.updateCell a f₂) := by
  obtain ⟨i⟩ := a
  simp only [Heap.lookup] at hl
  unfold ExecState.updateCell
  by_cases h1 : i < σ₁.heap.size
  · have h2 : i < σ₂.heap.size := by
      have := hl
      rw [Array.getElem?_eq_getElem h1] at this
      exact (Array.getElem?_eq_some_iff.mp this).1
    have hc : σ₂.heap[i] = σ₁.heap[i] := by
      have := hl
      rw [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] at this
      exact Option.some.inj this
    simp only [dif_pos h1, dif_pos h2]
    rw [hc]
    exact exceptCong.bind_congr (hf _) fun _ _ _ => trivial
  · have h2 : ¬ i < σ₂.heap.size := by
      intro h2
      have := hl
      rw [Array.getElem?_eq_getElem h2] at this
      exact h1 (Array.getElem?_eq_some_iff.mp this.symm).1
    simp only [dif_neg h1, dif_neg h2]
    exact rfl

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
    -- ONE root write (A3): the class congruence of `updateCell`, then the
    -- per-cell update functions agree in class arm by arm.
    refine ExecState.updateCell_congr hl' fun c => ?_
    cases c with
    | value ty v₀ =>
      refine exceptCong.bind_congr (normalizeValueForTy_congr htypes hcc)
        fun _ _ _ => ?_
      exact trivial
    | mapPayload _ _ => exact rfl
    | chanPayload _ _ _ => exact rfl
  | field b tid fname ih =>
    intro v w hl hcc
    simp only [storeLoc]
    rw [loadLoc_root_congr htypes (l := b) hl,
      structTagCompatible_congr htypes]
    cases hload : loadLoc σ₁ b with
    | error e => exact rfl
    | ok bv =>
      cases bv <;> try exact rfl
      case struct actual fields =>
        refine exceptCong.of_ok_bind ?_
        refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
        refine exceptCong.bind_congr (StructFields.set_congr hcc)
          fun u₁ u₂ hu => ?_
        exact ih hl ⟨rfl, hu⟩
  | index b i ih =>
    intro v w hl hcc
    simp only [storeLoc]
    rw [loadLoc_root_congr htypes (l := b) hl]
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
    {body : α → Array GoValue → Except Stop (ForInStep (Array GoValue))}
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
    {body : α → β → Except Stop (ForInStep β)}
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
    {body : α → β → Except Stop (ForInStep β)} {a : α} {l : List α}
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
    | sync kind =>
      exact ⟨.syncData kind.zero, by
        simp [defaultValueFuel, pure, Except.pure]⟩
    | map kt vt =>
      exact ⟨.map { base := none }, by
        simp [defaultValueFuel, pure, Except.pure]⟩
    | pointer _ =>
      exact ⟨.nil, by simp [defaultValueFuel, pure, Except.pure]⟩
    | funcType _ _ _ =>
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
        | opaqueDecl _ => simp at h
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
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hbody
      obtain ⟨l, hl, v, hv, hs⟩ := hbody
      exact ⟨v, hs.symm⟩) _ hout
  simpa [List.length_range'] using hsz

/-- `exceptCong.self` strengthened with a success postcondition. -/
theorem exceptCong.self_post {α : Type} {P : α → Prop} {x : Except Stop α}
    (h : ∀ a, x = .ok a → P a) :
    exceptCong (fun a b : α => a = b ∧ P a) x x := by
  cases x with
  | ok a => exact ⟨rfl, h a rfl⟩
  | error e => rfl

/-- Two successes are trivially outcome-congruent. -/
theorem exceptCong.of_oks {α β : Type} {x : Except Stop α}
    {y : Except Stop β} (hx : ∃ a, x = .ok a) (hy : ∃ b, y = .ok b) :
    exceptCong (fun _ _ => True) x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact trivial

theorem bind_isOk {α β : Type} {x : Except Stop α}
    {f : α → Except Stop β} (hx : ∃ a, x = .ok a)
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
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hbody
          obtain ⟨v, hv, hs⟩ := hbody
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
      · refine bind_isOk ?_ fun vs => ⟨.array vs, rfl⟩
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
      -- The R16 growslice refusal (t5-maxalloc, 2026-09-02) is decided
      -- on newLen's byte size — a choice-FREE condition, so both streams
      -- take the same branch; the panic branch is the same error on
      -- both sides.
      refine exceptCong.bind_congr (R := Eq) (exceptCong.self fun _ => rfl)
        fun elemSize elemSize' hs => ?_
      subst hs
      refine exceptCong.ite_congr (fun _ => ?_) (fun _ => ?_)
      · exact rfl
      · refine exceptCong.bind_congr
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
        · show Heap.lookup (σ.heap.push _) (Loc.rootLoc tloc)
            = Heap.lookup (σ.heap.push _) (Loc.rootLoc tloc)
          rw [Heap.lookup_push_ne hkey, Heap.lookup_push_ne hkey]
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

/-! ### The TRY heads' half of the ∀-choices kit (Q-TRYLOCK, 2026-09-03)

`applySyncOp` threads the stream only for the TRY heads, whose apply is
pick-independent in outcome CLASS by the pre-commit discipline
(`applyTryLock`: the acquired cell is stored BEFORE the pick applies, and
`tryDeliver`'s success depends on the target list alone). -/

/-- `tryDeliver`'s outcome is the same `Except` shape for every value and
state: success and the stuck error both depend on `targets` alone. -/
theorem tryDeliver_ok_any {b : Bool} {σ : ExecState} {targets : List Assignee}
    {env : LocalEnv} {k : Cont} {r : Config × ExecState}
    (h : tryDeliver b σ targets env k = .ok r) (b₂ : Bool) (σ₂ : ExecState) :
    ∃ r₂, tryDeliver b₂ σ₂ targets env k = .ok r₂ := by
  cases targets with
  | nil => exact ⟨_, rfl⟩
  | cons t ts =>
    simp only [tryDeliver, enterRecvTargets] at h ⊢
    rcases htp : targetsPlan (t :: ts) with _ | ⟨_ | ⟨⟨sh, _ | ⟨e, ops⟩⟩, rest⟩⟩ <;>
      simp_all [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]

theorem tryDeliver_error_any {b : Bool} {σ : ExecState} {targets : List Assignee}
    {env : LocalEnv} {k : Cont} {e : Stop}
    (h : tryDeliver b σ targets env k = .error e) (b₂ : Bool) (σ₂ : ExecState) :
    tryDeliver b₂ σ₂ targets env k = .error e := by
  cases targets with
  | nil => simp [tryDeliver] at h
  | cons t ts =>
    simp only [tryDeliver, enterRecvTargets] at h ⊢
    rcases htp : targetsPlan (t :: ts) with _ | ⟨_ | ⟨⟨sh, _ | ⟨e, ops⟩⟩, rest⟩⟩ <;>
      simp_all [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]

/-- `applyTryLock`'s apply-SUCCESS is pick-independent (the pre-commit
discipline): `.ok` under one `spurious` flag ⇒ `.ok` under the other. -/
theorem applyTryLock_ok_any {σ : ExecState} {op : SyncOp} {loc : Loc}
    {pre : SyncPrim} {b₀ : Bool} {targets : List Assignee} {env : LocalEnv}
    {k : Cont} {r : Config × ExecState}
    (h : applyTryLock σ op loc pre b₀ targets env k = .ok r) (b : Bool) :
    ∃ r₂, applyTryLock σ op loc pre b targets env k = .ok r₂ := by
  rw [applyTryLock.eq_def] at h ⊢
  simp only [bind_eq_ok] at h
  obtain ⟨acq, hacq, h⟩ := h
  simp only [Bind.bind, Except.bind, hacq]
  cases acq with
  | none => exact ⟨_, h⟩
  | some post =>
    simp only [bind_eq_ok] at h
    obtain ⟨σA, hst, h⟩ := h
    simp only [hst]
    cases b₀ <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    all_goals first
      | exact ⟨_, h⟩
      | exact tryDeliver_ok_any h _ _

/-- `applyTryLock`'s ERROR is pick-independent too: every error fires
before the pick applies (`tryAcquire`, the pre-committed `storeLoc`) or
in `tryDeliver`, whose error is the same for both flags. -/
theorem applyTryLock_error_any {σ : ExecState} {op : SyncOp} {loc : Loc}
    {pre : SyncPrim} {b₀ : Bool} {targets : List Assignee} {env : LocalEnv}
    {k : Cont} {e : Stop}
    (h : applyTryLock σ op loc pre b₀ targets env k = .error e) (b : Bool) :
    applyTryLock σ op loc pre b targets env k = .error e := by
  rw [applyTryLock.eq_def] at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hacq : tryAcquire op pre with
  | error e' => rw [hacq] at h; simpa using h
  | ok acq =>
    rw [hacq] at h
    cases acq with
    | none => exact h
    | some post =>
      simp only [] at h ⊢
      cases hst : storeLoc σ loc (.syncData post) with
      | error e' => rw [hst] at h; simpa using h
      | ok σA =>
        rw [hst] at h
        cases b₀ <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        all_goals first
          | exact h
          | exact tryDeliver_error_any h _ _

/-- Is this configuration a TRY head's sync-apply position (the one sync
apply that draws the `tryLock` site — Q-TRYLOCK)? Conservative, like
`consumesSelect`: flags the held-cell apply too (bound 1, which pops
nothing) — the checkers fail closed there rather than reasoning about
acquirability; the membership enumerator's `stepNeeds` computes the
exact width. -/
def consumesTryLock : Config → Bool
  | .retV _ (.syncStK op _ [] _ _) => op.tryTargets?.isSome
  | _ => false

/-- `consumesTryLock`'s negation names the head: a non-TRY head. -/
theorem consumesTryLock_none {v : GoValue} {op : SyncOp} {done : List GoValue}
    {env : LocalEnv} {k : Cont}
    (h : consumesTryLock (.retV v (.syncStK op done [] env k)) = false) :
    op.tryTargets? = none := by
  simp only [consumesTryLock, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  exact h

/-- A non-TRY head's apply passes the stream through untouched, on
success — the `applyStmtOp_eq_core` twin. -/
theorem applySyncOp_core_ok {σ : ExecState} {ch₀ : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : ExecState} {ch' : Choices} (hop : op.tryTargets? = none)
    (h : applySyncOp σ ch₀ op vs env k = .ok (c', σ', ch')) :
    ch' = ch₀ ∧ ∀ ch : Choices, applySyncOp σ ch op vs env k = .ok (c', σ', ch) := by
  rw [applySyncOp.eq_def] at h
  rw [hop] at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨c₀, σ₀⟩, hcore, rfl, rfl, rfl⟩ := h
  refine ⟨rfl, fun ch => ?_⟩
  rw [applySyncOp.eq_def, hop]
  simp [hcore, Bind.bind, Except.bind]

/-- … and on error. -/
theorem applySyncOp_core_error {σ : ExecState} {ch₀ : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {e : Stop}
    (hop : op.tryTargets? = none)
    (h : applySyncOp σ ch₀ op vs env k = .error e) :
    ∀ ch : Choices, applySyncOp σ ch op vs env k = .error e := by
  intro ch
  rw [applySyncOp.eq_def] at h ⊢
  rw [hop] at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hcore : applySyncOpCore σ op vs env k with
  | error e' => rw [hcore] at h; simpa using h
  | ok r => rw [hcore] at h; cases h

/-- `applySyncOp`'s apply-SUCCESS is stream-independent: the non-TRY heads
never see the stream, the TRY heads by `applyTryLock_ok_any`. -/
theorem applySyncOp_ok_any_ch {σ : ExecState} {ch₀ : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : ExecState} {ch₁ : Choices}
    (h : applySyncOp σ ch₀ op vs env k = .ok (c', σ', ch₁)) (ch : Choices) :
    ∃ (c₂ : Config) (σ₂ : ExecState) (ch₂ : Choices),
      applySyncOp σ ch op vs env k = .ok (c₂, σ₂, ch₂) := by
  cases hop : op.tryTargets? with
  | none =>
    obtain ⟨-, hall⟩ := applySyncOp_core_ok hop h
    exact ⟨c', σ', ch, hall ch⟩
  | some targets =>
    rw [applySyncOp.eq_def] at h ⊢
    rw [hop] at h ⊢
    split at h
    · rename_i av
      simp only [bind_eq_ok] at h
      obtain ⟨loc, hloc, pre, hcell, ⟨c₀, σ₀⟩, happ, -⟩ := h
      obtain ⟨⟨c₂, σ₂⟩, happ₂⟩ := applyTryLock_ok_any happ
        ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch).1 == 1)
      refine ⟨c₂, σ₂, (Choices.consumeAt .tryLock (tryLockWidth op pre) ch).2, ?_⟩
      simp [hloc, hcell, happ₂, Bind.bind, Except.bind]
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at h
    · rename_i heq
      cases heq

/-- `applySyncOp`'s PANIC is stream-independent: every panic fires before
the pick (`valueAsLoc`; `applyTryLock_error_any` covers the rest). -/
theorem applySyncOp_panic_any_ch {σ : ExecState} {ch₀ : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {msg : String}
    (h : applySyncOp σ ch₀ op vs env k = .error (.panic msg)) (ch : Choices) :
    applySyncOp σ ch op vs env k = .error (.panic msg) := by
  cases hop : op.tryTargets? with
  | none => exact applySyncOp_core_error hop h ch
  | some targets =>
    rw [applySyncOp.eq_def] at h ⊢
    rw [hop] at h ⊢
    split at h
    · rename_i targets' av heq
      cases heq
      simp only [Bind.bind, Except.bind] at h ⊢
      cases hloc : valueAsLoc av with
      | error e' => rw [hloc] at h; simpa using h
      | ok loc =>
        rw [hloc] at h
        dsimp only at h ⊢
        cases hcell : syncCell σ loc with
        | error e' => rw [hcell] at h; simpa using h
        | ok pre =>
          rw [hcell] at h
          dsimp only at h ⊢
          cases happ : applyTryLock σ op loc pre
              ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch₀).1 == 1) targets env k with
          | error e' =>
            rw [happ] at h
            simp only [Except.error.injEq] at h
            subst h
            rw [applyTryLock_error_any happ]
          | ok r => rw [happ] at h; cases h
    · simp at h
    · rename_i heq
      cases heq

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
      refine ⟨env.declare nv (.base ⟨σ.heap.size⟩),
        { σ with heap := σ.heap.push (.value vt value) }, ?_⟩
      simp [isNormalForTy_sound hv, Bind.bind, Except.bind, ExecState.alloc, ExecState.allocCell,
        pure, Except.pure]
  | some nk =>
    cases vv with
    | none =>
      refine ⟨env.declare nk (.base ⟨σ.heap.size⟩),
        { σ with heap := σ.heap.push (.value kt key) }, ?_⟩
      simp [isNormalForTy_sound hk, Bind.bind, Except.bind, ExecState.alloc, ExecState.allocCell,
        pure, Except.pure]
    | some nv =>
      have hv' : normalizeValueForTy
          { σ with heap := σ.heap.push (.value kt key) }
          vt value = .ok value :=
        isNormalForTy_sound hv
      refine ⟨(env.declare nk (.base ⟨σ.heap.size⟩)).declare nv
          (.base ⟨(σ.heap.push (.value kt key)).size⟩),
        { σ with
          heap := (σ.heap.push (.value kt key)).push
            (.value vt value) }, ?_⟩
      simp [isNormalForTy_sound hk, hv', Bind.bind, Except.bind,
        ExecState.alloc, ExecState.allocCell, pure, Except.pure]

/-- `mapM` over `Except` preserves length on success. -/
theorem mapM_ok_length {α β : Type} {f : α → Except Stop β}
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
                simp [throw, throwThe, MonadExceptOf.throw, Stop.internal,
                  Stop.panic] at h
          | cons b rest =>
              simp only [Choices.consumeAt_l2Entry] at h ⊢
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
              | mk cl sr =>
                cases sr with
                | inl r => exact .inl ⟨_, rfl⟩
                | inr msg => exact .inl ⟨_, rfl⟩

/-- Non-`appendSlice` wide ops dispatch through the choices-free core:
the result is the core's, with the stream threaded through untouched —
on success AND on error. -/
theorem applyStmtOp_eq_core {σ : ExecState} {ch : Choices} {op : StmtOp}
    {nt : Nat} {vs : List GoValue} (hop : ∀ e, op ≠ .appendSlice e) :
    applyStmtOp σ ch op nt vs
      = (fun σ₂ => (σ₂, ch)) <$> applyStmtOpCore σ op vs := by
  cases op <;>
    first
    | exact absurd rfl (hop _)
    | (simp only [applyStmtOp, Bind.bind, Except.bind, Functor.map, Except.map,
         pure, Except.pure]
       all_goals (cases applyStmtOpCore σ _ vs <;> rfl))

/-- Mapping cannot manufacture or change an error. -/
theorem map_eq_error {ε α β : Type} {g : α → β} {x : Except ε α} {e : ε} :
    g <$> x = .error e ↔ x = .error e := by
  cases x <;> simp [Functor.map, Except.map]

/-- Successful pick-time candidates are self-normalized (the check is
inside `mapIterCandidates` — the sem-adequacy guard at its new home). -/
theorem mapIterCandidates_normalized {σ : ExecState} {keyTy valTy : Ty}
    {base : Option Loc} {produced : Array Nat}
    {cands : Array (Nat × GoValue × GoValue)}
    (h : mapIterCandidates σ keyTy valTy base produced = .ok cands) :
    snapshotEntriesSelfNormalized σ.types keyTy valTy cands = true := by
  unfold mapIterCandidates at h
  simp only [bind_eq_ok] at h
  obtain ⟨es, hes, h⟩ := h
  split at h
  · rename_i hchk
    simp only [pure_eq_ok, Except.ok.injEq] at h
    subst h
    exact hchk
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The nonempty mapIter pick succeeds under EVERY stream: the stop
slot is a pure return, and every candidate pick binds — the
candidates' self-normalization (validated inside `mapIterCandidates`)
makes `bindIterVars` succeed at every index. The (L) surgery's
choices-independence core (the COUPLING note's re-run demand). -/
theorem stepFn_mapIter_ok_any {σ : ExecState} {kv vv : Option String}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont}
    {cands : Array (Nat × GoValue × GoValue)} {mand : Bool}
    (hcands : mapIterCandidates σ kt vt base produced = .ok cands)
    (hmand : mapIterMandatoryRemains cands start = mand)
    (hne : ¬cands.isEmpty = true) :
    ∀ ch : Choices, ∃ out,
      stepFn σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
        = .ok out := by
  intro ch
  have hsnap := mapIterCandidates_normalized hcands
  simp only [stepFn, Choices.consumeAt_mapIter, hcands, Bind.bind, Except.bind]
  rw [hmand, if_neg hne]
  rcases hcons : ch.consume (cands.size + (if mand = true then 0 else 1))
    with ⟨idx', rest'⟩
  dsimp only
  split
  · exact ⟨_, rfl⟩
  next id' key' value' heq =>
    obtain ⟨hlt, hkv⟩ := Array.getElem?_eq_some_iff.mp heq
    have hmem := snapshotEntriesSelfNormalizedList_mem
      (types := σ.types) (kt := kt) (vt := vt)
      (l := cands.toList) hsnap
      (e := cands[idx'])
      (List.mem_of_getElem? (by
        rw [Array.getElem?_toList]
        exact Array.getElem?_eq_getElem hlt))
    rw [hkv] at hmem
    obtain ⟨env₂, σ₂, hbind₂⟩ := bindIterVars_ok_of_normal
      (env := env.pushScope) (kv := kv) (vv := vv)
      hmem.1 hmem.2
    simp [hbind₂]

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
  case evalStrictNullary e op r env k hplan hres hdel =>
    rcases toResult_cases hres with ⟨⟨v, s₂⟩, rfl, hX⟩ | ⟨msg, rfl, hX⟩ <;>
    cases e <;>
      first
        | (simp_all [stepFn, strictPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;> (simp_all [stepFn, strictPlan, Bind.bind, Except.bind]; done))
        | (simp only [strictPlan, Option.some.injEq, Prod.mk.injEq] at hplan
           obtain ⟨rfl, hargs⟩ := hplan
           simp_all [stepFn, strictPlan, Bind.bind, Except.bind])
  case stmtOpFirst stmt op nt e rest env k hplan =>
    cases stmt <;>
      first
        | (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done)
        | (rename_i o; cases o <;>
            (simp_all [stepFn, stmtPlan, Bind.bind, Except.bind]; done))
  case stmtOpApply op nt done v r env k ch₀ hres hdel =>
    have hop : goValueListSup (v :: done).reverse ≤ σ.nextAddr := by
      rw [goValueListSup_reverse]
      simp only [ConfigWf, Config.locSup, Cont.locSup, goValueListSup,
        exprListSup, Nat.max_le] at hc
      simp only [goValueListSup]
      omega
    rcases toResult_cases hres with ⟨⟨σ₂, ch₁⟩, rfl, happly⟩ | ⟨msg, rfl, happly⟩
    · -- a successful apply under `ch₀` succeeds under any stream
      -- (`applyStmtOp_ok_any_ch_wf`); the successor shape is the same.
      obtain ⟨⟨σ₃, ch₃⟩, hr⟩ := applyStmtOp_ok_any_ch_wf hop happly ch
      simp only [List.reverse_cons] at hr
      simp [stepFn, hr, List.reverse_cons, Bind.bind, Except.bind]
    · obtain ⟨m', hm'⟩ := applyStmtOp_panic_any_ch_wf hop happly ch
      simp only [List.reverse_cons] at hm'
      simp [stepFn, hm', List.reverse_cons, Bind.bind, Except.bind]
  case stmtOpShiftPlain op nt done v e rest env k hle =>
    simp only [stepFn]
    rw [if_neg (Nat.not_lt.mpr hle)]
    exact ⟨_, rfl⟩
  case mapIterNext keyVar valVar keyTy valTy body base produced start cands
      idx env env' k hidx hcands hbind =>
    exact stepFn_mapIter_ok_any hcands rfl
      (by simp only [Array.isEmpty_iff]; rintro rfl; simp at hidx) ch
  case mapIterStop keyVar valVar keyTy valTy body base produced start cands
      env k hne hmand hcands =>
    exact stepFn_mapIter_ok_any hcands hmand
      (by simp only [Array.isEmpty_iff, ← Array.size_eq_zero_iff]; exact hne) ch
  case mapIterDone keyVar valVar keyTy valTy body base produced start env k
      hcands =>
    simp [stepFn, hcands, Bind.bind, Except.bind]
  case panicUnwind chain k k' hpass =>
    cases k <;> simp_all [stepFn, panicPassthrough]
  case chanStFirst stmt op e rest env k hplan =>
    cases stmt <;>
      first
        | (simp_all [stepFn, chanPlan]; done)
        | (simp only [stepFn]; rw [hplan]; exact ⟨_, rfl⟩)
  case syncStFirst stmt op e rest env k hplan =>
    cases stmt <;>
      first
        | (simp_all [stepFn, syncPlan]; done)
        | (simp only [stepFn]; rw [hplan]; exact ⟨_, rfl⟩)
  case atomicStFirst stmt op e rest env k hplan =>
    cases stmt <;>
      first
        | (simp_all [stepFn, atomicPlan]; done)
        | (simp only [stepFn]; rw [hplan]; exact ⟨_, rfl⟩)
  -- The sync apply is pick-independent in apply-SUCCESS and in its panic
  -- (Q-TRYLOCK; `applySyncOp_ok_any_ch`/`applySyncOp_panic_any_ch`).
  case syncStApply op done v r env k ch₀ hres hdel =>
    rcases toResult_cases hres with ⟨⟨c₂, σ₂, ch₂⟩, rfl, happly⟩ | ⟨msg, rfl, happly⟩
    · obtain ⟨c₃, σ₃, ch₃, hap⟩ := applySyncOp_ok_any_ch happly ch
      simp only [List.reverse_cons] at hap
      simp [stepFn, hap, List.reverse_cons, Bind.bind, Except.bind]
    · have hap := applySyncOp_panic_any_ch happly ch
      simp only [List.reverse_cons] at hap
      simp [stepFn, hap, List.reverse_cons, Bind.bind, Except.bind]
  -- The select apply is pick-independent in apply-SUCCESS (slice 4;
  -- `applySelect_ok_or_panic_any_ch`): under any stream it lands `.ok`
  -- or a panic, and `stepFn` maps both to `.ok` configurations.
  case selectApply clauses default? done v r env k ch₀ hres hdel =>
    have hor : (∃ x, applySelect σ clauses default? (v :: done).reverse env k ch₀ = .ok x)
        ∨ (∃ msg, applySelect σ clauses default? (v :: done).reverse env k ch₀ = .error (.panic msg)) := by
      rcases toResult_cases hres with ⟨x, -, hX⟩ | ⟨msg, -, hX⟩
      · exact .inl ⟨x, hX⟩
      · exact .inr ⟨msg, hX⟩
    rcases applySelect_ok_or_panic_any_ch hor ch with
      ⟨⟨c₂, σ₂, ch₂, cl₂⟩, hap⟩ | ⟨msg, hap⟩ <;>
      simp only [List.reverse_cons] at hap
    · simp [stepFn, hap, List.reverse_cons, Bind.bind, Except.bind]
    · simp [stepFn, hap, List.reverse_cons, Bind.bind, Except.bind]
  -- The frame-entry rules: the entry classifies under EVERY stream
  -- (`enterFramePick_any_ch`), and `deliverS` then delivers.
  case callImmediate targets fid args plans r env k ch₀ ch₁ hplan hargs hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    simp [stepFn, hplan, hargs, hp, Bind.bind, Except.bind]
  case callArgsDoneEnter v fid plans vals r env k ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  case callValCalleeEnter fid captured plans r env k ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  case callValArgsEnter v fid captured plans vals r env k ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  case frameDeferFall targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  case frameDeferReturn targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  case panicFrameDefer chain targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  all_goals simp_all [stepFn, Bind.bind, Except.bind, valueAsBool]

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
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedSync_elim
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
      · exact absurd hstop (by simp)
      · exact absurd hstep step_blockedSync_elim
    · rcases hprog _ _ hreach with hstop | ⟨c'', σ'', hstep⟩
      · rename_i harm1 harm2 harm3 harm4 harm5 harm6 harm7 harm8 harm9
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
`stmtOpK` apply position (the former nullary wide-statement arm is a
refusal since A8 — no `stmtPlan` emits an empty operand list). -/
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
      | .next (.mapIterK keyVar valVar keyTy valTy body base produced start env k) =>
          -- BUG-005 (L): the branch bound moved from the CONFIGURATION
          -- (the retired snapshot's size) to the STATE (live candidates
          -- + the stop slot). Fail closed on a candidates/mandatory
          -- error. Self-inserting loops have genuinely unbounded trace
          -- sets under the ruled envelope — this checker runs out of
          -- fuel on them and returns false, BY DESIGN (memo §5 ruling:
          -- ∀-streams certification fails closed there; the membership
          -- lane carries such programs).
          match mapIterCandidates σ keyTy valTy base produced with
          | .error _ => false
          | .ok cands =>
              if cands.isEmpty then
                match stepFn σ (.next (.mapIterK keyVar valVar keyTy valTy body
                    base produced start env k)) [0] with
                | .ok (c', σ', _) => allStreamsOk fuel σ' c'
                | .error _ => false
              else
                -- (the mandatory test is pure since the B1 stamps)
                (List.range (cands.size
                    + (if mapIterMandatoryRemains cands start then 0 else 1))).all fun i =>
                  match stepFn σ (.next (.mapIterK keyVar valVar keyTy valTy body
                      base produced start env k)) [i] with
                  | .ok (c', σ', _) => allStreamsOk fuel σ' c'
                  | .error _ => false
      | c =>
          if consumesAppendSlice c || consumesSelect c || consumesNilValueMethod σ c || consumesTryLock c then false
          else
            match stepFn σ c [0] with
            | .ok (c', σ', _) => allStreamsOk fuel σ' c'
            | .error _ => false

/-- The `stmtOpK` apply-position shape flag transfers to the op. -/
theorem consumesAppendSlice_stmtOpK {v : GoValue} {op : StmtOp} {nt : Nat}
    {done : List GoValue} {env : LocalEnv} {k : Cont}
    (h : consumesAppendSlice (.retV v (.stmtOpK op nt done [] env k)) = false) :
    ∀ e, op ≠ .appendSlice e := by
  intro e he
  subst he
  simp [consumesAppendSlice] at h

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- **Stream obliviousness of the non-consuming arms**: away from the
four consuming shapes (a `mapIterK` at the `.next` position — excluded
by `hmi` — an `appendSlice` apply position — excluded by `hnc` — a
select apply position, whose `applySelect` may draw the L2 clause pick
— excluded by `hns`, slice 4 — a frame entry in BUG-087's wrapper
family, whose `enterFramePick` draws the `nilValueMethodText` pick —
excluded by `hnv` — and a TRY head's sync apply, which draws the
`tryLock` site — excluded by `hnt`, Q-TRYLOCK), a step
that succeeds under one stream succeeds under EVERY stream, with the SAME
successor and the stream returned untouched. Sweep over `stepFn`'s case
tree; a newly added stream-consuming arm breaks this proof loudly rather
than silently unsounding the checker. -/
theorem stepFn_oblivious {σ : ExecState} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (hmi : ∀ (kv vv : Option String) (kt vt : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array Nat)
      (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body base produced start env k))
    (hnc : consumesAppendSlice c = false)
    (hns : consumesSelect c = false)
    (hnv : consumesNilValueMethod σ c = false)
    (hnt : consumesTryLock c = false)
    (h : stepFn σ c ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepFn σ c ch = .ok (c', σ', ch) := by
  fun_cases stepFn σ c ch₀
  all_goals first
    | exact absurd rfl (hmi _ _ _ _ _ _ _ _ _ _)
    | (simp [consumesSelect] at hns; done)
    | (refine ⟨?_, fun ch => ?_⟩ <;> (simp_all [stepFn]; done))
    | skip
  -- 23 arms remain: every one binds through a choices-free helper
  -- (enterFrame / allocDecls / defaultValue / loadLoc / valueAsBool /
  -- mapRangeSnapshotEntries / loadMany+storeMany) or dispatches a
  -- non-appendSlice applyStmtOp (`hnc`). Uniform recipe: reduce the probe
  -- equation, invert its bind, replay the same bind at the arbitrary
  -- stream (the helpers never see the stream).
  case case77 =>
    -- A4: a global past the heap REFUSES (`.stuck`); no step is produced.
    rename_i hgid
    simp only [stepFn] at h
    rw [if_neg hgid] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case3 =>
    oblivious_entry h hnv
  case case13 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨⟨env', s₁⟩, hd, ?_⟩
    simp
  -- Channel receive entry (channels arc slice 1): the plan match needs
  -- its hypothesis rewritten in; both arms are stream-oblivious.
  case case41 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case42 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case43 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_pos hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case44 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_neg hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- Sync statements (spec-parity slice 2): the chan recipes — entry is
  -- stream-transparent; the APPLY is stream-transparent for every
  -- non-TRY head (`hnt` excludes the TRY heads — Q-TRYLOCK's
  -- `tryLock` site; `applySyncOp_core_ok`/`_error`).
  -- Sync statements (spec-parity slice 2): the chan recipes — entry is
  -- stream-transparent; the APPLY is stream-transparent for every
  -- non-TRY head (`hnt` excludes the TRY heads — Q-TRYLOCK's
  -- `tryLock` site; `applySyncOp_core_ok`/`_error`).
  case case133 =>
    have hnone := consumesTryLock_none hnt
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok]
    obtain ⟨r, hres, h⟩ := h
    rcases toResult_cases hres with ⟨⟨c₂, σ₂, ch₂⟩, rfl, happly⟩ | ⟨msg, rfl, happly⟩
    · simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, hall⟩ := applySyncOp_core_ok hnone happly
      refine ⟨rfl, fun ch => ?_⟩
      have hc := hall ch
      simp only [List.reverse_cons] at hc
      simp [stepFn, hc, Bind.bind, Except.bind]
    · simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      have hc := applySyncOp_core_error hnone happly ch
      simp only [List.reverse_cons] at hc
      simp [stepFn, hc, Bind.bind, Except.bind]
  case case60 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case61 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case62 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- sync/atomic statements (atomics arc wave 1): the sync recipes —
  -- entry is stream-transparent (the apply consumes nothing,
  -- applyAtomicOp's envelope statement).
  case case63 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case64 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case65 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case14 =>
    simp_all [stepFn, bind_eq_ok]
    obtain ⟨v, hd, h1, h2, h3⟩ := h
    exact ⟨h3.symm, v, hd, h1, h2⟩
  case case36 =>
    oblivious_entry h hnv
  case case69 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨v, hd, ?_⟩
    simp
  case case83 =>
    oblivious_apply h
  case case86 =>
    oblivious_apply h
  case case87 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case88 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case89 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨b, hb, ?_⟩
    simp
  case case90 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case91 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case93 =>
    oblivious_entry h hnv
  case case94 =>
    rename_i hlt
    simp only [stepFn, if_pos hlt] at h
    (try simp only [Bind.bind, Except.bind] at h)
    split at h
    · simp at h
    · rename_i r hres
      cases r with
      | ok a =>
        simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch => by simp [stepFn, if_pos hlt, hres, Bind.bind, Except.bind]⟩
      | panic msg =>
        simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch => by simp [stepFn, if_pos hlt, hres, Bind.bind, Except.bind]⟩
  case case95 =>
    rename_i hlt
    simp only [stepFn, if_neg hlt, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, if_neg hlt]
    rfl
  case case96 =>
    have hop := consumesAppendSlice_stmtOpK hnc
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok]
    obtain ⟨r, hres, h⟩ := h
    rcases toResult_cases hres with ⟨⟨σ₂, ch₂⟩, rfl, happly⟩ | ⟨msg, rfl, happly⟩
    · simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [applyStmtOp_eq_core hop, map_eq_ok] at happly
      obtain ⟨σ₃, hcore, heq⟩ := happly
      injection heq with h1 h2
      subst h1
      subst h2
      -- (the opening `simp_all only [bind_eq_ok]` left the ∀-goal in its
      -- ∃-form: name the classified result at the arbitrary stream)
      refine ⟨rfl, fun ch => ⟨.ok (σ₃, ch), ?_, rfl⟩⟩
      rw [applyStmtOp_eq_core hop, hcore]
      rfl
    · simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [applyStmtOp_eq_core hop, map_eq_error] at happly
      refine ⟨rfl, fun ch => ⟨.panic msg, ?_, rfl⟩⟩
      rw [applyStmtOp_eq_core hop, happly]
      rfl
  case case97 =>
    oblivious_entry h hnv
  case case103 =>
    oblivious_entry h hnv
  case case113 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨bs, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨bs, hd, ?_⟩
    simp
  case case116 =>
    oblivious_apply h
  case case126 =>
    oblivious_apply h
  case case135 =>
    oblivious_apply h
  case case143 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case144 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨vs, hload, ?_⟩
    simp
  case case146 =>
    oblivious_entry h hnv
  case case154 =>
    oblivious_apply h
  case case180 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case181 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨vs, hload, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨vs, hload, ?_⟩
    simp
  case case183 =>
    oblivious_entry h hnv

/-- The done-check `mapIterK` step is oblivious: with no candidate
left it pops the continuation at every stream (BUG-005 (L): "no
candidate" is a STATE fact — the live cell minus the produced set). -/
theorem stepFn_mapIter_done {σ : ExecState} {kv vv : Option String}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont}
    (hcands : mapIterCandidates σ kt vt base produced = .ok #[]) :
    ∀ ch : Choices,
      stepFn σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
        = .ok (.next k, σ, ch) := by
  intro ch
  simp [stepFn, hcands, Bind.bind, Except.bind]

set_option linter.unusedSimpArgs false in
/-- The nonempty `mapIterK` step at a PICK index, factored through the
consumed choice: the successor is a function of the pick index alone
(`bindIterVars` never sees the stream), and the stream moves to the
consume's tail. One probe per index covers every stream whose choice
reduces to that index. -/
theorem stepFn_mapIter_pick {σ : ExecState} {kv vv : Option String}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont}
    {cands : Array (Nat × GoValue × GoValue)} {mand : Bool}
    {ch : Choices} {idx : Nat} {tail : Choices}
    (hcands : mapIterCandidates σ kt vt base produced = .ok cands)
    (hmand : mapIterMandatoryRemains cands start = mand)
    (hne : ¬ cands.isEmpty = true)
    (hcons : Choices.consume ch (cands.size + (if mand = true then 0 else 1))
      = (idx, tail))
    (hlt : idx < cands.size) :
    stepFn σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
      = ((bindIterVars env.pushScope σ kv vv kt vt
            cands[idx].2.1 cands[idx].2.2).map
          fun p => (.exec body p.1
            (.mapIterK kv vv kt vt body base (produced.push cands[idx].1)
              start env k),
            p.2, tail)) := by
  simp only [stepFn, Choices.consumeAt_mapIter, hcands, Bind.bind, Except.bind]
  rw [hmand, if_neg hne, hcons]
  dsimp only
  split
  · rename_i heq
    rw [Array.getElem?_eq_getElem hlt] at heq
    cases heq
  · rename_i id key value heq
    rw [Array.getElem?_eq_getElem hlt] at heq
    injection heq with heq
    have h1 : cands[idx].1 = id := congrArg Prod.fst heq
    have h2 : cands[idx].2.1 = key := congrArg (fun p => p.2.1) heq
    have h3 : cands[idx].2.2 = value := congrArg (fun p => p.2.2) heq
    subst h1
    subst h2
    subst h3
    cases hbind : bindIterVars env.pushScope σ kv vv kt vt
        cands[idx].2.1 cands[idx].2.2 <;>
      simp [hbind, Except.map, Bind.bind, Except.bind]

/-- The nonempty `mapIterK` step at the STOP slot (index = candidate
count; the slot exists only when no mandatory start key remains): the
iteration ends at every stream whose choice lands there. -/
theorem stepFn_mapIter_stop {σ : ExecState} {kv vv : Option String}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont}
    {cands : Array (Nat × GoValue × GoValue)}
    {ch : Choices} {tail : Choices}
    (hcands : mapIterCandidates σ kt vt base produced = .ok cands)
    (hmand : mapIterMandatoryRemains cands start = false)
    (hne : ¬ cands.isEmpty = true)
    (hcons : Choices.consume ch (cands.size + 1) = (cands.size, tail)) :
    stepFn σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
      = .ok (.next k, σ, tail) := by
  simp only [stepFn, Choices.consumeAt_mapIter, hcands, Bind.bind, Except.bind]
  rw [hmand, if_neg hne]
  have hred : (cands.size + if false = true then 0 else 1)
      = cands.size + 1 := by simp
  rw [hred, hcons]
  dsimp only
  split
  · rfl
  · rename_i key value heq
    exfalso
    have := (Array.getElem?_eq_some_iff.mp heq).1
    omega

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
         | .blockedSync _ _ _ _ => throw .deadlock
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
  -- blockedSync (spec-parity slice 2): one more deadlock-classified arm.
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
    · -- the mapIterK pick point (BUG-005 (L): candidates + stop from
      -- the STATE)
      rename_i keyVar valVar keyTy valTy body base produced start env k
      split at hall
      · -- candidates error: checker false
        exact absurd hall (by simp)
      rename_i cands hcands
      split at hall
      · -- no candidate: the oblivious done pop
        rename_i hemp
        rw [Array.isEmpty_iff] at hemp
        subst hemp
        split at hall
        · rename_i c₁ σ₁ ch₁ hprobe
          rw [stepFn_mapIter_done hcands [0]] at hprobe
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
            by rw [execStmtLoop_step (stepFn_mapIter_done hcands ch)]; exact hrun⟩
        · exact absurd hall (by simp)
      · -- candidates remain: every pick (and the stop slot, when
        -- legal) was checked; the stream's choice is one of them
        rename_i hne
        -- the mandatory test is pure (B1 stamps); name its value
        obtain ⟨mand, hmand⟩ : ∃ m, mapIterMandatoryRemains cands start = m := ⟨_, rfl⟩
        rw [hmand] at hall
        rw [List.all_eq_true] at hall
        rcases hcons : Choices.consume ch
          (cands.size + (if mand = true then 0 else 1)) with ⟨idx, tail⟩
        have hpos : 0 < cands.size := by
          rcases Nat.eq_zero_or_pos cands.size with hz | hp
          · exact absurd (by simpa [Array.isEmpty_iff, Array.size_eq_zero_iff]
              using hz) hne
          · exact hp
        have hltw : idx < cands.size + (if mand = true then 0 else 1) := by
          have hb := consume_fst_lt (ch := ch)
            (bound := cands.size + (if mand = true then 0 else 1))
            (by cases mand <;> simp <;> omega)
          rw [hcons] at hb
          exact hb
        have hidx := hall idx (by simpa using List.mem_range.mpr hltw)
        have hconsi : Choices.consume [idx]
            (cands.size + (if mand = true then 0 else 1)) = (idx, []) := by
          simp [Choices.consume,
            Nat.mod_eq_of_lt (show idx < max 1 (cands.size
              + (if mand = true then 0 else 1)) by omega)]
        by_cases hlt : idx < cands.size
        · -- a pick
          rw [stepFn_mapIter_pick hcands hmand hne hconsi hlt] at hidx
          cases hbind : bindIterVars env.pushScope σ keyVar valVar keyTy valTy
              cands[idx].2.1 cands[idx].2.2 with
          | error e =>
            rw [hbind] at hidx
            simp [Except.map] at hidx
          | ok p =>
            rw [hbind] at hidx
            simp only [Except.map] at hidx
            obtain ⟨out, ch', hrun⟩ := ih hidx tail
            refine ⟨out, ch', ?_⟩
            rw [execStmtLoop_step
              (by rw [stepFn_mapIter_pick hcands hmand hne hcons hlt, hbind]; rfl)]
            exact hrun
        · -- the stop slot: idx = cands.size, legal only when mand-free
          have hmandf : mand = false := by
            cases mand
            · rfl
            · exfalso
              simp at hltw
              omega
          subst hmandf
          have hidxeq : idx = cands.size := by
            simp at hltw
            omega
          subst hidxeq
          have hconsi' : Choices.consume [cands.size] (cands.size + 1)
              = (cands.size, []) := by
            simpa using hconsi
          have hcons' : Choices.consume ch (cands.size + 1)
              = (cands.size, tail) := by
            simpa using hcons
          rw [stepFn_mapIter_stop hcands hmand hne hconsi'] at hidx
          obtain ⟨out, ch', hrun⟩ := ih hidx tail
          refine ⟨out, ch', ?_⟩
          rw [execStmtLoop_step (stepFn_mapIter_stop hcands hmand hne hcons')]
          exact hrun
    · -- the oblivious catch-all
      rename_i hx1 hx2 hx3 hx4 hx5
      cases hnc : (consumesAppendSlice c || consumesSelect c || consumesNilValueMethod σ c || consumesTryLock c) with
      | true =>
        rw [hnc] at hall
        simp at hall
      | false =>
        rw [hnc] at hall
        simp only [Bool.false_eq_true, if_false] at hall
        obtain ⟨⟨⟨hnc1, hnc2⟩, hnc3⟩, hnc4⟩ : ((consumesAppendSlice c = false
            ∧ consumesSelect c = false) ∧ consumesNilValueMethod σ c = false)
            ∧ consumesTryLock c = false := by
          simpa using hnc
        split at hall
        · rename_i c₁ σ₁ ch₁ hprobe
          obtain ⟨-, hobl⟩ := stepFn_oblivious
            (fun kv vv kt vt b bs pr st e kk heq =>
              hx5 kv vv kt vt b bs pr st e kk heq)
            hnc1 hnc2 hnc3 hnc4 hprobe
          obtain ⟨out, ch', hrun⟩ := ih hall ch
          exact ⟨out, ch', by rw [execStmtLoop_step (hobl ch)]; exact hrun⟩
        · exact absurd hall (by simp)
