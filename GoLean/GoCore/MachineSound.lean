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
    (Choices.consume ch bound).1 < bound :=
  Choices.consume_fst_lt hb

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

/-- **Frame exit is sound for BOTH of its entries** (B4): a successful
`stepFrameExit` is a `Step` from the fall-through configuration (`.next`
at the frame — `frameFall`/`frameFallTargets`/`frameDeferFall`/
`frameDeferNilFall`) AND from the return configuration (`.signal .ret` at
the frame — the `frameReturn*` twins), with the same successor. -/
theorem stepFrameExit_sound {s : ExecState} {targets : List (TargetShape × List Expr)}
    {tenv : LocalEnv} {results : List Loc} {ds : List (GoValue × List GoValue)}
    {k' : Cont} {w : Bool} {ch : Choices} {c' : Config} {s' : ExecState} {ch' : Choices}
    (h : stepFrameExit s targets tenv results ds k' w ch = .ok (c', s', ch')) :
    Step (.next (.frame targets tenv results ds k' w)) s c' s'
      ∧ Step (.signal .ret (.frame targets tenv results ds k' w)) s c' s' := by
  fun_cases stepFrameExit s targets tenv results ds k' w ch
  · simp only [stepFrameExit, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨Step.frameFall, Step.frameReturn⟩
  · simp only [stepFrameExit, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [stepFrameExit, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨vs, hload, rfl, rfl, rfl⟩ := h
    exact ⟨Step.frameFallTargets hload, Step.frameReturnTargets hload⟩
  · simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h
  · simp only [stepFrameExit, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨⟨r, ch₁⟩, hpick, h⟩ := h
    (try simp only at h)
    cases r with
    | ok a =>
      simp only [deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      exact ⟨Step.frameDeferFall hpick (by first | rfl | simp only [deliver_ok]),
        Step.frameDeferReturn hpick (by first | rfl | simp only [deliver_ok])⟩
    | panic msg =>
      simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      exact ⟨Step.frameDeferFall hpick rfl, Step.frameDeferReturn hpick rfl⟩
  · simp only [stepFrameExit, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨Step.frameDeferNilFall, Step.frameDeferNilReturn⟩
  · simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h

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
  case case75 =>
    -- A4: a global past the heap REFUSES (`.stuck`); no step is produced.
    rename_i hgid
    simp only [stepFn] at h
    rw [if_neg hgid] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case1 =>
    simp_all only [stepFn, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.panicFrameEmpty
  case case2 =>
    entry_arm h Step.panicFrameDefer
  case case142 =>
    rename_i hrec
    simp_all only [stepFn, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.panicResumeContinue (Bool.eq_false_iff.mpr hrec)
  case case11 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
    exact Step.block hd
  case case12 =>
    simp_all [stepFn, bind_eq_ok]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.initialization hd rfl
  case case34 =>
    entry_arm h (Step.callImmediate ‹_› ‹_›)
  case case67 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    exact Step.evalVar ‹_› hd
  case case76 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.evalAnd
  case case77 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.evalOr
  case case78 =>
    simp only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.evalRecover rfl
  case case81 =>
    deliver_arm h (Step.evalStrictNullary ‹_›)
  case case84 =>
    deliver_arm h Step.strictApply
  case case85 =>
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
  case case86 =>
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
  case case87 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    obtain rfl := valueAsBool_ok hb
    exact Step.boolCoerce
  case case88 =>
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
  case case89 =>
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
  case case91 =>
    entry_arm h Step.callArgsDoneEnter
  case case92 =>
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
  case case93 =>
    simp_all only [stepFn, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.stmtOpShiftPlain (Nat.le_of_not_lt ‹_›)
  case case94 =>
    deliver_arm h Step.stmtOpApply
  case case95 =>
    entry_arm h Step.callValCalleeEnter
  case case101 =>
    entry_arm h Step.callValArgsEnter
  case case111 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨bs, hd, rfl, rfl, rfl⟩ := h
    exact Step.mapRangeStart (base := bs.1) (start := bs.2) hd
  case case114 =>
    deliver_arm h Step.chanStApply
  case case116 =>
    deliver_arm h Step.selectApply
  case case124 =>
    deliver_arm h Step.rhsStores
  case case131 =>
    deliver_arm h Step.syncStApply
  case case133 =>
    deliver_arm h Step.atomicStApply
  case case145 =>
    -- BUG-005 (L): the pick arm is ONE fun_cases equation now (the
    -- candidates load precedes every split), so done/stop/pick are
    -- separated manually here.
    rename_i keyVar valVar keyTy valTy body base produced start env k'
    simp only [stepFn, bind_eq_ok] at h
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
      rcases hcons : Choices.consumeAt .mapIter (cands.size + (if mand then 0 else 1)) ch
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
          have hb := Choices.consumeAt_fst_lt (site := .mapIter)
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
  case case146 =>
    deliver_arm h Step.storeStep
  case case39 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.chanStFirst hplan
  case case40 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case41 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_pos hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case42 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_neg hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- Sync statements (spec-parity slice 2): the chan handlers' shapes.
  case case58 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.syncStFirst hplan
  case case59 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case60 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- sync/atomic statements (atomics arc wave 1): the sync handlers'
  -- shapes verbatim (entry / two throws / the apply's panic arm).
  case case61 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Step.atomicStFirst hplan
  case case62 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case63 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

  case case6 =>
    -- B4: the ABORT raises the `panic` terminal; no `.ok` step exists.
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨msg, -, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case140 =>
    -- B4: frame exit on the fall-through entry (`stepFrameExit`).
    simp only [stepFn] at h
    exact (stepFrameExit_sound h).1
  case case151 =>
    -- B4: frame exit on the `return` entry — the same function, the twin
    -- rules.
    simp only [stepFn, signalStep_frame] at h
    exact (stepFrameExit_sound h).2

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
      exact ⟨$ch, $ch', by simp [stepFn, stepFrameExit, $hpick:ident, Bind.bind, Except.bind]⟩
    · subst ha
      obtain ⟨h1, h2⟩ := deliver_panic_eq $hdel:ident
      subst h1; subst h2
      exact ⟨$ch, $ch', by simp [stepFn, stepFrameExit, $hpick:ident, Bind.bind, Except.bind]⟩))

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
    -- The mandatory test is pure (B1 stamps); name its value.
    obtain ⟨mand, hmand⟩ : ∃ m, mapIterMandatoryRemains cands start = m := ⟨_, rfl⟩
    have hwidth : idx < cands.size + (if mand then 0 else 1) := by
      cases mand <;> simp <;> omega
    -- The witness stream `[idx]` realizes the pick (at width 1 the pick
    -- is the forced 0 and the stream is untouched — the uniform rule).
    rcases hcons : Choices.consumeAt .mapIter
        (cands.size + (if mand then 0 else 1)) [idx] with ⟨idx', tail⟩
    have hidx' : idx = idx' := by
      have := Choices.consumeAt_fst_singleton (site := .mapIter) hwidth
      rw [hcons] at this
      exact this.symm
    subst hidx'
    refine ⟨[idx], tail, ?_⟩
    simp only [stepFn, hcands, hmand, bind_eq_ok]
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
    have hcons : Choices.consumeAt .mapIter (cands.size + 1) [cands.size]
        = (cands.size, []) := by
      rw [Choices.consumeAt_of_lt (by omega)]
      simp [Choices.consume, Nat.mod_eq_of_lt
        (show cands.size < max 1 (cands.size + 1) by omega)]
    simp only [stepFn, hcands, hmand, bind_eq_ok]
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
    cases k <;> simp_all [stepFn, panicPassthrough, Cont.isGlue, Cont.class, Cont.tail]
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
  -- B4: the signal statements and the table (`signalStmt`/`signal`), and
  -- the frame-exit twins through `stepFrameExit`.
  case signalStmt =>
    rename_i stmt sg env k hsig
    refine ⟨[], [], ?_⟩
    cases stmt <;> simp_all [stepFn, Stmt.signal?]
  case signal =>
    rename_i sg k hstep
    exact ⟨[], [], by simp [stepFn, hstep]⟩
  all_goals
    exact ⟨[], [], by simp_all [stepFn, stepFrameExit, Bind.bind, Except.bind, valueAsBool]⟩

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
  -- blockedSync (spec-parity slice 2): one more deadlock-classified arm.
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
    (h : execStmtLoop fuel σ c ch = .ok (σf, chf)) :
    Steps c σ (.next .stop) σf := by
  fun_induction execStmtLoop fuel σ c ch with
  | case1 =>
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Steps.refl _ _
  | case2 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case3 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case4 => simp [throw, throwThe, MonadExceptOf.throw] at h
  -- blockedSync (spec-parity slice 2): one more deadlock-classified arm.
  | case5 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case6 => simp [throw, throwThe, MonadExceptOf.throw] at h
  | case7 =>
      rename_i ih
      rw [bind_eq_ok] at h
      obtain ⟨⟨c', s', ch'⟩, hstep, hrun⟩ := h
      exact (Steps.single (stepFn_sound hstep)).trans (ih _ _ _ hrun)

theorem execStmt_sound_normal {fuel : Nat} {env : LocalEnv} {σ : ExecState}
    {ch : Choices} {prog : Stmt} {σf : ExecState} {chf : Choices}
    (h : execStmt fuel env σ ch prog = .ok (σf, chf)) :
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
      (r : ExecState × Choices),
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
    {ch : Choices} {prog : Stmt} {r : ExecState × Choices}
    (hle : fuel ≤ fuel')
    (h : execStmt fuel env σ ch prog = .ok r) :
    execStmt fuel' env σ ch prog = .ok r :=
  execStmtLoop_mono fuel fuel' _ _ _ _ hle h

/-- The ABORT is genuinely terminal for the relation, not just for the
driver (B4): no rule's source configuration is an unrecovered chain at
`.stop` — the unwinding rules match a frame, the resume marker, or glue
(`panicPassthrough` refuses `.stop`) — so a reachable abort can never be
discharged by "it still steps" in a progress hypothesis. -/
theorem step_abort_elim {chain : List PanicEntry} {σ : ExecState} {c' : Config}
    {σ' : ExecState} : ¬ Step (.panicking chain .stop) σ c' σ' := by
  intro h
  cases h
  simp [panicPassthrough, Cont.isGlue, Cont.class] at *

/-! The three unwound-`.stop` terminals are ALSO genuinely terminal for
the relation (audit response 2026-08-04; B4: ONE fact now — the signal
table has no `.stop` row, `signalStep_stop`, and the frame-exit rules
match a `.frame`), so no rule applies to a signal at `.stop`. With
`step_abort_elim` these pin `execStmtLoop_ok_or_fuelOut`'s success
disjunct to the one terminal: under a relation-Progress hypothesis
(every reachable configuration is `.next .stop` or steps), a reachable
unwound-`.stop` configuration is a CONTRADICTION — and since B4 the
driver does not even classify it (a signal at `.stop` is a refusal). -/

@[inherit_doc step_abort_elim]
theorem step_signal_stop_elim {sg : Signal} {σ : ExecState} {c' : Config}
    {σ' : ExecState} : ¬ Step (.signal sg .stop) σ c' σ' := by
  intro h
  cases h
  simp_all

/-- THE terminal is relation-terminal (audit fix R6, 2026-09-05): no rule
steps `.next .stop` — every `.next` rule matches a frame. This is the
`val_stuck` obligation of the consumer interface for the one value
`to_val ⟨.next, .stop⟩ = some ()` (`docs/2026-09-05_c-arc-b4-design.md`
§6; `Config.isTerminal`/`Config.terminal` name the shape). -/
theorem step_terminal_elim {σ : ExecState} {c' : Config} {σ' : ExecState} :
    ¬ Step (.next .stop) σ c' σ' := by
  intro h
  cases h


/-! Blocked configurations (channels arc slice 1) are relation-TERMINAL:
no rule steps a blocked goroutine — pairing is the slice-2 pool's job.
Under a relation-Progress hypothesis a reachable blocked configuration
is therefore a contradiction, which keeps
`execStmtLoop_ok_or_fuelOut`'s meaning intact: a proven sequential
Progress still implies the run never deadlocks. -/

@[inherit_doc step_abort_elim]
theorem step_blockedSend_elim {chl : Option Loc} {v : GoValue} {k : Cont}
    {σ : ExecState} {c' : Config} {σ' : ExecState} :
    ¬ Step (.blockedSend chl v k) σ c' σ' := by
  intro h
  cases h

@[inherit_doc step_abort_elim]
theorem step_blockedRecv_elim {chl : Option Loc} {targets : List Assignee}
    {elem : Ty} {env : LocalEnv} {k : Cont} {σ : ExecState} {c' : Config}
    {σ' : ExecState} :
    ¬ Step (.blockedRecv chl targets elem env k) σ c' σ' := by
  intro h
  cases h

@[inherit_doc step_abort_elim]
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
`defaultValue_ok_of_normalize_ok` (padding defaults derivable from
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
/-- Normalization congruence, TYPE layer: along `capCong` values,
normalization results agree up to `capCong` (successes) or panic-class
(errors — normalization never panics, but the statement does not need
that fact), given the same for the `.defined` callback. -/
theorem normalizeValueForTyTy_congr {f : TypeIdx → GoValue → Except Stop GoValue}
    (hf : ∀ i v w, GoValue.capCong v w →
      exceptCong GoValue.capCong (f i v) (f i w)) :
    ∀ (ty : Ty) (v w : GoValue), GoValue.capCong v w →
      exceptCong GoValue.capCong (normalizeValueForTyTy f ty v)
        (normalizeValueForTyTy f ty w) := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v w hcc
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
      simp only [normalizeValueForTyTy, hlen]
      refine exceptCong.ite_congr (fun _ => rfl) fun _ => ?_
      refine exceptCong.map_congr
        (normalizeListWith_congr (fun a b hab => ih a b hab) hl)
        fun as bs habs => ?_
      exact habs
  | leaf ty hne =>
    intro v w hcc
    cases ty with
    | array => exact absurd rfl (hne _ _)
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
    | defined i => exact hf i v w hcc
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
        simp_all [GoValue.capCong, normalizeValueForTyTy, exceptCong,
          Stop.isPanic]
    | pointer _ => exact hcc

set_option maxHeartbeats 3200000 in
/-- Normalization congruence, INDEX layer (by induction on the bound). -/
theorem normalizeValueForTyAt_congr (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx) (v w : GoValue), GoValue.capCong v w →
      exceptCong GoValue.capCong (normalizeValueForTyAt types bound i v)
        (normalizeValueForTyAt types bound i w) := by
  intro bound
  induction bound with
  | zero =>
    intro i v w _
    simp [normalizeValueForTyAt, typeIndexExhausted, exceptCong, Stop.isPanic]
  | succ n ih =>
    intro i v w hcc
    simp only [normalizeValueForTyAt]
    cases hlook : types[i]? with
    | none => exact rfl
    | some e =>
      obtain ⟨name, td⟩ := e
      cases td with
      | defined target => exact normalizeValueForTyTy_congr ih target v w hcc
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
              (fun ty a b hab => normalizeValueForTyTy_congr ih ty a b hab) fields.toList hf)
            fun as bs habs => ?_
          exact ⟨rfl, habs⟩

theorem normalizeValueForTy_congr {σ₁ σ₂ : ExecState}
    (htypes : σ₂.types = σ₁.types) {ty : Ty} {v w : GoValue}
    (hcc : GoValue.capCong v w) :
    exceptCong GoValue.capCong (normalizeValueForTy σ₁ ty v)
      (normalizeValueForTy σ₂ ty w) := by
  unfold normalizeValueForTy
  rw [htypes]
  exact normalizeValueForTyTy_congr (normalizeValueForTyAt_congr _ _) ty v w hcc

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

/-- Padding defaults are derivable from any normalization success, TYPE
layer: if SOME value normalizes at `ty`, `ty` has a default — given the
same for the two `.defined` callbacks. The two walks refuse the same type
shapes (`unsupported`/unknown index/interface-def), so a normalizable type
is defaultable. -/
theorem defaultValueTy_ok_of_normalizeTy_ok
    {g : TypeIdx → GoValue → Except Stop GoValue} {f : TypeIdx → Except Stop GoValue}
    (hgf : ∀ i v r, g i v = .ok r → ∃ d, f i = .ok d) :
    ∀ (ty : Ty) (v r : GoValue),
      normalizeValueForTyTy g ty v = .ok r →
      ∃ d, defaultValueTy f ty = .ok d := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v r h
    by_cases hlen : length = 0
    · exact ⟨.array #[], by
        simp [defaultValueTy, hlen, pure, Except.pure]⟩
    · cases v
      case array values =>
        simp only [normalizeValueForTyTy] at h
        by_cases hsz : (values.size != length) = true
        · rw [if_pos hsz] at h
          simp [Bind.bind, Except.bind, stuck_def] at h
        · rw [if_neg hsz] at h
          have h' : GoValue.array <$> normalizeListWith
              (normalizeValueForTyTy g elem) values.toList = .ok r := h
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
            obtain ⟨d, hd⟩ := ih v₀ head hhead
            exact ⟨.array (Array.replicate length d), by
              simp [defaultValueTy, hlen, hd, Bind.bind, Except.bind, pure,
                Except.pure]⟩
      all_goals simp [normalizeValueForTyTy] at h
  | leaf ty hne =>
    intro v r h
    cases ty with
    | array => exact absurd rfl (hne _ _)
    | int kind =>
      exact ⟨.int 0 kind, by simp [defaultValueTy, pure, Except.pure]⟩
    | float kind =>
      exact ⟨.float 0 kind, by simp [defaultValueTy, pure, Except.pure]⟩
    | bool =>
      exact ⟨.bool false, by simp [defaultValueTy, pure, Except.pure]⟩
    | string =>
      exact ⟨.string GoString.empty, by
        simp [defaultValueTy, pure, Except.pure]⟩
    | slice elem =>
      exact ⟨.slice { base := none, offset := 0, len := 0, cap := 0 }, by
        simp [defaultValueTy, pure, Except.pure]⟩
    | chan _ _ =>
      exact ⟨.chan { base := none }, by
        simp [defaultValueTy, pure, Except.pure]⟩
    | sync kind =>
      exact ⟨.syncData kind.zero, by
        simp [defaultValueTy, pure, Except.pure]⟩
    | map kt vt =>
      exact ⟨.map { base := none }, by
        simp [defaultValueTy, pure, Except.pure]⟩
    | pointer _ =>
      exact ⟨.nil, by simp [defaultValueTy, pure, Except.pure]⟩
    | funcType _ _ _ =>
      exact ⟨.nil, by simp [defaultValueTy, pure, Except.pure]⟩
    | interface _ =>
      exact ⟨.nil, by simp [defaultValueTy, pure, Except.pure]⟩
    | unsupported _ => simp [normalizeValueForTyTy] at h
    | defined i => exact hgf i v r h

/-- Padding defaults are derivable from any normalization success, INDEX
layer: both descents at the same bound. -/
theorem defaultValueAt_ok_of_normalizeAt_ok (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx) (v r : GoValue),
      normalizeValueForTyAt types bound i v = .ok r →
      ∃ d, defaultValueAt types bound i = .ok d := by
  intro bound
  induction bound with
  | zero => intro i v r h; simp [normalizeValueForTyAt, typeIndexExhausted] at h
  | succ n ih =>
    intro i v r h
    simp only [normalizeValueForTyAt] at h
    cases hlook : types[i]? with
    | none => rw [hlook] at h; simp at h
    | some e =>
      rw [hlook] at h
      obtain ⟨name, td⟩ := e
      cases td with
      | defined target =>
        obtain ⟨d, hd⟩ := defaultValueTy_ok_of_normalizeTy_ok
          (fun i v r hh => ih i v r hh) target v r h
        exact ⟨d, by simp [defaultValueAt, hlook, hd]⟩
      | opaqueDecl _ => simp at h
      | interfaceDef _ => simp at h
      | struct fields =>
        have h' : normalizeStructValueWith
            (normalizeValueForTyTy (normalizeValueForTyAt types n))
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
                simp [defaultValueAt, hlook, h3, defaultFieldsWith,
                  pure, Except.pure, Functor.map, Except.map]⟩
            · rw [if_neg hesc] at h'
              simp [Bind.bind, Except.bind, stuck_def] at h'
          · rw [if_neg hty] at h'
            by_cases hsz : (fieldsValue.size != fields.size) = true
            · rw [if_pos hsz] at h'
              simp [Bind.bind, Except.bind, stuck_def] at h'
            · rw [if_neg hsz] at h'
              have h'' : GoValue.struct name <$> normalizeFieldsWith
                  (normalizeValueForTyTy (normalizeValueForTyAt types n)) fields.toList
                  fieldsValue.toList = .ok r := h'
              rw [map_eq_ok] at h''
              obtain ⟨arr, harr, _⟩ := h''
              suffices haux : ∀ (fds : List FieldDef)
                  (vals : List (String × GoValue))
                  (out : Array (String × GoValue)),
                  normalizeFieldsWith
                      (normalizeValueForTyTy (normalizeValueForTyAt types n)) fds vals
                    = .ok out →
                  vals.length = fds.length →
                  ∃ ds, defaultFieldsWith
                    (defaultValueTy (defaultValueAt types n)) fds = .ok ds by
                have hlen : fieldsValue.toList.length = fields.toList.length :=
                  (by simpa [bne_iff_ne] using hsz :
                    fieldsValue.size = fields.size)
                obtain ⟨ds, hds⟩ := haux fields.toList fieldsValue.toList arr
                  harr hlen
                exact ⟨.struct name ds, by
                  simp [defaultValueAt, hlook, hds, map_eq_ok]⟩
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
                    have hnorm' : (normalizeValueForTyTy (normalizeValueForTyAt types n) fd.typ pv >>=
                        fun head =>
                          normalizeFieldsWith
                              (normalizeValueForTyTy (normalizeValueForTyAt types n))
                              fdRest valRest >>= fun tail =>
                            pure (#[(fd.name, head)] ++ tail)) = .ok out := hnorm
                    rw [bind_eq_ok] at hnorm'
                    obtain ⟨head, hhead, hrest⟩ := hnorm'
                    rw [bind_eq_ok] at hrest
                    obtain ⟨tail, htail, _⟩ := hrest
                    obtain ⟨d, hd⟩ := defaultValueTy_ok_of_normalizeTy_ok
                      (fun i v r hh => ih i v r hh) fd.typ pv head hhead
                    obtain ⟨ds, hds⟩ := ihf valRest tail htail
                      (by simpa using hlen)
                    exact ⟨#[(fd.name, d)] ++ ds, by
                      simp [defaultFieldsWith, hd, hds, Bind.bind, Except.bind,
                        pure, Except.pure]⟩
        all_goals exact absurd h' (by simp [normalizeStructValueWith])

/-- The wrapper form: a normalization success at `ty` yields a default. -/
theorem defaultValue_ok_of_normalize_ok {σ : ExecState} {ty : Ty} {v r : GoValue}
    (h : normalizeValueForTy σ ty v = .ok r) : ∃ d, defaultValue σ ty = .ok d := by
  unfold normalizeValueForTy at h
  unfold defaultValue
  exact defaultValueTy_ok_of_normalizeTy_ok
    (fun i v r hh => defaultValueAt_ok_of_normalizeAt_ok _ _ i v r hh) ty v r h

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
      exact defaultValue_ok_of_normalize_ok hnv
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

/-- A `.picks` outcome carries ≥ 2 commits — one per ready clause, and
the `[]`/`[c]` readiness lists take `applySelectCore`'s other arms — so
`selectConsult?`'s `some` is exactly a POPPING consult under the uniform
rule (G-U audit fix L6; the twin of `one_lt_appendSpillWidth` and
`arrivalCases_multi_length`). -/
theorem applySelectCore_picks_length {σ : ExecState}
    {clauses : List (SelectClauseHead × Stmt)} {default? : Option Stmt}
    {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {commits : List (EvClause × Sum (Config × ExecState) String)}
    (h : applySelectCore σ clauses default? vs env k = .ok (.picks commits)) :
    1 < commits.length := by
  unfold applySelectCore at h
  simp only [Bind.bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h <;> cases h
      · split at h <;> cases h
      · rename_i hnil hsingle
        split at h
        · cases h
        · rename_i cs hmap
          simp only [pure, Except.pure, Except.ok.injEq, SelectOutcome.picks.injEq] at h
          subst h
          rw [mapM_ok_length hmap]
          -- the ready list fell through `[]` and `[c]`: length ≥ 2
          have key : ∀ l : List EvClause, (l = [] → False) → (∀ c, l = [c] → False)
              → 1 < l.length := by
            intro l h0 h1
            cases l with
            | nil => exact absurd rfl h0
            | cons a t =>
              cases t with
              | nil => exact absurd rfl (h1 a)
              | cons b t' => simp
          exact key _ hnil hsingle

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
              rcases hcons : Choices.consumeAt .l2Entry (b :: rest).length ch
                with ⟨idx, ch'⟩
              have hlt : idx < (b :: rest).length := by
                have := Choices.consumeAt_fst_lt (site := .l2Entry) (ch := ch)
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
  simp only [stepFn, hcands, Bind.bind, Except.bind]
  rw [hmand, if_neg hne]
  rcases hcons : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch
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
    cases k <;> simp_all [stepFn, panicPassthrough, Cont.isGlue, Cont.class, Cont.tail]
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
    simp [stepFn, stepFrameExit, hp, Bind.bind, Except.bind]
  case frameDeferReturn targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, stepFrameExit, hp, Bind.bind, Except.bind]
  -- B4: the signal statements and the table.
  case signalStmt stmt sg env k hsig =>
    cases stmt <;> simp_all [stepFn, Stmt.signal?]
  case signal sg k hstep =>
    simp [stepFn, hstep]
  case panicFrameDefer chain targets tenv results fid captured args ds k w r ch₀ ch₁ hpick hdel =>
    obtain ⟨r₂, ch₂, hp⟩ := enterFramePick_any_ch hpick ch
    (try simp only [List.append_assoc] at hp)
    simp [stepFn, hp, Bind.bind, Except.bind]
  all_goals simp_all [stepFn, stepFrameExit, Bind.bind, Except.bind, valueAsBool]

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
run — under EVERY choice stream — returns `.ok` at the one terminal or
`.error .fuelOut`; never stuck, never an unrecovered panic, never
unsupported/internal. Fuel induction carrying reachability (to keep the
progress hypothesis applicable) and `MachineWf` (via
`stepFn_preserves_wf`); the abort and the signals at `.stop` are
excluded by progress + `step_abort_elim`/`step_signal_stop_elim` — and
since B4 the driver classifies NEITHER as a completion (a signal at
`.stop` is a refusal `stepFn` raises), so the former audit-response
concern (2026-08-04: unconstrained `.returned`/`.broke`/`.continued`
completions silently accepted) has no shape left to arise in. -/
theorem execStmtLoop_ok_or_fuelOut {σ₀ : ExecState} {c₀ : Config}
    (hprog : ∀ (c' : Config) (σ' : ExecState), Steps c₀ σ₀ c' σ' →
      c' = .next .stop ∨ ∃ (c'' : Config) (σ'' : ExecState), Step c' σ' c'' σ'')
    (hwf : MachineWf σ₀ c₀) :
    ∀ (fuel : Nat) (ch : Choices),
      (∃ (σf : ExecState) (ch' : Choices),
        execStmtLoop fuel σ₀ c₀ ch = .ok (σf, ch'))
      ∨ execStmtLoop fuel σ₀ c₀ ch = .error .fuelOut := by
  suffices haux : ∀ (fuel : Nat) (c : Config) (σ : ExecState),
      Steps c₀ σ₀ c σ → MachineWf σ c → ∀ ch : Choices,
      (∃ (σf : ExecState) (ch' : Choices),
        execStmtLoop fuel σ c ch = .ok (σf, ch'))
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
      · rename_i harm1 harm2 harm3 harm4 harm5
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

/-! ### Panic-freeness of the store path (wave-(iii) audit fix F1, 2026-09-04)

The consumption theorem's `some` half first carried a second disjunct — "a
delivered panic AFTER the pop restores the pre-apply stream" — for two
sites. Both are REFUTED here: a TRY head's apply never raises a recoverable
panic (`applyTryLock_noPanic`), and a spilling append whose target is a
root cell (the frontend's hoisted temp — `Config.appendTargetLocal`) never
does either (`storeLoc_base_noPanic`, `buildAppendBackingValue_noPanic`).
The only panic sources on the store path are `arrayGet`/`arraySet`'s
index-out-of-range (unreachable through a PATH the machine just loaded, and
absent at a root cell); normalization and default values refuse but never
panic. -/

/-- `x` is not a recoverable panic. -/
def NoPanic {α : Type} (x : Except Stop α) : Prop := ∀ msg, x ≠ .error (Stop.panic msg)

theorem NoPanic.ok {α : Type} (a : α) : NoPanic (Except.ok a : Except Stop α) :=
  fun _ h => by cases h
theorem NoPanic.pure {α : Type} (a : α) : NoPanic (pure a : Except Stop α) :=
  fun _ h => by cases h
theorem NoPanic.stuck {α : Type} (m : String) : NoPanic (stuck m : Except Stop α) :=
  fun _ h => by cases h
theorem NoPanic.unsupported {α : Type} (m : String) : NoPanic (unsupported m : Except Stop α) :=
  fun _ h => by cases h
theorem NoPanic.internal {α : Type} (m : String) :
    NoPanic (throw (Stop.internal m) : Except Stop α) :=
  fun _ h => by simp [throw, throwThe, MonadExceptOf.throw] at h
theorem NoPanic.bind {α β : Type} {x : Except Stop α} {f : α → Except Stop β}
    (hx : NoPanic x) (hf : ∀ a, NoPanic (f a)) : NoPanic (x >>= f) := by
  intro msg h
  cases x with
  | error e =>
    simp only [Bind.bind, Except.bind] at h
    exact hx msg (congrArg (fun e => (Except.error e : Except Stop α)) (Except.error.inj h))
  | ok a => simp only [Bind.bind, Except.bind] at h; exact hf a msg h
theorem NoPanic.map {α β : Type} {x : Except Stop α} (g : α → β) (hx : NoPanic x) :
    NoPanic (g <$> x) := by
  intro msg h
  cases x with
  | error e =>
    simp only [Functor.map, Except.map] at h
    exact hx msg (congrArg (fun e => (Except.error e : Except Stop α)) (Except.error.inj h))
  | ok a => simp [Functor.map, Except.map] at h
theorem NoPanic.ite {α : Type} {c : Prop} [Decidable c] {a b : Except Stop α}
    (ha : NoPanic a) (hb : NoPanic b) : NoPanic (if c then a else b) := by
  split <;> assumption
theorem NoPanic.of_ok {α : Type} {x : Except Stop α} {a : α} (h : x = .ok a) : NoPanic x := by
  subst h; exact NoPanic.ok a

/-- Discharge a `NoPanic` goal over a do-pipeline of the combinators above. -/
macro "no_panic" : tactic =>
  `(tactic| repeat first
    | exact NoPanic.ok _
    | exact NoPanic.pure _
    | exact NoPanic.stuck _
    | exact NoPanic.unsupported _
    | exact NoPanic.internal _
    | assumption
    | apply NoPanic.ite
    | apply NoPanic.map
    | (apply NoPanic.bind; rotate_left)
    | intro _)

theorem normalizeListWith_noPanic {f : GoValue → Except Stop GoValue}
    (hf : ∀ v, NoPanic (f v)) : ∀ l, NoPanic (normalizeListWith f l)
  | [] => by unfold normalizeListWith; exact NoPanic.pure _
  | v :: rest => by
      unfold normalizeListWith
      exact NoPanic.bind (hf v) fun _ =>
        NoPanic.bind (normalizeListWith_noPanic hf rest) fun _ => NoPanic.pure _

theorem normalizeFieldsWith_noPanic {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ t v, NoPanic (f t v)) :
    ∀ fs vs, NoPanic (normalizeFieldsWith f fs vs)
  | [], vs => by intro msg h; simp [normalizeFieldsWith] at h
  | _ :: _, [] => by intro msg h; simp [normalizeFieldsWith] at h
  | field :: fr, (af, v) :: vr => by
      unfold normalizeFieldsWith
      (try dsimp only)
      refine NoPanic.ite ?_ ?_
      · exact NoPanic.bind (NoPanic.stuck _) fun _ => NoPanic.bind (hf _ _) fun _ =>
          NoPanic.bind (normalizeFieldsWith_noPanic hf fr vr) fun _ => NoPanic.pure _
      · exact NoPanic.bind (hf _ _) fun _ =>
          NoPanic.bind (normalizeFieldsWith_noPanic hf fr vr) fun _ => NoPanic.pure _

theorem normalizeStructValueWith_noPanic {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ t v, NoPanic (f t v)) (name : TypeId) (fields : Array FieldDef) :
    ∀ v, NoPanic (normalizeStructValueWith f name fields v) := by
  intro v
  cases v <;> simp only [normalizeStructValueWith] <;> (try exact NoPanic.stuck _)
  (try dsimp only)
  split
  · split
    · exact NoPanic.pure _
    · exact NoPanic.stuck _
  · (try dsimp only)
    split
    · exact NoPanic.stuck _
    · (try dsimp only)
      exact NoPanic.map _ (normalizeFieldsWith_noPanic hf _ _)

/-- The normalizer's TYPE layer never panics, given the same for the
`.defined` callback. -/
theorem normalizeValueForTyTy_noPanic {f : TypeIdx → GoValue → Except Stop GoValue}
    (hf : ∀ i v, NoPanic (f i v)) :
    ∀ (ty : Ty) (v : GoValue), NoPanic (normalizeValueForTyTy f ty v) := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v
    cases v <;> simp only [normalizeValueForTyTy]
    all_goals (try exact NoPanic.stuck _)
    all_goals (try dsimp only)
    all_goals (try split)
    all_goals (try dsimp only)
    all_goals first
      | exact NoPanic.map _ (normalizeListWith_noPanic (fun v => ih v) _)
      | exact NoPanic.bind (NoPanic.stuck _) fun _ =>
          NoPanic.map _ (normalizeListWith_noPanic (fun v => ih v) _)
  | leaf ty hne =>
    -- `ty` stays a variable: the match splits on every arm, and the
    -- array arms are dismissed by `hne`.
    intro v
    unfold normalizeValueForTyTy
    split
    all_goals (try dsimp only)
    all_goals (try split)
    all_goals (try dsimp only)
    all_goals first
      | exact NoPanic.pure _
      | exact NoPanic.ok _
      | exact NoPanic.stuck _
      | exact NoPanic.unsupported _
      | exact hf _ _
      | exact absurd rfl (hne _ _)

/-- The normalizer's INDEX layer never panics (induction on the bound). -/
theorem normalizeValueForTyAt_noPanic (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx) (v : GoValue),
      NoPanic (normalizeValueForTyAt types bound i v) := by
  intro bound
  induction bound with
  | zero =>
    intro i v
    simp only [normalizeValueForTyAt, typeIndexExhausted]
    exact NoPanic.unsupported _
  | succ n ih =>
    intro i v
    unfold normalizeValueForTyAt
    split
    · exact normalizeStructValueWith_noPanic
        (fun t v => normalizeValueForTyTy_noPanic (fun i v => ih i v) t v) _ _ _
    · exact normalizeValueForTyTy_noPanic (fun i v => ih i v) _ _
    · exact NoPanic.unsupported _
    · exact NoPanic.unsupported _
    · exact NoPanic.unsupported _

theorem normalizeValueForTy_noPanic (s : ExecState) (ty : Ty) (v : GoValue) :
    NoPanic (normalizeValueForTy s ty v) := by
  unfold normalizeValueForTy
  exact normalizeValueForTyTy_noPanic (fun i v => normalizeValueForTyAt_noPanic _ _ i v) ty v

theorem defaultFieldsWith_noPanic {f : Ty → Except Stop GoValue}
    (hf : ∀ t, NoPanic (f t)) : ∀ fs, NoPanic (defaultFieldsWith f fs)
  | [] => by unfold defaultFieldsWith; exact NoPanic.pure _
  | field :: rest => by
      unfold defaultFieldsWith
      exact NoPanic.bind (hf _) fun _ =>
        NoPanic.bind (defaultFieldsWith_noPanic hf rest) fun _ => NoPanic.pure _

/-- The zero value's TYPE layer never panics, given the same for the
`.defined` callback. -/
theorem defaultValueTy_noPanic {f : TypeIdx → Except Stop GoValue}
    (hf : ∀ i, NoPanic (f i)) :
    ∀ (ty : Ty), NoPanic (defaultValueTy f ty) := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    simp only [defaultValueTy]
    split
    · exact NoPanic.pure _
    · exact NoPanic.bind ih fun _ => NoPanic.pure _
  | leaf ty hne =>
    unfold defaultValueTy
    split
    all_goals (try dsimp only)
    all_goals first
      | exact NoPanic.pure _
      | exact NoPanic.ok _
      | exact NoPanic.unsupported _
      | exact hf _
      | exact absurd rfl (hne _ _)

/-- The zero value's INDEX layer never panics (induction on the bound). -/
theorem defaultValueAt_noPanic (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx), NoPanic (defaultValueAt types bound i) := by
  intro bound
  induction bound with
  | zero =>
    intro i
    simp only [defaultValueAt, typeIndexExhausted]
    exact NoPanic.unsupported _
  | succ n ih =>
    intro i
    unfold defaultValueAt
    split
    · exact NoPanic.map _ (defaultFieldsWith_noPanic (fun t => defaultValueTy_noPanic ih t) _)
    · exact defaultValueTy_noPanic ih _
    · exact NoPanic.unsupported _
    · exact NoPanic.unsupported _
    · exact NoPanic.unsupported _

theorem defaultValue_noPanic (s : ExecState) (ty : Ty) : NoPanic (defaultValue s ty) := by
  unfold defaultValue
  exact defaultValueTy_noPanic (fun i => defaultValueAt_noPanic _ _ i) ty

/-- A loop whose every body step is panic-free is panic-free. -/
theorem forIn_noPanic {α β : Type} {body : α → β → Except Stop (ForInStep β)}
    (hb : ∀ a b, NoPanic (body a b)) :
    ∀ (l : List α) (acc : β), NoPanic (forIn l acc body)
  | [], acc => by rw [List.forIn_nil]; exact NoPanic.pure _
  | a :: as, acc => by
      rw [List.forIn_cons]
      refine NoPanic.bind (hb a acc) fun r => ?_
      cases r with
      | done b => exact NoPanic.pure _
      | yield b => exact forIn_noPanic hb as b

theorem buildAppendBackingValue_noPanic (s : ExecState) (elem : Ty)
    (oldValues elemValues : Array GoValue) (newCap : Nat) :
    NoPanic (buildAppendBackingValue s elem oldValues elemValues newCap) := by
  unfold buildAppendBackingValue
  dsimp only
  rw [← Array.forIn_toList]
  refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun values => ?_
  · exact NoPanic.bind (normalizeValueForTy_noPanic _ _ _) fun _ => NoPanic.pure _
  · refine NoPanic.ite ?_ ?_
    · refine NoPanic.bind (NoPanic.stuck _) fun _ => ?_
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun _ => NoPanic.pure _
      exact NoPanic.bind (defaultValue_noPanic _ _) fun _ => NoPanic.pure _
    · rw [Std.Legacy.Range.forIn_eq_forIn_range']
      refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun _ => NoPanic.pure _
      exact NoPanic.bind (defaultValue_noPanic _ _) fun _ => NoPanic.pure _

theorem StructFields.set_noPanic (fields : Array (String × GoValue)) (needle : String)
    (value : GoValue) : NoPanic (StructFields.set fields needle value) := by
  unfold StructFields.set
  dsimp only
  rw [← Array.forIn_toList]
  refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun _ => ?_
  · obtain ⟨name, old⟩ := a
    (try dsimp only)
    split <;> exact NoPanic.pure _
  · (try dsimp only)
    exact NoPanic.ite (NoPanic.pure _) (NoPanic.stuck _)

/-- A root-cell store never panics: the cell exists or the store is
`.internal`, and normalization at the cell's type refuses but never panics. -/
theorem storeLoc_base_noPanic (s : ExecState) (a : Addr) (v : GoValue) :
    NoPanic (storeLoc s (.base a) v) := by
  unfold storeLoc ExecState.updateCell
  split
  · refine NoPanic.bind ?_ fun _ => NoPanic.pure _
    dsimp only
    split
    · exact NoPanic.bind (normalizeValueForTy_noPanic _ _ _) fun _ => NoPanic.pure _
    · exact NoPanic.stuck _
    · exact NoPanic.stuck _
  · exact NoPanic.internal _

/-- An in-range read makes the same index writable. -/
theorem arraySet_ok_of_arrayGet_ok {vs : Array GoValue} {i : Int} {x : GoValue}
    (h : arrayGet vs i = .ok x) (v : GoValue) : ∃ vs', arraySet vs i v = .ok vs' := by
  unfold arrayGet at h
  unfold arraySet
  cases hj : arrayIndexNat vs i with
  | error e => (try rw [hj] at h); simp [Bind.bind, Except.bind] at h
  | ok j =>
    (try rw [hj] at h)
    simp only [Bind.bind, Except.bind] at h ⊢
    cases hg : vs[j]? with
    | none =>
      (try rw [hg] at h)
      simp only [indexOutOfRangePanic, GoLean.GoCore.panic, throw, throwThe, MonadExceptOf.throw] at h
      split at h <;> cases h
    | some w => (try rw [hg]); exact ⟨_, rfl⟩

/-- A store through a PATH the machine can load never panics: the only
panic on the store path is `arraySet`'s bounds check, and the load's
success puts the index in range. -/
theorem storeLoc_noPanic_of_loadLoc_ok (s : ExecState) :
    ∀ (loc : Loc) {v₀ : GoValue}, loadLoc s loc = .ok v₀ → ∀ v, NoPanic (storeLoc s loc v)
  | .base a, _, _, v => storeLoc_base_noPanic s a v
  | .field base typeId fieldName, v₀, h, v => by
      unfold loadLoc at h
      unfold storeLoc
      cases hb : loadLoc s base with
      | error e => (try rw [hb] at h); simp [Bind.bind, Except.bind] at h
      | ok w =>
        (try rw [hb] at h)
        simp only [Bind.bind, Except.bind] at h ⊢
        cases w <;> (try (simp [stuck, throw, throwThe, MonadExceptOf.throw] at h; done))
        dsimp only
        refine NoPanic.ite ?_ ?_
        · -- the tag-mismatch refusal heads the branch: a `stuck`, never a panic
          intro msg hm
          simp only [stuck, throw, throwThe, MonadExceptOf.throw] at hm <;> cases hm
        · exact NoPanic.bind (StructFields.set_noPanic _ _ _) fun updated =>
            storeLoc_noPanic_of_loadLoc_ok s base hb _
  | .index base index, v₀, h, v => by
      unfold loadLoc at h
      unfold storeLoc
      cases hb : loadLoc s base with
      | error e => (try rw [hb] at h); simp [Bind.bind, Except.bind] at h
      | ok w =>
        (try rw [hb] at h)
        simp only [Bind.bind, Except.bind] at h ⊢
        cases w <;> (try (simp [stuck, throw, throwThe, MonadExceptOf.throw] at h; done))
        dsimp only at h ⊢
        obtain ⟨vs', hset⟩ := arraySet_ok_of_arrayGet_ok h v
        rw [hset]
        exact storeLoc_noPanic_of_loadLoc_ok s base hb _

theorem tryAcquire_noPanic (op : SyncOp) (pre : SyncPrim) : NoPanic (tryAcquire op pre) := by
  unfold tryAcquire
  split <;> first | exact NoPanic.pure _ | exact NoPanic.stuck _ | exact NoPanic.internal _

theorem enterRecvTargets_noPanic (s : ExecState) (targets : List Assignee) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k : Cont) :
    NoPanic (enterRecvTargets s targets vals body env k) := by
  unfold enterRecvTargets
  split <;> first | exact NoPanic.pure _ | exact NoPanic.stuck _

theorem tryDeliver_noPanic (b : Bool) (s : ExecState) (targets : List Assignee)
    (env : LocalEnv) (k : Cont) : NoPanic (tryDeliver b s targets env k) := by
  unfold tryDeliver
  split
  · exact NoPanic.pure _
  · exact NoPanic.bind (enterRecvTargets_noPanic _ _ _ _ _ _) fun _ => NoPanic.pure _

/-- **Site 2 of the retired disjunct**: a TRY head's apply never raises a
recoverable panic — `tryAcquire` refuses at most, the acquired cell is
stored through the location the apply just READ (`syncCell`), and the
result delivery is an `.evalE` entry or a refusal. -/
theorem applyTryLock_noPanic {s : ExecState} {loc : Loc} {pre : SyncPrim}
    (hcell : syncCell s loc = .ok pre) (op : SyncOp) (spurious : Bool)
    (targets : List Assignee) (env : LocalEnv) (k : Cont) :
    NoPanic (applyTryLock s op loc pre spurious targets env k) := by
  have hload : ∃ w, loadLoc s loc = .ok w := by
    unfold syncCell at hcell
    cases hl : loadLoc s loc with
    | error e => rw [hl] at hcell; simp [Bind.bind, Except.bind] at hcell
    | ok w => exact ⟨w, rfl⟩
  obtain ⟨w, hw⟩ := hload
  unfold applyTryLock
  refine NoPanic.bind (tryAcquire_noPanic _ _) fun r => ?_
  cases r with
  | none => exact tryDeliver_noPanic _ _ _ _ _
  | some post =>
    refine NoPanic.bind (storeLoc_noPanic_of_loadLoc_ok s loc hw _) fun _ => ?_
    exact NoPanic.ite (tryDeliver_noPanic _ _ _ _ _) (tryDeliver_noPanic _ _ _ _ _)

/-! ### The per-site stream lemmas behind `stepFn_consumption` (B8) -/

theorem except_bind_ok {ε α β : Type} (a : α)
    (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- Stream pass-through of a two-stage `Except` pipeline ending in a
`(·, choices)` pair — the shape of `applyStmtOp`'s append branches. -/
theorem bind_pair_stream {α : Type} (T : Except Stop α)
    (g : α → Except Stop ExecState) (ch : Choices) :
    (do let a ← T; let x ← g a;
        pure ((x, ch) : ExecState × Choices))
      = (match (do let a ← T; let x ← g a;
                   pure ((x, ([] : Choices)) : ExecState × Choices)) with
         | .ok (s', _) => .ok (s', ch)
         | .error e => .error e) := by
  cases T with
  | error e => rfl
  | ok a =>
    simp only [Bind.bind, Except.bind]
    cases g a with
    | error e => rfl
    | ok x => rfl

/-- A `.done` readiness analysis: `applySelect` passes the stream through. -/
theorem applySelect_done_stream {σ : ExecState} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {c₁ : Config} {s₁ : ExecState} {cl? : Option EvClause}
    (h : applySelectCore σ clauses default? vs env k = .ok (.done c₁ s₁ cl?)) (ch : Choices) :
    applySelect σ clauses default? vs env k ch = .ok (c₁, s₁, ch, cl?) := by
  simp [applySelect, h, Bind.bind, Except.bind]

/-- A multi-ready analysis: `applySelect`'s stream is the L2 pop, and the
outcome depends on the stream only through the pick. -/
theorem applySelect_picks_stream {σ : ExecState} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {commits : List (EvClause × Sum (Config × ExecState) String)}
    (h : applySelectCore σ clauses default? vs env k = .ok (.picks commits)) (ch : Choices) :
    applySelect σ clauses default? vs env k ch =
      (match commits[(Choices.consumeAt .l2Entry commits.length ch).1]? with
       | some (cl, .inl (c', s')) => .ok (c', s', (Choices.consumeAt .l2Entry commits.length ch).2, some cl)
       | some (cl, .inr msg) =>
           .ok (.panicking [panicEntry msg] k, σ, (Choices.consumeAt .l2Entry commits.length ch).2, some cl)
       | none => .error (.internal "select ready-clause pick out of range")) := by
  simp only [applySelect, h, Bind.bind, Except.bind]
  rfl

/-- An error of the analysis is an error of the apply. -/
theorem applySelect_error_stream {σ : ExecState} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont} {e : Stop}
    (h : applySelectCore σ clauses default? vs env k = .error e) (ch : Choices) :
    applySelect σ clauses default? vs env k ch = .error e := by
  simp [applySelect, h, Bind.bind, Except.bind]

/-- A TRY head's apply, in terms of the site's pop. -/
theorem applySyncOp_try_stream {σ : ExecState} {op : SyncOp} {targets : List Assignee}
    {av : GoValue} {loc : Loc} {pre : SyncPrim} {env : LocalEnv} {k : Cont}
    (ht : op.tryTargets? = some targets) (hl : valueAsLoc av = .ok loc)
    (hc : syncCell σ loc = .ok pre) (ch : Choices) :
    applySyncOp σ ch op [av] env k =
      (applyTryLock σ op loc pre
        ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch).1 == 1) targets env k).map
        fun p => (p.1, p.2, (Choices.consumeAt .tryLock (tryLockWidth op pre) ch).2) := by
  simp only [applySyncOp, ht, hl, hc, Bind.bind, Except.bind, Except.map]
  cases applyTryLock σ op loc pre
      ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch).1 == 1) targets env k <;> rfl

/-- A TRY head whose consult does not pop (`tryLockConsult? = none` at a
resolvable receiver) is stream-oblivious: width 1 pops nothing and forces
pick 0. -/
theorem applySyncOp_try_nopop {σ : ExecState} {op : SyncOp} {targets : List Assignee}
    {av : GoValue} {loc : Loc} {pre : SyncPrim} {env : LocalEnv} {k : Cont}
    (ht : op.tryTargets? = some targets) (hl : valueAsLoc av = .ok loc)
    (hc : syncCell σ loc = .ok pre) (hw : tryLockWidth op pre ≤ 1) (ch : Choices) :
    applySyncOp σ ch op [av] env k =
      (applyTryLock σ op loc pre false targets env k).map fun p => (p.1, p.2, ch) := by
  rw [applySyncOp_try_stream ht hl hc ch, Choices.consumeAt_le_one hw]
  rfl

/-- A two-stage `Except` pipeline ending in a `(·, ch)` pair is the
pipeline's value paired with `ch`. -/
theorem bind_pair_map {α : Type} (T : Except Stop α)
    (g : α → Except Stop ExecState) (ch : Choices) :
    (do let a ← T; let x ← g a;
        pure ((x, ch) : ExecState × Choices))
      = (do let a ← T; g a).map fun s' => (s', ch) := by
  cases T with
  | error e => rfl
  | ok a =>
    simp only [Bind.bind, Except.bind]
    cases g a with
    | error e => rfl
    | ok x => rfl

/-- The spill decision agrees with the arm: at `appendSpill? = none` the
apply is stream-oblivious — a state result `r` (in place, a refusal or
the R16 panic before the consult) paired with the untouched stream. -/
theorem applyStmtOp_appendSlice_nospill {σ : ExecState} {elem : Ty} {nt : Nat}
    {vs : List GoValue} (hw : appendSpill? σ elem vs = none) :
    ∃ r : Except Stop ExecState, ∀ ch : Choices,
      applyStmtOp σ ch (.appendSlice elem) nt vs = r.map fun s' => (s', ch) := by
  match vs, hw with
  | [], _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | [_], _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | [_, _], _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | _ :: _ :: _ :: _ :: _, _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | [tv, sliceV, elemsV], hw =>
    unfold appendSpill? at hw
    unfold applyStmtOp
    dsimp only
    cases hsl : valueAsSlice sliceV with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok slice =>
    simp only [except_bind_ok]
    cases hel : valueAsSlice elemsV with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok elems =>
    simp only [except_bind_ok]
    cases hv1 : validateSlice slice with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok u1 =>
    simp only [except_bind_ok]
    cases hv2 : validateSlice elems with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok u2 =>
    simp only [except_bind_ok]
    cases hvis : sliceVisibleValues σ elems with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok elemValues =>
    simp only [except_bind_ok]
    cases htl : valueAsLoc tv with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok tloc =>
    simp only [except_bind_ok]
    simp only [hsl, hel, hv1, hv2, hvis, htl] at hw
    by_cases hcap : slice.len + elemValues.size ≤ slice.cap
    · simp only [if_pos hcap]
      exact ⟨_, fun ch => bind_pair_map _ _ ch⟩
    · simp only [if_neg hcap]
      cases hts : tySizeBytes σ.types elem with
      | error e => exact ⟨.error e, fun _ => rfl⟩
      | ok elemSize =>
      simp only [except_bind_ok]
      simp only [if_neg hcap, hts] at hw
      split
      · exact ⟨.error (.panic "runtime error: growslice: len out of range"), fun _ => rfl⟩
      · rename_i hr16
        simp only [if_neg hr16] at hw
        cases hold : sliceVisibleValues σ slice with
        | error e => exact ⟨.error e, fun _ => rfl⟩
        | ok oldValues => rw [hold] at hw; cases hw

/-- **The spill's pop**: at `appendSpill? = some w` the arm reaches the
consult and the apply is a function `g` of the `appendSpill` pick alone,
its stream the site's pop at bound `w` — a spilling append depends on the
stream only through that pick. Moreover `g` never raises a recoverable
panic when the target operand addresses a ROOT cell (the frontend's
hoisted temp, `Config.appendTargetLocal`): the grown backing is built by
panic-free normalization and stored into an existing or `.internal`-
refused cell (audit fix F1 — the refutation of the retired disjunct). -/
theorem applyStmtOp_appendSlice_spill {σ : ExecState} {elem : Ty} {nt : Nat}
    {vs : List GoValue} {w : Nat} (hw : appendSpill? σ elem vs = some w) :
    ∃ g : Nat → Except Stop ExecState,
      (∀ ch : Choices,
        applyStmtOp σ ch (.appendSlice elem) nt vs
          = (g (Choices.consumeAt .appendSpill w ch).1).map
              fun s' => (s', (Choices.consumeAt .appendSpill w ch).2))
      ∧ (∀ a rest, vs = .addr (.base a) :: rest → ∀ pick, NoPanic (g pick)) := by
  match vs, hw with
  | [tv, sliceV, elemsV], hw =>
    unfold appendSpill? at hw
    cases hsl : valueAsSlice sliceV with
    | error e => simp [hsl] at hw
    | ok slice =>
    cases hel : valueAsSlice elemsV with
    | error e => simp [hsl, hel] at hw
    | ok elems =>
    cases hv1 : validateSlice slice with
    | error e => simp [hsl, hel, hv1] at hw
    | ok u1 =>
    cases hv2 : validateSlice elems with
    | error e => simp [hsl, hel, hv1, hv2] at hw
    | ok u2 =>
    cases hvis : sliceVisibleValues σ elems with
    | error e => simp [hsl, hel, hv1, hv2, hvis] at hw
    | ok elemValues =>
    cases htl : valueAsLoc tv with
    | error e => simp [hsl, hel, hv1, hv2, hvis, htl] at hw
    | ok tloc =>
    simp only [hsl, hel, hv1, hv2, hvis, htl] at hw
    split at hw
    · cases hw
    rename_i hcap
    cases hts : tySizeBytes σ.types elem with
    | error e => rw [hts] at hw; cases hw
    | ok elemSize =>
    simp only [hts] at hw
    split at hw
    · cases hw
    rename_i hr16
    cases hold : sliceVisibleValues σ slice with
    | error e => rw [hold] at hw; cases hw
    | ok oldValues =>
    rw [hold] at hw
    simp only [Option.some.injEq] at hw
    subst hw
    unfold applyStmtOp
    dsimp only
    simp only [hsl, hel, hv1, hv2, hvis, htl, except_bind_ok, if_neg hcap, hts, if_neg hr16, hold]
    refine ⟨fun extra => ?_, fun ch => ?_, fun a rest hvs pick => ?_⟩
    · exact do
        let newCap := slice.len + elemValues.size +
          ((appendGrowthCap slice.cap (slice.len + elemValues.size) - (slice.len + elemValues.size) + extra)
            % appendSpillWidth slice.cap (slice.len + elemValues.size))
        let backing ← buildAppendBackingValue σ elem oldValues elemValues newCap
        let p := σ.alloc backing (.array newCap elem)
        storeLoc p.2 tloc (.slice { base := some p.1, offset := 0, len := slice.len + elemValues.size, cap := newCap })
    · rcases hc : Choices.consumeAt .appendSpill (appendSpillWidth slice.cap (slice.len + elemValues.size)) ch
        with ⟨extra, rest⟩
      exact bind_pair_map _ _ rest
    · -- the target is a root cell: the post-consult tail cannot panic
      simp only [List.cons.injEq] at hvs
      obtain ⟨rfl, -⟩ := hvs
      simp only [valueAsLoc, pure_eq_ok, Except.ok.injEq] at htl
      subst htl
      exact NoPanic.bind (buildAppendBackingValue_noPanic _ _ _ _ _) fun _ =>
        storeLoc_base_noPanic _ _ _

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
    (hcons : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch
      = (idx, tail))
    (hlt : idx < cands.size) :
    stepFn σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
      = ((bindIterVars env.pushScope σ kv vv kt vt
            cands[idx].2.1 cands[idx].2.2).map
          fun p => (.exec body p.1
            (.mapIterK kv vv kt vt body base (produced.push cands[idx].1)
              start env k),
            p.2, tail)) := by
  simp only [stepFn, hcands, Bind.bind, Except.bind]
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
    (hcons : Choices.consumeAt .mapIter (cands.size + 1) ch = (cands.size, tail)) :
    stepFn σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
      = .ok (.next k, σ, tail) := by
  simp only [stepFn, hcands, Bind.bind, Except.bind]
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

/-! ### The consumption theorem (design-hygiene wave (iii), B8, 2026-09-04)

`seqConsumption` (Machine.lean) is the machine's own account of WHERE
`stepFn` consults the stream and at what bound. `stepFn_consumption_none`
and `stepFn_consumption_some` are the guarantee: a `none` step is
stream-oblivious; a `some (site, b)` step's stream is the site's pop at
bound `b` and the step depends on the stream only through that pick. The
former hand-flag theorem `stepFn_oblivious` is a corollary
(`seqConsumption_none_of_flags`). -/

/-- The entry arms of the `none` sweep: the entry classifies stream-free
(outside the family, or a non-panicking entry — `entryConsult?_none`). -/
macro "oblivious_entry_with " h:ident hpk:term : tactic =>
  `(tactic| (
    have hpk' := $hpk
    rw [hpk' _] at $h:ident
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
        exact ⟨rfl, fun ch => by
          (try simp only [List.append_assoc] at hpk' hx)
          simp [stepFn, hpk', hx, Except.map, Bind.bind, Except.bind]⟩
      | panic msg =>
        simp only [Except.map, Bind.bind, Except.bind, pure_eq_ok, Pure.pure, Except.pure,
          deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
        obtain ⟨h1, h2, h3⟩ := $h:ident
        subst h1; subst h2; subst h3
        exact ⟨rfl, fun ch => by
          (try simp only [List.append_assoc] at hpk' hx)
          simp [stepFn, hpk', hx, Except.map, Bind.bind, Except.bind]⟩))

macro "consumption_entry_none " h:ident hsc:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, seqConsumption, Config.applyPos, entryCallSite?]
    rcases entryConsult?_none $hsc:ident with hnv | hnp
    · oblivious_entry_with $h:ident (enterFramePick_oblivious_of_isSome_false hnv)
    · oblivious_entry_with $h:ident (enterFramePick_of_nopanic hnp)))

/-- The entry arms of the `some` sweep: the family's width-2 pop on the
panic path (`entryConsult?_some`, `enterFramePick_panic`). -/
macro "consumption_entry_some " h:ident hsc:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, seqConsumption, Config.applyPos, entryCallSite?]
    obtain ⟨hsite, hb, hw, msg, hpanic⟩ := entryConsult?_some $hsc:ident
    subst hsite; subst hb
    rw [enterFramePick_panic hpanic] at $h:ident
    simp only [Bind.bind, Except.bind, pure_eq_ok, Pure.pure, Except.pure, deliverS_panic,
      Except.ok.injEq, Prod.mk.injEq] at $h:ident
    obtain ⟨h1, h2, h3⟩ := $h:ident
    subst h1; subst h2; subst h3
    refine ⟨rfl, fun ch₁ hpk => ?_⟩
    (try simp only [List.append_assoc] at hpanic hpk)
    simp [stepFn, enterFramePick_panic hpanic, hpk, Bind.bind, Except.bind]))

/-- A wide-statement apply whose consult is `none` is a stream-oblivious
apply: `applyStmtOpCore` for every non-append head, the non-spilling /
refusing append otherwise. -/
theorem applyStmtOp_of_stmtConsult?_none {σ : ExecState} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} (h : stmtConsult? σ op vs = none) :
    ∃ r : Except Stop ExecState, ∀ ch : Choices,
      applyStmtOp σ ch op nt vs = r.map fun s' => (s', ch) := by
  by_cases hap : ∀ e, op ≠ .appendSlice e
  · refine ⟨applyStmtOpCore σ op vs, fun ch => ?_⟩
    rw [applyStmtOp_eq_core hap]
    rfl
  · obtain ⟨e, rfl⟩ : ∃ e, op = .appendSlice e := by
      cases op <;>
        first
        | exact ⟨_, rfl⟩
        | exact absurd (fun e h => by cases h) hap
    simp only [stmtConsult?, Option.map_eq_none_iff] at h
    exact applyStmtOp_appendSlice_nospill h

theorem stmtConsult?_some {σ : ExecState} {op : StmtOp} {vs : List GoValue}
    {site : ChoiceSite} {b : Nat} (h : stmtConsult? σ op vs = some (site, b)) :
    ∃ elem, op = .appendSlice elem ∧ site = .appendSpill ∧ appendSpill? σ elem vs = some b := by
  cases op with
  | appendSlice elem =>
    simp only [stmtConsult?, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    exact ⟨elem, rfl, rfl, hw⟩
  | _ => simp [stmtConsult?] at h

set_option linter.unusedSimpArgs false in
/-- An unwinding configuration is an entry position only at a frame whose
head defer is a function value. -/
theorem entryCallSite?_panicking {chain : List PanicEntry} {k : Cont} {p : FuncId × List GoValue}
    (h : entryCallSite? (.panicking chain k) = some p) :
    ∃ t te r fid captured args ds k' w,
      k = .frame t te r ((.funcVal fid captured, args) :: ds) k' w := by
  cases k <;> simp [entryCallSite?] at h
  rename_i t te r ds k' w
  cases ds with
  | nil => simp [entryCallSite?] at h
  | cons d ds =>
    obtain ⟨cv, args⟩ := d
    cases cv <;> simp [entryCallSite?] at h
    exact ⟨t, te, r, _, _, args, ds, k', w, rfl⟩

/-- The wide-statement apply arm at a stream-oblivious apply. -/
theorem stepFn_stmtOp_oblivious {σ : ExecState} {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {env : LocalEnv} {k : Cont} {r : Except Stop ExecState}
    (hr : ∀ ch : Choices, applyStmtOp σ ch op nt (v :: done).reverse = r.map fun s' => (s', ch))
    {ch₀ : Choices} {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (h : stepFn σ (.retV v (.stmtOpK op nt done [] env k)) ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFn σ (.retV v (.stmtOpK op nt done [] env k)) ch = .ok (c', σ', ch) := by
  unfold stepFn at h
  dsimp only at h
  rw [hr ch₀] at h
  cases r with
  | error e =>
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      pure_eq_ok, deliverS_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case panic msg =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl
  | ok s₂ =>
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl

/-- The wide-statement apply arm at a SPILLING append: the `appendSpill`
pop, and pick-dependence only. -/
theorem stepFn_stmtOp_spill {σ : ExecState} {elem : Ty} {nt : Nat} {done : List GoValue}
    {v : GoValue} {env : LocalEnv} {k : Cont} {w : Nat}
    {g : Nat → Except Stop ExecState}
    (hg : ∀ ch : Choices, applyStmtOp σ ch (.appendSlice elem) nt (v :: done).reverse
      = (g (Choices.consumeAt .appendSpill w ch).1).map
          fun s' => (s', (Choices.consumeAt .appendSpill w ch).2))
    (hnp : ∀ pick, NoPanic (g pick))
    {ch₀ : Choices} {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (h : stepFn σ (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) ch₀
      = .ok (c', σ', ch₀')) :
    ch₀' = (Choices.consumeAt .appendSpill w ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt .appendSpill w ch).1 = (Choices.consumeAt .appendSpill w ch₀).1 →
      stepFn σ (.retV v (.stmtOpK (.appendSlice elem) nt done [] env k)) ch
        = .ok (c', σ', (Choices.consumeAt .appendSpill w ch).2) := by
  unfold stepFn at h
  dsimp only at h
  rw [hg ch₀] at h
  cases hgv : g (Choices.consumeAt .appendSpill w ch₀).1 with
  | error e =>
    rw [hgv] at h
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      pure_eq_ok, deliverS_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case panic msg =>
    -- refuted: the post-consult tail never panics (`hnp`)
    exact absurd hgv (hnp _ msg)
  | ok s₂ =>
    rw [hgv] at h
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch hpk => ?_⟩
    unfold stepFn
    dsimp only
    rw [hg ch, hpk, hgv]
    rfl

/-- The sync apply arm at a stream-oblivious apply (`r.map` with the
stream passed through). -/
theorem stepFn_syncApply_oblivious {σ : ExecState} {op : SyncOp} {done : List GoValue}
    {v : GoValue} {env : LocalEnv} {k : Cont} {r : Except Stop (Config × ExecState)}
    (hr : ∀ ch : Choices, applySyncOp σ ch op (v :: done).reverse env k
      = r.map fun p => (p.1, p.2, ch))
    {ch₀ : Choices} {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (h : stepFn σ (.retV v (.syncStK op done [] env k)) ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFn σ (.retV v (.syncStK op done [] env k)) ch = .ok (c', σ', ch) := by
  unfold stepFn at h
  dsimp only at h
  rw [hr ch₀] at h
  cases r with
  | error e =>
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      pure_eq_ok, deliverS_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case panic msg =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl
  | ok p =>
    obtain ⟨c₂, σ₂⟩ := p
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl

set_option maxHeartbeats 1600000 in

/-- Frame exit consumes the stream only at a deferred call's ENTRY, and
there exactly as every entry does (`entryConsult?`): with the consult
`none` the exit is stream-oblivious — on BOTH its entries (B4). -/
theorem stepFrameExit_consumption_none {σ : ExecState}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv} {results : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {w : Bool} {c : Config}
    {ch₀ : Choices} {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (hc : c = .next (.frame targets tenv results ds k' w)
      ∨ c = .signal .ret (.frame targets tenv results ds k' w))
    (hsc : seqConsumption σ c = none)
    (h : stepFrameExit σ targets tenv results ds k' w ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFrameExit σ targets tenv results ds k' w ch = .ok (c', σ', ch) := by
  fun_cases stepFrameExit σ targets tenv results ds k' w ch₀
  · simp only [stepFrameExit, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit]⟩
  · simp only [stepFrameExit, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [stepFrameExit, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨vs, hload, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit, hload, Bind.bind, Except.bind]⟩
  · simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h
  · -- the deferred call's ENTRY: the exit's one consult
    rcases hc with rfl | rfl <;>
      simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc <;>
      simp only [stepFrameExit] at h <;>
      rcases entryConsult?_none hsc with hnv | hnp <;>
      (first
        | have hpk' := enterFramePick_oblivious_of_isSome_false hnv
        | have hpk' := enterFramePick_of_nopanic hnp) <;>
      (rw [hpk' _] at h
       cases hx : toResult (enterFrame _ _ _) with
       | error e =>
         rw [hx] at h
         simp [Except.map, Bind.bind, Except.bind] at h
       | ok r =>
         rw [hx] at h
         cases r with
         | ok a =>
           simp only [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
             deliverS_ok, Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨h1, h2, h3⟩ := h
           subst h1; subst h2; subst h3
           exact ⟨rfl, fun ch => by
             (try simp only [List.append_assoc] at hpk' hx)
             simp [stepFrameExit, hpk', hx, Except.map, Bind.bind, Except.bind]⟩
         | panic msg =>
           simp only [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
             deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨h1, h2, h3⟩ := h
           subst h1; subst h2; subst h3
           exact ⟨rfl, fun ch => by
             (try simp only [List.append_assoc] at hpk' hx)
             simp [stepFrameExit, hpk', hx, Except.map, Bind.bind, Except.bind]⟩)
  · simp only [stepFrameExit, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit]⟩
  · simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h

/-- A signal the table resolves sits on no call frame, so it is no frame
ENTRY (the consumption projection sees `none` there). -/
theorem entryCallSite?_of_signalStep {sg : Signal} {k : Cont} {c' : Config}
    (h : signalStep sg k = some c') : entryCallSite? (.signal sg k) = none := by
  cases k <;> simp_all [entryCallSite?]

/-- The `some` half for frame exit: the deferred entry's width-2 pop on
the panic path (`entryConsult?_some`, `enterFramePick_panic`), on both
entries (B4). -/
theorem stepFrameExit_consumption_some {σ : ExecState}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv} {results : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {w : Bool} {c : Config}
    {ch₀ : Choices} {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    {site : ChoiceSite} {b : Nat}
    (hc : c = .next (.frame targets tenv results ds k' w)
      ∨ c = .signal .ret (.frame targets tenv results ds k' w))
    (hsc : seqConsumption σ c = some (site, b))
    (h : stepFrameExit σ targets tenv results ds k' w ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFrameExit σ targets tenv results ds k' w ch
        = .ok (c', σ', (Choices.consumeAt site b ch).2) := by
  fun_cases stepFrameExit σ targets tenv results ds k' w ch₀
  all_goals try (rcases hc with rfl | rfl <;>
    simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
  all_goals try (simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h; done)
  rcases hc with rfl | rfl <;>
    simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc <;>
    (obtain ⟨hsite, hb, hw, msg, hpanic⟩ := entryConsult?_some hsc
     subst hsite; subst hb
     simp only [stepFrameExit] at h
     rw [enterFramePick_panic hpanic] at h
     simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, deliverS_panic,
       Except.ok.injEq, Prod.mk.injEq] at h
     obtain ⟨h1, h2, h3⟩ := h
     subst h1; subst h2; subst h3
     refine ⟨rfl, fun ch₁ hpk => ?_⟩
     (try simp only [List.append_assoc] at hpanic hpk)
     simp [stepFrameExit, enterFramePick_panic hpanic, hpk, Bind.bind, Except.bind])

set_option linter.unusedSimpArgs false in
/-- **The consumption theorem, `none` half**: a step whose projection is
`none` is stream-oblivious — it succeeds under EVERY stream with the same
successor and the stream returned untouched. Sweep over `stepFn`'s case
tree; every arm binds through stream-free helpers or through one of the
five consults at a non-popping instance (`applyStmtOp_of_stmtConsult?_none`,
`applySelect_done_stream`, `applySyncOp_try_nopop`/`_core_ok`,
`stepFn_mapIter_done`, `entryConsult?_none`). A newly added
stream-consuming arm breaks this proof loudly. -/
theorem stepFn_consumption_none {σ : ExecState} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : ExecState} {ch₀' : Choices}
    (hsc : seqConsumption σ c = none)
    (h : stepFn σ c ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepFn σ c ch = .ok (c', σ', ch) := by
  fun_cases stepFn σ c ch₀
  all_goals first
    | (refine ⟨?_, fun ch => ?_⟩ <;> (simp_all [stepFn]; done))
    | skip
  case case2 =>
    consumption_entry_none h hsc
  case case34 =>
    consumption_entry_none h hsc
  case case91 =>
    consumption_entry_none h hsc
  case case95 =>
    consumption_entry_none h hsc
  case case101 =>
    consumption_entry_none h hsc
  case case6 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨msg, -, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case140 =>
    simp only [stepFn] at h ⊢
    exact stepFrameExit_consumption_none (.inl rfl) hsc h
  case case151 =>
    simp only [stepFn, signalStep_frame] at h ⊢
    exact stepFrameExit_consumption_none (.inr rfl) hsc h
  case case94 =>
    simp only [seqConsumption, Config.applyPos] at hsc
    obtain ⟨r, hr⟩ := applyStmtOp_of_stmtConsult?_none hsc
    exact stepFn_stmtOp_oblivious hr h
  case case116 =>
    rename_i v clauses default? done env k'
    simp only [seqConsumption, Config.applyPos, selectConsult?] at hsc
    cases hcore : applySelectCore σ clauses default? ((v :: done).reverse) env k' with
    | error e =>
      unfold stepFn at h
      dsimp only at h
      rw [applySelect_error_stream hcore ch₀] at h
      cases_stop e <;> simp only [toResult_panic, toResult_refusal, toResult_fatal,
        toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
        pure_eq_ok, deliverS_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      case panic msg =>
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      unfold stepFn
      dsimp only
      rw [applySelect_error_stream hcore ch]
      rfl
    | ok o =>
      cases o with
      | done c₁ s₁ cl? =>
        unfold stepFn at h
        dsimp only at h
        rw [applySelect_done_stream hcore ch₀] at h
        simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
          Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨rfl, fun ch => ?_⟩
        unfold stepFn
        dsimp only
        rw [applySelect_done_stream hcore ch]
        rfl
      | picks commits =>
        rw [hcore] at hsc
        simp at hsc
  case case131 =>
    rename_i v op done env k'
    simp only [seqConsumption, Config.applyPos, syncConsult?, Option.map_eq_none_iff] at hsc
    cases hop : op.tryTargets? with
    | none =>
      -- a non-TRY head: the stream-free core (`applySyncOp_core_ok/_error`)
      cases hap : applySyncOp σ ch₀ op ((v :: done).reverse) env k' with
      | error e =>
        exact stepFn_syncApply_oblivious (r := .error e)
          (fun ch => by rw [applySyncOp_core_error hop hap ch]; rfl) h
      | ok p =>
        obtain ⟨c₂, σ₂, ch₂⟩ := p
        obtain ⟨rfl, hall⟩ := applySyncOp_core_ok hop hap
        exact stepFn_syncApply_oblivious (r := .ok (c₂, σ₂))
          (fun ch => by rw [hall ch]; rfl) h
    | some targets =>
      -- a TRY head: the receiver must resolve to a cell whose consult is width ≤ 1
      cases done with
      | cons hd tl =>
        exfalso
        unfold stepFn at h
        dsimp only at h
        unfold applySyncOp at h
        rw [hop] at h
        rcases hrev : (v :: hd :: tl).reverse with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · have := congrArg List.length hrev; simp at this
        · have := congrArg List.length hrev; simp at this
        · rw [hrev] at h
          simp [stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      | nil =>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at hsc
        unfold tryLockConsult? at hsc
        rw [hop] at hsc
        (try dsimp only at hsc)
        cases hl : valueAsLoc v with
        | error e =>
          refine stepFn_syncApply_oblivious (r := .error e) (fun ch => ?_) h
          simp [applySyncOp, hop, hl, Bind.bind, Except.bind, Except.map]
        | ok loc =>
          rw [hl] at hsc
          (try dsimp only at hsc)
          cases hcell : syncCell σ loc with
          | error e =>
            refine stepFn_syncApply_oblivious (r := .error e) (fun ch => ?_) h
            simp [applySyncOp, hop, hl, hcell, Bind.bind, Except.bind, Except.map]
          | ok pre =>
            rw [hcell] at hsc
            (try dsimp only at hsc)
            have hw : tryLockWidth op pre ≤ 1 := by
              by_cases hle : tryLockWidth op pre ≤ 1
              · exact hle
              · simp [hle] at hsc
            exact stepFn_syncApply_oblivious
              (r := applyTryLock σ op loc pre false targets env k')
              (fun ch => by simpa using applySyncOp_try_nopop hop hl hcell hw ch) h
  case case145 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates σ kt vt base produced with
    | error e =>
      exfalso
      simp [stepFn, hcands, Bind.bind, Except.bind] at h
    | ok cands =>
      rw [hcands] at hsc
      (try dsimp only at hsc)
      by_cases hemp : cands.isEmpty
      · rw [Array.isEmpty_iff] at hemp
        subst hemp
        rw [stepFn_mapIter_done hcands ch₀] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch => stepFn_mapIter_done hcands ch⟩
      · -- G-U: a width-1 consult (the last MANDATORY candidate) pops
        -- nothing and forces pick 0 — the step is oblivious.
        rw [if_neg hemp] at hsc
        obtain ⟨mand, hmand⟩ : ∃ m, mapIterMandatoryRemains cands start = m := ⟨_, rfl⟩
        rw [hmand] at hsc
        have hw : cands.size + (if mand = true then 0 else 1) ≤ 1 := by
          by_cases hle : cands.size + (if mand = true then 0 else 1) ≤ 1
          · exact hle
          · simp [hle] at hsc
        have hpos : 0 < cands.size := by
          rcases Nat.eq_zero_or_pos cands.size with hz | hp
          · exact absurd (by simpa [Array.isEmpty_iff, Array.size_eq_zero_iff] using hz) hemp
          · exact hp
        have hcons : ∀ ch : Choices,
            Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch
              = (0, ch) :=
          fun ch => Choices.consumeAt_le_one hw
        rw [stepFn_mapIter_pick hcands hmand hemp (hcons ch₀) hpos] at h
        cases hbind : bindIterVars env.pushScope σ kv vv kt vt cands[0].2.1 cands[0].2.2 with
        | error e => rw [hbind] at h; simp [Except.map] at h
        | ok p =>
          rw [hbind] at h
          simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch => ?_⟩
          rw [stepFn_mapIter_pick hcands hmand hemp (hcons ch) hpos, hbind]
          rfl
  case case75 =>
    -- A4: a global past the heap REFUSES (`.stuck`); no step is produced.
    rename_i hgid
    simp only [stepFn] at h
    rw [if_neg hgid] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case11 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨⟨env', s₁⟩, hd, ?_⟩
    simp
  -- Channel receive entry (channels arc slice 1): the plan match needs
  -- its hypothesis rewritten in; both arms are stream-oblivious.
  case case39 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case40 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case41 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, if_pos hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case42 =>
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
  case case58 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case59 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case60 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- sync/atomic statements (atomics arc wave 1): the sync recipes —
  -- entry is stream-transparent (the apply consumes nothing,
  -- applyAtomicOp's envelope statement).
  case case61 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case62 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case63 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case12 =>
    simp_all [stepFn, bind_eq_ok]
    obtain ⟨v, hd, h1, h2, h3⟩ := h
    exact ⟨h3.symm, v, hd, h1, h2⟩
  case case67 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨v, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨v, hd, ?_⟩
    simp
  case case81 =>
    oblivious_apply h
  case case84 =>
    oblivious_apply h
  case case85 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case86 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case87 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨b, hb, ?_⟩
    simp
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
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case92 =>
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
  case case93 =>
    rename_i hlt
    simp only [stepFn, if_neg hlt, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, if_neg hlt]
    rfl
  case case111 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨bs, hd, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, bind_eq_ok]
    refine ⟨bs, hd, ?_⟩
    simp
  case case114 =>
    oblivious_apply h
  case case124 =>
    oblivious_apply h
  case case133 =>
    oblivious_apply h
  case case146 =>
    oblivious_apply h

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- **The consumption theorem, `some` half**: a step whose projection is
`some (site, b)` DRAWS the site's pick at bound `b`, its stream is the
site's pop, and it depends on the stream only through that pick — any
stream drawing the same pick yields the same successor with its own popped
tail. The one hypothesis, `Config.appendTargetLocal`, is the frontend's
lowering contract at an `appendSlice` apply (the target is a hoisted local
temp, a ROOT cell); under it the post-consult tail of a spilling append
cannot panic (`applyStmtOp_appendSlice_spill`), as a TRY head's apply never
can (`applyTryLock_noPanic`) — the "post-pop panic restores the pre-apply
stream" disjunct the first statement carried was a PROOF ARTIFACT of
stating the theorem over arbitrary configurations, refuted here (wave-(iii)
audit fix F1; design note §B8). -/
theorem stepFn_consumption_some {σ : ExecState} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : ExecState} {ch₀' : Choices} {site : ChoiceSite} {b : Nat}
    (hloc : c.appendTargetLocal)
    (hsc : seqConsumption σ c = some (site, b))
    (h : stepFn σ c ch₀ = .ok (c', σ', ch₀')) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFn σ c ch = .ok (c', σ', (Choices.consumeAt site b ch).2) := by
  fun_cases stepFn σ c ch₀
  all_goals first
    | (simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
    | (simp [stepFn] at h; done)
    | (simp_all [stepFn]; done)
    | (simp_all [seqConsumption, Config.applyPos, entryCallSite?]; done)
    | skip
  case case2 =>
    consumption_entry_some h hsc
  case case34 =>
    consumption_entry_some h hsc
  case case91 =>
    consumption_entry_some h hsc
  case case95 =>
    consumption_entry_some h hsc
  case case101 =>
    consumption_entry_some h hsc
  case case140 =>
    simp only [stepFn] at h ⊢
    exact stepFrameExit_consumption_some (.inl rfl) hsc h
  case case150 =>
    -- B4: a signal the table resolves consumes nothing (no entry, no apply).
    exfalso
    simp [seqConsumption, Config.applyPos, entryCallSite?_of_signalStep ‹_›] at hsc
  case case151 =>
    simp only [stepFn, signalStep_frame] at h ⊢
    exact stepFrameExit_consumption_some (.inr rfl) hsc h
  case case94 =>
    simp only [seqConsumption, Config.applyPos] at hsc
    obtain ⟨elem, rfl, rfl, hw⟩ := stmtConsult?_some hsc
    obtain ⟨g, hg, hnp⟩ := applyStmtOp_appendSlice_spill hw
    simp only [Config.appendTargetLocal] at hloc
    obtain ⟨a, rest, hvs⟩ := hloc
    exact stepFn_stmtOp_spill hg (hnp a rest hvs) h
  case case116 =>
    rename_i v clauses default? done env k'
    simp only [seqConsumption, Config.applyPos, selectConsult?] at hsc
    cases hcore : applySelectCore σ clauses default? ((v :: done).reverse) env k' with
    | error e => rw [hcore] at hsc; cases hsc
    | ok o =>
      cases o with
      | done c₁ s₁ cl? => rw [hcore] at hsc; cases hsc
      | picks commits =>
        rw [hcore] at hsc
        simp only [Option.some.injEq, Prod.mk.injEq] at hsc
        obtain ⟨rfl, rfl⟩ := hsc
        unfold stepFn at h
        dsimp only at h
        rw [applySelect_picks_stream hcore ch₀] at h
        cases hget : commits[(Choices.consumeAt .l2Entry commits.length ch₀).1]? with
        | none =>
          rw [hget] at h
          simp [Bind.bind, Except.bind] at h
        | some p =>
          rw [hget] at h
          obtain ⟨cl, r⟩ := p
          cases r with
          | inl q =>
            obtain ⟨c₂, s₂⟩ := q
            simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            unfold stepFn
            dsimp only
            rw [applySelect_picks_stream hcore ch, hpk, hget]
            rfl
          | inr msg =>
            simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            unfold stepFn
            dsimp only
            rw [applySelect_picks_stream hcore ch, hpk, hget]
            rfl
  case case131 =>
    rename_i v op done env k'
    simp only [seqConsumption, Config.applyPos, syncConsult?, Option.map_eq_some_iff,
      Prod.mk.injEq] at hsc
    obtain ⟨w, hw, rfl, rfl⟩ := hsc
    unfold tryLockConsult? at hw
    cases hop : op.tryTargets? with
    | none => rw [hop] at hw; cases hw
    | some targets =>
      rw [hop] at hw
      cases done with
      | cons hd tl =>
        exfalso
        rcases hrev : (v :: hd :: tl).reverse with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · have := congrArg List.length hrev; simp at this
        · have := congrArg List.length hrev; simp at this
        · rw [hrev] at hw; cases hw
      | nil =>
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at h hw
        (try dsimp only at hw)
        cases hl : valueAsLoc v with
        | error e => rw [hl] at hw; cases hw
        | ok loc =>
          rw [hl] at hw
          (try dsimp only at hw)
          cases hcell : syncCell σ loc with
          | error e => rw [hcell] at hw; cases hw
          | ok pre =>
            rw [hcell] at hw
            (try dsimp only at hw)
            split at hw
            · cases hw
            · simp only [Option.some.injEq] at hw
              subst hw
              have hap := applySyncOp_try_stream (env := env) (k := k') hop hl hcell
              unfold stepFn at h
              dsimp only at h
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at h
              rw [hap ch₀] at h
              cases hat : applyTryLock σ op loc pre
                  ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch₀).1 == 1) targets env k' with
              | error e =>
                rw [hat] at h
                cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal,
                  toResult_fatal, toResult_deadlock, toResult_raceDetected, toResult_fuelOut,
                  Bind.bind, Except.bind, pure_eq_ok, deliverS_panic, Except.ok.injEq,
                  Prod.mk.injEq, reduceCtorEq] at h
                case panic msg =>
                -- refuted: a TRY head's apply never panics (`applyTryLock_noPanic`)
                exact absurd hat (applyTryLock_noPanic hcell _ _ _ _ _ msg)
              | ok p =>
                obtain ⟨c₂, σ₂⟩ := p
                rw [hat] at h
                simp only [Except.map, toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
                  Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                refine ⟨rfl, fun ch hpk => ?_⟩
                unfold stepFn
                dsimp only
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                rw [hap ch, hpk, hat]
                rfl
  case case145 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates σ kt vt base produced with
    | error e => rw [hcands] at hsc; cases hsc
    | ok cands =>
      rw [hcands] at hsc
      (try dsimp only at hsc)
      by_cases hemp : cands.isEmpty
      · simp [hemp] at hsc
      · rw [if_neg hemp] at hsc
        obtain ⟨mand, hmand⟩ : ∃ m, mapIterMandatoryRemains cands start = m := ⟨_, rfl⟩
        rw [hmand] at hsc
        -- G-U: the projection reports the consult only at width ≥ 2.
        have hsc' : ChoiceSite.mapIter = site ∧ (cands.size + (if mand = true then 0 else 1)) = b := by
          by_cases hle : cands.size + (if mand = true then 0 else 1) ≤ 1
          · simp [hle] at hsc
          · simpa [hle] using hsc
        obtain ⟨rfl, rfl⟩ := hsc'
        rcases hcons : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch₀ with ⟨idx, tail⟩
        have hpos : 0 < cands.size := by
          rcases Nat.eq_zero_or_pos cands.size with hz | hp
          · exact absurd (by simpa [Array.isEmpty_iff, Array.size_eq_zero_iff] using hz) hemp
          · exact hp
        have hltw : idx < cands.size + (if mand = true then 0 else 1) := by
          have hb := Choices.consumeAt_fst_lt (site := .mapIter) (ch := ch₀)
            (bound := cands.size + (if mand = true then 0 else 1))
            (by cases mand <;> simp <;> omega)
          rw [hcons] at hb
          exact hb
        by_cases hlt : idx < cands.size
        · rw [stepFn_mapIter_pick hcands hmand hemp hcons hlt] at h
          cases hbind : bindIterVars env.pushScope σ kv vv kt vt cands[idx].2.1 cands[idx].2.2 with
          | error e => rw [hbind] at h; simp [Except.map] at h
          | ok p =>
            rw [hbind] at h
            simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            rcases hcons₁ : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch with ⟨idx₁, tail₁⟩
            rw [hcons₁] at hpk
            simp only at hpk
            subst hpk
            rw [stepFn_mapIter_pick hcands hmand hemp hcons₁ hlt, hbind]
            rfl
        · have hmandf : mand = false := by
            cases mand
            · rfl
            · exfalso; simp at hltw; omega
          subst hmandf
          have hidx : idx = cands.size := by simp at hltw; omega
          subst hidx
          have hcons' : Choices.consumeAt .mapIter (cands.size + 1) ch₀ = (cands.size, tail) := by simpa using hcons
          rw [stepFn_mapIter_stop hcands hmand hemp hcons'] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch hpk => ?_⟩
          rcases hcons₁ : Choices.consumeAt .mapIter (cands.size + (if false = true then 0 else 1)) ch with ⟨idx₁, tail₁⟩
          have hcons₁' : Choices.consumeAt .mapIter (cands.size + 1) ch = (idx₁, tail₁) := by
            simpa using hcons₁
          rw [hcons₁] at hpk
          simp only at hpk
          subst hpk
          rw [stepFn_mapIter_stop hcands hmand hemp hcons₁']

set_option linter.unusedSimpArgs false in
/-- The apply-position accessor's inversions (A7): a `some` names the frame. -/
theorem applyPos_stmt {c : Config} {op : StmtOp} {nt : Nat} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} (h : c.applyPos = some (.stmt op nt, vs, env, k)) :
    ∃ v done, c = .retV v (.stmtOpK op nt done [] env k) ∧ vs = (v :: done).reverse := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.stmt.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl⟩

set_option linter.unusedSimpArgs false in
theorem applyPos_select {c : Config} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    (h : c.applyPos = some (.select clauses default?, vs, env, k)) :
    ∃ v done, c = .retV v (.selectOpsK clauses default? done [] env k) := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.select.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl⟩

set_option linter.unusedSimpArgs false in
theorem applyPos_sync {c : Config} {op : SyncOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} (h : c.applyPos = some (.sync op, vs, env, k)) :
    ∃ v done, c = .retV v (.syncStK op done [] env k) := by
  unfold Config.applyPos at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, ApplyHead.sync.injEq,
    reduceCtorEq, false_and] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨_, _, rfl⟩

/-- The five hand flags of the retired sweep entail a `none` projection. -/
theorem seqConsumption_none_of_flags {σ : ExecState} {c : Config}
    (hmi : ∀ (kv vv : Option String) (kt vt : Ty) (body : Stmt)
      (base : Option Loc) (produced start : Array Nat)
      (env : LocalEnv) (k : Cont),
      c ≠ .next (.mapIterK kv vv kt vt body base produced start env k))
    (hnc : consumesAppendSlice c = false)
    (hns : consumesSelect c = false)
    (hnv : consumesNilValueMethod σ c = false)
    (hnt : consumesTryLock c = false) :
    seqConsumption σ c = none := by
  revert hmi hnc hns hnv hnt
  unfold seqConsumption
  split <;> intro hmi hnc hns hnv hnt
  · exact absurd rfl (hmi _ _ _ _ _ _ _ _ _ _)
  · split
    all_goals first
      | rfl
      | (rename_i heq
         obtain ⟨v, done, rfl, rfl⟩ := applyPos_stmt heq
         cases ‹StmtOp› <;> simp_all [stmtConsult?, consumesAppendSlice])
      | (rename_i heq
         obtain ⟨v, done, rfl⟩ := applyPos_select heq
         simp [consumesSelect] at hns)
      | (rename_i heq
         obtain ⟨v, done, rfl⟩ := applyPos_sync heq
         simp only [consumesTryLock, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnt
         simp [syncConsult?, tryLockConsult?, hnt])
      | (split
         · rename_i fid args heq
           unfold consumesNilValueMethod at hnv
           rw [heq] at hnv
           (try dsimp only at hnv)
           unfold entryConsult?
           rw [if_pos (by unfold nilValueMethodWidth; simp [hnv])]
         · rfl)

/-- **Stream obliviousness of the non-consuming arms** — the retired sweep
(W3.2 slice 1 stage A) as a COROLLARY of the consumption theorem: away
from the five consuming shapes (a `mapIterK` at the `.next` position —
excluded by `hmi` — an `appendSlice` apply position — excluded by `hnc` —
a select apply position — excluded by `hns` — a frame entry in BUG-087's
wrapper family — excluded by `hnv` — and a TRY head's sync apply —
excluded by `hnt`), a step that succeeds under one stream succeeds under
EVERY stream, with the SAME successor and the stream returned untouched.
Its consumers (`allStreamsOk`'s soundness, the pool-level
`stepThread_oblivious`) are unchanged. -/
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
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepFn σ c ch = .ok (c', σ', ch) :=
  stepFn_consumption_none (seqConsumption_none_of_flags hmi hnc hns hnv hnt) h

/-- The one-layer unfolding of `execStmtLoop`, as an EQUATION (the loop
is fuel-structural, so the definitional unfolding needs the fuel
constructor exposed — `cases fuel` then `rfl`). -/
theorem execStmtLoop_unfold (fuel : Nat) (σ : ExecState) (c : Config)
    (ch : Choices) :
    execStmtLoop fuel σ c ch
      = (match c with
         | .next .stop => .ok (σ, ch)
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
      ∀ ch : Choices, ∃ (σf : ExecState) (ch' : Choices),
        execStmtLoop fuel σ c ch = .ok (σf, ch') := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ c hall ch
    simp [allStreamsOk] at hall
  | succ n ih =>
    intro σ c hall ch
    unfold allStreamsOk at hall
    split at hall
    · exact ⟨σ, ch, rfl⟩
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
        rcases hcons : Choices.consumeAt .mapIter
          (cands.size + (if mand = true then 0 else 1)) ch with ⟨idx, tail⟩
        have hpos : 0 < cands.size := by
          rcases Nat.eq_zero_or_pos cands.size with hz | hp
          · exact absurd (by simpa [Array.isEmpty_iff, Array.size_eq_zero_iff]
              using hz) hne
          · exact hp
        have hltw : idx < cands.size + (if mand = true then 0 else 1) := by
          have hb := Choices.consumeAt_fst_lt (site := .mapIter) (ch := ch)
            (bound := cands.size + (if mand = true then 0 else 1))
            (by cases mand <;> simp <;> omega)
          rw [hcons] at hb
          exact hb
        have hidx := hall idx (by simpa using List.mem_range.mpr hltw)
        -- the probe stream `[idx]` realizes the pick (its tail is
        -- irrelevant: the checker discards the probe's stream)
        obtain ⟨probeTail, hconsi⟩ : ∃ t, Choices.consumeAt .mapIter
            (cands.size + (if mand = true then 0 else 1)) [idx] = (idx, t) :=
          ⟨_, Prod.ext (Choices.consumeAt_fst_singleton hltw) rfl⟩
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
          have hconsi' : Choices.consumeAt .mapIter (cands.size + 1) [cands.size]
              = (cands.size, probeTail) := by
            simpa using hconsi
          have hcons' : Choices.consumeAt .mapIter (cands.size + 1) ch
              = (cands.size, tail) := by
            simpa using hcons
          rw [stepFn_mapIter_stop hcands hmand hne hconsi'] at hidx
          obtain ⟨out, ch', hrun⟩ := ih hidx tail
          refine ⟨out, ch', ?_⟩
          rw [execStmtLoop_step (stepFn_mapIter_stop hcands hmand hne hcons')]
          exact hrun
    · -- the oblivious catch-all
      rename_i hx1 hx2
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
              hx2 kv vv kt vt b bs pr st e kk heq)
            hnc1 hnc2 hnc3 hnc4 hprobe
          obtain ⟨out, ch', hrun⟩ := ih hall ch
          exact ⟨out, ch', by rw [execStmtLoop_step (hobl ch)]; exact hrun⟩
        · exact absurd hall (by simp)
