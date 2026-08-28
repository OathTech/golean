import GoLeanProofs.Frame.PlugRule
import GoLean.GoCore.MachineSound

/-!
# THE PLUG RULE, part 5 (G-BIND): the fill–step INVERSION
(`docs/2026-08-28_iris-corpus-plan.md` §4.1's new obligation;
unit log `docs/g-bind-log.md`)

The landed walk `stepFn_plug` is forward-only (fill-then-step). A bind
law also needs step-then-decompose: a step of the FILLED configuration
is the `plugC`-image of a step of the canonical one. On the executable
this reduces to ERROR TRANSFER — if the canonical step refuses, the
plugged step refuses too (`stepFn_plug_err`, the walk below); combined
with the forward walk and `stepFn` being a function, the ok-inverse
`stepFn_plug_ok_inv` follows without a second commutation argument,
and `MachineSound`'s two-way correspondence transports both directions
to the relation (`step_plug` / `step_plug_inv` — the latter is OUR
geometry's `primStep_fill_inv`, stated with the barrier premise; the
unconditional class-shaped inverse is FALSE here, counterexample in
the unit log, D-2).

LINEAGE: the ectx-language `fill_step_inv` obligation (Iris
`EctxLanguage`), realized on the executable machine because our
continuations are configuration data. The premises are the §7
non-locality census, unchanged.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option autoImplicit false

variable {env' : LocalEnv} {k' : Cont}

/-- The per-step error-transfer correspondence: IF the canonical step
refuses, the plugged step refuses (with its own payload — panic
rendering and message text may differ across the fill, so only the
refusal CLASS transfers). -/
def PE (env' : LocalEnv) (k' : Cont)
    (x y : Except GoError (Config × ExecState × Choices)) : Prop :=
  ∀ ⦃e : GoError⦄, x = .error e → ∃ e', y = .error e'

theorem PE.okRefute {r : Config × ExecState × Choices}
    {y : Except GoError (Config × ExecState × Choices)} :
    PE env' k' (.ok r) y := fun _ h => nomatch h

theorem PE.pure {r : Config × ExecState × Choices}
    {y : Except GoError (Config × ExecState × Choices)} :
    PE env' k' (pure r) y := PE.okRefute

/-- Close an error arm: the plugged side computes to a refusal. -/
theorem PE.err {x : Except GoError (Config × ExecState × Choices)}
    {y : Except GoError (Config × ExecState × Choices)} {e' : GoError}
    (h : y = .error e') : PE env' k' x y := fun _ _ => ⟨e', h⟩

/-- Close an error arm with the payload existential (the shape `simp`
closes via `exists_eq'` after reducing the plugged step). -/
theorem PE.of_ex {x : Except GoError (Config × ExecState × Choices)}
    {y : Except GoError (Config × ExecState × Choices)}
    (h : ∃ e', y = .error e') : PE env' k' x y := fun _ _ => h

/-- Frame entry transfers refusals: `enterFrameStep` errors exactly when
`enterFrame` errors non-panic, and `enterFrame` sees only state and
argument values — both fill-invariant. -/
theorem PE.enterFrameStep {s : ExecState} {fid : FuncId}
    {args : List GoValue} {mk mk' : Func → LocalEnv → List Loc → Config}
    {k₁ k₂ : Cont} {ch : Choices} :
    PE env' k' (enterFrameStep s fid args mk k₁ ch)
      (enterFrameStep s fid args mk' k₂ ch) := by
  intro e h
  unfold GoLean.GoCore.Machine.enterFrameStep at h ⊢
  split at h
  next => exact nomatch h
  next => exact nomatch h
  next => exact ⟨_, rfl⟩

/-- Panic-path deferred entry, same argument. -/
theorem PE.enterFrameDeferPanicking {s : ExecState} {fid : FuncId}
    {args : List GoValue} {mk mk' : Func → LocalEnv → Config}
    {chain : List PanicEntry} {kr₁ kr₂ : Cont} {ch : Choices} :
    PE env' k' (enterFrameDeferPanicking s fid args mk chain kr₁ ch)
      (enterFrameDeferPanicking s fid args mk' chain kr₂ ch) := by
  intro e h
  unfold GoLean.GoCore.Machine.enterFrameDeferPanicking at h ⊢
  split at h
  next => exact nomatch h
  next => exact nomatch h
  next => exact ⟨_, rfl⟩

set_option maxHeartbeats 12800000 in
/-- **THE ERROR-TRANSFER WALK** (the fill–step inversion's engine): on
a barrier-carrying configuration, under the §7 context premises, a
refusal of the canonical step forces a refusal of the plugged step.
The walk mirrors `stepFn_plug` arm for arm; each arm either refutes
(the canonical result is an `.ok`) or computes the plugged refusal
through the same `_plug`/`_bar` helper equations the forward walk
landed. -/
theorem stepFn_plug_err
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    {σ : ExecState} {c : Config} {ch : Choices}
    (hbar : hasBarrierC c = true) :
    PE env' k' (stepFn σ c ch) (stepFn σ (plugC env' k' c) ch) := by
  fun_cases stepFn σ c ch
  all_goals first
    | exact PE.okRefute
    | exact PE.pure
    | exact PE.enterFrameStep
    | exact PE.enterFrameDeferPanicking
    | (simp only [hasBarrierC, hasBarrierK] at hbar; done)
    | (refine PE.err ?_ <;>
        simp_all [stepFn, plugC, plugK, hasBarrierC, hasBarrierK,
          seqCont_plug, contHeadLabel_plug, pushDefer_plug,
          panicPassthrough_plug, recoverResult_plug,
          contAfterStmtOp_plug, contAfterStmtOp_bar,
          applyChanOp_plug, applyChanOp_bar,
          applySyncOp_plug, applySyncOp_bar,
          applySelect_plug, applySelect_bar,
          enterRecvTargets_plug, enterRecvTargets_bar,
          commitClause_plug,
          plugK_frame_of_bar, hasBarrierK_frame_of_tail,
          throw, throwThe, MonadExceptOf.throw,
          Except.map, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none]); done
    | (intro e h
       revert h
       simp_all [stepFn, plugC, plugK, hasBarrierC, hasBarrierK,
          seqCont_plug, contHeadLabel_plug, pushDefer_plug,
          panicPassthrough_plug, recoverResult_plug,
          contAfterStmtOp_plug, contAfterStmtOp_bar,
          applyChanOp_plug, applyChanOp_bar,
          applySyncOp_plug, applySyncOp_bar,
          applySelect_plug, applySelect_bar,
          enterRecvTargets_plug, enterRecvTargets_bar,
          commitClause_plug,
          plugK_frame_of_bar, hasBarrierK_frame_of_tail,
          throw, throwThe, MonadExceptOf.throw,
          Except.map, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none]); done
    | skip
  -- ROUND 2: the bind-scrutinee arms — the canonical side is a
  -- do-chain; split it: error legs transfer through the same
  -- state-based scrutinees (fill-invariant), ok legs refute.
  all_goals first
    | (intro e h
       simp only [bind, Except.bind, pure, Except.pure] at h
       (repeat' split at h) <;>
         simp_all [stepFn, plugC, plugK, hasBarrierC, hasBarrierK,
               seqCont_plug, contHeadLabel_plug, pushDefer_plug,
               panicPassthrough_plug, recoverResult_plug,
               contAfterStmtOp_plug, contAfterStmtOp_bar,
               applyChanOp_plug, applyChanOp_bar,
               applySyncOp_plug, applySyncOp_bar,
               applySelect_plug, applySelect_bar,
               enterRecvTargets_plug, enterRecvTargets_bar,
               commitClause_plug,
               plugK_frame_of_bar, hasBarrierK_frame_of_tail,
               throw, throwThe, MonadExceptOf.throw,
               Except.map, bind, Except.bind, pure, Except.pure,
               Option.map_some, Option.map_none]
       done)
    | skip
  -- ROUND 3: the surviving throw arms, with the payload existential as
  -- the goal so `simp` can instantiate it after reducing the plugged
  -- step through the same helper equations.
  all_goals first
    | (refine PE.of_ex ?_
       simp_all [stepFn, plugC, plugK, hasBarrierC, hasBarrierK,
          seqCont_plug, contHeadLabel_plug, pushDefer_plug,
          panicPassthrough_plug, recoverResult_plug,
          contAfterStmtOp_plug, contAfterStmtOp_bar,
          applyChanOp_plug, applyChanOp_bar,
          applySyncOp_plug, applySyncOp_bar,
          applySelect_plug, applySelect_bar,
          enterRecvTargets_plug, enterRecvTargets_bar,
          commitClause_plug,
          plugK_frame_of_bar, hasBarrierK_frame_of_tail,
          throw, throwThe, MonadExceptOf.throw,
          Except.map, bind, Except.bind, pure, Except.pure,
          Option.map_some, Option.map_none]
       done)
    | skip
  -- ROUND 4: the hand arms (the walk's residue — enterFrame entries,
  -- context-inspecting helpers, and catch-all continuations).
  case case3 =>
    rename_i chain t te r args ds k2 w fid captured
    have hred : stepFn σ (plugC env' k' (.panicking chain
        (.frame t te r ((.funcVal fid captured, args) :: ds) k2 w))) ch
        = enterFrameDeferPanicking σ fid (captured ++ args)
            (fun func frameEnv => .exec func.body frameEnv
              (.frame [] [] [] [] (.panicResumeK chain
                (plugK env' k' (.frame t te r ds k2 w))) func.wrapper))
            chain (plugK env' k' (.frame t te r ds k2 w)) ch := by
      by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        rfl
      · simp [plugC, plugK_frame_of_ne hb2, stepFn]
    rw [hred]
    exact PE.enterFrameDeferPanicking
  case case5 =>
    rename_i chain t te r args ds k2 w other hnf hnn
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      cases other <;>
        simp_all [plugC, plugK, stepFn, throw, throwThe,
          MonadExceptOf.throw]
    · cases other <;>
        simp_all [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
          MonadExceptOf.throw]
  case case11 =>
    rename_i chain k h4 h3 h2 h1 hpass
    cases k
    case stop => exact absurd rfl h1
    case panicResumeK a b => exact absurd rfl (h2 _ _)
    case frame t te r ds k3 w =>
        cases ds with
        | nil => exact absurd rfl (h4 _ _ _ _ _)
        | cons dd ds2 =>
            obtain ⟨cv, av⟩ := dd
            exact absurd rfl (h3 _ _ _ _ _ _ _ _)
    all_goals simp [panicPassthrough] at hpass
  case case16 =>
    rename_i env2 k p hnseq
    refine PE.of_ex ?_
    cases k
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case seq a b c => exact absurd rfl (hnseq _ _ _)
    case frame t2 te2 r2 ds2 k3 w2 =>
      obtain ⟨a, b, c, d, e2, f, hfs⟩ :=
        plugK_frame_shape (env' := env') (k' := k') t2 te2 r2 ds2 k3 w2
      simp only [plugC, plugK]
      rw [hfs]
      simp [stepFn, throw, throwThe, MonadExceptOf.throw]
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case36 =>
    rename_i env2 k targets fid args plans hplan hargs
    have hred : stepFn σ (plugC env' k'
        (.exec (.call targets fid args) env2 k)) ch
        = enterFrameStep σ fid []
            (fun func fe rls => .exec func.body fe
              (.frame plans env2 rls [] (plugK env' k' k) func.wrapper))
            (plugK env' k' k) ch := by
      simp only [plugC]
      simp only [stepFn.eq_def]
      rw [hplan, hargs]
    rw [hred]
    exact PE.enterFrameStep
  case case42 =>
    rename_i env2 k targets chE elem op hplan
    refine PE.of_ex ?_
    simp only [plugC]
    simp only [stepFn.eq_def]
    (repeat' split) <;>
      simp_all [throw, throwThe, MonadExceptOf.throw]
  case case43 =>
    rename_i env2 k targets chE elem hplan hsz
    refine PE.of_ex ?_
    simp only [plugC]
    simp only [stepFn.eq_def]
    (repeat' split) <;>
      simp_all [throw, throwThe, MonadExceptOf.throw]
  case case44 =>
    rename_i env2 k targets chE elem hplan hsz
    refine PE.of_ex ?_
    simp only [plugC]
    simp only [stepFn.eq_def]
    (repeat' split) <;>
      simp_all [throw, throwThe, MonadExceptOf.throw]
  case case61 =>
    rename_i env2 k op args targets sop hplan
    refine PE.of_ex ?_
    simp only [plugC]
    simp only [stepFn.eq_def]
    (repeat' split) <;>
      simp_all [throw, throwThe, MonadExceptOf.throw]
  case case62 =>
    rename_i env2 k op args targets hplan
    refine PE.of_ex ?_
    simp only [plugC]
    simp only [stepFn.eq_def]
    (repeat' split) <;>
      simp_all [throw, throwThe, MonadExceptOf.throw]
  case case147 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      obtain ⟨a, b, c, d, e2, f, hfs⟩ :=
        plugK_frame_shape (env' := env') (k' := k') t2 te2 r2 ds2 k3 w2
      simp only [plugC, plugK]
      rw [hfs]
      simp [stepFn, throw, throwThe, MonadExceptOf.throw]
    case strictK =>
      rename List Expr => pend
      cases pend <;> grind
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case153 =>
    rename_i tenv rl rls k2 w
    refine PE.of_ex ?_
    by_cases hb2 : (List.nil (α := TargetShape × List Expr)) = []
        ∧ k2 = .stop ∧ w = false
    · obtain ⟨_, h2, h3⟩ := hb2; subst h2; subst h3
      cases hlm : loadMany σ (rl :: rls) <;>
        simp [plugC, plugK, stepFn, hlm, bind, Except.bind, throw,
          throwThe, MonadExceptOf.throw]
    · cases hlm : loadMany σ (rl :: rls) <;>
        simp [plugC, plugK_frame_of_ne hb2, stepFn, hlm, bind,
          Except.bind, throw, throwThe, MonadExceptOf.throw]
  case case156 =>
    rename_i t te r args ds k2 w fid captured
    have hred : stepFn σ (plugC env' k' (.next
        (.frame t te r ((.funcVal fid captured, args) :: ds) k2 w))) ch
        = enterFrameStep σ fid (captured ++ args)
            (fun func frameEnv _ => .exec func.body frameEnv
              (.frame [] [] [] []
                (plugK env' k' (.frame t te r ds k2 w)) func.wrapper))
            (plugK env' k' (.frame t te r ds k2 w)) ch := by
      by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        simp [plugC, plugK, stepFn]
      · simp [plugC, plugK_frame_of_ne hb2, stepFn]
    rw [hred]
    exact PE.enterFrameStep
  case case158 =>
    rename_i t te r args ds k2 w other hnf hnn
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      cases other <;>
        simp_all [plugC, plugK, stepFn, throw, throwThe,
          MonadExceptOf.throw]
    · cases other <;>
        simp_all [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
          MonadExceptOf.throw]
  case case169 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      by_cases hb2 : t2 = [] ∧ k3 = .stop ∧ w2 = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        rcases r2 with _ | ⟨r0, rs⟩ <;> rcases ds2 with _ | ⟨⟨cv, av⟩, dss⟩ <;>
          first
            | grind
            | simp_all [plugC, plugK, stepFn, throw, throwThe,
                MonadExceptOf.throw]
      · rcases t2 with _ | ⟨⟨sh, ops⟩, ts⟩ <;>
          (try rcases ops with _ | ⟨o, os⟩) <;>
          rcases r2 with _ | ⟨r0, rs⟩ <;>
          rcases ds2 with _ | ⟨⟨cv, av⟩, dss⟩ <;>
          first
            | grind
            | simp_all [plugC, plugK_frame_of_ne hb2, stepFn, throw,
                throwThe, MonadExceptOf.throw]
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case175 =>
    rename_i t te r ds k2 w
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      simp [plugC, plugK, stepFn, throw, throwThe, MonadExceptOf.throw]
    · simp [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
        MonadExceptOf.throw]
  case case177 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      first
        | grind
        | simp_all
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case183 =>
    rename_i t te r ds k2 w
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      simp [plugC, plugK, stepFn, throw, throwThe, MonadExceptOf.throw]
    · simp [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
        MonadExceptOf.throw]
  case case185 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      first
        | grind
        | simp_all
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case192 =>
    rename_i tenv rl rls k2 w
    refine PE.of_ex ?_
    by_cases hb2 : (List.nil (α := TargetShape × List Expr)) = []
        ∧ k2 = .stop ∧ w = false
    · obtain ⟨_, h2, h3⟩ := hb2; subst h2; subst h3
      cases hlm : loadMany σ (rl :: rls) <;>
        simp [plugC, plugK, stepFn, hlm, bind, Except.bind, throw,
          throwThe, MonadExceptOf.throw]
    · cases hlm : loadMany σ (rl :: rls) <;>
        simp [plugC, plugK_frame_of_ne hb2, stepFn, hlm, bind,
          Except.bind, throw, throwThe, MonadExceptOf.throw]
  case case195 =>
    rename_i t te r args ds k2 w fid captured
    have hred : stepFn σ (plugC env' k' (.returning
        (.frame t te r ((.funcVal fid captured, args) :: ds) k2 w))) ch
        = enterFrameStep σ fid (captured ++ args)
            (fun func frameEnv _ => .exec func.body frameEnv
              (.frame [] [] [] []
                (plugK env' k' (.frame t te r ds k2 w)) func.wrapper))
            (plugK env' k' (.frame t te r ds k2 w)) ch := by
      by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        simp [plugC, plugK, stepFn]
      · simp [plugC, plugK_frame_of_ne hb2, stepFn]
    rw [hred]
    exact PE.enterFrameStep
  case case197 =>
    rename_i t te r args ds k2 w other hnf hnn
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      cases other <;>
        simp_all [plugC, plugK, stepFn, throw, throwThe,
          MonadExceptOf.throw]
    · cases other <;>
        simp_all [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
          MonadExceptOf.throw]
  case case199 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      by_cases hb2 : t2 = [] ∧ k3 = .stop ∧ w2 = false
      · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
        rcases r2 with _ | ⟨r0, rs⟩ <;> rcases ds2 with _ | ⟨⟨cv, av⟩, dss⟩ <;>
          first
            | grind
            | simp_all [plugC, plugK, stepFn, throw, throwThe,
                MonadExceptOf.throw]
      · rcases t2 with _ | ⟨⟨sh, ops⟩, ts⟩ <;>
          (try rcases ops with _ | ⟨o, os⟩) <;>
          rcases r2 with _ | ⟨r0, rs⟩ <;>
          rcases ds2 with _ | ⟨⟨cv, av⟩, dss⟩ <;>
          first
            | grind
            | simp_all [plugC, plugK_frame_of_ne hb2, stepFn, throw,
                throwThe, MonadExceptOf.throw]
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case206 =>
    rename_i L t te r ds k2 w
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      simp [plugC, plugK, stepFn, throw, throwThe, MonadExceptOf.throw]
    · simp [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
        MonadExceptOf.throw]
  case case208 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      first
        | grind
        | simp_all
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]
  case case217 =>
    rename_i L t te r ds k2 w
    refine PE.of_ex ?_
    by_cases hb2 : t = [] ∧ k2 = .stop ∧ w = false
    · obtain ⟨h1, h2, h3⟩ := hb2; subst h1; subst h2; subst h3
      simp [plugC, plugK, stepFn, throw, throwThe, MonadExceptOf.throw]
    · simp [plugC, plugK_frame_of_ne hb2, stepFn, throw, throwThe,
        MonadExceptOf.throw]
  case case219 =>
    rename Cont => kk
    refine PE.of_ex ?_
    cases kk
    case stop => simp [hasBarrierC, hasBarrierK] at hbar
    case frame =>
      rename Bool => w2
      rename Cont => k3
      rename List (TargetShape × List Expr) => t2
      rename List Loc => r2
      rename List (GoValue × List GoValue) => ds2
      rename LocalEnv => te2
      first
        | grind
        | simp_all
    all_goals
      first
        | grind
        | simp_all [plugC, plugK, stepFn, throw, throwThe,
            MonadExceptOf.throw]

/-! ## The derived inverses (executable, then relation-level) -/

/-- **The executable ok-inverse**: a successful plugged step is the
`plugC`-image of a successful canonical step at the same state, stream,
and (post-)choices — by the error-transfer walk (a canonical refusal
would force a plugged refusal), the forward walk, and `stepFn` being a
function. The classification disjunct is the forward walk's. -/
theorem stepFn_plug_ok_inv
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    {σ : ExecState} {c : Config} {ch : Choices}
    {d' : Config} {σ' : ExecState} {ch' : Choices}
    (hbar : hasBarrierC c = true)
    (h : stepFn σ (plugC env' k' c) ch = .ok (d', σ', ch')) :
    ∃ d, stepFn σ c ch = .ok (d, σ', ch') ∧ d' = plugC env' k' d
      ∧ (hasBarrierC d = true ∨ d = .next .stop
          ∨ ∃ chain, d = .panicking chain .stop) := by
  cases hcan : stepFn σ c ch with
  | error e =>
      obtain ⟨e', hpe⟩ := stepFn_plug_err hmf hrc hbar hcan
      rw [h] at hpe
      exact absurd hpe (by simp)
  | ok r =>
      obtain ⟨d, σ₁, ch₁⟩ := r
      obtain ⟨hplug, hcls⟩ := stepFn_plug hmf hrc hbar hcan
      rw [h] at hplug
      obtain ⟨h1, h2, h3⟩ : d' = plugC env' k' d ∧ σ' = σ₁ ∧ ch' = ch₁ := by
        simpa using hplug
      refine ⟨d, ?_, h1, hcls⟩
      rw [h2, h3]
      try exact hcan

/-- **The relation-level forward fill**: a canonical `Step` transports to
the plugged configuration (via completeness at some stream, the forward
walk, and soundness) — the `primStep_fill` half for our geometry. -/
theorem step_plug
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    {σ σ' : ExecState} {c d : Config}
    (hbar : hasBarrierC c = true)
    (h : Step c σ d σ') :
    Step (plugC env' k' c) σ (plugC env' k' d) σ'
      ∧ (hasBarrierC d = true ∨ d = .next .stop
          ∨ ∃ chain, d = .panicking chain .stop) := by
  obtain ⟨ch, ch2, hstep⟩ := step_complete h
  obtain ⟨hplug, hcls⟩ := stepFn_plug hmf hrc hbar hstep
  exact ⟨stepFn_sound hplug, hcls⟩

/-- **THE FILL–STEP INVERSION** (`primStep_fill_inv` for our geometry,
the plan of record's named new obligation, §4.1): a `Step` of the FILLED
configuration decomposes as the `plugC`-image of a `Step` of the
canonical one — stated with the barrier premise, which is exactly what
excludes the configurations where the CONTEXT could step instead (the
unconditional typeclass shape is false here; unit log D-2). The "e is a
value" half of the classic inverse never arises: a barrier-carrying
configuration is never the value, and the exit/crossed arrivals surface
in the classification disjunct instead. -/
theorem step_plug_inv
    (hmf : mapIterFree k' = true)
    (hrc : recoverThroughWrappers k' = none)
    {σ σ' : ExecState} {c d' : Config}
    (hbar : hasBarrierC c = true)
    (h : Step (plugC env' k' c) σ d' σ') :
    ∃ d, d' = plugC env' k' d ∧ Step c σ d σ'
      ∧ (hasBarrierC d = true ∨ d = .next .stop
          ∨ ∃ chain, d = .panicking chain .stop) := by
  obtain ⟨ch, ch2, hstep⟩ := step_complete h
  obtain ⟨d, hcan, hd', hcls⟩ := stepFn_plug_ok_inv hmf hrc hbar hstep
  exact ⟨d, hd', stepFn_sound hcan, hcls⟩

/-! ## Value/terminal facts for the WP layer (`Laws/Bind`) -/

/-- A barrier-carrying configuration is not the terminal value. -/
theorem ne_next_stop_of_hasBarrierC {c : Config}
    (hbar : hasBarrierC c = true) : c ≠ .next .stop := by
  intro hc; subst hc
  simp [hasBarrierC, hasBarrierK] at hbar

/-- The fill of a barrier-carrying configuration is not the terminal
value either (the plug preserves heads; the barrier spine is never bare
`.stop`). -/
theorem plugK_ne_stop_of_bar {k : Cont} (hb : hasBarrierK k = true) :
    plugK env' k' k ≠ .stop := by
  cases k
  case stop => simp [hasBarrierK] at hb
  case frame t te r ds k2 w =>
    obtain ⟨a, b, c2, d, e2, f, hfs⟩ :=
      plugK_frame_shape (env' := env') (k' := k') t te r ds k2 w
    simp [hfs]
  all_goals simp [plugK]

theorem plugC_ne_next_stop {c : Config}
    (hbar : hasBarrierC c = true) :
    plugC env' k' c ≠ .next .stop := by
  cases c
  case next k =>
    simp only [plugC]
    intro hc
    injection hc with hk
    exact plugK_ne_stop_of_bar (by simpa [hasBarrierC] using hbar) hk
  case panicked msg => simp [hasBarrierC] at hbar
  all_goals simp [plugC]

/-- The fill of the terminal value is the context resumption. -/
theorem plugC_next_stop :
    plugC env' k' (.next .stop) = .next k' := rfl

/-- `.panicked` is terminal in the relation: no rule steps from it. -/
theorem not_step_panicked {msg : String} {σ σ' : ExecState} {c' : Config} :
    ¬ Step (.panicked msg) σ c' σ' := by
  intro h
  obtain ⟨ch, ch2, hstep⟩ := step_complete h
  simp [stepFn, throw, throwThe, MonadExceptOf.throw] at hstep

/-- Steps from the crossed panic shape only render: the successor is
`.panicked` at the same state. -/
theorem step_panicking_stop_inv {chain : List PanicEntry}
    {σ σ' : ExecState} {c' : Config}
    (h : Step (.panicking chain .stop) σ c' σ') :
    ∃ msg, c' = .panicked msg ∧ σ' = σ := by
  obtain ⟨ch, ch2, hstep⟩ := step_complete h
  cases chain with
  | nil => simp [stepFn, throw, throwThe, MonadExceptOf.throw] at hstep
  | cons first rest =>
      cases hrend : renderPanicHead σ first rest with
      | none =>
          simp [stepFn, hrend, throw, throwThe, MonadExceptOf.throw]
            at hstep
      | some msg =>
          simp only [stepFn, hrend, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at hstep
          exact ⟨msg, hstep.1.symm, hstep.2.1.symm⟩

/-- The context's panic-drain head steps whenever the passthrough
classifies it — the discharge lemma for the bind rule's `hdrain`
premise at pop-headed contexts. -/
theorem step_panicking_of_passthrough {chain : List PanicEntry}
    {k k₂ : Cont} {σ : ExecState}
    (h : panicPassthrough k = some k₂) :
    Step (.panicking chain k) σ (.panicking chain k₂) σ :=
  Step.panicUnwind h

/-- The frame-headed drain steps (no defers left: the frame pops; with
defers: the drain enters the deferred call — either way a step exists).
Stated for the defer-free head, the common caller shape. -/
theorem step_panicking_frame_empty {chain : List PanicEntry}
    {t : List (TargetShape × List Expr)} {te : LocalEnv} {r : List Loc}
    {k : Cont} {w : Bool} {σ : ExecState} :
    Step (.panicking chain (.frame t te r [] k w)) σ
      (.panicking chain k) σ :=
  Step.panicFrameEmpty

end GoLean.Frame
