import Lean
import GoLean.GoCore.PrefixFacts

/-!
# What `stepFn` can raise (window charter row 2b, packet B)

[AGENT packet B worker] 2026-09-28. The error classification the bridges' fuel statements and
the four-way classification rest on: away from the abort and the four blocked forms, `stepFn`
raises only a REFUSAL or the unrecoverable `fatal` — never a Go panic (no stray panic, audit F1
machine-checked), never the deadlock, never the race terminal, never fuel-out.

Driven by the combinator predicate `ErrP` (a property of every `.error` a computation can
return) and the tactic `errp`. Two properties: `Stop.Strict` (a refusal or `fatal`) and
`Stop.Tame` (additionally a recoverable panic — what a helper under `toResult` may raise).
-/

namespace GoLean.GoCore.Machine

open GoLean

variable {ctx : ProgramCtx}

/-- A refusal or the unrecoverable `fatal`. -/
def _root_.GoLean.Stop.Strict : Stop → Prop
  | .refusal _ => True
  | .terminal (.fatal _) => True
  | _ => False

/-- A refusal, `fatal`, or a recoverable panic. -/
def _root_.GoLean.Stop.Tame : Stop → Prop
  | .refusal _ => True
  | .terminal (.fatal _) => True
  | .terminal (.panic _) => True
  | _ => False

/-- Every `.error` of `x` satisfies `Q`. -/
def ErrP {ε α : Type} (Q : ε → Prop) (x : Except ε α) : Prop := ∀ e, x = .error e → Q e

theorem ErrP.ok {ε α : Type} {Q : ε → Prop} {a : α} : ErrP Q (.ok a : Except ε α) :=
  fun _ h => by cases h
theorem ErrP.pure {ε α : Type} {Q : ε → Prop} {a : α} : ErrP Q (pure a : Except ε α) :=
  fun _ h => by cases h
theorem ErrP.error {ε α : Type} {Q : ε → Prop} {e : ε} (h : Q e) : ErrP Q (.error e : Except ε α) :=
  fun _ he => by cases he; exact h
theorem ErrP.throw {ε α : Type} {Q : ε → Prop} {e : ε} (h : Q e) : ErrP Q (throw e : Except ε α) :=
  fun _ he => by cases he; exact h
theorem ErrP.bind {ε α β : Type} {Q : ε → Prop} {x : Except ε α} {f : α → Except ε β}
    (hx : ErrP Q x) (hf : ∀ a, ErrP Q (f a)) : ErrP Q (x >>= f) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; exact hf a e h
theorem ErrP.bind_eq {ε α β : Type} {Q : ε → Prop} {x : Except ε α} {f : α → Except ε β}
    (hx : ErrP Q x) (hf : ∀ a, x = .ok a → ErrP Q (f a)) : ErrP Q (x >>= f) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; exact hf a hx' e h
theorem ErrP.map {ε α β : Type} {Q : ε → Prop} {x : Except ε α} {g : α → β}
    (hx : ErrP Q x) : ErrP Q (g <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; cases h
theorem ErrP.exmap {ε α β : Type} {Q : ε → Prop} {x : Except ε α} {g : α → β}
    (hx : ErrP Q x) : ErrP Q (Except.map g x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx _ hx'
  | ok a => rw [hx'] at h; cases h
theorem ErrP.mono {ε α : Type} {Q R : ε → Prop} {x : Except ε α} (hQR : ∀ e, Q e → R e)
    (hx : ErrP Q x) : ErrP R x := fun e h => hQR e (hx e h)

theorem _root_.GoLean.Stop.Strict.tame {e : Stop} (h : e.Strict) : e.Tame := by
  rcases e with (_ | _ | _) | (_ | _ | _ | _) | _ <;> first | exact True.intro | exact h.elim

theorem ErrP.tame_of_strict {α : Type} {x : Except Stop α} (h : ErrP Stop.Strict x) :
    ErrP Stop.Tame x := ErrP.mono (fun _ => Stop.Strict.tame) h

/-- A panic-free tame computation is strict. -/
theorem ErrP.strict_of_noPanic {α : Type} {x : Except Stop α} (ht : ErrP Stop.Tame x)
    (hn : NoPanic x) : ErrP Stop.Strict x := by
  intro e h
  have := ht e h
  rcases e with (_ | _ | _) | (_ | _ | _ | _) | _ <;>
    first | exact True.intro | exact this.elim | exact absurd h (hn _)

/-- `toResult` absorbs the panic: a tame computation's classification is strict. -/
theorem ErrP.strict_toResult {α : Type} {x : Except Stop α} (h : ErrP Stop.Tame x) :
    ErrP Stop.Strict (toResult x) := by
  intro e he
  cases x with
  | ok a => cases he
  | error e' =>
    have hq := h e' rfl
    rcases e' with (_ | _ | _) | (_ | _ | _ | _) | _ <;>
      (try simp only [toResult, Except.error.injEq] at he) <;> (try subst he) <;>
      first | exact True.intro | exact hq.elim | cases he

/-- `toResult` of a tame computation is tame. -/
theorem ErrP.tame_toResult {α : Type} {x : Except Stop α} (h : ErrP Stop.Tame x) :
    ErrP Stop.Tame (toResult x) := (ErrP.strict_toResult h).tame_of_strict

theorem ErrP.forIn_list {ε α β : Type} {Q : ε → Prop} {l : List α} {init : β}
    {body : α → β → Except ε (ForInStep β)} (hb : ∀ a b, ErrP Q (body a b)) :
    ErrP Q (forIn l init body) := by
  induction l generalizing init with
  | nil => exact ErrP.pure
  | cons a as ih =>
    rw [List.forIn_cons]
    refine ErrP.bind (hb a init) fun r => ?_
    cases r with
    | done b => exact ErrP.pure
    | yield b => exact ih

theorem ErrP.forIn_array {ε α β : Type} {Q : ε → Prop} {l : Array α} {init : β}
    {body : α → β → Except ε (ForInStep β)} (hb : ∀ a b, ErrP Q (body a b)) :
    ErrP Q (forIn l init body) := by
  rw [← Array.forIn_toList]
  exact ErrP.forIn_list hb

theorem ErrP.forIn_range {ε β : Type} {Q : ε → Prop} {r : Std.Legacy.Range} {init : β}
    {body : Nat → β → Except ε (ForInStep β)} (hb : ∀ a b, ErrP Q (body a b)) :
    ErrP Q (forIn r init body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact ErrP.forIn_list hb

theorem ErrP.of_eq {ε α : Type} {Q : ε → Prop} {x : Except ε α} {e : ε} (hx : ErrP Q x)
    (h : x = .error e) : Q e := hx e h

open Lean Elab Tactic Meta in
/-- A passed-through error `Except.error e` whose origin `x = .error e` is in context:
reduce the goal to `ErrP Q x`. -/
elab "errp_heq" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  match t.getAppFnArgs with
  | (``ErrP, #[ε, α, q, x]) =>
    match x.cleanupAnnotations.getAppFnArgs with
    | (``Except.error, #[_, _, e]) =>
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let ty := (← instantiateMVars d.type).cleanupAnnotations
        match ty.getAppFnArgs with
        | (``Eq, #[_, lhs, rhs]) =>
          match rhs.cleanupAnnotations.getAppFnArgs with
          | (``Except.error, #[_, _, e']) =>
            if ← isDefEq e e' then
              let lty ← inferType lhs
              let m ← mkFreshExprSyntheticOpaqueMVar (mkApp4 (mkConst ``ErrP) ε (lty.getAppArgs[1]!) q lhs)
              let pf ← mkAppM ``ErrP.of_eq #[m, d.toExpr]
              let pf2 ← mkAppOptM ``ErrP.error #[some ε, some α, some q, some e, some pf]
              g.assign pf2
              replaceMainGoal [m.mvarId!]
              return
          | _ => pure ()
        | _ => pure ()
      throwError "errp_heq: no origin hypothesis"
    | _ => throwError "errp_heq: not a passed-through error"
  | _ => throwError "errp_heq: not an ErrP goal"

theorem ErrP.mapM_loop {ε α β : Type} {Q : ε → Prop} {f : α → Except ε β}
    (hf : ∀ a, ErrP Q (f a)) : ∀ (l : List α) (acc : List β), ErrP Q (List.mapM.loop f l acc)
  | [], acc => by unfold List.mapM.loop; exact ErrP.pure
  | a :: as, acc => by
    unfold List.mapM.loop
    exact ErrP.bind (hf a) fun _ => ErrP.mapM_loop hf as _

theorem ErrP.mapM {ε α β : Type} {Q : ε → Prop} {f : α → Except ε β} {l : List α}
    (hf : ∀ a, ErrP Q (f a)) : ErrP Q (List.mapM f l) := by
  unfold List.mapM
  exact ErrP.mapM_loop hf l []

open Lean Elab Tactic Meta in
/-- A commit run inside a delivery: find the plan (or entry) it came from. -/
elab "errp_commit" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  match t.getAppFnArgs with
  | (``ErrP, #[_, _, _, x]) =>
    match x.cleanupAnnotations.getAppFnArgs with
    | (``runCommit, #[_, c, s]) =>
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        let ty := (← instantiateMVars d.type).cleanupAnnotations
        match ty.getAppFnArgs with
        | (``Eq, #[_, lhs, rhs]) =>
          match lhs.cleanupAnnotations.getAppFnArgs, rhs.cleanupAnnotations.getAppFnArgs with
          | (``toResult, #[_, plan]), (``Except.ok, #[_, _, r]) =>
            match r.cleanupAnnotations.getAppFnArgs with
            | (``Result.ok, #[_, c']) =>
              if ← isDefEq c c' then
                let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM `GoLean.GoCore.Machine.CommitOk #[plan])
                let pf ← mkAppM `GoLean.GoCore.Machine.runCommit_of_toResult #[m, d.toExpr, s]
                let pfT ← mkAppM `GoLean.GoCore.Machine.ErrP.tame_of_strict #[pf]
                if ← isDefEq (← inferType pf) t then g.assign pf
                else if ← isDefEq (← inferType pfT) t then g.assign pfT
                else continue
                replaceMainGoal [m.mvarId!]
                return
            | _ => pure ()
          | (``enterFramePickV, _), (``Except.ok, #[_, _, _]) =>
            let h1 ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``Prod.fst #[rhs.appArg!])
              (← mkAppOptM ``Result.ok #[none, c]))
            let pf ← mkAppM `GoLean.GoCore.Machine.runCommit_of_entry #[d.toExpr, h1, s]
            let pfT ← mkAppM `GoLean.GoCore.Machine.ErrP.tame_of_strict #[pf]
            if ← isDefEq (← inferType pf) t then g.assign pf
            else if ← isDefEq (← inferType pfT) t then g.assign pfT
            else continue
            let rest ← evalTacticAt (← `(tactic| first | rfl | assumption)) h1.mvarId!
            replaceMainGoal rest
            return
          | _, _ => pure ()
        | _ => pure ()
      throwError "errp_commit: no origin"
    | _ => throwError "errp_commit: not a commit run"
  | _ => throwError "errp_commit: not an ErrP goal"

/-- The extension point: helper lemmas register here. -/
syntax "errp_leaf" : tactic
macro_rules | `(tactic| errp_leaf) => `(tactic| fail "no errp leaf")

open Lean Elab Tactic Meta in
/-- Unfold the head constant of a stuck `ErrP` goal when it is a NON-recursive definition
(the unfolded goal must not mention the constant again). -/
elab "errp_unfold" : tactic => do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  match t.getAppFnArgs with
  | (``ErrP, #[_, _, _, x]) =>
    match x.cleanupAnnotations.getAppFn with
    | .const n _ =>
      if [``Bind.bind, ``Pure.pure, ``MonadExcept.throw, ``throw, ``toResult, ``forIn,
          ``Functor.map, ``Except.map, ``runCommit, ``ite, ``dite].contains n then
        throwError "errp_unfold: blacklisted {n}"
      let r ← Lean.Meta.unfoldTarget g n
      let t' ← instantiateMVars (← r.getType)
      if (t'.find? (fun e => e.isConstOf n)).isSome then
        throwError "errp_unfold: recursive {n}"
      replaceMainGoal [r]
    | _ => throwError "errp_unfold: no constant head"
  | _ => throwError "errp_unfold: not an ErrP goal"

/-- Descend a do-pipeline for an `ErrP` goal. -/
macro "errp" : tactic => `(tactic| repeat' (first
  | exact ErrP.ok
  | exact ErrP.pure
  | (refine ErrP.throw ?_; exact True.intro)
  | (refine ErrP.error ?_; exact True.intro)
  | errp_heq
  | errp_commit
  | refine ErrP.bind_eq ?_ (fun _ _ => ?_)
  | refine ErrP.map ?_
  | refine ErrP.exmap ?_
  | (apply_assumption; done)
  | refine ErrP.strict_toResult ?_
  | refine ErrP.tame_toResult ?_
  | errp_leaf
  | exact ErrP.tame_of_strict (by errp_leaf)
  | (unfold deliverS)
  | (unfold deliverV)
  | refine ErrP.mapM (fun _ => ?_)
  | refine ErrP.mapM_loop (fun _ => ?_)
  | refine ErrP.forIn_list (fun _ _ => ?_)
  | refine ErrP.forIn_array (fun _ _ => ?_)
  | refine ErrP.forIn_range (fun _ _ => ?_)
  | split
  | (dsimp only)
  | (dsimp (config := { zetaDelta := true }) only)
  | errp_unfold))

/-! ## Leaf lemmas: the recursive helpers -/

theorem normalizeListWithAux_strict {f : GoValue → Except Stop GoValue}
    (hf : ∀ v, ErrP Stop.Strict (f v)) :
    ∀ (acc : Array GoValue) (l : List GoValue), ErrP Stop.Strict (normalizeListWithAux f acc l)
  | acc, [] => by unfold normalizeListWithAux; errp
  | acc, v :: rest => by
    unfold normalizeListWithAux
    exact ErrP.bind (hf v) fun a => normalizeListWithAux_strict hf _ rest

theorem normalizeFieldsWithAux_strict {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ t v, ErrP Stop.Strict (f t v)) :
    ∀ (acc : Array (String × GoValue)) (defs : List FieldDef) (vals : List (String × GoValue)),
      ErrP Stop.Strict (normalizeFieldsWithAux f acc defs vals)
  | acc, fd :: defs, (a, v) :: vals => by
    have ih := fun acc => normalizeFieldsWithAux_strict hf acc defs vals
    unfold normalizeFieldsWithAux
    errp
  | acc, [], _ => by unfold normalizeFieldsWithAux; errp
  | acc, _ :: _, [] => by unfold normalizeFieldsWithAux; errp

theorem normalizeValueForTyTy_strict {f : TypeIdx → GoValue → Except Stop GoValue}
    (hf : ∀ i v, ErrP Stop.Strict (f i v)) :
    ∀ (ty : Ty) (v : GoValue), ErrP Stop.Strict (normalizeValueForTyTy f ty v) := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih =>
    intro v
    cases v <;> simp only [normalizeValueForTyTy] <;> errp
    all_goals exact normalizeListWithAux_strict ih _ _
  | leaf ty hne =>
    intro v
    unfold normalizeValueForTyTy
    split
    all_goals first
      | exact absurd rfl (hne _ _)
      | errp

theorem normalizeValueForTyAt_strict (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx) (v : GoValue),
      ErrP Stop.Strict (normalizeValueForTyAt types bound i v) := by
  intro bound
  induction bound with
  | zero => intro i v; unfold normalizeValueForTyAt; errp
  | succ n ih =>
    intro i v
    have h1 := normalizeValueForTyTy_strict ih
    have h2 := fun fs vals acc => normalizeFieldsWithAux_strict (acc := acc) (defs := fs) (vals := vals)
      (normalizeValueForTyTy_strict ih)
    unfold normalizeValueForTyAt
    errp

theorem normalizeValueForTy_strict {ty : Ty} {v : GoValue} :
    ErrP Stop.Strict (normalizeValueForTy ctx ty v) :=
  normalizeValueForTyTy_strict (normalizeValueForTyAt_strict _ _) ty v
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact normalizeValueForTy_strict)

theorem defaultFieldsWith_strict {f : Ty → Except Stop GoValue}
    (hf : ∀ t, ErrP Stop.Strict (f t)) :
    ∀ fs, ErrP Stop.Strict (defaultFieldsWith f fs)
  | [] => by unfold defaultFieldsWith; errp
  | fd :: rest => by
    have ih := defaultFieldsWith_strict hf rest
    unfold defaultFieldsWith
    errp

theorem defaultValueTy_strict {f : TypeIdx → Except Stop GoValue}
    (hf : ∀ i, ErrP Stop.Strict (f i)) : ∀ ty, ErrP Stop.Strict (defaultValueTy f ty) := by
  intro ty
  induction ty using Ty.arrayInduction with
  | array length elem ih => simp only [defaultValueTy]; errp
  | leaf ty hne =>
    unfold defaultValueTy
    split
    all_goals first
      | exact absurd rfl (hne _ _)
      | errp

theorem defaultValueAt_strict (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx), ErrP Stop.Strict (defaultValueAt types bound i) := by
  intro bound
  induction bound with
  | zero => intro i; unfold defaultValueAt; errp
  | succ n ih =>
    intro i
    have h1 := defaultValueTy_strict ih
    have h2 := defaultFieldsWith_strict (defaultValueTy_strict ih)
    unfold defaultValueAt
    errp

theorem defaultValue_strict {ty : Ty} : ErrP Stop.Strict (defaultValue ctx ty) :=
  defaultValueTy_strict (defaultValueAt_strict _ _) ty
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact defaultValue_strict)

theorem loadLoc_tame {s : Store} : ∀ {l : Loc}, ErrP Stop.Tame (loadLoc ctx s l)
  | .base a => by unfold loadLoc; errp
  | .field b t f => by
    have ih := @loadLoc_tame s b
    unfold loadLoc; errp
  | .index b i => by
    have ih := @loadLoc_tame s b
    unfold loadLoc; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact loadLoc_tame)

theorem buildStructFields_strict :
    ∀ {fs : List FieldDef} {vs : List GoValue}, ErrP Stop.Strict (buildStructFields ctx fs vs)
  | fd :: fs, v :: vs => by
    have ih := @buildStructFields_strict fs vs
    unfold buildStructFields; errp
  | [], _ => by unfold buildStructFields; errp
  | _ :: _, [] => by unfold buildStructFields; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact buildStructFields_strict)

theorem resolve_strict (types : TypeEnv) (bound : Nat) (ty : Ty) :
    ErrP Stop.Strict (types.resolve bound ty) := by
  fun_induction TypeEnv.resolve types bound ty <;> errp
theorem resolve_strict' {types : TypeEnv} {bound : Nat} {ty : Ty} :
    ErrP Stop.Strict (types.resolve bound ty) := resolve_strict types bound ty
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact resolve_strict')

theorem allocDecls_strict : ∀ {env : LocalEnv} {s : Store} {ps : List Param},
    ErrP Stop.Strict (allocDecls ctx env s ps)
  | env, s, [] => by unfold allocDecls; errp
  | env, s, p :: rest => by
    have ih := fun env s => @allocDecls_strict env s rest
    unfold allocDecls; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact allocDecls_strict)

theorem Mem.loadElems_tame {s : Store} {base : Loc} :
    ∀ {start n : Nat}, ErrP Stop.Tame (Mem.loadElems ctx s base start n)
  | start, 0 => by unfold Mem.loadElems; errp
  | start, n + 1 => by
    have ih := @Mem.loadElems_tame s base (start + 1) n
    unfold Mem.loadElems; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact Mem.loadElems_tame)

theorem loadResults_strict {s : Store} : ∀ {ls : List Loc}, ErrP Stop.Strict (loadResults ctx s ls)
  | [] => by unfold loadResults; errp
  | l :: ls => by
    have ih := @loadResults_strict s ls
    unfold loadResults; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact loadResults_strict)

theorem unseqAtoms_strict {env : LocalEnv} {s : Store} :
    ∀ {es : List Expr}, ErrP Stop.Strict (unseqAtoms ctx env s es)
  | [] => by unfold unseqAtoms; errp
  | e :: es => by
    have ih := @unseqAtoms_strict env s es
    unfold unseqAtoms; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact unseqAtoms_strict)

theorem unseqLookupTarget_strict : ∀ {tg : List (VarId × TargetRef)} {t : VarId},
    ErrP Stop.Strict (unseqLookupTarget tg t)
  | [], t => by unfold unseqLookupTarget; errp
  | (n, r) :: rest, t => by
    have ih := @unseqLookupTarget_strict rest t
    unfold unseqLookupTarget; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact unseqLookupTarget_strict)

theorem unseqStorePlan_strict {s : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)} :
    ∀ {sts : List (VarId × VarId)}, ErrP Stop.Strict (unseqStorePlan ctx s env tg sts)
  | [] => by unfold unseqStorePlan; errp
  | (t, v) :: rest => by
    have ih := @unseqStorePlan_strict s env tg rest
    unfold unseqStorePlan; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact unseqStorePlan_strict)

theorem stepDown_strict (types : TypeEnv) (b : Nat) (ty : Ty) (st : PathStep) :
    ErrP Stop.Strict (Ty.stepDown types b ty st) := by
  fun_induction Ty.stepDown types b ty st <;> errp
theorem stepDown_strict' {types : TypeEnv} {b : Nat} {ty : Ty} {st : PathStep} :
    ErrP Stop.Strict (Ty.stepDown types b ty st) := stepDown_strict types b ty st
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact stepDown_strict')

theorem normalizeValueForTyTy_strict' {b : Nat} {ty : Ty} {v : GoValue} :
    ErrP Stop.Strict (normalizeValueForTyTy (normalizeValueForTyAt ctx.types b) ty v) :=
  normalizeValueForTyTy_strict (normalizeValueForTyAt_strict _ _) ty v
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact normalizeValueForTyTy_strict')

theorem ErrP.modifyM {ε α : Type} {Q : ε → Prop} {xs : Array α} {i : Nat} {f : α → Except ε α}
    (h : ∀ a, ErrP Q (f a)) : ErrP Q (xs.modifyM i f) := by
  unfold Array.modifyM
  split
  · exact ErrP.bind (h _) fun _ => ErrP.pure
  · exact ErrP.pure

theorem writeAt_tame (b : Nat) (ty : Ty) (cur : GoValue) (p : List PathStep) (v : GoValue) :
    ErrP Stop.Tame (writeAt ctx b ty cur p v) := by
  fun_induction writeAt ctx b ty cur p v
  all_goals errp
theorem writeAt_tame' {b : Nat} {ty : Ty} {cur : GoValue} {p : List PathStep} {v : GoValue} :
    ErrP Stop.Tame (writeAt ctx b ty cur p v) := writeAt_tame b ty cur p v


macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact writeAt_tame')

theorem valueEq_tame_all :
    (∀ ty l r, ErrP Stop.Tame (valueEq ctx ty l r)) ∧
    (∀ fs l r, ErrP Stop.Tame (valueEqFields ctx fs l r)) ∧
    (∀ elem l r, ErrP Stop.Tame (valueEqList ctx elem l r)) := by
  apply valueEq.mutual_induct ctx (fun ty l r => ErrP Stop.Tame (valueEq ctx ty l r))
    (fun fs l r => ErrP Stop.Tame (valueEqFields ctx fs l r))
    (fun elem l r => ErrP Stop.Tame (valueEqList ctx elem l r))
  all_goals intros
  all_goals first
    | (unfold valueEq; (try simp only [*]); errp; done)
    | (unfold valueEqFields; (try simp only [*]); errp; done)
    | (unfold valueEqList; (try simp only [*]); errp; done)
    | (rename_i hres
       unfold valueEq
       rw [hres]
       exact ErrP.error (ErrP.of_eq resolve_strict' hres).tame)

theorem valueEq_tame {ty : Ty} {l r : GoValue} : ErrP Stop.Tame (valueEq ctx ty l r) :=
  valueEq_tame_all.1 ty l r
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact valueEq_tame)

theorem writeAt_strict {b : Nat} {ty : Ty} {cur : GoValue} {p : List PathStep} {v : GoValue} :
    ErrP Stop.Strict (writeAt ctx b ty cur p v) :=
  ErrP.strict_of_noPanic writeAt_tame' (writeAt_noPanic _ _ _ _ _)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact writeAt_strict)

set_option maxHeartbeats 4000000 in
theorem applyStrictOp_tame {s : Store} {leafOf : Loc → Loc} {op : StrictOp} {vs : List GoValue} :
    ErrP Stop.Tame (applyStrictOp ctx s leafOf op vs) := by
  unfold applyStrictOp
  errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyStrictOp_tame)

theorem structSizeAlignWith_strict {f : Ty → Except Stop (Nat × Nat)}
    (hf : ∀ t, ErrP Stop.Strict (f t)) (fs : List FieldDef) (a b c d : Nat) :
    ErrP Stop.Strict (structSizeAlignWith f fs a b c d) := by
  fun_induction structSizeAlignWith f fs a b c d <;> errp

theorem tySizeAlignTy_strict {p : Platform} {f : TypeIdx → Except Stop (Nat × Nat)}
    (hf : ∀ i, ErrP Stop.Strict (f i)) (ty : Ty) : ErrP Stop.Strict (tySizeAlignTy p f ty) := by
  induction ty using Ty.arrayInduction with
  | array n e ih => unfold tySizeAlignTy; errp
  | leaf t hne =>
    unfold tySizeAlignTy
    split
    all_goals first
      | exact absurd rfl (hne _ _)
      | errp

theorem tySizeAlignAt_strict (p : Platform) (types : TypeEnv) :
    ∀ (bound : Nat) (i : TypeIdx), ErrP Stop.Strict (tySizeAlignAt p types bound i) := by
  intro bound
  induction bound with
  | zero => intro i; unfold tySizeAlignAt; errp
  | succ n ih =>
    intro i
    have h1 := tySizeAlignTy_strict (p := p) ih
    have h2 := structSizeAlignWith_strict (tySizeAlignTy_strict (p := p) ih)
    unfold tySizeAlignAt
    errp

theorem tySizeAlignTy_strict' {p : Platform} {types : TypeEnv} {b : Nat} {ty : Ty} :
    ErrP Stop.Strict (tySizeAlignTy p (tySizeAlignAt p types b) ty) :=
  tySizeAlignTy_strict (tySizeAlignAt_strict p types b) ty
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact tySizeAlignTy_strict')

theorem renderPrint_strict {nl : Bool} : ∀ {vs : List GoValue}, ErrP Stop.Strict (renderPrint nl vs)
  | [] => by unfold renderPrint; errp
  | v :: vs => by
    have ih := @renderPrint_strict nl vs
    unfold renderPrint; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact renderPrint_strict)

theorem intElems_strict : ∀ {vs : List GoValue}, ErrP Stop.Strict (intElems vs)
  | [] => by unfold intElems; errp
  | v :: vs => by
    have ih := @intElems_strict vs
    cases v <;> (unfold intElems; errp)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact intElems_strict)

theorem evalClauses_strict (cl : List (SelectClauseHead × Stmt)) (vs : List GoValue) :
    ErrP Stop.Strict (evalClauses cl vs) := by
  fun_induction evalClauses cl vs <;> errp
theorem evalClauses_strict' {cl : List (SelectClauseHead × Stmt)} {vs : List GoValue} :
    ErrP Stop.Strict (evalClauses cl vs) := evalClauses_strict cl vs
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact evalClauses_strict')

theorem readyClauses_tame {s : Store} : ∀ {cs : List EvClause}, ErrP Stop.Tame (readyClauses s cs)
  | [] => by unfold readyClauses; errp
  | c :: cs => by
    have ih := @readyClauses_tame s cs
    unfold readyClauses; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact readyClauses_tame)

theorem Mem.storeElems_tame {base : Loc} :
    ∀ {s : Store} {start : Nat} {vs : List GoValue}, ErrP Stop.Tame (Mem.storeElems ctx s base start vs)
  | s, start, [] => by unfold Mem.storeElems; errp
  | s, start, v :: vs => by
    have ih := fun s => @Mem.storeElems_tame base s (start + 1) vs
    unfold Mem.storeElems; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact Mem.storeElems_tame)

set_option maxHeartbeats 4000000 in
theorem applyChanOp_tame {s : Store} {op : ChanStOp} {vs : List GoValue} {env : LocalEnv} {k : Cont} :
    ErrP Stop.Tame (applyChanOp ctx s op vs env k) := by
  unfold applyChanOp
  errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyChanOp_tame)

set_option maxHeartbeats 4000000 in
theorem applyRhsOp_tame {s : Store} {op : RhsOp} {vs : List GoValue} :
    ErrP Stop.Tame (applyRhsOp ctx s op vs) := by
  unfold applyRhsOp
  errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyRhsOp_tame)

set_option maxHeartbeats 4000000 in
theorem applyAtomicOp_tame {s : Store} {op : AtomicOp} {vs : List GoValue} {env : LocalEnv} {k : Cont} :
    ErrP Stop.Tame (applyAtomicOp ctx s op vs env k) := by
  unfold applyAtomicOp
  errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyAtomicOp_tame)

set_option maxHeartbeats 4000000 in
theorem applySelect_tame {s : Store} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont} {ch : Choices} :
    ErrP Stop.Tame (applySelect ctx s clauses default? vs env k ch) := by
  unfold applySelect
  errp

set_option maxHeartbeats 4000000 in
theorem applySyncOp_tame {s : Store} {ch : Choices} {op : SyncOp} {vs : List GoValue}
    {env : LocalEnv} {k : Cont} :
    ErrP Stop.Tame (applySyncOp ctx s ch op vs env k) := by
  unfold applySyncOp
  errp

/-- A plan's commits are tame on every store. -/
def CommitOk {α : Type} (plan : Except Stop (Commit α)) : Prop :=
  OkP (fun c : Commit α => ∀ s, ErrP Stop.Tame (c s)) plan

set_option maxHeartbeats 4000000 in
theorem applyStmtOp_plan_tame {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat} {vs : List GoValue} :
    ErrP Stop.Tame (applyStmtOp.plan ctx s ch op nt vs) := by
  unfold applyStmtOp.plan
  errp

set_option maxHeartbeats 4000000 in
theorem applyStmtOpCore_plan_commitOk {s : Store} {op : StmtOp} {vs : List GoValue} :
    CommitOk (applyStmtOpCore.plan ctx s op vs) := by
  unfold CommitOk applyStmtOpCore.plan
  okp
  all_goals (try (intro s; (try dsimp only); errp))

set_option maxHeartbeats 4000000 in
theorem applyStmtOp_plan_commitOk {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} : CommitOk (applyStmtOp.plan ctx s ch op nt vs) := by
  unfold CommitOk applyStmtOp.plan
  split
  · okp
    all_goals (try (intro s; (try dsimp only); errp))
  · refine OkP.bind_eq (fun c hc => OkP.pure (fun s' => ?_))
    unfold Commit.withStream
    exact ErrP.bind (applyStmtOpCore_plan_commitOk c hc s') (fun _ => ErrP.pure)

macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applySelect_tame)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applySyncOp_tame)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyStmtOp_plan_tame)

theorem resolveChain_tame (s : Store) (cur : GoValue) (st : List TargetStep) (idx : List GoValue) :
    ErrP Stop.Tame (resolveChain ctx s cur st idx) := by
  fun_induction resolveChain ctx s cur st idx <;> errp
theorem resolveChain_tame' {s : Store} {cur : GoValue} {st : List TargetStep} {idx : List GoValue} :
    ErrP Stop.Tame (resolveChain ctx s cur st idx) := resolveChain_tame s cur st idx
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact resolveChain_tame')

theorem bindParams_strict (env : LocalEnv) (s : Store) (ps : List Param) (vs : List GoValue) :
    ErrP Stop.Strict (bindParams ctx env s ps vs) := by
  fun_induction bindParams ctx env s ps vs <;> errp
theorem bindParams_strict' {env : LocalEnv} {s : Store} {ps : List Param} {vs : List GoValue} :
    ErrP Stop.Strict (bindParams ctx env s ps vs) := bindParams_strict env s ps vs
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact bindParams_strict')

theorem pinResultLocs_strict (env : LocalEnv) (ps : List Param) :
    ErrP Stop.Strict (pinResultLocs env ps) := by
  fun_induction pinResultLocs env ps <;> errp
theorem pinResultLocs_strict' {env : LocalEnv} {ps : List Param} :
    ErrP Stop.Strict (pinResultLocs env ps) := pinResultLocs_strict env ps
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact pinResultLocs_strict')

theorem CommitOk.run {α : Type} {plan : Except Stop (Commit α)} {c : Commit α}
    (h : CommitOk plan) (hc : plan = .ok c) (s : Store) : ErrP Stop.Tame (c s) := h c hc s

set_option maxHeartbeats 4000000 in
theorem mapAssignValue_plan_tame {s : Store} {kt vt : Ty} {b k v : GoValue} :
    ErrP Stop.Tame (mapAssignValue.plan ctx s kt vt b k v) := by
  unfold mapAssignValue.plan; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact mapAssignValue_plan_tame)

set_option maxHeartbeats 4000000 in
theorem mapAssignValue_plan_commitOk {s : Store} {kt vt : Ty} {b k v : GoValue} :
    CommitOk (mapAssignValue.plan ctx s kt vt b k v) := by
  unfold CommitOk mapAssignValue.plan
  okp
  all_goals (try (intro s; (try dsimp only); errp))

set_option maxHeartbeats 4000000 in
theorem storeTarget_plan_tame {s : Store} {r : TargetRef} {v : GoValue} :
    ErrP Stop.Tame (storeTarget.plan ctx s r v) := by
  unfold storeTarget.plan; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact storeTarget_plan_tame)

set_option maxHeartbeats 4000000 in
theorem storeTarget_plan_commitOk {s : Store} {r : TargetRef} {v : GoValue} :
    CommitOk (storeTarget.plan ctx s r v) := by
  unfold storeTarget.plan
  split
  · unfold CommitOk; okp
    all_goals (try (intro s; (try dsimp only); errp))
  · exact mapAssignValue_plan_commitOk

set_option maxHeartbeats 4000000 in
theorem unseqLoad_plan_tame {s : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)}
    {b t : VarId} : ErrP Stop.Tame (unseqLoad.plan ctx s env tg b t) := by
  unfold unseqLoad.plan; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact unseqLoad_plan_tame)

set_option maxHeartbeats 4000000 in
theorem unseqLoad_plan_commitOk {s : Store} {env : LocalEnv} {tg : List (VarId × TargetRef)}
    {b t : VarId} : CommitOk (unseqLoad.plan ctx s env tg b t) := by
  unfold CommitOk unseqLoad.plan
  okp
  all_goals (try (intro s; (try dsimp only); errp))

/-- The promotion path walk (G-P S2, `receiverAt`'s spine): a refusal or the
nil-dereference panic — never a stray error class. -/
theorem promotionHop_tame {s : Store} {cur : WalkCursor} {hop : PromotionHop} :
    ErrP Stop.Tame (promotionHop ctx s cur hop) := by
  unfold promotionHop
  (try dsimp only)
  errp
theorem promotionWalk_tame {s : Store} :
    ∀ {cur : WalkCursor} {hops : List PromotionHop}, ErrP Stop.Tame (promotionWalk ctx s cur hops)
  | cur, [] => by unfold promotionWalk; errp
  | cur, h :: hs => by
    have ih := fun cur => @promotionWalk_tame s cur hs
    have hh := promotionHop_tame (ctx := ctx) (s := s) (cur := cur) (hop := h)
    unfold promotionWalk; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact promotionWalk_tame)

set_option maxHeartbeats 4000000 in
theorem enterFrame_plan_tame {s : Store} {fid : FuncId} {args : List GoValue} :
    ErrP Stop.Tame (enterFrame.plan ctx s fid args) := by
  unfold enterFrame.plan; errp
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact enterFrame_plan_tame)

set_option maxHeartbeats 4000000 in
theorem enterFrame_plan_commitOk {s : Store} {fid : FuncId} {args : List GoValue} :
    CommitOk (enterFrame.plan ctx s fid args) := by
  unfold CommitOk enterFrame.plan
  okp
  all_goals (try (intro s; (try dsimp only); errp))

/-! ## The commit phase and the delivery -/

/-- `runCommit` refuses a commit's panic by name: a tame commit runs strict. -/
theorem runCommit_strict {α : Type} {c : Commit α} {s : Store} (h : ErrP Stop.Tame (c s)) :
    ErrP Stop.Strict (runCommit c s) := by
  intro e he
  unfold runCommit at he
  cases hcs : c s with
  | ok a => rw [hcs] at he; cases he
  | error e' =>
    rw [hcs] at he
    have ht := h e' hcs
    rcases e' with (_ | _ | _) | (_ | _ | _ | _) | _ <;>
      simp [throw, throwThe, MonadExceptOf.throw] at he <;> subst he <;>
      first | exact True.intro | exact ht.elim

theorem runCommit_of_toResult {α : Type} {plan : Except Stop (Commit α)} {c : Commit α}
    (hc : CommitOk plan) (h : toResult plan = .ok (.ok c)) (s : Store) :
    ErrP Stop.Strict (runCommit c s) :=
  runCommit_strict (hc.run (toResult_eq_ok_ok.mp h) s)

theorem runCommit_of_entry {σ : Store} {fid : FuncId} {args : List GoValue} {ch : Choices}
    {x : Result (Commit (Entry × Store × AccessTrace)) × Choices × List PickRecord}
    {c : Commit (Entry × Store × AccessTrace)}
    (hx : enterFramePickV ctx σ fid args ch = .ok x) (h1 : x.1 = .ok c) (s : Store) :
    ErrP Stop.Strict (runCommit c s) := by
  obtain ⟨r, ch', ps⟩ := x
  simp only at h1
  subst h1
  rcases enterFramePickV_cases hx with ⟨c', hce, hplan, -, -⟩ | ⟨msg, hr, -, -⟩
  · cases hce
    exact runCommit_strict (enterFrame_plan_commitOk.run hplan s)
  · cases hr

theorem signalRefusal_strict {sg : Signal} {k : Cont} : (signalRefusal sg k).Strict := by
  unfold signalRefusal
  repeat' split
  all_goals exact True.intro

macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact applyStmtOp_plan_commitOk)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact storeTarget_plan_commitOk)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact unseqLoad_plan_commitOk)
macro_rules | `(tactic| errp_leaf) => `(tactic| with_reducible exact enterFrame_plan_commitOk)
macro_rules | `(tactic| errp_leaf) => `(tactic| exact ErrP.throw signalRefusal_strict)

/-! ## `stepFn` -/

/-- The four blocked forms, as a Boolean. -/
def Config.blockedB : Config → Bool
  | .blockedSend .. | .blockedRecv .. | .blockedSelect .. | .blockedSync .. => true
  | _ => false

set_option maxHeartbeats 8000000 in
/-- **What `stepFn` raises** away from the abort and the blocked forms: a refusal or `fatal`
only — never a Go panic (no stray panic), never the deadlock or the race terminal, never
fuel-out. -/
theorem stepFn_strict {σ : Store} {c : Config} {ch : Choices}
    (hab : c.abort? = none) (hnb : c.blockedB = false) :
    ErrP Stop.Strict (stepFn ctx σ c ch) := by
  fun_cases stepFn ctx σ c ch
  all_goals (try (simp [Config.abort?] at hab; done))
  all_goals (try (simp [Config.blockedB] at hnb; done))
  all_goals (try (errp; done))
  all_goals errp

end GoLean.GoCore.Machine
