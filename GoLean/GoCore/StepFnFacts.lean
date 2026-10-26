import GoLean.GoCore.StepFn
import GoLean.GoCore.StateWf
import GoLean.GoCore.Consumes

/-!
# Facts about the executable step `stepFn` (the proof-support layer kept on main)

[AGENT] 2026-10-20, lane `core/retire-relation-1020`. This module is what remains of
`MachineSound.lean` after the mainline relation (`Step`/`Steps`, `Machine.lean`) and its
coherence proofs (`stepFn_sound`, `step_complete`, the driver-level soundness, the sem()
correspondence kit, the ∀-choices congruence kits, the ∀-streams checker) were RETIRED from
the build (tag `relational/last-main-2026-10-20`; the archive entry is in `docs/ARCHIVE.md`).
Every declaration below is UNCHANGED from its origin — statement, proof and name
(namespace `GoLean.GoCore.Machine`) — and was kept because the surfaces that stay on main
depend on it: the `stepFn_eqns` equation library (`Equations.lean`), the `Prefix`/`Finish`
execution statement and its proofs (`ExecutionStatement.lean`, `Prefix.lean`,
`PrefixFacts.lean`, `StepErrors.lean`) and the counted trace (`Trace.lean`). The set is the
dependency closure of those modules' proof terms (a Lean-level constant walk over the built
environment, not a hand choice) PLUS five small lemmas that closure does not contain but the
kept proof TEXT names and so needs to elaborate — `PlanNoPanic.{stuck, unsupported, internal,
panic}` (alternatives of the `plan_no_panic` tactic) and `except_bind_ok` (a `simp` argument
the final terms do not use) — kept rather than editing proofs; the tactics `commit_no_panic`,
`plan_no_panic`, `oblivious_apply`/`_applyV`/`_entry_with`, `consumption_entry_none`/`_some`
come with the proofs that invoke them. Nothing here mentions the relation.

What is here, in the origin's order: the `NoPanic`/`PlanNoPanic` discipline of the memory
module's write path and the validate/commit seam (with the `commit_no_panic` /
`plan_no_panic` tactics), the composed applies' inversions, the per-arm stream shapes of the
preprint and `unseq` step functions, `execStmtLoop_mono`, the sync/select/append/intn/convCap
apply stream lemmas, the obliviousness and pick lemmas behind the consumption theorem, the
consumption theorem itself (`stepFn_consumption_none`/`_some`), and the driver's one-step
unfoldings (`execStmtLoop_unfold`, `execStmtLoop_step`). The choice-site shape predicates
these lemmas are stated over (`consumesTryLock`, `consumesSelect`, …) are executable and
live in `Consumes.lean`.
-/

namespace GoLean.GoCore.Machine

open GoLean

-- B7 (2026-09-17): the program context is an IMPLICIT parameter of every
-- theorem here (lemma applications stay as they were).
variable {ctx : ProgramCtx}

/-! The Except-monad reduction helpers (`pure_eq_ok`, `stuck_def`,
`panic_def`, `unsupported_def`, `bind_eq_ok`) moved upstream to
`StateWf.lean` (sem-adequacy slice 3) — same names, same namespace. -/

/-- Inverting a successful bool coercion: only `.bool` values pass. -/
theorem valueAsBool_ok {v : GoValue} {b : Bool} (h : valueAsBool v = .ok b) :
    v = .bool b := by
  cases v <;> simp_all [valueAsBool]

/-! ### The write path never panics — the NoPanic section, moved above the coherence proofs
at C1 S3 (its facts feed the completeness proofs below); `Loc.rootLoc` with it -/

/-- The root `.base` location of an access path — the only heap KEY
`loadLoc`/`storeLoc` ever look up along the path. -/
def Loc.rootLoc (l : Loc) : Loc := .base ⟨Loc.rootBase l⟩

theorem Loc.rootPath_fst (l : Loc) : (Loc.rootPath l).1.id = Loc.rootBase l := by
  induction l with
  | base a => rfl
  | field b _ _ ih => simpa [Loc.rootPath, Loc.rootBase] using ih
  | index b _ ih => simpa [Loc.rootPath, Loc.rootBase] using ih

theorem Loc.rootLoc_eq (l : Loc) : Loc.rootLoc l = .base (Loc.rootPath l).1 := by
  have h := Loc.rootPath_fst l
  unfold Loc.rootLoc
  rcases hx : (Loc.rootPath l).1 with ⟨i⟩
  rw [hx] at h
  simp only at h
  rw [h]

/-! ### Panic-freeness of the store path (wave-(iii) audit fix F1, 2026-09-04)

The consumption theorem's `some` half first carried a second disjunct — "a
delivered panic AFTER the pop restores the pre-apply stream" — for two
sites. Both are REFUTED here: a TRY head's apply never raises a recoverable
panic (`applyTryLock_noPanic`), and a spilling append whose target is a
root cell (the frontend's hoisted temp — `Config.appendTargetLocal`) never
does either (`storeLoc_base_noPanic`, `buildAppendBackingValue_noPanic`).
The only panic sources on the store path are `arrayGet`'s / the leaf write's
(`writeAt`) index-out-of-range (unreachable through a PATH the machine just loaded, and
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

theorem normalizeListWith_noPanic {f : GoValue → Except Stop GoValue}
    (hf : ∀ v, NoPanic (f v)) : ∀ l, NoPanic (normalizeListWith f l)
  | [] => by rw [normalizeListWith_nil]; exact NoPanic.pure _
  | v :: rest => by
      rw [normalizeListWith_cons]
      exact NoPanic.bind (hf v) fun _ =>
        NoPanic.bind (normalizeListWith_noPanic hf rest) fun _ => NoPanic.pure _

theorem normalizeFieldsWith_noPanic {f : Ty → GoValue → Except Stop GoValue}
    (hf : ∀ t v, NoPanic (f t v)) :
    ∀ fs vs, NoPanic (normalizeFieldsWith f fs vs)
  | [], vs => by rw [normalizeFieldsWith_nil_left]; exact NoPanic.pure _
  | _ :: _, [] => by rw [normalizeFieldsWith_nil_right]; exact NoPanic.pure _
  | field :: fr, (af, v) :: vr => by
      rw [normalizeFieldsWith_cons]
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

theorem normalizeValueForTy_noPanic (ty : Ty) (v : GoValue) :
    NoPanic (normalizeValueForTy ctx ty v) := by
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

theorem defaultValue_noPanic (ty : Ty) : NoPanic (defaultValue ctx ty) := by
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

theorem buildAppendBackingValue_noPanic (elem : Ty)
    (oldValues elemValues : Array GoValue) (newCap : Nat) :
    NoPanic (buildAppendBackingValue ctx elem oldValues elemValues newCap) := by
  unfold buildAppendBackingValue
  dsimp only
  rw [← Array.forIn_toList]
  refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun values => ?_
  · exact NoPanic.bind (normalizeValueForTy_noPanic _ _) fun _ => NoPanic.pure _
  · refine NoPanic.ite ?_ ?_
    · refine NoPanic.bind (NoPanic.stuck _) fun _ => ?_
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun _ => NoPanic.pure _
      exact NoPanic.bind (defaultValue_noPanic _) fun _ => NoPanic.pure _
    · rw [Std.Legacy.Range.forIn_eq_forIn_range']
      refine NoPanic.bind (forIn_noPanic (fun a b => ?_) _ _) fun _ => NoPanic.pure _
      exact NoPanic.bind (defaultValue_noPanic _) fun _ => NoPanic.pure _

/-- `Store.alloc` never panics: the normalizer does not, and the push is pure. -/
theorem Store.alloc_noPanic (s : Store) (v : GoValue) (ty : Ty) :
    NoPanic (Store.alloc ctx s v ty) := by
  unfold Store.alloc
  exact NoPanic.bind (normalizeValueForTy_noPanic _ _) fun _ => NoPanic.pure _

/-! #### The root-first read (C1 S1): `loadLoc` as a root lookup + path read

`loadLoc` is leaf-first on the `Loc`; the module's write is root-first on
`Loc.rootPath`. The bridge below reads root-first and proves it IS
`loadLoc`, which is what the store-side NoPanic argument descends along. -/

variable (ctx) in
/-- One projection step (the `loadLoc` field/index arms, root-first). -/
def projectStep : GoValue → PathStep → Except Stop GoValue
  | .struct actualType fields, .field typeId fieldName =>
      if actualType != typeId && !structTagCompatible ctx actualType typeId then
        stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
      else
        match StructFields.lookup fields fieldName with
        | some value => return value
        | none => stuck s!"unknown GoCore struct field: {fieldName}"
  | other, .field _ _ => stuck s!"expected struct base for field load, got {repr other}"
  | .array values, .index index => arrayGet values index
  | other, .index _ => stuck s!"expected array base for index load, got {repr other}"

variable (ctx) in
/-- Root-first read along a path. -/
def readAt : GoValue → List PathStep → Except Stop GoValue
  | v, [] => pure v
  | v, step :: rest => do readAt (← projectStep ctx v step) rest

theorem readAt_append (v : GoValue) (p : List PathStep) (step : PathStep) :
    readAt ctx v (p ++ [step]) = (readAt ctx v p >>= fun x => readAt ctx x [step]) := by
  induction p generalizing v with
  | nil => simp [readAt, Bind.bind, Except.bind]
  | cons s rest ih =>
    simp only [List.cons_append, readAt]
    cases projectStep ctx v s with
    | error e => simp [Bind.bind, Except.bind]
    | ok w => simp only [Bind.bind, Except.bind]; exact ih w

/-- `loadLoc` IS the root lookup followed by the root-first read. -/
theorem loadLoc_eq_readAt (s : Store) : ∀ l : Loc,
    loadLoc ctx s l =
      match Heap.lookup s.heap (.base (Loc.rootPath l).1) with
      | some (.value _ root) => readAt ctx root (Loc.rootPath l).2
      | some (.mapPayload ..) => stuck s!"value load from a map payload cell {repr (Loc.rootLoc l)}"
      | some (.chanPayload ..) => stuck s!"value load from a channel payload cell {repr (Loc.rootLoc l)}"
      | none => stuck s!"unbound GoCore heap location: {repr (Loc.rootLoc l)}" := by
  intro l
  induction l with
  | base a =>
    obtain ⟨i⟩ := a
    simp only [loadLoc, Loc.rootPath, Loc.rootLoc, Loc.rootBase]
    split <;> simp_all [readAt]
  | field b tid f ih =>
    have hroot : (Loc.rootPath (.field b tid f)).1 = (Loc.rootPath b).1 := rfl
    have hpath : (Loc.rootPath (.field b tid f)).2 = (Loc.rootPath b).2 ++ [.field tid f] := rfl
    simp only [loadLoc]
    rw [ih]
    simp only [hroot, hpath, Loc.rootLoc_eq, readAt_append]
    split
    · rename_i ty root _
      cases hread : readAt ctx root (Loc.rootPath b).2 with
      | error e => simp [Bind.bind, Except.bind]
      | ok w =>
        simp only [Bind.bind, Except.bind]
        cases w with
        | struct actualType fields =>
          simp only [readAt, projectStep, Bind.bind, Except.bind]
          by_cases hc : (actualType != tid && !structTagCompatible ctx actualType tid) = true
          · simp [hc, stuck, throw, throwThe, MonadExceptOf.throw]
          · have hc' : (actualType != tid && !structTagCompatible ctx actualType tid) = false := by
              simpa using hc
            simp only [hc', Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
            cases StructFields.lookup fields f <;>
              simp [stuck, throw, throwThe, MonadExceptOf.throw]
        | _ => simp [readAt, projectStep, Bind.bind, Except.bind, stuck, throw, throwThe,
                MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
  | index b i ih =>
    have hroot : (Loc.rootPath (.index b i)).1 = (Loc.rootPath b).1 := rfl
    have hpath : (Loc.rootPath (.index b i)).2 = (Loc.rootPath b).2 ++ [.index i] := rfl
    simp only [loadLoc]
    rw [ih]
    simp only [hroot, hpath, Loc.rootLoc_eq, readAt_append]
    split
    · rename_i ty root _
      cases hread : readAt ctx root (Loc.rootPath b).2 with
      | error e => simp [Bind.bind, Except.bind]
      | ok w =>
        simp only [Bind.bind, Except.bind]
        cases w with
        | array values =>
          simp only [readAt, projectStep, Bind.bind, Except.bind]
          cases arrayGet values i <;> rfl
        | _ => simp [readAt, projectStep, Bind.bind, Except.bind, stuck, throw, throwThe,
                MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]

/-! #### The field-position search agrees with `StructFields.lookup` -/

theorem Ty.stepDown_noPanic (types : TypeEnv) :
    ∀ (b : Nat) (ty : Ty) (step : PathStep), NoPanic (Ty.stepDown types b ty step) := by
  intro b
  induction b with
  | zero =>
    intro ty step
    unfold Ty.stepDown
    split
    all_goals
      first
        | exact NoPanic.pure _
        | exact NoPanic.unsupported _
        | exact NoPanic.stuck _
        | (dsimp only; exact NoPanic.unsupported _)
  | succ n ih =>
    intro ty step
    unfold Ty.stepDown
    split
    -- Order-independent (audit fix round F3, 2026-09-18: the identity-type
    -- arms joined the match): every leaf arm — `pure` (the `.array` hop and
    -- the identity types), `stuck`, `unsupported` — closes here; the ONE arm
    -- left standing is the `.defined` table walk, taken below. A new arm
    -- that is none of these fails loudly at the second block.
    all_goals
      first
        | exact NoPanic.pure _
        | exact NoPanic.stuck _
        | exact NoPanic.unsupported _
        | (dsimp only; exact NoPanic.unsupported _)
        | skip
    all_goals
      (try dsimp only
       split
       · try dsimp only
         split
         · split <;> first | exact NoPanic.pure _ | exact NoPanic.stuck _
         · exact NoPanic.stuck _
       · exact ih _ _
       · exact NoPanic.unsupported _
       · exact NoPanic.unsupported _
       · exact NoPanic.unsupported _)

theorem Array.modifyM_noPanic {α : Type} {xs : Array α} {i : Nat} {f : α → Except Stop α}
    (h : (hi : i < xs.size) → NoPanic (f xs[i])) : NoPanic (xs.modifyM i f) := by
  unfold Array.modifyM
  split
  · rename_i hi
    exact NoPanic.bind (h hi) fun _ => NoPanic.pure _
  · exact NoPanic.pure _

theorem arrayIndexNatFormed_noPanic (values : Array GoValue) (i : Int) :
    NoPanic (arrayIndexNatFormed values i) := by
  unfold arrayIndexNatFormed
  split
  · exact NoPanic.pure _
  · exact NoPanic.internal _

/-- The root-first write never raises a recoverable panic (C1 S3): the leaf
normalization and the type descent refuse but never panic, and the index
re-check is a machine-invariant `.internal`. -/
theorem writeAt_noPanic :
    ∀ (path : List PathStep) (b : Nat) (ty : Ty) (root v : GoValue),
      NoPanic (writeAt ctx b ty root path v) := by
  intro path
  induction path with
  | nil =>
    intro b ty root v
    simp only [writeAt]
    exact normalizeValueForTyTy_noPanic (fun _ _ => normalizeValueForTyAt_noPanic _ _ _ _) _ _
  | cons step rest ih =>
    intro b ty root v
    cases step with
    | field tid f =>
      cases root with
      | struct actual fields =>
        unfold writeAt
        dsimp only
        -- do-notation duplicates the continuation into both `if` branches
        refine NoPanic.ite (c := (actual != tid && !structTagCompatible ctx actual tid) = true)
          (NoPanic.bind (NoPanic.stuck _) fun _ => ?tail) ?tail
        cases fieldIdx? fields f with
        | none => exact NoPanic.stuck _
        | some k =>
          refine NoPanic.bind (Ty.stepDown_noPanic _ _ _ _) fun p => ?_
          obtain ⟨fty, b'⟩ := p
          refine NoPanic.bind (Array.modifyM_noPanic fun _ => ?_) fun _ => NoPanic.pure _
          refine NoPanic.bind ?_ fun _ => NoPanic.pure _
          exact ih _ _ _ _
      | _ =>
        simp only [writeAt]
        split <;> exact NoPanic.stuck _
    | index i =>
      cases root with
      | array values =>
        simp only [writeAt]
        refine NoPanic.bind (arrayIndexNatFormed_noPanic _ _) fun k => ?_
        refine NoPanic.bind (Ty.stepDown_noPanic _ _ _ _) fun p => ?_
        obtain ⟨ety, b'⟩ := p
        exact NoPanic.bind (Array.modifyM_noPanic fun _ => ih _ _ _ _) fun _ => NoPanic.pure _
      | _ =>
        simp only [writeAt]
        split <;> exact NoPanic.stuck _

/-- The ancestor statement (wave-(iii) audit fix F1): a write along a path the read
walks never panics — since C1 S3 a corollary of `writeAt_noPanic` (no path condition). -/
theorem writeAt_noPanic_of_readAt_ok :
    ∀ {path : List PathStep} {b : Nat} {ty : Ty} {root v₀ : GoValue},
      readAt ctx root path = .ok v₀ → ∀ v, NoPanic (writeAt ctx b ty root path v) :=
  fun _ v => writeAt_noPanic _ _ _ _ v

/-- A store through a PATH the machine can load never panics: the only
panic on the store path is the index bounds check, and the load's success
puts the index in range (root-first, through `loadLoc_eq_readAt`). -/
theorem storeLoc_noPanic_of_loadLoc_ok (s : Store) :
    ∀ (loc : Loc) {v₀ : GoValue}, loadLoc ctx s loc = .ok v₀ → ∀ v, NoPanic (storeLoc ctx s loc v) := by
  intro loc v₀ h v
  rw [loadLoc_eq_readAt] at h
  unfold storeLoc Store.updateCell
  dsimp only
  split
  · rename_i hi
    refine NoPanic.bind ?_ fun _ => NoPanic.pure _
    try dsimp only
    have hcell : Heap.lookup s.heap (.base (Loc.rootPath loc).1)
        = some s.heap[(Loc.rootPath loc).1.id] := by
      simp [Heap.lookup, Array.getElem?_eq_getElem hi]
    rw [hcell] at h
    split
    · rename_i ty root hroot
      rw [hroot] at h
      exact NoPanic.map _ (writeAt_noPanic_of_readAt_ok h v)
    · split <;> exact NoPanic.stuck _
    · split <;> exact NoPanic.stuck _
  · exact NoPanic.internal _

theorem tryAcquire_noPanic (op : SyncOp) (pre : SyncPrim) : NoPanic (tryAcquire op pre) := by
  unfold tryAcquire
  split <;> first | exact NoPanic.pure _ | exact NoPanic.stuck _ | exact NoPanic.internal _

theorem enterRecvTargets_noPanic (s : Store) (targets : List Assignee) (vals : List GoValue)
    (body : Stmt) (env : LocalEnv) (k : Cont) :
    NoPanic (enterRecvTargets s targets vals body env k) := by
  unfold enterRecvTargets
  split <;> first | exact NoPanic.pure _ | exact NoPanic.stuck _

theorem tryDeliver_noPanic (b : Bool) (s : Store) (targets : List Assignee)
    (env : LocalEnv) (k : Cont) : NoPanic (tryDeliver b s targets env k) := by
  unfold tryDeliver
  split
  · exact NoPanic.pure _
  · exact NoPanic.bind (enterRecvTargets_noPanic _ _ _ _ _ _) fun _ => NoPanic.pure _

/-- **Site 2 of the retired disjunct**: a TRY head's apply never raises a
recoverable panic — `tryAcquire` refuses at most, the acquired cell is
stored through the location the apply just READ (`syncCell`), and the
result delivery is an `.evalE` entry or a refusal. -/
theorem applyTryLock_noPanic {s : Store} {loc : Loc} {pre : SyncPrim}
    (hcell : syncCell ctx s loc = .ok pre) (op : SyncOp) (spurious : Bool)
    (targets : List Assignee) (env : LocalEnv) (k : Cont) :
    NoPanic (applyTryLock ctx s op loc pre spurious targets env k) := by
  have hload : ∃ w, loadLoc ctx s loc = .ok w := by
    unfold syncCell at hcell
    cases hl : loadLoc ctx s loc with
    | error e => rw [hl] at hcell; simp [Bind.bind, Except.bind] at hcell
    | ok w => exact ⟨w, rfl⟩
  obtain ⟨w, hw⟩ := hload
  unfold applyTryLock
  try dsimp only
  -- The labelled delivery: `tryDeliver`, then a `pure` of the label (C1 S2c).
  have hdel : ∀ (b : Bool) (σ : Store) (tr : AccessTrace),
      NoPanic (do let (c', s') ← tryDeliver b σ targets env k
                  pure ((c', s', tr) : Config × Store × AccessTrace)) := fun b σ tr =>
    NoPanic.bind (tryDeliver_noPanic _ _ _ _ _) fun p => by
      obtain ⟨c, s⟩ := p
      exact NoPanic.pure _
  refine NoPanic.bind (tryAcquire_noPanic _ _) fun r => ?_
  cases r with
  | none => exact hdel _ _ _
  | some post =>
    refine NoPanic.bind (storeLoc_noPanic_of_loadLoc_ok s loc hw _) fun _ => ?_
    exact NoPanic.ite (hdel _ _ _) (hdel _ _ _)

/-! ### The validate/commit seam (C1 S3, cost B — `docs/2026-09-17_c1-memory-module-charter.md`
§2 B(b), §6 S3): the write path never panics, so every commit runs on the store it owns

`Commit`/`runCommit` (Machine.lean) and `deliverV` (StepFn.lean) split each store-bearing
apply into a VALIDATE phase that only reads and a COMMIT that only writes. The facts here:
the write primitives never raise a recoverable panic (`writeAt_noPanic` …
`Mem.storeRun_noPanic` — the index re-check is `arrayIndexNatFormed`'s `.internal`), hence
every commit a validate phase can return is panic-free (`PlanNoPanic`, the per-family
`…_commit_noPanic`), hence a delivered panic is the validate phase's and the store the step
returns is the pre-apply store — the panic convention as a theorem, not a saved copy. The
bridges (`toResult_plan_ok/_panic`, the `_inv_` inversions, `enterFramePickV_of_*`) connect
`stepFn`'s split arms to the relation's composed premises in both directions. -/

/-- A store through ANY path never raises a recoverable panic (C1 S3). -/
theorem storeLoc_noPanic (s : Store) (l : Loc) (v : GoValue) : NoPanic (storeLoc ctx s l v) := by
  unfold storeLoc Store.updateCell
  dsimp only
  split
  · refine NoPanic.bind ?_ fun _ => NoPanic.pure _
    try dsimp only
    split
    · exact NoPanic.map _ (writeAt_noPanic _ _ _ _ _)
    · split <;> exact NoPanic.stuck _
    · split <;> exact NoPanic.stuck _
  · exact NoPanic.internal _

theorem Mem.store_noPanic (s : Store) (l : Loc) (v : GoValue) : NoPanic (Mem.store ctx s l v) :=
  NoPanic.bind (storeLoc_noPanic _ _ _) fun _ => NoPanic.pure _

theorem storeMapPayload_noPanic (s : Store) (l : Loc) (es : Array (Nat × GoValue × GoValue))
    (n : Nat) : NoPanic (storeMapPayload s l es n) := by
  unfold storeMapPayload
  split
  · unfold Store.updateCell
    split
    · refine NoPanic.bind ?_ fun _ => NoPanic.pure _
      try dsimp only
      split <;> first | exact NoPanic.pure _ | exact NoPanic.stuck _
    · exact NoPanic.internal _
  · exact NoPanic.stuck _

theorem Mem.mapWrite_noPanic (s : Store) (l : Loc) (es : Array (Nat × GoValue × GoValue))
    (n : Nat) : NoPanic (Mem.mapWrite s l es n) :=
  NoPanic.bind (storeMapPayload_noPanic _ _ _ _) fun _ => NoPanic.pure _

theorem Mem.storeElems_noPanic : ∀ (vs : List GoValue) (s : Store) (base : Loc) (start : Nat),
    NoPanic (Mem.storeElems ctx s base start vs)
  | [], s, base, start => by
      simp only [Mem.storeElems]
      exact NoPanic.pure _
  | v :: vs, s, base, start => by
      simp only [Mem.storeElems]
      refine NoPanic.bind (Mem.store_noPanic _ _ _) fun p => ?_
      obtain ⟨s₁, t⟩ := p
      refine NoPanic.bind (Mem.storeElems_noPanic vs s₁ base (start + 1)) fun q => ?_
      obtain ⟨s₂, ts⟩ := q
      exact NoPanic.pure _

theorem Mem.storeRun_noPanic (s : Store) (sl : SliceValue) (start : Nat) (vs : List GoValue) :
    NoPanic (Mem.storeRun ctx s sl start vs) := by
  unfold Mem.storeRun
  split
  · exact Mem.storeElems_noPanic _ _ _ _
  · split
    · exact NoPanic.pure _
    · exact NoPanic.stuck _

theorem bindParams_noPanic : ∀ (env : LocalEnv) (s : Store) (ps : List Param) (vs : List GoValue),
    NoPanic (bindParams ctx env s ps vs)
  | env, s, [], [] => by simp only [bindParams]; exact NoPanic.pure _
  | env, s, p :: ps, v :: vs => by
      simp only [bindParams]
      refine NoPanic.bind (normalizeValueForTy_noPanic _ _) fun v' => ?_
      refine NoPanic.bind (Store.alloc_noPanic _ _ _) fun q => ?_
      obtain ⟨loc, s₁⟩ := q
      exact bindParams_noPanic _ s₁ ps vs
  | _, _, [], _ :: _ => by simp only [bindParams]; exact NoPanic.stuck _
  | _, _, _ :: _, [] => by simp only [bindParams]; exact NoPanic.stuck _

theorem allocDecls_noPanic : ∀ (env : LocalEnv) (s : Store) (ps : List Param),
    NoPanic (allocDecls ctx env s ps)
  | env, s, [] => by simp only [allocDecls]; exact NoPanic.pure _
  | env, s, p :: ps => by
      simp only [allocDecls]
      refine NoPanic.bind (defaultValue_noPanic _) fun v => ?_
      refine NoPanic.bind (Store.alloc_noPanic _ _ _) fun q => ?_
      obtain ⟨loc, s₁⟩ := q
      exact allocDecls_noPanic _ s₁ ps

theorem pinResultLocs_noPanic (env : LocalEnv) : ∀ (ps : List Param),
    NoPanic (pinResultLocs env ps)
  | [] => by simp only [pinResultLocs]; exact NoPanic.pure _
  | p :: ps => by
      simp only [pinResultLocs]
      split
      · exact NoPanic.bind (pinResultLocs_noPanic env ps) fun _ => NoPanic.pure _
      · exact NoPanic.stuck _

/-- «Every commit the validate phase can return is panic-free» — the per-family
statement, over the phase's `Except`. -/
def PlanNoPanic {α : Type} (p : Except Stop (Commit α)) : Prop :=
  ∀ c, p = .ok c → ∀ s, NoPanic (c s)

theorem PlanNoPanic.error {α : Type} (e : Stop) : PlanNoPanic (.error e : Except Stop (Commit α)) :=
  fun _ h => by cases h
theorem PlanNoPanic.stuck {α : Type} (m : String) :
    PlanNoPanic (GoCore.stuck m : Except Stop (Commit α)) := fun _ h => by cases h
theorem PlanNoPanic.unsupported {α : Type} (m : String) :
    PlanNoPanic (GoCore.unsupported m : Except Stop (Commit α)) := fun _ h => by cases h
theorem PlanNoPanic.internal {α : Type} (m : String) :
    PlanNoPanic (throw (Stop.internal m) : Except Stop (Commit α)) :=
  fun _ h => by simp [throw, throwThe, MonadExceptOf.throw] at h
theorem PlanNoPanic.panic {α : Type} (m : String) :
    PlanNoPanic (GoCore.panic m : Except Stop (Commit α)) := fun _ h => by cases h
theorem PlanNoPanic.pure {α : Type} {c : Commit α} (h : ∀ s, NoPanic (c s)) :
    PlanNoPanic (pure c : Except Stop (Commit α)) := fun c' hc => by
  obtain rfl := Except.ok.inj hc
  exact h
theorem PlanNoPanic.bind {α β : Type} {x : Except Stop β} {f : β → Except Stop (Commit α)}
    (hf : ∀ b, x = .ok b → PlanNoPanic (f b)) : PlanNoPanic (x >>= f) := fun c h => by
  cases hx : x with
  | error e => rw [hx] at h; simp [Bind.bind, Except.bind] at h
  | ok b => rw [hx] at h; simp only [Bind.bind, Except.bind] at h; exact hf b hx c h
theorem PlanNoPanic.ite {α : Type} {P : Prop} [Decidable P] {a b : Except Stop (Commit α)}
    (ha : PlanNoPanic a) (hb : PlanNoPanic b) : PlanNoPanic (if P then a else b) := by
  split <;> assumption

/-- Discharge `NoPanic` over a COMMIT body: the write primitives, the allocators,
the entry's binders, pure returns, and pair destructuring at every bind. -/
macro "commit_no_panic" : tactic =>
  `(tactic| (repeat first
    | exact NoPanic.ok _
    | exact NoPanic.pure _
    | exact NoPanic.stuck _
    | exact NoPanic.unsupported _
    | exact NoPanic.internal _
    | exact Store.alloc_noPanic _ _ _
    | exact Mem.store_noPanic _ _ _
    | exact Mem.mapWrite_noPanic _ _ _ _
    | exact Mem.storeRun_noPanic _ _ _ _
    | exact Mem.storeElems_noPanic _ _ _ _
    | exact bindParams_noPanic _ _ _ _
    | exact allocDecls_noPanic _ _ _
    | exact pinResultLocs_noPanic _ _
    | assumption
    | apply NoPanic.ite
    | apply NoPanic.map
    | (apply NoPanic.bind; rotate_left)
    | unfold Commit.withStream
    | (intro p; obtain ⟨_, _⟩ := p)
    | intro _
    | dsimp only))

/-- Discharge `PlanNoPanic` over a VALIDATE phase: every arm's returned commit through
`commit_no_panic`, every bind, `if` and `match` opened. -/
macro "plan_no_panic" : tactic =>
  `(tactic| (repeat' first
    | exact PlanNoPanic.error _
    | exact PlanNoPanic.stuck _
    | exact PlanNoPanic.internal _
    | exact PlanNoPanic.panic _
    | exact PlanNoPanic.unsupported _
    | (apply PlanNoPanic.pure; intro s; commit_no_panic; done)
    | (apply PlanNoPanic.bind; intro b hb
       try (simp only [pure_eq_ok, Except.ok.injEq] at hb; subst hb))
    | apply PlanNoPanic.ite
    | dsimp only
    | split))

theorem mapAssignValue_commit_noPanic (s : Store) (keyTy valueTy : Ty)
    (baseV keyV valueV : GoValue) :
    PlanNoPanic (mapAssignValue.plan ctx s keyTy valueTy baseV keyV valueV) := by
  unfold mapAssignValue.plan
  plan_no_panic

theorem applyStmtOpCore_commit_noPanic (s : Store) (op : StmtOp) (vs : List GoValue) :
    PlanNoPanic (applyStmtOpCore.plan ctx s op vs) := by
  rw [applyStmtOpCore.plan.eq_def]
  split
  all_goals first
    | exact mapAssignValue_commit_noPanic _ _ _ _ _ _
    | plan_no_panic
  all_goals first
    | exact mapAssignValue_commit_noPanic _ _ _ _ _ _
    | plan_no_panic

theorem applyStmtOp_commit_noPanic (s : Store) (ch : Choices) (op : StmtOp) (nt : Nat)
    (vs : List GoValue) : PlanNoPanic (applyStmtOp.plan ctx s ch op nt vs) := by
  rw [applyStmtOp.plan.eq_def]
  split
  · plan_no_panic
  · -- the `[0, n)` draw (unit 5b): the consult, then one `int` store or nothing
    plan_no_panic
  · -- every other head: the core's commit, lifted beside the stream
    refine PlanNoPanic.bind fun c hc => PlanNoPanic.pure fun s' => ?_
    unfold Commit.withStream
    refine NoPanic.bind (applyStmtOpCore_commit_noPanic _ _ _ c hc s') fun p => ?_
    obtain ⟨_, _⟩ := p
    exact NoPanic.pure _

theorem storeTarget_commit_noPanic (s : Store) (r : TargetRef) (v : GoValue) :
    PlanNoPanic (storeTarget.plan ctx s r v) := by
  unfold storeTarget.plan
  cases r with
  | chain anchor idxs steps => plan_no_panic
  | mapElem b k kt vt => exact mapAssignValue_commit_noPanic _ _ _ _ _ _

theorem enterFrame_commit_noPanic (s : Store) (fid : FuncId) (argVals : List GoValue) :
    PlanNoPanic (enterFrame.plan ctx s fid argVals) := by
  unfold enterFrame.plan
  plan_no_panic

/-! #### `runCommit`, `deliverV` and the composed apply -/

theorem runCommit_eq_ok {α : Type} {c : Commit α} {s : Store} {a : α} :
    runCommit c s = .ok a ↔ c s = .ok a := by
  unfold runCommit
  split
  · rename_i msg heq
    rw [heq]
    simp [throw, throwThe, MonadExceptOf.throw]
  · exact Iff.rfl

theorem runCommit_withStream {ch : Choices} {ps : List PickRecord} {c : Commit (Store × AccessTrace)}
    {s : Store} :
    runCommit (Commit.withStream ch ps c) s = (runCommit c s).map fun p => (p.1, ch, ps, p.2) := by
  unfold runCommit Commit.withStream
  cases hcs : c s with
  | error e =>
    simp only [Bind.bind, Except.bind]
    split <;> split <;> simp_all [Except.map, throw, throwThe, MonadExceptOf.throw]
  | ok p =>
    obtain ⟨s', tr⟩ := p
    simp [Bind.bind, Except.bind, Except.map, pure, Except.pure]

theorem deliverV_ok_inv {α : Type} {s : Store} {k : Cont} {ch : Choices}
    {next : α → Config × Store × Choices × StepLabel} {c : Commit α} {chain : List PanicEntry}
    {ps : List PickRecord} {out : Config × Store × Choices × StepLabel}
    (h : deliverV s k ch next (.ok c) chain ps = .ok out) : ∃ a, c s = .ok a ∧ next a = out := by
  simp only [deliverV_ok] at h
  cases hr : runCommit c s with
  | error e => rw [hr] at h; simp [Functor.map, Except.map] at h
  | ok a =>
    rw [hr] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨a, runCommit_eq_ok.mp hr, h⟩

/-! #### The per-family inversions (the composed apply's `.ok`/`.panic` read back to its phases) -/

theorem applyStmtOp_inv_ok {s : Store} {ch : Choices} {op : StmtOp} {nt : Nat} {vs : List GoValue}
    {a : Store × Choices × List PickRecord × AccessTrace} (h : applyStmtOp ctx s ch op nt vs = .ok a) :
    ∃ c, applyStmtOp.plan ctx s ch op nt vs = .ok c ∧ c s = .ok a := by
  unfold applyStmtOp at h
  exact bind_eq_ok.mp h

theorem storeTarget_inv_ok {s : Store} {r : TargetRef} {v : GoValue} {a : Store × AccessTrace}
    (h : storeTarget ctx s r v = .ok a) :
    ∃ c, storeTarget.plan ctx s r v = .ok c ∧ c s = .ok a := by
  unfold storeTarget at h
  exact bind_eq_ok.mp h

theorem enterFrame_inv_ok {s : Store} {fid : FuncId} {args : List GoValue}
    {a : Entry × Store × AccessTrace} (h : enterFrame ctx s fid args = .ok a) :
    ∃ c, enterFrame.plan ctx s fid args = .ok c ∧ c s = .ok a := by
  unfold enterFrame at h
  exact bind_eq_ok.mp h

theorem enterFrame_inv_panic {s : Store} {fid : FuncId} {args : List GoValue} {msg : String}
    (h : enterFrame ctx s fid args = .error (.panic msg)) :
    enterFrame.plan ctx s fid args = .error (.panic msg) := by
  unfold enterFrame at h
  rcases plan_run_error h with hp | ⟨c, hc, hcs⟩
  · exact hp
  · exact absurd hcs (enterFrame_commit_noPanic _ _ _ c hc s msg)

/-! #### The V entry funnel against the composed one -/

theorem enterFramePickV_of_plan_ok {s : Store} {fid : FuncId} {args : List GoValue}
    {c : Commit (Entry × Store × AccessTrace)}
    (h : enterFrame.plan ctx s fid args = .ok c) (ch : Choices) :
    enterFramePickV ctx s fid args ch = .ok (.ok c, ch, []) := by
  simp [enterFramePickV, h]

theorem enterFramePickV_of_plan_panic {s : Store} {fid : FuncId} {args : List GoValue}
    {msg : String} (h : enterFrame.plan ctx s fid args = .error (.panic msg)) (ch : Choices) :
    enterFramePickV ctx s fid args ch
      = .ok (.panic (entryPanicText ctx fid args msg
            (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1),
          (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).2,
          (PickRecord.ofPick .nilValueMethodText (nilValueMethodWidth ctx fid args) (Choices.consumeAt .nilValueMethodText (nilValueMethodWidth ctx fid args) ch).1)) := by
  simp [enterFramePickV, h, Choices.consumeAtE_eq]

/-- An entry that does NOT panic never touches the stream — the V twin of
`enterFramePick_of_nopanic`. -/
theorem enterFramePickV_of_nopanic {s : Store} {fid : FuncId} {args : List GoValue}
    (hnp : ∀ msg, enterFrame ctx s fid args ≠ .error (.panic msg)) (ch : Choices) :
    enterFramePickV ctx s fid args ch = (toResult (enterFrame.plan ctx s fid args)).map (·, ch, []) := by
  unfold enterFramePickV
  cases hx : toResult (enterFrame.plan ctx s fid args) with
  | error e => rfl
  | ok r =>
    cases r with
    | ok c => rfl
    | panic msg =>
      exfalso
      apply hnp msg
      simp [enterFrame, toResult_eq_ok_panic.mp hx, Bind.bind, Except.bind]

/-! #### The wide-statement plan's stream shape -/

/-- Every non-append head's plan is the core's plan lifted beside the stream. -/
theorem applyStmtOp_plan_eq_core {σ : Store} {ch : Choices} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} (hop : ∀ e, op ≠ .appendSlice e) (hri : op ≠ .randIntn) :
    applyStmtOp.plan ctx σ ch op nt vs = (applyStmtOpCore.plan ctx σ op vs).map (Commit.withStream ch []) := by
  cases op <;>
    first
    | exact absurd rfl (hop _)
    | exact absurd rfl hri
    | (simp only [applyStmtOp.plan, Bind.bind, Except.bind, Except.map, pure, Except.pure]
       try (cases applyStmtOpCore.plan ctx σ _ vs <;> rfl))

/-! ### Soundness -/

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
      obtain ⟨h1, h2, h3, h4⟩ := $h:ident
      subst h1; subst h2; subst h3; subst h4
      exact ⟨rfl, fun ch => by simp [stepFn, hres, Bind.bind, Except.bind]⟩
    | panic msg =>
      simp only [deliverS_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3, h4⟩ := $h:ident
      subst h1; subst h2; subst h3; subst h4
      exact ⟨rfl, fun ch => by simp [stepFn, hres, Bind.bind, Except.bind]⟩))

/-- B2 + C1 S3 VALIDATE/COMMIT apply arm of the `none` sweep: the plan reads no
stream, the commit reads no stream. -/
macro "oblivious_applyV " h:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, bind_eq_ok]
    obtain ⟨r, hres, $h:ident⟩ := $h:ident
    (try simp only [List.reverse_cons] at hres)
    cases r with
    | ok c =>
      obtain ⟨a, hc, $h:ident⟩ := deliverV_ok_inv $h:ident
      simp only [Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3, h4⟩ := $h:ident
      subst h1; subst h2; subst h3; subst h4
      exact ⟨rfl, fun ch => by
        simp [stepFn, hres, runCommit_eq_ok.mpr hc, Functor.map, Except.map, Bind.bind, Except.bind]⟩
    | panic msg =>
      simp only [deliverV_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
      obtain ⟨h1, h2, h3, h4⟩ := $h:ident
      subst h1; subst h2; subst h3; subst h4
      exact ⟨rfl, fun ch => by simp [stepFn, hres, Bind.bind, Except.bind]⟩))

/-! ### The preprint phase's step functions (BUG-004 item 4, unit 6b)

`stepPanicStop`/`stepRetOther`/`stepNextOther` (StepFn.lean) sit at three
existing `stepFn` arm positions (the `.stop` arm, the `.retV` and `.next`
catch-alls), proved here against their `Step` rules and their stream
contract — the `stepFrameExit_sound` pattern. -/

/-- The `.retV` catch-all is stream-oblivious: it draws nothing. -/
theorem stepRetOther_stream {s : Store} {v : GoValue} {k : Cont} {ch₀ : Choices}
    {c' : Config} {s' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepRetOther s v k ch₀ = .ok (c', s', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepRetOther s v k ch = .ok (c', s', ch, tr) := by
  unfold stepRetOther at h ⊢
  split at h
  · split at h
    · simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun ch => rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `.next` catch-all is stream-oblivious: the resolution reads the
store, never the stream. -/
theorem stepNextOther_stream {s : Store} {k : Cont} {ch₀ : Choices}
    {c' : Config} {s' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepNextOther ctx s k ch₀ = .ok (c', s', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepNextOther ctx s k ch = .ok (c', s', ch, tr) := by
  unfold stepNextOther at h ⊢
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨r, hr, h⟩ := h
    simp only [pure_eq_ok, Except.ok.injEq] at h
    cases r with
    | ok a =>
      obtain ⟨fid, recv, tr₀⟩ := a
      simp only [deliverS_ok, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun ch => by simp [hr, Bind.bind, Except.bind, deliverS]⟩
    | panic msg =>
      simp only [deliverS_panic, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, fun ch => by simp [hr, Bind.bind, Except.bind, deliverS]⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `.stop` arm's consumption, `none` half: no collision — the phase
step pops nothing and is stream-oblivious (a settled chain never returns
`.ok`). -/
theorem stepPanicStop_consumption_none {σ : Store} {first : PanicEntry} {rest : List PanicEntry}
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (hsc : seqConsumption ctx σ (.panicking (first :: rest) .stop) = none)
    (h : stepPanicStop ctx σ first rest ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepPanicStop ctx σ first rest ch = .ok (c', σ', ch, tr) := by
  unfold stepPanicStop at h ⊢
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨msg, -, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i older entry newer hsplit
    simp only [seqConsumption, hsplit] at hsc
    split at h
    · -- the decision step (2026-10-23): no draw, stream-oblivious
      simp only [bind_eq_ok] at h
      obtain ⟨m, hm, h⟩ := h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      rw [hm]
      rfl
    · rename_i m hp
      have hpend : entry.isPending = true := by simp [PanicEntry.isPending, hp]
      simp only [hpend, Bool.true_and] at hsc
      have hcol : preprintCollide older entry = false := by
        cases hc : preprintCollide older entry
        · rfl
        · simp [hc] at hsc
      have hw : preprintWidth older entry = 1 := by simp [preprintWidth, hcol]
      rw [hw, Choices.consumeAtE_le_one (Nat.le_refl 1)] at h
      simp only [hcol, Bool.false_and, Bool.false_eq_true, ↓reduceIte, pure_eq_ok, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      simp [hw, Choices.consumeAtE_le_one (Nat.le_refl 1), hcol]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `.stop` arm's consumption, `some` half: a collision — the
`repanicCollapse` pop at bound 2; the step depends on the stream only
through the pick. -/
theorem stepPanicStop_consumption_some {σ : Store} {first : PanicEntry} {rest : List PanicEntry}
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    {site : ChoiceSite} {b : Nat}
    (hsc : seqConsumption ctx σ (.panicking (first :: rest) .stop) = some (site, b))
    (h : stepPanicStop ctx σ first rest ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepPanicStop ctx σ first rest ch = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) := by
  unfold stepPanicStop at h ⊢
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨msg, -, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i older entry newer hsplit
    simp only [seqConsumption, hsplit] at hsc
    split at h
    · -- the decision step (2026-10-23) reports no site
      rename_i hu
      exfalso
      have : entry.isPending = false := by simp [PanicEntry.isPending, hu]
      simp [this] at hsc
    · rename_i m hp
      have hpend : entry.isPending = true := by simp [PanicEntry.isPending, hp]
      simp only [hpend, Bool.true_and] at hsc
      have hcol : preprintCollide older entry = true := by
        cases hc : preprintCollide older entry
        · simp [hc] at hsc
        · rfl
      simp only [hcol, ite_true, Option.some.injEq, Prod.mk.injEq] at hsc
      obtain ⟨rfl, rfl⟩ := hsc
      have hw : preprintWidth older entry = 2 := by simp [preprintWidth, hcol]
      rw [hw] at h ⊢
      rcases hx : Choices.consumeAtE .repanicCollapse 2 ch₀ with ⟨pick, ch'', ps⟩
      rw [hx] at h
      simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, hx'⟩ := Choices.consumeAtE_inv hx
      refine ⟨by rw [hx'], fun ch hpk => ?_⟩
      rw [hx'] at hpk
      obtain ⟨p, cs, hpc⟩ : ∃ p cs, Choices.consumeAt .repanicCollapse 2 ch = (p, cs) := ⟨_, _, rfl⟩
      rw [hpc] at hpk ⊢
      simp only at hpk
      subst hpk
      simp [hpc, Choices.consumeAtE_eq]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ### The `unseq` construct's step functions (Stage B, 2026-09-16)

`stepUnseqEnter`/`stepUnseqValue`/`stepUnseqNext` (StepFn.lean) are the
three `stepFn` arms of the sweep frame, proved here against their `Step`
rules and their stream contract, then consumed by the positional cases of
`stepFn_sound` and the consumption theorems — the `stepFrameExit_sound`
pattern, which keeps the arms' internal splits out of `stepFn`'s
positional case tags. -/

theorem stepUnseqEnter_stream {s : Store} {g : UnseqGraph} {thenB : Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices} {c' : Config} {s' : Store} {ch' : Choices} {tr : StepLabel}
    (h : stepUnseqEnter ctx s g thenB env k ch = .ok (c', s', ch', tr)) :
    ch' = ch ∧ ∀ ch₂ : Choices, stepUnseqEnter ctx s g thenB env k ch₂ = .ok (c', s', ch₂, tr) := by
  unfold stepUnseqEnter at h
  split at h
  · split at h
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i heq _ hwf _ hentry
          subst heq
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl, rfl⟩ := h
          exact ⟨rfl, fun ch₂ => by simp [stepUnseqEnter, hwf, hentry, hd, Bind.bind, Except.bind]⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem stepUnseqValue_stream {s : Store} {v : GoValue} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (VarId × TargetRef)} {env : LocalEnv} {ph : UnseqPhase}
    {k : Cont} {ch : Choices} {c' : Config} {s' : Store} {ch' : Choices} {tr : StepLabel}
    (h : stepUnseqValue ctx s v g thenB st tg env ph k ch = .ok (c', s', ch', tr)) :
    ch' = ch ∧ ∀ ch₂ : Choices, stepUnseqValue ctx s v g thenB st tg env ph k ch₂ = .ok (c', s', ch₂, tr) := by
  unfold stepUnseqValue at h
  split at h
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i i o hget
      split at h
      · rename_i bind head hbody
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨loc, hloc, ⟨s₂, trs⟩, hst, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqValue, hget, hbody, hloc, hst, Bind.bind, Except.bind]⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The run/wait phases of the sweep frame never touch the stream (the
common tail of the two consumption lemmas). -/
theorem stepUnseqNext_run_wait_stream {s : Store} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (VarId × TargetRef)} {env : LocalEnv} {ph : UnseqPhase}
    {k : Cont} {ch : Choices} {c' : Config} {s' : Store} {ch' : Choices} {tr : StepLabel}
    (hph : ph ≠ .pick)
    (h : stepUnseqNext ctx s g thenB st tg env ph k ch = .ok (c', s', ch', tr)) :
    ch' = ch ∧ ∀ ch₂ : Choices, stepUnseqNext ctx s g thenB st tg env ph k ch₂ = .ok (c', s', ch₂, tr) := by
  unfold stepUnseqNext at h
  split at h
  · exact absurd rfl hph
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i i o hget
      split at h
      · rename_i bind head hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i binds callee args hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i binds ch elem hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i bind spec hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i binds spec hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i bind tgt hbody
        simp only [bind_eq_ok] at h
        obtain ⟨r, hres, h⟩ := h
        cases r with
        | ok c =>
          obtain ⟨a, hc, h⟩ := deliverV_ok_inv h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨rfl, fun ch₂ => by
            simp [stepUnseqNext, hget, hbody, hres, runCommit_eq_ok.mpr hc, Functor.map, Except.map, Bind.bind, Except.bind]⟩
        | panic msg =>
          simp only [deliverV_panic, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody, hres, Bind.bind, Except.bind]⟩
      · rename_i bind lhs hbody
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨r, trr⟩, hplan, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody, hplan, Bind.bind, Except.bind]⟩
      · rename_i test w out hbody
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨st', s₂, trg⟩, hg, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody, hg, Bind.bind, Except.bind]⟩
  · split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i i o hget
      split at h
      · rename_i binds callee args hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i binds ch elem hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i bind spec hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · rename_i binds spec hbody
        simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch₂ => by simp [stepUnseqNext, hget, hbody]⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The scheduler's step is stream-oblivious when its projection is `none`:
a run/wait phase, a completion, or a pick over a ready set of size ≤ 1 (a
bound-≤-1 consult is inert, G-U). -/
theorem stepUnseqNext_consumption_none {σ : Store} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (VarId × TargetRef)} {env : LocalEnv} {ph : UnseqPhase}
    {k : Cont} {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (hsc : seqConsumption ctx σ (.next (.unseqK g thenB st tg env ph k)) = none)
    (h : stepUnseqNext ctx σ g thenB st tg env ph k ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepUnseqNext ctx σ g thenB st tg env ph k ch = .ok (c', σ', ch, tr) := by
  cases ph with
  | run i => exact stepUnseqNext_run_wait_stream (by simp) h
  | wait i => exact stepUnseqNext_run_wait_stream (by simp) h
  | pick =>
    have hle : (g.ready st).length ≤ 1 := by
      simp only [seqConsumption] at hsc
      split at hsc
      · cases hsc
      · omega
    have h' := h
    simp only [stepUnseqNext] at h'
    split at h'
    · simp [throw, throwThe, MonadExceptOf.throw] at h'
    · rename_i hdep
      split at h'
      · rename_i hall
        split at h'
        · simp [throw, throwThe, MonadExceptOf.throw] at h'
        · rename_i hprod
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h'
          obtain ⟨⟨refs, vals⟩, hplan, rfl, rfl, rfl, rfl⟩ := h'
          exact ⟨rfl, fun ch => by
            simp [stepUnseqNext, hdep, hall, hprod, hplan, Bind.bind, Except.bind]⟩
      · rename_i hall
        split at h'
        · rename_i i hi
          rw [Choices.consumeAtE_le_one hle] at hi h'
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h' hi
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
          exact ⟨rfl, fun ch => by
            simp [stepUnseqNext, hdep, hall, Choices.consumeAtE_le_one hle, hi]⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h'

/-- The scheduler's pick DRAWS the `unseqNext` site at bound `|ready|` and
depends on the stream only through that pick. -/
theorem stepUnseqNext_consumption_some {σ : Store} {g : UnseqGraph} {thenB : Stmt}
    {st : List UnseqStatus} {tg : List (VarId × TargetRef)} {env : LocalEnv} {ph : UnseqPhase}
    {k : Cont} {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    {site : ChoiceSite} {b : Nat}
    (hsc : seqConsumption ctx σ (.next (.unseqK g thenB st tg env ph k)) = some (site, b))
    (h : stepUnseqNext ctx σ g thenB st tg env ph k ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepUnseqNext ctx σ g thenB st tg env ph k ch = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) := by
  cases ph with
  | run i => simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc
  | wait i => simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc
  | pick =>
    obtain ⟨rfl, rfl, hge⟩ : site = .unseqNext ∧ b = (g.ready st).length
        ∧ 2 ≤ (g.ready st).length := by
      simp only [seqConsumption] at hsc
      split at hsc
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsc
        exact ⟨hsc.1.symm, hsc.2.symm, ‹_›⟩
      · cases hsc
    have h' := h
    simp only [stepUnseqNext] at h'
    split at h'
    · simp [throw, throwThe, MonadExceptOf.throw] at h'
    · rename_i hdep
      split at h'
      · rename_i hall
        have := UnseqGraph.ready_nil_of_allSettled hall
        rw [this] at hge
        simp at hge
      · rename_i hall
        split at h'
        · rename_i i hi
          rw [Choices.consumeAtE_eq] at hi h'
          obtain ⟨p, cs, hpc⟩ : ∃ p cs,
              Choices.consumeAt .unseqNext (g.ready st).length ch₀ = (p, cs) := ⟨_, _, rfl⟩
          rw [hpc] at hi h'
          simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h' hi
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
          refine ⟨by rw [hpc], fun ch hpk => ?_⟩
          rw [hpc] at hpk
          obtain ⟨p₂, cs₂, hpc₂⟩ : ∃ p cs,
              Choices.consumeAt .unseqNext (g.ready st).length ch = (p, cs) := ⟨_, _, rfl⟩
          rw [hpc₂] at hpk ⊢
          simp only at hpk
          subst hpk
          simp [stepUnseqNext, hdep, hall, hpc₂, hi, Choices.consumeAtE_eq]
        · simp [throw, throwThe, MonadExceptOf.throw] at h'

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
    ∀ (fuel fuel' : Nat) (σ : Store) (c : Config) (ch : Choices)
      (r : Store × Choices),
    fuel ≤ fuel' → execStmtLoop ctx fuel σ c ch = .ok r →
    execStmtLoop ctx fuel' σ c ch = .ok r := by
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
    cases hstep : stepFn ctx σ c ch with
    | error e => rw [hstep] at h; simp [Except.bind] at h
    | ok trip =>
      obtain ⟨c', σ', ch', tr⟩ := trip
      rw [hstep] at h
      simp only [Except.bind] at h ⊢
      exact ih _ _ _ _ _ _ (by omega) h

-- `structTagCompatible_congr` («the tag-compatibility check reads only the
-- types map», triage L7) is RETIRED with B7: the check takes the fixed
-- `ProgramCtx`, so two stores cannot disagree on it — the lemma was
-- `htypes ▸ rfl`. Tombstone in `docs/2026-09-17_b7-context-store-handoff.md`.

/-! ### The TRY heads' half of the ∀-choices kit (Q-TRYLOCK, 2026-09-03)

`applySyncOp` threads the stream only for the TRY heads, whose apply is
pick-independent in outcome CLASS by the pre-commit discipline
(`applyTryLock`: the acquired cell is stored BEFORE the pick applies, and
`tryDeliver`'s success depends on the target list alone). -/

/-- A non-TRY head's apply passes the stream through untouched, on
success — the `applyStmtOp_eq_core` twin. -/
theorem applySyncOp_core_ok {σ : Store} {ch₀ : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {c' : Config}
    {σ' : Store} {ch' : Choices} {ps : List PickRecord} {tr : AccessTrace}
    (hop : op.tryTargets? = none)
    (h : applySyncOp ctx σ ch₀ op vs env k = .ok (c', σ', ch', ps, tr)) :
    ch' = ch₀ ∧ ps = [] ∧
      ∀ ch : Choices, applySyncOp ctx σ ch op vs env k = .ok (c', σ', ch, [], tr) := by
  rw [applySyncOp.eq_def] at h
  rw [hop] at h
  simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨c₀, σ₀, tr₀⟩, hcore, rfl, rfl, rfl, rfl, rfl⟩ := h
  refine ⟨rfl, rfl, fun ch => ?_⟩
  rw [applySyncOp.eq_def, hop]
  simp [hcore, Bind.bind, Except.bind]

/-- … and on error. -/
theorem applySyncOp_core_error {σ : Store} {ch₀ : Choices} {op : SyncOp}
    {vs : List GoValue} {env : LocalEnv} {k : Cont} {e : Stop}
    (hop : op.tryTargets? = none)
    (h : applySyncOp ctx σ ch₀ op vs env k = .error e) :
    ∀ ch : Choices, applySyncOp ctx σ ch op vs env k = .error e := by
  intro ch
  rw [applySyncOp.eq_def] at h ⊢
  rw [hop] at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hcore : applySyncOpCore ctx σ op vs env k with
  | error e' => rw [hcore] at h; simpa using h
  | ok r => rw [hcore] at h; cases h

/-! ### The per-site stream lemmas behind `stepFn_consumption` (B8) -/

theorem except_bind_ok {ε α β : Type} (a : α)
    (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- A `.done` readiness analysis: `applySelect` passes the stream through. -/
theorem applySelect_done_stream {σ : Store} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {c₁ : Config} {s₁ : Store} {cl? : Option EvClause} {tr : AccessTrace}
    (h : applySelectCore ctx σ clauses default? vs env k = .ok (.done c₁ s₁ cl? tr)) (ch : Choices) :
    applySelect ctx σ clauses default? vs env k ch = .ok (c₁, s₁, ch, [], cl?, tr) := by
  simp [applySelect, h, Bind.bind, Except.bind]

/-- A multi-ready analysis: `applySelect`'s stream is the L2 pop, and the
outcome depends on the stream only through the pick. -/
theorem applySelect_picks_stream {σ : Store} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont}
    {poll : AccessTrace} {commits : List (EvClause × Sum (Config × Store × AccessTrace) String)}
    (h : applySelectCore ctx σ clauses default? vs env k = .ok (.picks poll commits)) (ch : Choices) :
    applySelect ctx σ clauses default? vs env k ch =
      (match commits[(Choices.consumeAt .l2Entry commits.length ch).1]? with
       | some (cl, .inl (c', s', tr)) =>
           .ok (c', s', (Choices.consumeAt .l2Entry commits.length ch).2,
             PickRecord.ofPick .l2Entry commits.length (Choices.consumeAt .l2Entry commits.length ch).1, some cl, poll ++ tr)
       | some (cl, .inr msg) =>
           .ok (.panicking [panicEntry msg] k, σ, (Choices.consumeAt .l2Entry commits.length ch).2,
             PickRecord.ofPick .l2Entry commits.length (Choices.consumeAt .l2Entry commits.length ch).1, some cl, poll)
       | none => .error (.internal "select ready-clause pick out of range")) := by
  simp only [applySelect, h, Bind.bind, Except.bind, Choices.consumeAtE_eq]
  rfl

/-- An error of the analysis is an error of the apply. -/
theorem applySelect_error_stream {σ : Store} {clauses : List (SelectClauseHead × Stmt)}
    {default? : Option Stmt} {vs : List GoValue} {env : LocalEnv} {k : Cont} {e : Stop}
    (h : applySelectCore ctx σ clauses default? vs env k = .error e) (ch : Choices) :
    applySelect ctx σ clauses default? vs env k ch = .error e := by
  simp [applySelect, h, Bind.bind, Except.bind]

/-- A TRY head's apply, in terms of the site's pop. -/
theorem applySyncOp_try_stream {σ : Store} {op : SyncOp} {targets : List Assignee}
    {av : GoValue} {loc : Loc} {pre : SyncPrim} {env : LocalEnv} {k : Cont}
    (ht : op.tryTargets? = some targets) (hl : valueAsLoc av = .ok loc)
    (hc : syncCell ctx σ loc = .ok pre) (ch : Choices) :
    applySyncOp ctx σ ch op [av] env k =
      (applyTryLock ctx σ op loc pre
        ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch).1 == 1) targets env k).map
        fun p => (p.1, p.2.1, (Choices.consumeAt .tryLock (tryLockWidth op pre) ch).2,
          PickRecord.ofPick .tryLock (tryLockWidth op pre)
            (Choices.consumeAt .tryLock (tryLockWidth op pre) ch).1, p.2.2) := by
  simp only [applySyncOp, ht, hl, hc, Bind.bind, Except.bind, Except.map, Choices.consumeAtE_eq]
  cases applyTryLock ctx σ op loc pre
      ((Choices.consumeAt .tryLock (tryLockWidth op pre) ch).1 == 1) targets env k <;> rfl

/-- A TRY head whose consult does not pop (`tryLockConsult? = none` at a
resolvable receiver) is stream-oblivious: width 1 pops nothing and forces
pick 0. -/
theorem applySyncOp_try_nopop {σ : Store} {op : SyncOp} {targets : List Assignee}
    {av : GoValue} {loc : Loc} {pre : SyncPrim} {env : LocalEnv} {k : Cont}
    (ht : op.tryTargets? = some targets) (hl : valueAsLoc av = .ok loc)
    (hc : syncCell ctx σ loc = .ok pre) (hw : tryLockWidth op pre ≤ 1) (ch : Choices) :
    applySyncOp ctx σ ch op [av] env k =
      (applyTryLock ctx σ op loc pre false targets env k).map fun p => (p.1, p.2.1, ch, [], p.2.2) := by
  rw [applySyncOp_try_stream ht hl hc ch, Choices.consumeAt_le_one hw]
  simp [PickRecord.ofPick, hw]

/-- A non-spilling append: the plan is one stream-free commit lifted beside the stream
(C1 S3: the plan-level restatement of the retired `applyStmtOp_appendSlice_nospill`). -/
theorem applyStmtOp_plan_appendSlice_nospill {σ : Store} {elem : Ty} {nt : Nat}
    {vs : List GoValue} (hw : appendSpill? ctx σ elem vs = none) :
    ∃ r : Except Stop (Commit (Store × AccessTrace)), ∀ ch : Choices,
      applyStmtOp.plan ctx σ ch (.appendSlice elem) nt vs = r.map (Commit.withStream ch []) := by
  match vs, hw with
  | [], _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | [_], _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | [_, _], _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | _ :: _ :: _ :: _ :: _, _ => exact ⟨.error (.stuck "malformed appendSlice operands"), fun _ => rfl⟩
  | [tv, sliceV, elemsV], hw =>
    unfold appendSpill? at hw
    unfold applyStmtOp.plan
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
    cases hvis : Mem.loadSlice ctx σ elems with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok pE =>
    obtain ⟨elemValues, trE⟩ := pE
    simp only [except_bind_ok]
    cases htl : valueAsLoc tv with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok tloc =>
    simp only [except_bind_ok]
    simp only [hsl, hel, hv1, hv2, hvis, htl] at hw
    by_cases hcap : slice.len + elemValues.size ≤ slice.cap
    · simp only [ite_eq_left hcap]
      exact ⟨.ok fun s => do
          let (current, trW) ← Mem.storeRun ctx s slice slice.len elemValues.toList
          let (s', trT) ← Mem.store ctx current tloc
            (.slice { slice with len := slice.len + elemValues.size })
          pure (s', trE ++ trW ++ trT), fun ch => rfl⟩
    · simp only [ite_eq_right hcap]
      cases hts : tySizeBytes ctx.types elem with
      | error e => exact ⟨.error e, fun _ => rfl⟩
      | ok elemSize =>
      simp only [except_bind_ok]
      simp only [ite_eq_right hcap, hts] at hw
      split
      · exact ⟨.error (.panic "runtime error: growslice: len out of range"), fun _ => rfl⟩
      · rename_i hr16
        simp only [ite_eq_right hr16] at hw
        cases hhp : tyHasPointers ctx.types elem with
        | error e => exact ⟨.error e, fun _ => rfl⟩
        | ok pointerful =>
        simp only [except_bind_ok]
        simp only [hhp] at hw
        cases hold : Mem.loadSlice ctx σ slice with
        | error e => exact ⟨.error e, fun _ => rfl⟩
        | ok oldValues => rw [hold] at hw; cases hw

/-- **The spill's pop** (C1 S3, the plan-level restatement of the retired
`applyStmtOp_appendSlice_spill`): at `appendSpill? = some w` the plan reaches the
consult and is a function `g` of the `appendSpill` pick alone, lifted beside the site's
pop at bound `w` — and `g` never raises a recoverable panic (the post-consult tail is the
fresh backing's panic-free construction; the COMMIT's panic-freeness is
`applyStmtOp_commit_noPanic`, for EVERY target — the former root-target proviso is gone). -/
theorem applyStmtOp_plan_appendSlice_spill {σ : Store} {elem : Ty} {nt : Nat}
    {vs : List GoValue} {w : Nat} (hw : appendSpill? ctx σ elem vs = some w) :
    ∃ g : Nat → Except Stop (Commit (Store × AccessTrace)),
      (∀ ch : Choices,
        applyStmtOp.plan ctx σ ch (.appendSlice elem) nt vs
          = (g (Choices.consumeAt .appendSpill w ch).1).map
              (Commit.withStream (Choices.consumeAt .appendSpill w ch).2
                [⟨.appendSpill, w, (Choices.consumeAt .appendSpill w ch).1⟩]))
      ∧ (∀ pick, NoPanic (g pick)) := by
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
    cases hvis : Mem.loadSlice ctx σ elems with
    | error e => simp [hsl, hel, hv1, hv2, hvis] at hw
    | ok pE =>
    obtain ⟨elemValues, trE⟩ := pE
    cases htl : valueAsLoc tv with
    | error e => simp [hsl, hel, hv1, hv2, hvis, htl] at hw
    | ok tloc =>
    simp only [hsl, hel, hv1, hv2, hvis, htl] at hw
    split at hw
    · cases hw
    rename_i hcap
    cases hts : tySizeBytes ctx.types elem with
    | error e => rw [hts] at hw; cases hw
    | ok elemSize =>
    simp only [hts] at hw
    split at hw
    · cases hw
    rename_i hr16
    cases hhp : tyHasPointers ctx.types elem with
    | error e => rw [hhp] at hw; cases hw
    | ok pointerful =>
    simp only [hhp] at hw
    cases hold : Mem.loadSlice ctx σ slice with
    | error e => rw [hold] at hw; cases hw
    | ok pO =>
    obtain ⟨oldValues, trO⟩ := pO
    rw [hold] at hw
    simp only [Option.some.injEq] at hw
    subst hw
    unfold applyStmtOp.plan
    dsimp only
    simp only [hsl, hel, hv1, hv2, hvis, htl, except_bind_ok, ite_eq_right hcap, hts, ite_eq_right hr16,
      hhp, hold]
    refine ⟨fun extra => ?_, fun ch => ?_, fun pick => ?_⟩
    · exact do
        let newCap := appendSpillCapAt elemSize pointerful slice.cap (slice.len + elemValues.size) extra
        let backing ← buildAppendBackingValue ctx elem oldValues elemValues newCap
        pure fun s => do
          let (base, current) ← Store.alloc ctx s backing (.array newCap elem)
          let (s', trT) ← Mem.store ctx current tloc
            (.slice { base := some base, offset := 0, len := slice.len + elemValues.size, cap := newCap })
          pure (s', trE ++ trO ++ trT)
    · have hw1 := one_lt_appendSpillWidth slice.cap (slice.len + elemValues.size)
      simp only [Choices.consumeAtE_eq, PickRecord.ofPick, ite_eq_right (Nat.not_le_of_lt hw1)]
      rcases hc : Choices.consumeAt .appendSpill (appendSpillWidth slice.cap (slice.len + elemValues.size)) ch
        with ⟨extra, rest⟩
      try dsimp only
      cases buildAppendBackingValue ctx elem oldValues elemValues _ <;> rfl
    · exact NoPanic.bind (buildAppendBackingValue_noPanic _ _ _ _) fun _ => NoPanic.pure _

/-! ### The `[0, n)` draw's stream lemmas (`Stmt.randIntn`, window unit 5b, 2026-09-30) -/

/-- Unpacking the draw's consult width: a `some w` is one of the two operand shapes
with an `int` bound `n ≥ 2` and `w = n.toNat` — and, in the target shape, a target
that IS an address (the arm's `valueAsLoc` succeeds ahead of the consult). -/
theorem intnBound?_some {vs : List GoValue} {w : Nat} (h : intnBound? vs = some w) :
    (∃ tv n tloc, vs = [tv, .int n .int] ∧ valueAsLoc tv = .ok tloc ∧ 2 ≤ n ∧ w = n.toNat)
      ∨ (∃ n : Int, vs = [.int n .int] ∧ 2 ≤ n ∧ w = n.toNat) := by
  unfold intnBound? at h
  split at h
  · rename_i tv n
    cases htl : valueAsLoc tv with
    | error e => simp only [htl] at h; cases h
    | ok tloc =>
      simp only [htl] at h
      by_cases h2 : 2 ≤ n
      · rw [ite_eq_left h2] at h
        exact .inl ⟨tv, n, tloc, rfl, htl, h2, (Option.some.inj h).symm⟩
      · rw [ite_eq_right h2] at h; cases h
  · rename_i n
    by_cases h2 : 2 ≤ n
    · rw [ite_eq_left h2] at h
      exact .inr ⟨n, rfl, h2, (Option.some.inj h).symm⟩
    · rw [ite_eq_right h2] at h; cases h
  · cases h

/-- The draw's consult width is a genuine pop (`≥ 2`). -/
theorem intnBound?_gt_one {vs : List GoValue} {w : Nat} (h : intnBound? vs = some w) : 1 < w := by
  rcases intnBound?_some h with ⟨_, n, _, -, -, h2, rfl⟩ | ⟨n, -, h2, rfl⟩ <;> omega

/-- The `[0, n)` draw at a NON-popping instance (`intnBound? = none`: a malformed
operand shape, a target that is not an address, a forged bound `≤ 0`, or the bound
`1`) is stream-oblivious — the refusal or panic ahead of the consult, or the bound-1
consult that pops nothing and stores 0. -/
theorem applyStmtOp_plan_randIntn_nodraw {σ : Store} {nt : Nat} {vs : List GoValue}
    (hw : intnBound? vs = none) :
    ∃ r : Except Stop (Commit (Store × AccessTrace)), ∀ ch : Choices,
      applyStmtOp.plan ctx σ ch .randIntn nt vs = r.map (Commit.withStream ch []) := by
  unfold applyStmtOp.plan
  dsimp only
  split
  · rename_i tv n
    simp only [intnBound?] at hw
    cases htl : valueAsLoc tv with
    | error e => exact ⟨.error e, fun _ => rfl⟩
    | ok tloc =>
      simp only [htl] at hw
      by_cases hlt : n < 1
      · refine ⟨.error (.stuck s!"rand-intn: bound {n} ≤ 0 reached the draw (the lowering's guard was bypassed — forged wire)"),
          fun ch => ?_⟩
        simp only [except_bind_ok, ite_eq_left hlt]
        rfl
      · have hn2 : ¬ 2 ≤ n := by
          intro h2; rw [ite_eq_left h2] at hw; cases hw
        have hn1 : n.toNat ≤ 1 := by omega
        refine ⟨.ok (fun s => do
            let (s', trT) ← Mem.store ctx s tloc (.int 0 .int)
            return (s', trT)), fun ch => ?_⟩
        simp only [except_bind_ok, ite_eq_right hlt, Choices.consumeAtE_le_one hn1]
        rfl
  · rename_i n
    simp only [intnBound?] at hw
    by_cases hlt : n < 1
    · refine ⟨.error (.stuck s!"rand-intn: bound {n} ≤ 0 reached the draw (the lowering's guard was bypassed — forged wire)"),
        fun ch => ?_⟩
      simp only [ite_eq_left hlt]
      rfl
    · have hn2 : ¬ 2 ≤ n := by
        intro h2; rw [ite_eq_left h2] at hw; cases hw
      have hn1 : n.toNat ≤ 1 := by omega
      refine ⟨.ok (fun s => return (s, [])), fun ch => ?_⟩
      simp only [ite_eq_right hlt, Choices.consumeAtE_le_one hn1]
      rfl
  · exact ⟨.error (.stuck "malformed rand-intn operands (expected [target address,] an int bound)"),
      fun _ => rfl⟩

/-- **The draw's pop** (the twin of `applyStmtOp_plan_appendSlice_spill`): at
`intnBound? = some w` the plan reaches the consult and is a function `g` of the `intn`
pick alone, lifted beside the site's pop at bound `w` — and `g` never raises a
recoverable panic (its commit is one `int` store into an address that
`valueAsLoc` already validated, or nothing). -/
theorem applyStmtOp_plan_randIntn_draw {σ : Store} {nt : Nat} {vs : List GoValue} {w : Nat}
    (hw : intnBound? vs = some w) :
    ∃ g : Nat → Except Stop (Commit (Store × AccessTrace)),
      (∀ ch : Choices,
        applyStmtOp.plan ctx σ ch .randIntn nt vs
          = (g (Choices.consumeAt .intn w ch).1).map
              (Commit.withStream (Choices.consumeAt .intn w ch).2
                [⟨.intn, w, (Choices.consumeAt .intn w ch).1⟩]))
      ∧ (∀ pick, NoPanic (g pick)) := by
  have hw1 := intnBound?_gt_one hw
  rcases intnBound?_some hw with ⟨tv, n, tloc, rfl, htl, h2, rfl⟩ | ⟨n, rfl, h2, rfl⟩
  · have hlt : ¬ n < 1 := by omega
    unfold applyStmtOp.plan
    dsimp only
    simp only [htl, except_bind_ok, ite_eq_right hlt, Choices.consumeAtE_eq, PickRecord.ofPick,
      ite_eq_right (Nat.not_le_of_lt hw1)]
    refine ⟨fun pick => .ok (fun s => do
        let (s', trT) ← Mem.store ctx s tloc (.int pick .int)
        return (s', trT)), fun ch => ?_, fun pick => NoPanic.ok _⟩
    rcases hc : Choices.consumeAt .intn n.toNat ch with ⟨pick, rest⟩
    rfl
  · have hlt : ¬ n < 1 := by omega
    unfold applyStmtOp.plan
    dsimp only
    simp only [ite_eq_right hlt, Choices.consumeAtE_eq, PickRecord.ofPick, ite_eq_right (Nat.not_le_of_lt hw1)]
    refine ⟨fun _ => .ok (fun s => return (s, [])), fun ch => ?_, fun pick => NoPanic.ok _⟩
    rcases hc : Choices.consumeAt .intn n.toNat ch with ⟨pick, rest⟩
    rfl

/-! ### The conversion funnel's stream lemmas (`ChoiceSite.convCap`, R3 / b6, 2026-10-07)

The strict apply draws the capacity pick of `[]byte(s)` / `[]rune(s)` inside
`applyStrictOpPick` (Machine.lean). The lemmas below are the strict twins of the wide-op
kit above: the post-consult tail never panics, the consult's `some`/`none` unpack, the
pick-lifted and the oblivious shapes of the funnel, the two `stepFn` arm lemmas the
consumption sweeps close with, and the DERIVED step rule (design D6, the intn D7 shape). -/

/-- `convCapApplyAt` never raises a recoverable panic: one allocation, which refuses or
succeeds. -/
theorem convCapApplyAt_noPanic (s : Store) (kind : ConvKind) (literal : Bool) (value : GoString)
    (pick : Nat) : NoPanic (convCapApplyAt ctx s kind literal value pick) := by
  unfold convCapApplyAt
  dsimp only
  exact NoPanic.bind (buildAppendBackingValue_noPanic _ _ _ _) fun _ =>
    NoPanic.bind (Store.alloc_noPanic _ _ _) fun _ => NoPanic.pure _

/-- Unpacking the strict consult's `some`: the site is `convCap`, the head a conversion
head on a string operand, the bound its member count — a genuine pop (`≥ 2`). -/
theorem strictConsult?_some {op : StrictOp} {vs : List GoValue} {site : ChoiceSite} {b : Nat}
    (h : strictConsult? op vs = some (site, b)) :
    site = .convCap ∧ ∃ kind literal value, op.convKind? = some (kind, literal)
      ∧ convOperand? vs = some value ∧ b = convCapWidth kind literal value ∧ 1 < b := by
  unfold strictConsult? at h
  split at h
  · rename_i kind literal value hk hv
    split at h
    · cases h
    · rename_i hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, kind, literal, value, hk, hv, rfl, Nat.lt_of_not_le hw⟩
  · cases h

/-- The strict apply at a NON-popping instance (`strictConsult? = none`) is
stream-oblivious: the pure apply at a non-conversion head; at a conversion head, the
refusal ahead of the consult (a non-string operand, a malformed arity) or the bound-1
consult that pops nothing. -/
theorem applyStrictOpPick_of_strictConsult?_none {s : Store} {leafOf : Loc → Loc} {op : StrictOp}
    {vs : List GoValue} (h : strictConsult? op vs = none) :
    ∃ r : Except Stop (GoValue × Store × AccessTrace), ∀ ch : Choices,
      applyStrictOpPick ctx s leafOf op vs ch = r.map fun x => (x, ch, []) := by
  cases hk : op.convKind? with
  | none => exact ⟨applyStrictOp ctx s leafOf op vs, fun ch => applyStrictOpPick_of_convKind?_none hk⟩
  | some p =>
    obtain ⟨kind, literal⟩ := p
    cases hv : convOperand? vs with
    | none => exact ⟨convRefuse kind vs, fun ch => applyStrictOpPick_refuse hk hv⟩
    | some value =>
      have hw : convCapWidth kind literal value ≤ 1 := by
        by_cases hgt : convCapWidth kind literal value ≤ 1
        · exact hgt
        · simp [strictConsult?, hk, hv, hgt] at h
      refine ⟨convCapApplyAt ctx s kind literal value 0, fun ch => ?_⟩
      rw [applyStrictOpPick_conv hk hv, Choices.consumeAt_le_one hw, PickRecord.ofPick, ite_eq_left hw]

/-- **The conversion's pop** (the twin of `applyStmtOp_plan_randIntn_draw`): at a conversion
head on a string operand with a popping width, the funnel is a function `g` of the
`convCap` pick alone, lifted beside the site's pop and its record — and `g` never raises a
recoverable panic. -/
theorem applyStrictOpPick_draw {s : Store} {leafOf : Loc → Loc} {op : StrictOp} {vs : List GoValue}
    {kind : ConvKind} {literal : Bool} {value : GoString}
    (hk : op.convKind? = some (kind, literal)) (hv : convOperand? vs = some value)
    (hw : 1 < convCapWidth kind literal value) :
    ∃ g : Nat → Except Stop (GoValue × Store × AccessTrace),
      (∀ ch : Choices,
        applyStrictOpPick ctx s leafOf op vs ch
          = (g (Choices.consumeAt .convCap (convCapWidth kind literal value) ch).1).map
              fun r => (r, (Choices.consumeAt .convCap (convCapWidth kind literal value) ch).2,
                [⟨.convCap, convCapWidth kind literal value,
                  (Choices.consumeAt .convCap (convCapWidth kind literal value) ch).1⟩]))
      ∧ (∀ pick, NoPanic (g pick)) := by
  refine ⟨fun pick => convCapApplyAt ctx s kind literal value pick, fun ch => ?_,
    fun pick => convCapApplyAt_noPanic _ _ _ _ _⟩
  rw [applyStrictOpPick_conv hk hv]
  simp only [PickRecord.ofPick, ite_eq_right (Nat.not_le_of_lt hw)]

/-- The strict apply arm at a stream-oblivious funnel: the classified result is the same
at every stream and the arm returns its own stream untouched. -/
theorem stepFn_strict_oblivious {σ : Store} {op : StrictOp} {done : List GoValue} {v : GoValue}
    {env : LocalEnv} {k : Cont} {r : Except Stop (GoValue × Store × AccessTrace)}
    (hr : ∀ ch : Choices, applyStrictOpPick ctx σ (projChainTarget ctx σ k) op (v :: done).reverse ch
      = r.map fun x => (x, ch, []))
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepFn ctx σ (.retV v (.strictK op done [] env k)) ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFn ctx σ (.retV v (.strictK op done [] env k)) ch = .ok (c', σ', ch, tr) := by
  unfold stepFn at h
  dsimp only at h
  rw [hr ch₀] at h
  cases r with
  | error e =>
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      deliverS_panic, reduceCtorEq] at h
    case panic msg =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl
  | ok x =>
    obtain ⟨out, s₂, tr₂⟩ := x
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverS_ok] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl

/-- The strict apply arm at a POPPING conversion: the `convCap` pop, and pick-dependence
only (the post-consult tail is panic-free, so the delivered panic is unreachable). -/
theorem stepFn_strict_pick {σ : Store} {op : StrictOp} {done : List GoValue} {v : GoValue}
    {env : LocalEnv} {k : Cont} {w : Nat} {g : Nat → Except Stop (GoValue × Store × AccessTrace)}
    (hg : ∀ ch : Choices, applyStrictOpPick ctx σ (projChainTarget ctx σ k) op (v :: done).reverse ch
      = (g (Choices.consumeAt .convCap w ch).1).map
          fun r => (r, (Choices.consumeAt .convCap w ch).2,
            [⟨.convCap, w, (Choices.consumeAt .convCap w ch).1⟩]))
    (hnp : ∀ pick, NoPanic (g pick))
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepFn ctx σ (.retV v (.strictK op done [] env k)) ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt .convCap w ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt .convCap w ch).1 = (Choices.consumeAt .convCap w ch₀).1 →
      stepFn ctx σ (.retV v (.strictK op done [] env k)) ch
        = .ok (c', σ', (Choices.consumeAt .convCap w ch).2, tr) := by
  unfold stepFn at h
  dsimp only at h
  rw [hg ch₀] at h
  cases hgv : g (Choices.consumeAt .convCap w ch₀).1 with
  | error e =>
    rw [hgv] at h
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      deliverS_panic, reduceCtorEq] at h
    case panic msg =>
    -- refuted: the post-consult tail never panics (`hnp`)
    exact absurd hgv (hnp _ msg)
  | ok x =>
    obtain ⟨out, s₂, tr₂⟩ := x
    rw [hgv] at h
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverS_ok] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch hpk => ?_⟩
    unfold stepFn
    dsimp only
    rw [hg ch, hpk, hgv]
    rfl

/-- A wide-statement apply whose consult is `none` is a stream-oblivious plan: the core's
plan for every non-append head, the non-spilling / refusing append otherwise. -/
theorem applyStmtOp_plan_of_stmtConsult?_none {σ : Store} {op : StmtOp} {nt : Nat}
    {vs : List GoValue} (h : stmtConsult? ctx σ op vs = none) :
    ∃ r : Except Stop (Commit (Store × AccessTrace)), ∀ ch : Choices,
      applyStmtOp.plan ctx σ ch op nt vs = r.map (Commit.withStream ch []) := by
  by_cases hap : (∀ e, op ≠ .appendSlice e) ∧ op ≠ .randIntn
  · exact ⟨applyStmtOpCore.plan ctx σ op vs, fun ch => applyStmtOp_plan_eq_core hap.1 hap.2⟩
  · rcases (show (∃ e, op = .appendSlice e) ∨ op = .randIntn by
        cases op <;>
          first
          | exact .inl ⟨_, rfl⟩
          | exact .inr rfl
          | exact absurd (And.intro (fun _ h => nomatch h) (fun h => nomatch h)) hap) with ⟨e, rfl⟩ | rfl
    · simp only [stmtConsult?, Option.map_eq_none_iff] at h
      exact applyStmtOp_plan_appendSlice_nospill h
    · simp only [stmtConsult?, Option.map_eq_none_iff] at h
      exact applyStmtOp_plan_randIntn_nodraw h

/-- The done-check `mapIterK` step is oblivious: with no candidate
left it pops the continuation at every stream (BUG-005 (L): "no
candidate" is a STATE fact — the live cell minus the produced set). -/
theorem stepFn_mapIter_done {σ : Store} {kv vv : Option VarId}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont} {tr : AccessTrace}
    (hcands : mapIterCandidates ctx σ kt vt base produced = .ok (#[], tr)) :
    ∀ ch : Choices,
      stepFn ctx σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
        = .ok (.next k, σ, ch, ⟨tr, [], []⟩) := by
  intro ch
  simp [stepFn, hcands, Bind.bind, Except.bind]

/-- The nonempty `mapIterK` step at a PICK index, factored through the
consumed choice: the successor is a function of the pick index alone
(`bindIterVars` never sees the stream), and the stream moves to the
consume's tail. One probe per index covers every stream whose choice
reduces to that index. -/
theorem stepFn_mapIter_pick {σ : Store} {kv vv : Option VarId}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont}
    {cands : Array (Nat × GoValue × GoValue)} {mand : Bool} {tr : AccessTrace}
    {ch : Choices} {idx : Nat} {tail : Choices}
    (hcands : mapIterCandidates ctx σ kt vt base produced = .ok (cands, tr))
    (hmand : mapIterMandatoryRemains cands start = mand)
    (hne : ¬ cands.isEmpty = true)
    (hcons : Choices.consumeAt .mapIter (cands.size + (if mand = true then 0 else 1)) ch
      = (idx, tail))
    (hlt : idx < cands.size) :
    stepFn ctx σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
      = ((bindIterVars ctx env.pushScope σ kv vv kt vt
            cands[idx].2.1 cands[idx].2.2).map
          fun p => (.exec body p.1
            (.mapIterK kv vv kt vt body base (produced.push cands[idx].1)
              start env k),
            p.2, tail, ⟨tr, PickRecord.ofPick .mapIter (cands.size + (if mand = true then 0 else 1)) idx, []⟩)) := by
  simp only [stepFn, hcands, Bind.bind, Except.bind]
  rw [hmand, ite_eq_right hne, Choices.consumeAtE_eq, hcons]
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
    cases hbind : bindIterVars ctx env.pushScope σ kv vv kt vt
        cands[idx].2.1 cands[idx].2.2 <;>
      simp [Except.map]

/-- The nonempty `mapIterK` step at the STOP slot (index = candidate
count; the slot exists only when no mandatory start key remains): the
iteration ends at every stream whose choice lands there. -/
theorem stepFn_mapIter_stop {σ : Store} {kv vv : Option VarId}
    {kt vt : Ty} {body : Stmt} {base : Option Loc}
    {produced start : Array Nat} {env : LocalEnv} {k : Cont}
    {cands : Array (Nat × GoValue × GoValue)} {tr : AccessTrace}
    {ch : Choices} {tail : Choices}
    (hcands : mapIterCandidates ctx σ kt vt base produced = .ok (cands, tr))
    (hmand : mapIterMandatoryRemains cands start = false)
    (hne : ¬ cands.isEmpty = true)
    (hcons : Choices.consumeAt .mapIter (cands.size + 1) ch = (cands.size, tail)) :
    stepFn ctx σ (.next (.mapIterK kv vv kt vt body base produced start env k)) ch
      = .ok (.next k, σ, tail, ⟨tr, [⟨.mapIter, cands.size + 1, cands.size⟩], []⟩) := by
  simp only [stepFn, hcands, Bind.bind, Except.bind]
  rw [hmand, ite_eq_right hne]
  have hred : (cands.size + if false = true then 0 else 1)
      = cands.size + 1 := by simp
  rw [hred, Choices.consumeAtE_eq, hcons]
  have hsz : ¬ (cands.size + 1 ≤ 1) := by
    simp only [Array.isEmpty_iff] at hne
    have := Array.size_pos_iff.mpr hne
    omega
  simp only [PickRecord.ofPick, ite_eq_right hsz]
  try dsimp only
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
    cases hx : toResult (enterFrame.plan ctx _ _ _) with
    | error e =>
      rw [hx] at $h:ident
      simp [Except.map, Bind.bind, Except.bind] at $h:ident
    | ok r =>
      rw [hx] at $h:ident
      cases r with
      | ok c =>
        simp only [Except.map, Bind.bind, Except.bind, deliverV_ok] at $h:ident
        cases hrc : runCommit c _ with
        | error e =>
          rw [hrc] at $h:ident
          simp [Functor.map, Except.map] at $h:ident
        | ok a =>
          rw [hrc] at $h:ident
          simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at $h:ident
          obtain ⟨h1, h2, h3, h4⟩ := $h:ident
          subst h1; subst h2; subst h3; subst h4
          exact ⟨rfl, fun ch => by
            (try simp only [List.append_assoc] at hpk' hx hrc)
            simp [stepFn, hpk', hx, hrc, Except.map, Bind.bind, Except.bind, Functor.map]⟩
      | panic msg =>
        simp only [Except.map, Bind.bind, Except.bind, deliverV_panic,
          Except.ok.injEq, Prod.mk.injEq] at $h:ident
        obtain ⟨h1, h2, h3, h4⟩ := $h:ident
        subst h1; subst h2; subst h3; subst h4
        exact ⟨rfl, fun ch => by
          (try simp only [List.append_assoc] at hpk' hx)
          simp [stepFn, hpk', hx, Except.map, Bind.bind, Except.bind]⟩))

macro "consumption_entry_none " h:ident hsc:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, seqConsumption, Config.applyPos, entryCallSite?]
    rcases entryConsult?_none $hsc:ident with hnv | hnp
    · oblivious_entry_with $h:ident (enterFramePickV_of_isSome_false hnv)
    · oblivious_entry_with $h:ident (enterFramePickV_of_nopanic hnp)))

/-- The entry arms of the `some` sweep: the family's width-2 pop on the
panic path (`entryConsult?_some`, `enterFramePick_panic`). -/
macro "consumption_entry_some " h:ident hsc:ident : tactic =>
  `(tactic| (
    simp_all only [stepFn, seqConsumption, Config.applyPos, entryCallSite?]
    obtain ⟨hsite, hb, hw, msg, hpanic⟩ := entryConsult?_some $hsc:ident
    subst hsite; subst hb
    have hpanic' := enterFrame_inv_panic hpanic
    rw [enterFramePickV_of_plan_panic hpanic' _] at $h:ident
    simp only [Bind.bind, Except.bind, deliverV_panic, Except.ok.injEq, Prod.mk.injEq] at $h:ident
    obtain ⟨h1, h2, h3, h4⟩ := $h:ident
    subst h1; subst h2; subst h3; subst h4
    refine ⟨rfl, fun ch₁ hpk => ?_⟩
    (try simp only [List.append_assoc] at hpanic' hpk)
    simp [stepFn, enterFramePickV_of_plan_panic hpanic', hpk, Bind.bind, Except.bind]))

/-- A popping wide-statement consult is one of the TWO consuming wide ops: a
spilling append at `appendSpill`, or (unit 5b) the `[0, n)` draw at `intn`
with bound `n ≥ 2`. -/
theorem stmtConsult?_some {σ : Store} {op : StmtOp} {vs : List GoValue}
    {site : ChoiceSite} {b : Nat} (h : stmtConsult? ctx σ op vs = some (site, b)) :
    (∃ elem, op = .appendSlice elem ∧ site = .appendSpill ∧ appendSpill? ctx σ elem vs = some b)
      ∨ (op = .randIntn ∧ site = .intn ∧ intnBound? vs = some b) := by
  cases op with
  | appendSlice elem =>
    simp only [stmtConsult?, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    exact .inl ⟨elem, rfl, rfl, hw⟩
  | randIntn =>
    simp only [stmtConsult?, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨w, hw, rfl, rfl⟩ := h
    exact .inr ⟨rfl, rfl, hw⟩
  | _ => simp [stmtConsult?] at h

/-- The wide-statement apply arm at a stream-oblivious plan (C1 S3: the plan is one
commit lifted beside the stream; the commit reads no stream). -/
theorem stepFn_stmtOp_oblivious {σ : Store} {op : StmtOp} {nt : Nat} {done : List GoValue}
    {v : GoValue} {env : LocalEnv} {k : Cont} {r : Except Stop (Commit (Store × AccessTrace))}
    (hr : ∀ ch : Choices, applyStmtOp.plan ctx σ ch op nt (v :: done).reverse = r.map (Commit.withStream ch []))
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepFn ctx σ (.retV v (.stmtOpK op nt done [] env k)) ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFn ctx σ (.retV v (.stmtOpK op nt done [] env k)) ch = .ok (c', σ', ch, tr) := by
  unfold stepFn at h
  dsimp only at h
  rw [hr ch₀] at h
  cases r with
  | error e =>
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      deliverV_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case panic msg =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl
  | ok c =>
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream] at h
    cases hrc : runCommit c σ with
    | error e => rw [hrc] at h; simp [Functor.map, Except.map] at h
    | ok p =>
      obtain ⟨s₂, tr₂⟩ := p
      rw [hrc] at h
      simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch => ?_⟩
      unfold stepFn
      dsimp only
      rw [hr ch]
      simp [Except.map, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream, hrc, Functor.map]

/-- The wide-statement apply arm at a POPPING consult — a SPILLING append at
`appendSpill`, or (unit 5b) the `[0, n)` draw at `intn`: the site's pop, and
pick-dependence only (C1 S3: `g` is the post-consult VALIDATE tail, panic-free; the
commit's panic is unreachable and refused, never an `.ok` with the wrong stream).
Stated over any `op`/`site` whose plan has the pick-lifted shape `hg`
(`applyStmtOp_plan_appendSlice_spill`, `applyStmtOp_plan_randIntn_draw`). -/
theorem stepFn_stmtOp_pick {σ : Store} {op : StmtOp} {site : ChoiceSite} {nt : Nat}
    {done : List GoValue} {v : GoValue} {env : LocalEnv} {k : Cont} {w : Nat}
    {g : Nat → Except Stop (Commit (Store × AccessTrace))}
    (hg : ∀ ch : Choices, applyStmtOp.plan ctx σ ch op nt (v :: done).reverse
      = (g (Choices.consumeAt site w ch).1).map
          (Commit.withStream (Choices.consumeAt site w ch).2
            [⟨site, w, (Choices.consumeAt site w ch).1⟩]))
    (hnp : ∀ pick, NoPanic (g pick))
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepFn ctx σ (.retV v (.stmtOpK op nt done [] env k)) ch₀
      = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt site w ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site w ch).1 = (Choices.consumeAt site w ch₀).1 →
      stepFn ctx σ (.retV v (.stmtOpK op nt done [] env k)) ch
        = .ok (c', σ', (Choices.consumeAt site w ch).2, tr) := by
  unfold stepFn at h
  dsimp only at h
  rw [hg ch₀] at h
  cases hgv : g (Choices.consumeAt site w ch₀).1 with
  | error e =>
    rw [hgv] at h
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      deliverV_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case panic msg =>
    -- refuted: the post-consult validate tail never panics (`hnp`)
    exact absurd hgv (hnp _ msg)
  | ok c =>
    rw [hgv] at h
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream] at h
    cases hrc : runCommit c σ with
    | error e => rw [hrc] at h; simp [Functor.map, Except.map] at h
    | ok p =>
      obtain ⟨s₂, tr₂⟩ := p
      rw [hrc] at h
      simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun ch hpk => ?_⟩
      unfold stepFn
      dsimp only
      rw [hg ch, hpk, hgv]
      simp [Except.map, Bind.bind, Except.bind, deliverV_ok, runCommit_withStream, hrc, Functor.map]

/-- The sync apply arm at a stream-oblivious apply (`r.map` with the
stream passed through). -/
theorem stepFn_syncApply_oblivious {σ : Store} {op : SyncOp} {done : List GoValue}
    {v : GoValue} {env : LocalEnv} {k : Cont} {r : Except Stop (Config × Store × AccessTrace)}
    (hr : ∀ ch : Choices, applySyncOp ctx σ ch op (v :: done).reverse env k
      = r.map fun p => (p.1, p.2.1, ch, [], p.2.2))
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (h : stepFn ctx σ (.retV v (.syncStK op done [] env k)) ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFn ctx σ (.retV v (.syncStK op done [] env k)) ch = .ok (c', σ', ch, tr) := by
  unfold stepFn at h
  dsimp only at h
  rw [hr ch₀] at h
  cases r with
  | error e =>
    cases_stop e <;> simp only [Except.map, toResult_panic, toResult_refusal, toResult_fatal,
      toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
      pure_eq_ok, deliverS_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    case panic msg =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl
  | ok p =>
    obtain ⟨c₂, σ₂, tr₂⟩ := p
    simp only [Except.map, toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    unfold stepFn
    dsimp only
    rw [hr ch]
    rfl


/-- Frame exit consumes the stream only at a deferred call's ENTRY, and
there exactly as every entry does (`entryConsult?`): with the consult
`none` the exit is stream-oblivious — on BOTH its entries (B4). -/
theorem stepFrameExit_consumption_none {σ : Store}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv} {results : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {fr : FuncId} {c : Config}
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (hc : c = .next (.frame targets tenv results ds k' fr)
      ∨ c = .signal .ret (.frame targets tenv results ds k' fr))
    (hsc : seqConsumption ctx σ c = none)
    (h : stepFrameExit ctx σ targets tenv results ds k' fr ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices,
      stepFrameExit ctx σ targets tenv results ds k' fr ch = .ok (c', σ', ch, tr) := by
  fun_cases stepFrameExit ctx σ targets tenv results ds k' fr ch₀
  · simp only [stepFrameExit, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit]⟩
  · -- unit 6b: the preprint delivery reads a cell, never the stream
    simp only [stepFrameExit, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨v, trv⟩, hload, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit, hload, Bind.bind, Except.bind]⟩
  · simp only [stepFrameExit, bind_eq_ok] at h
    obtain ⟨vs, _, h⟩ := h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [stepFrameExit, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨vs, trv⟩, hload, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit, hload, Bind.bind, Except.bind]⟩
  · simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h
  · -- the deferred call's ENTRY: the exit's one consult
    rcases hc with rfl | rfl <;>
      simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc <;>
      simp only [stepFrameExit] at h <;>
      rcases entryConsult?_none hsc with hnv | hnp <;>
      (first
        | have hpk' := enterFramePickV_of_isSome_false hnv
        | have hpk' := enterFramePickV_of_nopanic hnp) <;>
      (rw [hpk' _] at h
       cases hx : toResult (enterFrame.plan ctx _ _ _) with
       | error e =>
         rw [hx] at h
         simp [Except.map, Bind.bind, Except.bind] at h
       | ok r =>
         rw [hx] at h
         cases r with
         | ok c =>
           simp only [Except.map, Bind.bind, Except.bind, deliverV_ok] at h
           cases hrc : runCommit c _ with
           | error e =>
             rw [hrc] at h
             simp [Functor.map, Except.map] at h
           | ok a =>
             rw [hrc] at h
             simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨h1, h2, h3, h4⟩ := h
             subst h1; subst h2; subst h3; subst h4
             exact ⟨rfl, fun ch => by
               (try simp only [List.append_assoc] at hpk' hx hrc)
               simp [stepFrameExit, hpk', hx, hrc, Except.map, Bind.bind, Except.bind, Functor.map]⟩
         | panic msg =>
           simp only [Except.map, Bind.bind, Except.bind, deliverV_panic,
             Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨h1, h2, h3, h4⟩ := h
           subst h1; subst h2; subst h3; subst h4
           exact ⟨rfl, fun ch => by
             (try simp only [List.append_assoc] at hpk' hx)
             simp [stepFrameExit, hpk', hx, Except.map, Bind.bind, Except.bind]⟩)
  · simp only [stepFrameExit, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun ch => by simp [stepFrameExit]⟩
  · simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h

/-- A signal the table resolves sits on no call frame, so it is no frame
ENTRY (the consumption projection sees `none` there). -/
theorem entryCallSite?_of_signalStep {sg : Signal} {k : Cont} {c' : Config}
    (h : signalStep sg k = some c') : entryCallSite? (.signal sg k) = none := by
  cases_cont k <;> simp_all [entryCallSite?]

/-- The `some` half for frame exit: the deferred entry's width-2 pop on
the panic path (`entryConsult?_some`, `enterFramePick_panic`), on both
entries (B4). -/
theorem stepFrameExit_consumption_some {σ : Store}
    {targets : List (TargetShape × List Expr)} {tenv : LocalEnv} {results : List Loc}
    {ds : List (GoValue × List GoValue)} {k' : Cont} {fr : FuncId} {c : Config}
    {ch₀ : Choices} {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    {site : ChoiceSite} {b : Nat}
    (hc : c = .next (.frame targets tenv results ds k' fr)
      ∨ c = .signal .ret (.frame targets tenv results ds k' fr))
    (hsc : seqConsumption ctx σ c = some (site, b))
    (h : stepFrameExit ctx σ targets tenv results ds k' fr ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFrameExit ctx σ targets tenv results ds k' fr ch
        = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) := by
  fun_cases stepFrameExit ctx σ targets tenv results ds k' fr ch₀
  all_goals try (rcases hc with rfl | rfl <;>
    simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
  all_goals try (simp [stepFrameExit, throw, throwThe, MonadExceptOf.throw] at h; done)
  rcases hc with rfl | rfl <;>
    simp only [seqConsumption, Config.applyPos, entryCallSite?] at hsc <;>
    (obtain ⟨hsite, hb, hw, msg, hpanic⟩ := entryConsult?_some hsc
     subst hsite; subst hb
     have hpanic' := enterFrame_inv_panic hpanic
     simp only [stepFrameExit] at h
     rw [enterFramePickV_of_plan_panic hpanic' _] at h
     simp only [Bind.bind, Except.bind, deliverV_panic, Except.ok.injEq, Prod.mk.injEq] at h
     obtain ⟨h1, h2, h3, h4⟩ := h
     subst h1; subst h2; subst h3; subst h4
     refine ⟨rfl, fun ch₁ hpk => ?_⟩
     (try simp only [List.append_assoc] at hpanic' hpk)
     simp [stepFrameExit, enterFramePickV_of_plan_panic hpanic', hpk, Bind.bind, Except.bind])

/-- **The consumption theorem, `none` half**: a step whose projection is
`none` is stream-oblivious — it succeeds under EVERY stream with the same
successor and the stream returned untouched. Sweep over `stepFn`'s case
tree; every arm binds through stream-free helpers or through one of the
five consults at a non-popping instance (`applyStmtOp_of_stmtConsult?_none`,
`applySelect_done_stream`, `applySyncOp_try_nopop`/`_core_ok`,
`stepFn_mapIter_done`, `entryConsult?_none`). A newly added
stream-consuming arm breaks this proof loudly. -/
theorem stepFn_consumption_none {σ : Store} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : Store} {ch₀' : Choices} {tr : StepLabel}
    (hsc : seqConsumption ctx σ c = none)
    (h : stepFn ctx σ c ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = ch₀ ∧ ∀ ch : Choices, stepFn ctx σ c ch = .ok (c', σ', ch, tr) := by
  fun_cases stepFn ctx σ c ch₀
  -- G-C3 (packet C): the `.retV`/`.next` catch-all refusals closed directly,
  -- as in `stepFn_sound` (the generic `simp_all [stepFn]` is ~9 s there).
  -- Unit 6b: the catch-alls carry the preprint frame's stream-free steps.
  -- Packet D (packet B audit F2): closed by the shape `stepFn` reduces to, not by
  -- the positional tags (see `stepFn_sound`).
  all_goals first
    | (guard_hyp h : stepFn _ _ (Config.retV _ (_ :: _)) _ = _; skip)
    | (guard_hyp h : stepFn _ _ (Config.retV _ []) _ = _; skip)
    | (guard_hyp h : stepFn _ _ (Config.retV _ _) _ = _; simp only [stepFn] at h ⊢; exact stepRetOther_stream h)
    | (guard_hyp h : stepFn _ _ (Config.next (_ :: _)) _ = _; skip)
    | (guard_hyp h : stepFn _ _ (Config.next []) _ = _; skip)
    | (guard_hyp h : stepFn _ _ (Config.next _) _ = _; simp only [stepFn] at h ⊢; exact stepNextOther_stream h)
    | skip
  all_goals first
    | (refine ⟨?_, fun ch => ?_⟩ <;> (simp_all [stepFn]; done))
    | skip
  case case6 =>
    -- The probe's panic-path consult: the projection says `some`, never `none`.
    simp [seqConsumption] at hsc
  -- The `unseq` construct (Stage B): ENTER and a value head's result never
  -- touch the stream; the scheduler is oblivious when its projection is
  -- `none` (a run/wait phase, a completion, a ready set of size ≤ 1).
  case case63 =>
    simp only [stepFn] at h ⊢
    exact stepUnseqEnter_stream h
  case case135 =>
    simp only [stepFn] at h ⊢
    exact stepUnseqValue_stream h
  case case151 =>
    simp only [stepFn] at h ⊢
    exact stepUnseqNext_consumption_none hsc h
  case case2 =>
    consumption_entry_none h hsc
  case case32 =>
    consumption_entry_none h hsc
  case case91 =>
    consumption_entry_none h hsc
  case case95 =>
    consumption_entry_none h hsc
  case case101 =>
    consumption_entry_none h hsc
  case case7 =>
    -- The `.stop` arm (unit 6b): the abort never returns `.ok`; the phase
    -- step at a non-colliding entry pops nothing.
    simp only [stepFn] at h ⊢
    exact stepPanicStop_consumption_none hsc h
  case case142 =>
    simp only [stepFn] at h ⊢
    exact stepFrameExit_consumption_none (.inl rfl) hsc h
  case case154 =>
    simp only [stepFn, signalStep_frame] at h ⊢
    exact stepFrameExit_consumption_none (.inr rfl) hsc h
  case case94 =>
    simp only [seqConsumption, Config.applyPos] at hsc
    obtain ⟨r, hr⟩ := applyStmtOp_plan_of_stmtConsult?_none hsc
    exact stepFn_stmtOp_oblivious hr h
  case case116 =>
    rename_i v clauses default? done env k'
    simp only [seqConsumption, Config.applyPos, selectConsult?] at hsc
    cases hcore : applySelectCore ctx σ clauses default? ((v :: done).reverse) env k' with
    | error e =>
      unfold stepFn at h
      dsimp only at h
      rw [applySelect_error_stream hcore ch₀] at h
      cases_stop e <;> simp only [toResult_panic, toResult_refusal, toResult_fatal,
        toResult_deadlock, toResult_raceDetected, toResult_fuelOut, Bind.bind, Except.bind,
        pure_eq_ok, deliverS_panic, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      case panic msg =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
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
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
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
      cases hap : applySyncOp ctx σ ch₀ op ((v :: done).reverse) env k' with
      | error e =>
        exact stepFn_syncApply_oblivious (r := .error e)
          (fun ch => by rw [applySyncOp_core_error hop hap ch]; rfl) h
      | ok p =>
        obtain ⟨c₂, σ₂, ch₂, ps₂, tr₂⟩ := p
        obtain ⟨rfl, rfl, hall⟩ := applySyncOp_core_ok hop hap
        exact stepFn_syncApply_oblivious (r := .ok (c₂, σ₂, tr₂))
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
          cases hcell : syncCell ctx σ loc with
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
              (r := applyTryLock ctx σ op loc pre false targets env k')
              (fun ch => by simpa using applySyncOp_try_nopop hop hl hcell hw ch) h
  case case147 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates ctx σ kt vt base produced with
    | error e =>
      exfalso
      simp [stepFn, hcands, Bind.bind, Except.bind] at h
    | ok pc =>
      obtain ⟨cands, trc⟩ := pc
      rw [hcands] at hsc
      (try dsimp only at hsc)
      by_cases hemp : cands.isEmpty
      · rw [Array.isEmpty_iff] at hemp
        subst hemp
        rw [stepFn_mapIter_done hcands ch₀] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch => stepFn_mapIter_done hcands ch⟩
      · -- G-U: a width-1 consult (the last MANDATORY candidate) pops
        -- nothing and forces pick 0 — the step is oblivious.
        rw [ite_eq_right hemp] at hsc
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
        cases hbind : bindIterVars ctx env.pushScope σ kv vv kt vt cands[0].2.1 cands[0].2.2 with
        | error e => rw [hbind] at h; simp [Except.map] at h
        | ok p =>
          rw [hbind] at h
          simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch => ?_⟩
          rw [stepFn_mapIter_pick hcands hmand hemp (hcons ch) hpos, hbind]
          rfl
  case case75 =>
    -- A4: a global past the heap REFUSES (`.stuck`); no step is produced.
    rename_i hgid
    simp only [stepFn] at h
    rw [ite_eq_right hgid] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case12 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨env', s₁⟩, hd, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only
    refine ⟨⟨env', s₁⟩, hd, ?_⟩
    simp
  -- Channel receive entry (channels arc slice 1): the plan match needs
  -- its hypothesis rewritten in; both arms are stream-oblivious.
  case case37 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case38 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case39 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, ite_eq_left hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case40 =>
    rename_i hplan hgt
    simp only [stepFn] at h
    rw [hplan, ite_eq_right hgt] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- Sync statements (spec-parity slice 2): the chan recipes — entry is
  -- stream-transparent; the APPLY is stream-transparent for every
  -- non-TRY head (`hnt` excludes the TRY heads — Q-TRYLOCK's
  -- `tryLock` site; `applySyncOp_core_ok`/`_error`).
  -- Sync statements (spec-parity slice 2): the chan recipes — entry is
  -- stream-transparent; the APPLY is stream-transparent for every
  -- non-TRY head (`hnt` excludes the TRY heads — Q-TRYLOCK's
  -- `tryLock` site; `applySyncOp_core_ok`/`_error`).
  case case56 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case57 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case58 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  -- sync/atomic statements (atomics arc wave 1): the sync recipes —
  -- entry is stream-transparent (the apply consumes nothing,
  -- applyAtomicOp's envelope statement).
  case case59 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp only [pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨rfl, fun ch => ?_⟩
    simp only [stepFn]
    rw [hplan]
    rfl
  case case60 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case61 =>
    rename_i hplan
    simp only [stepFn] at h
    rw [hplan] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  case case67 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨v, trv⟩, hd, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only
    refine ⟨(v, trv), hd, ?_⟩
    simp
  case case81 =>
    oblivious_apply h
  case case84 =>
    -- R3 / b6: the strict apply through the funnel; a `none` projection is a
    -- non-popping instance (`applyStrictOpPick_of_strictConsult?_none`).
    rename_i v op done env k'
    simp only [seqConsumption, Config.applyPos] at hsc
    obtain ⟨r, hr⟩ := applyStrictOpPick_of_strictConsult?_none (ctx := ctx) (s := σ)
      (leafOf := projChainTarget ctx σ k') hsc
    exact stepFn_strict_oblivious hr h
  case case85 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case86 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case87 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨b, hb, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only
    refine ⟨b, hb, ?_⟩
    simp
  case case88 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case89 =>
    simp only [stepFn, bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    obtain rfl := valueAsBool_ok hb
    cases b <;>
      (simp only [Bool.false_eq_true, reduceIte, pure_eq_ok, Except.ok.injEq,
         Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl, rfl⟩ := h
       refine ⟨by simp, fun ch => ?_⟩
       simp [stepFn, valueAsBool, Bind.bind, Except.bind])
  case case92 =>
    rename_i hlt
    simp only [stepFn, ite_eq_left hlt] at h
    (try simp only [Bind.bind, Except.bind] at h)
    split at h
    · simp at h
    · rename_i r hres
      cases r with
      | ok a =>
        simp only [deliverS_ok] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch => by simp [stepFn, hres, Bind.bind, Except.bind]⟩
      | panic msg =>
        simp only [deliverS_panic] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, fun ch => by simp [stepFn, ite_eq_left hlt, hres, Bind.bind, Except.bind]⟩
  case case93 =>
    rename_i hlt
    simp only [stepFn, ite_eq_right hlt, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only [stepFn, ite_eq_right hlt]
    rfl
  case case111 =>
    simp_all only [stepFn, bind_eq_ok, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq]
    obtain ⟨⟨base, start, trm⟩, hd, rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by simp, fun ch => ?_⟩
    simp only
    refine ⟨(base, start, trm), hd, ?_⟩
    simp
  case case114 =>
    oblivious_apply h
  case case124 =>
    oblivious_apply h
  case case133 =>
    oblivious_apply h
  case case148 =>
    oblivious_applyV h

-- A `fun_cases stepFn` sweep (every arm of the step function in ONE declaration), so the
-- per-arm costs sum against one budget: fails at 400000, passes at 800000 (measured
-- 2026-10-26, lane core/dc12-warnings-1026); 2x the measured need. The split that would
-- retire this is a per-phase decomposition of the case tree, not attempted.
set_option maxHeartbeats 1600000 in
/-- **The consumption theorem, `some` half**: a step whose projection is
`some (site, b)` DRAWS the site's pick at bound `b`, its stream is the
site's pop, and it depends on the stream only through that pick — any
stream drawing the same pick yields the same successor with its own popped
tail. PREMISE-FREE since packet D (2026-10-03; packet B audit F3, folding
`PrefixFacts.stepFn_consumption_some'` back here): the former hypothesis
`Config.appendTargetLocal` — the frontend's lowering contract at an
`appendSlice` apply (the target a hoisted local temp, a ROOT cell) — was
never read by this proof since C1 S3: the post-consult tail of a spilling
append is the VALIDATE phase's, panic-free for EVERY target
(`applyStmtOp_plan_appendSlice_spill`), as a TRY head's apply never panics
(`applyTryLock_noPanic`) — the "post-pop panic restores the pre-apply
stream" disjunct the first statement carried was a PROOF ARTIFACT of
stating the theorem over arbitrary configurations, refuted here (wave-(iii)
audit fix F1; design note §B8). -/
theorem stepFn_consumption_some {σ : Store} {c : Config} {ch₀ : Choices}
    {c' : Config} {σ' : Store} {ch₀' : Choices} {site : ChoiceSite} {b : Nat} {tr : StepLabel}
    (hsc : seqConsumption ctx σ c = some (site, b))
    (h : stepFn ctx σ c ch₀ = .ok (c', σ', ch₀', tr)) :
    ch₀' = (Choices.consumeAt site b ch₀).2 ∧ ∀ ch : Choices,
      (Choices.consumeAt site b ch).1 = (Choices.consumeAt site b ch₀).1 →
      stepFn ctx σ c ch = .ok (c', σ', (Choices.consumeAt site b ch).2, tr) := by
  fun_cases stepFn ctx σ c ch₀
  all_goals first
    | (simp [seqConsumption, Config.applyPos, entryCallSite?] at hsc; done)
    | (simp [stepFn] at h; done)
    | (simp_all [stepFn]; done)
    | (simp_all [seqConsumption, Config.applyPos, entryCallSite?]; done)
    | skip
  case case6 =>
    -- The `unseqPanic` pop (E13 option (b)): bound 2, the step depends on
    -- the stream only through the pick.
    rename_i chain k' pick ch'' ps hx
    simp only [seqConsumption, Option.some.injEq, Prod.mk.injEq] at hsc
    obtain ⟨rfl, rfl⟩ := hsc
    obtain ⟨rfl, hx'⟩ := Choices.consumeAtE_inv hx
    simp only [stepFn, hx, pure_eq_ok, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by rw [hx'], fun ch hpk => ?_⟩
    rw [hx'] at hpk
    obtain ⟨p, cs, hpc⟩ : ∃ p cs, Choices.consumeAt .unseqPanic 2 ch = (p, cs) := ⟨_, _, rfl⟩
    rw [hpc] at hpk ⊢
    simp only at hpk
    subst hpk
    simp [stepFn, hpc, Choices.consumeAtE_eq]
  -- The `unseq` scheduler's pick (Stage B): the `unseqNext` pop at bound
  -- `|ready|`, the step depending on the stream only through the pick.
  case case151 =>
    simp only [stepFn] at h ⊢
    exact stepUnseqNext_consumption_some hsc h
  case case2 =>
    consumption_entry_some h hsc
  case case32 =>
    consumption_entry_some h hsc
  case case91 =>
    consumption_entry_some h hsc
  case case95 =>
    consumption_entry_some h hsc
  case case101 =>
    consumption_entry_some h hsc
  case case7 =>
    -- The `.stop` arm (unit 6b): THE ABORT's consult step is the `panic`
    -- terminal (never `.ok`; the pool's `stepMulti_sound` carries its pick
    -- into the relation); the preprint PHASE's collision draw is a genuine
    -- bound-2 pop, the step depending on the stream only through the pick.
    simp only [stepFn] at h ⊢
    exact stepPanicStop_consumption_some hsc h
  case case142 =>
    simp only [stepFn] at h ⊢
    exact stepFrameExit_consumption_some (.inl rfl) hsc h
  case case153 =>
    -- B4: a signal the table resolves consumes nothing (no entry, no apply).
    exfalso
    simp [seqConsumption, Config.applyPos, entryCallSite?_of_signalStep ‹_›] at hsc
  case case154 =>
    simp only [stepFn, signalStep_frame] at h ⊢
    exact stepFrameExit_consumption_some (.inr rfl) hsc h
  case case84 =>
    -- R3 / b6: the strict apply through the funnel at a POPPING conversion
    -- (`strictConsult?_some`): the plan is pick-lifted (`applyStrictOpPick_draw`)
    -- and `stepFn_strict_pick` closes it.
    rename_i v op done env k'
    simp only [seqConsumption, Config.applyPos] at hsc
    obtain ⟨rfl, kind, literal, value, hk, hv, rfl, h1⟩ := strictConsult?_some hsc
    obtain ⟨g, hg, hnp⟩ := applyStrictOpPick_draw (ctx := ctx) (s := σ)
      (leafOf := projChainTarget ctx σ k') hk hv h1
    exact stepFn_strict_pick hg hnp h
  case case94 =>
    simp only [seqConsumption, Config.applyPos] at hsc
    -- The two consuming wide ops (`stmtConsult?_some`): the spilling append and
    -- (unit 5b) the `[0, n)` draw — each plan is pick-lifted (`_spill` /
    -- `_draw`), and `stepFn_stmtOp_pick` closes both. C1 S3: the post-consult
    -- tail is the validate phase's, panic-free for EVERY target — the
    -- root-target proviso `hloc` is no longer needed here (kept in the
    -- statement for its callers).
    rcases stmtConsult?_some hsc with ⟨elem, rfl, rfl, hw⟩ | ⟨rfl, rfl, hw⟩
    · obtain ⟨g, hg, hnp⟩ := applyStmtOp_plan_appendSlice_spill hw
      exact stepFn_stmtOp_pick hg hnp h
    · obtain ⟨g, hg, hnp⟩ := applyStmtOp_plan_randIntn_draw hw
      exact stepFn_stmtOp_pick hg hnp h
  case case116 =>
    rename_i v clauses default? done env k'
    simp only [seqConsumption, Config.applyPos, selectConsult?] at hsc
    cases hcore : applySelectCore ctx σ clauses default? ((v :: done).reverse) env k' with
    | error e => rw [hcore] at hsc; cases hsc
    | ok o =>
      cases o with
      | done c₁ s₁ cl? tr₁ => rw [hcore] at hsc; cases hsc
      | picks poll commits =>
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
            obtain ⟨c₂, s₂, tr₂⟩ := q
            simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            refine ⟨rfl, fun ch hpk => ?_⟩
            unfold stepFn
            dsimp only
            rw [applySelect_picks_stream hcore ch, hpk, hget]
            rfl
          | inr msg =>
            simp only [toResult_ok, Bind.bind, Except.bind, pure_eq_ok, deliverS_ok,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
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
          cases hcell : syncCell ctx σ loc with
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
              cases hat : applyTryLock ctx σ op loc pre
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
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                refine ⟨rfl, fun ch hpk => ?_⟩
                unfold stepFn
                dsimp only
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
                rw [hap ch, hpk, hat]
                rfl
  case case147 =>
    rename_i kv vv kt vt body base produced start env k'
    simp only [seqConsumption, mapIterConsult?] at hsc
    cases hcands : mapIterCandidates ctx σ kt vt base produced with
    | error e => rw [hcands] at hsc; cases hsc
    | ok pc =>
      obtain ⟨cands, trc⟩ := pc
      rw [hcands] at hsc
      (try dsimp only at hsc)
      by_cases hemp : cands.isEmpty
      · simp [hemp] at hsc
      · rw [ite_eq_right hemp] at hsc
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
          cases hbind : bindIterVars ctx env.pushScope σ kv vv kt vt cands[idx].2.1 cands[idx].2.2 with
          | error e => rw [hbind] at h; simp [Except.map] at h
          | ok p =>
            rw [hbind] at h
            simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
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
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨rfl, fun ch hpk => ?_⟩
          rcases hcons₁ : Choices.consumeAt .mapIter (cands.size + (if false = true then 0 else 1)) ch with ⟨idx₁, tail₁⟩
          have hcons₁' : Choices.consumeAt .mapIter (cands.size + 1) ch = (idx₁, tail₁) := by
            simpa using hcons₁
          rw [hcons₁] at hpk
          simp only at hpk
          subst hpk
          rw [stepFn_mapIter_stop hcands hmand hemp hcons₁']

/-- The one-layer unfolding of `execStmtLoop`, as an EQUATION (the loop
is fuel-structural, so the definitional unfolding needs the fuel
constructor exposed — `cases fuel` then `rfl`). -/
theorem execStmtLoop_unfold (fuel : Nat) (σ : Store) (c : Config)
    (ch : Choices) :
    execStmtLoop ctx fuel σ c ch
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
                 let (c', σ', choices', _) ← stepFn ctx σ c ch
                 execStmtLoop ctx fuel σ' c' choices') := by
  rw [execStmtLoop.eq_def]
  rfl

/-- One non-terminal step folds into the loop: `stepFn` throws on every
terminal shape, so a successful step means the loop at `fuel + 1` is
exactly the step followed by the loop at `fuel`. -/
theorem execStmtLoop_step {fuel : Nat} {σ : Store} {c : Config}
    {ch : Choices} {c₁ : Config} {σ₁ : Store} {ch₁ : Choices} {tr₁ : StepLabel}
    (h : stepFn ctx σ c ch = .ok (c₁, σ₁, ch₁, tr₁)) :
    execStmtLoop ctx (fuel + 1) σ c ch = execStmtLoop ctx fuel σ₁ c₁ ch₁ := by
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
