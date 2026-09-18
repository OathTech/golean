import GoLean.GoCore.MachineSound
import GoLean.GoCore.Race

/-!
# C1 frame-law spike (`docs/2026-09-17_c1-memory-module-charter.md` §5)

[AGENT] lane `core/c1-memory-module-0918`, S0. A ≤1-session, DISPOSABLE
check that the candidate representation — root cells with ROOT-FIRST
path-addressed leaf operations in the `Array.modifyM` discipline — admits
the disjoint-path frame law, INCLUDING the same-root half NPDRF.lean's
obstruction 6 records as unproved. Outside the lakefile and the gate; it
lands only as evidence (`docs/evidence/2026-09-18_c1-memory-module/`).
Nothing here is imported by `GoLean/`.

The charter's PASS criterion:
(a) the update primitives at distinct positions commute (`arraySet` at
    distinct indices; the field update at distinct names) — the two
    lemmas obstruction 6 names;
(b) the leaf congruence «normal root + normal leaf at the leaf type ⇒
    normal root after the write», at one `.field` and one `.index` depth;
(c) F1/F2 STATED against the stub and typechecked; F1 PROVED for depth ≤ 2
    (here: proved at EVERY depth — the path induction is no harder).

TWO FINDINGS (S0, this spike), both about the STATEMENT, neither about
the representation:

1. F1 with the charter's hypothesis `ShadowKey.overlap (.data l) (.data
   m) = false` is FALSE — `locPrefix` compares `.field` steps
   STRUCTURALLY, typeId included, so `.field b A f` and `.field b B f` (a
   struct-tag-compatible pointer alias, triage L7: `p.f` vs `(*B)(p).f`)
   are «disjoint» keys naming ONE memory word. `counterexample` exhibits
   it on a two-type table. F1 holds for the CANONICAL relation (typeIds
   erased, `pathsDisjoint`) — the key S2's trace should emit. The
   detector consequence (a missed race on tag-aliased fields — fail-OPEN
   vs `-race`) is a pre-existing defect of the conflict relation, filed
   as a finding, PENDING [USER].
2. F1 cannot be EXACT `Except` equality: the «wrong base kind» refusals
   (`expected array base for index load, got {repr other}`) embed the
   root VALUE, which the disjoint store changed. The law is agreement on
   SUCCESSFUL loads (`∀ w, load s' m = .ok w ↔ load s m = .ok w`);
   refusals stay refusals on both sides, their texts may differ.

The stub (`writeAt`/`stubStore`/`stubLoad`) is what S1's `storeLoc` will
be shaped like; it is NOT the S1 code (no `HeapNormal`, no refusal-text
discipline beyond what the lemmas need).
-/

namespace GoLean.GoCore.Machine

open GoLean

variable (ctx : ProgramCtx)

/-! ## Root-first paths -/

/-- One root-first path step (a `Loc` read from its root outwards). -/
inductive PathStep where
  | field (typeId : TypeId) (fieldName : String)
  | index (i : Int)
  deriving Repr, BEq, DecidableEq

/-- The MEMORY content of a step: the field NAME or the index — the
static `typeId` of a field step is a type-checking annotation, not an
address component. -/
def PathStep.canon : PathStep → String ⊕ Int
  | .field _ f => .inl f
  | .index i => .inr i

/-- The root address and the ROOT-FIRST path of a location (`Loc` nests
leaf-first: `.index (.field (.base a) T f) 3` is root `a`, then `f`,
then `3`). -/
def Loc.rootPath : Loc → Addr × List PathStep
  | .base a => (a, [])
  | .field b tid f => ((Loc.rootPath b).1, (Loc.rootPath b).2 ++ [.field tid f])
  | .index b i => ((Loc.rootPath b).1, (Loc.rootPath b).2 ++ [.index i])

theorem Loc.rootPath_fst (l : Loc) : (Loc.rootPath l).1.id = Loc.rootBase l := by
  induction l with
  | base a => rfl
  | field b _ _ ih => simpa [Loc.rootPath, Loc.rootBase] using ih
  | index b _ ih => simpa [Loc.rootPath, Loc.rootBase] using ih

/-- `rootPath` is injective (a path determines the location). -/
theorem Loc.rootPath_inj : ∀ {l m : Loc}, Loc.rootPath l = Loc.rootPath m → l = m := by
  intro l
  induction l with
  | base a =>
    intro m h
    cases m with
    | base b => simp_all [Loc.rootPath]
    | field mb _ _ => have := congrArg Prod.snd h; simp [Loc.rootPath] at this
    | index mb _ => have := congrArg Prod.snd h; simp [Loc.rootPath] at this
  | field b tid f ih =>
    intro m h
    cases m with
    | base c => have := congrArg Prod.snd h; simp [Loc.rootPath] at this
    | field mb mt mf =>
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp only [Loc.rootPath] at h1 h2
      obtain ⟨hp, hs⟩ := List.append_inj' h2 rfl
      simp only [List.cons.injEq, PathStep.field.injEq, and_true] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [ih (Prod.ext h1 hp)]
    | index mb mi =>
      have h2 := congrArg Prod.snd h
      dsimp only [Loc.rootPath] at h2
      obtain ⟨_, hs⟩ := List.append_inj' h2 rfl
      simp at hs
  | index b i ih =>
    intro m h
    cases m with
    | base c => have := congrArg Prod.snd h; simp [Loc.rootPath] at this
    | field mb mt mf =>
      have h2 := congrArg Prod.snd h
      dsimp only [Loc.rootPath] at h2
      obtain ⟨_, hs⟩ := List.append_inj' h2 rfl
      simp at hs
    | index mb mi =>
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp only [Loc.rootPath] at h1 h2
      obtain ⟨hp, hs⟩ := List.append_inj' h2 rfl
      simp only [List.cons.injEq, PathStep.index.injEq, and_true] at hs
      subst hs
      rw [ih (Prod.ext h1 hp)]

/-! ## The bridge: `locPrefix` is root equality + STRUCTURAL path prefix -/

theorem locPrefix_iff (l : Loc) : ∀ m : Loc, locPrefix l m = true ↔
    ((Loc.rootPath l).1 = (Loc.rootPath m).1 ∧ (Loc.rootPath l).2 <+: (Loc.rootPath m).2) := by
  intro m
  induction m with
  | base a =>
    constructor
    · intro h
      simp only [locPrefix, beq_iff_eq] at h
      subst h
      exact ⟨rfl, List.prefix_refl _⟩
    · rintro ⟨h1, h2⟩
      have hnil : (Loc.rootPath l).2 = [] := List.prefix_nil.mp h2
      have : l = .base a := Loc.rootPath_inj (Prod.ext h1 hnil)
      subst this
      simp [locPrefix]
  | field b tid f ih =>
    constructor
    · intro h
      simp only [locPrefix, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; exact ⟨rfl, List.prefix_refl _⟩
      · obtain ⟨h1, h2⟩ := ih.mp h
        exact ⟨h1, h2.trans (List.prefix_append _ _)⟩
    · rintro ⟨h1, h2⟩
      simp only [locPrefix, Bool.or_eq_true, beq_iff_eq]
      rcases List.prefix_concat_iff.mp h2 with h | h
      · exact Or.inl (Loc.rootPath_inj
          (Prod.ext h1 h : Loc.rootPath l = Loc.rootPath (.field b tid f)))
      · exact Or.inr (ih.mpr ⟨h1, h⟩)
  | index b i ih =>
    constructor
    · intro h
      simp only [locPrefix, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; exact ⟨rfl, List.prefix_refl _⟩
      · obtain ⟨h1, h2⟩ := ih.mp h
        exact ⟨h1, h2.trans (List.prefix_append _ _)⟩
    · rintro ⟨h1, h2⟩
      simp only [locPrefix, Bool.or_eq_true, beq_iff_eq]
      rcases List.prefix_concat_iff.mp h2 with h | h
      · exact Or.inl (Loc.rootPath_inj
          (Prod.ext h1 h : Loc.rootPath l = Loc.rootPath (.index b i)))
      · exact Or.inr (ih.mpr ⟨h1, h⟩)

/-- Two DATA keys do not overlap (structurally) iff neither location is a
structural ancestor-or-equal of the other, in `rootPath` terms. -/
theorem data_overlap_false_iff (l m : Loc) :
    ShadowKey.overlap (.data l) (.data m) = false ↔
      (¬ ((Loc.rootPath l).1 = (Loc.rootPath m).1 ∧ (Loc.rootPath l).2 <+: (Loc.rootPath m).2) ∧
       ¬ ((Loc.rootPath m).1 = (Loc.rootPath l).1 ∧ (Loc.rootPath m).2 <+: (Loc.rootPath l).2)) := by
  simp only [ShadowKey.overlap, locOverlap, Bool.or_eq_false_iff]
  simp only [Bool.eq_false_iff, ne_eq, locPrefix_iff]

/-- CANONICAL path disjointness: neither canonical path is a prefix of
the other — memory-level disjointness of two paths under one root. -/
def pathsDisjoint (p q : List PathStep) : Prop :=
  ¬ p.map PathStep.canon <+: q.map PathStep.canon ∧ ¬ q.map PathStep.canon <+: p.map PathStep.canon

/-! ## The stub: root-first read and in-place write on values -/

/-- First field position with the given name. -/
def fieldIdx? (fields : Array (String × GoValue)) (f : String) : Option Nat :=
  fields.findIdx? (·.1 == f)

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

/-- Root-first read along a path. -/
def readAt : GoValue → List PathStep → Except Stop GoValue
  | v, [] => pure v
  | v, step :: rest => do readAt (← projectStep ctx v step) rest

/-- Root-first IN-PLACE write along a path (`Array.modifyM` at every
level: the element is taken out of its array while rebuilt, so a
uniquely owned root is updated without copying). The leaf value `v` is
what the caller normalized at the leaf's declared type. -/
def writeAt : GoValue → List PathStep → GoValue → Except Stop GoValue
  | _, [], v => pure v
  | .struct actualType fields, .field typeId fieldName :: rest, v =>
      if actualType != typeId && !structTagCompatible ctx actualType typeId then
        stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
      else
        match fieldIdx? fields fieldName with
        | some k => do
            let fields' ← fields.modifyM k (fun (n, old) => do return (n, ← writeAt old rest v))
            return .struct actualType fields'
        | none => stuck s!"unknown GoCore struct field: {fieldName}"
  | other, .field _ _ :: _, _ => stuck s!"expected struct base for field store, got {repr other}"
  | .array values, .index index :: rest, v => do
      let k ← arrayIndexNat values index
      let values' ← values.modifyM k (fun old => writeAt old rest v)
      return .array values'
  | other, .index _ :: _, _ => stuck s!"expected array base for index store, got {repr other}"

/-- The leaf's declared type: descend the root's declared type along the
path, following `.defined` indirections through the table at each step. -/
def leafTy : Ty → List PathStep → Except Stop Ty
  | ty, [] => pure ty
  | ty, step :: rest => do
      match ← ctx.types.resolve ctx.types.size ty, step with
      | .struct _ fields, .field _ f =>
          match fields.find? (·.name == f) with
          | some fd => leafTy fd.typ rest
          | none => stuck s!"unknown GoCore struct field: {f}"
      | .plain (.array _ elem), .index _ => leafTy elem rest
      | _, _ => stuck "leaf descent: the declared type has no such component"

/-- The stub's store: leaf-typed normalization, in-place path write, ONE
root-cell update. -/
def stubStore (s : Store) (l : Loc) (v : GoValue) : Except Stop Store :=
  s.updateCell (Loc.rootPath l).1 fun
    | .value ty root => do
        let lt ← leafTy ctx ty (Loc.rootPath l).2
        let v' ← normalizeValueForTy ctx lt v
        return .value ty (← writeAt ctx root (Loc.rootPath l).2 v')
    | .mapPayload .. => stuck s!"value store into a map payload cell {repr (Loc.rootLoc l)}"
    | .chanPayload .. => stuck s!"value store into a channel payload cell {repr (Loc.rootLoc l)}"

/-- The stub's load: root cell, then the root-first read. -/
def stubLoad (s : Store) (l : Loc) : Except Stop GoValue :=
  match Heap.lookup s.heap (.base (Loc.rootPath l).1) with
  | some (.value _ root) => readAt ctx root (Loc.rootPath l).2
  | some (.mapPayload ..) => stuck s!"value load from a map payload cell {repr (Loc.rootLoc l)}"
  | some (.chanPayload ..) => stuck s!"value load from a channel payload cell {repr (Loc.rootLoc l)}"
  | none => stuck s!"unbound GoCore heap location: {repr (Loc.rootLoc l)}"

/-! ## `Array.modifyM` in `Except`, unfolded once -/

theorem Array.modifyM_ok_iff {α : Type} (xs : Array α) (i : Nat) (hi : i < xs.size)
    (f : α → Except Stop α) (ys : Array α) :
    xs.modifyM i f = .ok ys ↔ ∃ v, f xs[i] = .ok v ∧ ys = xs.set i v hi := by
  unfold Array.modifyM
  rw [dif_pos hi]
  constructor
  · intro h
    simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
    obtain ⟨v, hv, h⟩ := h
    exact ⟨v, hv, h.symm⟩
  · rintro ⟨v, hv, rfl⟩
    dsimp only
    rw [hv]
    rfl

/-! ## `StructFields.lookup` is the first match by name -/

/-- The `foldl` step of `StructFields.lookup`, named for the lemmas. -/
def lookupStep (needle : String) (found : Option GoValue) (nv : String × GoValue) :
    Option GoValue :=
  match found with
  | some value => some value
  | none => if nv.1 == needle then some nv.2 else none

theorem foldl_lookupStep_some (needle : String) (v : GoValue) :
    ∀ l : List (String × GoValue), l.foldl (lookupStep needle) (some v) = some v := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih => simpa [List.foldl, lookupStep] using ih

theorem foldl_lookupStep_none (needle : String) :
    ∀ l : List (String × GoValue),
      l.foldl (lookupStep needle) none = (l.find? (·.1 == needle)).map (·.2) := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih =>
    by_cases hx : x.1 == needle
    · simp [List.foldl, lookupStep, hx, foldl_lookupStep_some]
    · simp [List.foldl, lookupStep, hx, ih]

theorem StructFields.lookup_eq_find? (fields : Array (String × GoValue)) (needle : String) :
    StructFields.lookup fields needle = (fields.toList.find? (·.1 == needle)).map (·.2) := by
  simp only [StructFields.lookup]
  rw [← Array.foldl_toList]
  exact foldl_lookupStep_none needle fields.toList

/-- The first match, characterized by position. -/
theorem List.find?_eq_of_first {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k : Nat) (hk : k < l.length),
      p l[k] = true → (∀ j (hj : j < k), p (l[j]'(Nat.lt_trans hj hk)) = false) →
      l.find? p = some l[k] := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons x rest ih =>
    intro k hk hpk hbefore
    cases k with
    | zero => simp_all
    | succ k =>
      have hx : p x = false := hbefore 0 (Nat.zero_lt_succ _)
      simp only [List.getElem_cons_succ] at hpk
      have hstep : List.find? p (x :: rest) = List.find? p rest :=
        List.find?_cons_of_neg (by simp [hx])
      rw [hstep, List.getElem_cons_succ]
      exact ih k (by simpa using hk) hpk
        (fun j hj => hbefore (j + 1) (Nat.succ_lt_succ hj))

/-- `find?` after replacing the FIRST match by a still-matching element. -/
theorem List.find?_set_first {α : Type} (p : α → Bool) :
    ∀ (l : List α) (k : Nat) (hk : k < l.length) (x : α),
      (∀ j (hj : j < k), p (l[j]'(Nat.lt_trans hj hk)) = false) → p x = true →
      (l.set k x).find? p = some x := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons y rest ih =>
    intro k hk x hbefore hx
    cases k with
    | zero => simp [List.set, hx]
    | succ k =>
      have hy : p y = false := hbefore 0 (Nat.zero_lt_succ _)
      have hstep : List.find? p (y :: rest.set k x) = List.find? p (rest.set k x) :=
        List.find?_cons_of_neg (by simp [hy])
      simp only [List.set]
      rw [hstep]
      exact ih k (by simpa using hk) x
        (fun j hj => hbefore (j + 1) (Nat.succ_lt_succ hj)) hx

/-- `find?` for a predicate that FAILS on both the replaced element and
its replacement is unchanged by the replacement. -/
theorem List.find?_set_of_neg {α : Type} (q : α → Bool) :
    ∀ (l : List α) (k : Nat) (hk : k < l.length) (x : α),
      q l[k] = false → q x = false → (l.set k x).find? q = l.find? q := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons y rest ih =>
    intro k hk x hk0 hx
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hk0
      simp [List.set, hk0, hx]
    | succ k =>
      simp only [List.getElem_cons_succ] at hk0
      by_cases hqy : q y = true
      · simp [List.set, hqy]
      · simp only [Bool.not_eq_true] at hqy
        have h1 : List.find? q (y :: rest.set k x) = List.find? q (rest.set k x) :=
          List.find?_cons_of_neg (by simp [hqy])
        have h2 : List.find? q (y :: rest) = List.find? q rest :=
          List.find?_cons_of_neg (by simp [hqy])
        simp only [List.set]
        rw [h1, h2]
        exact ih k (by simpa using hk) x hk0 hx

/-- What `fieldIdx? fields f = some k` says: in range, the name matches,
no earlier name does. -/
theorem fieldIdx?_spec (fields : Array (String × GoValue)) (f : String) (k : Nat)
    (h : fieldIdx? fields f = some k) :
    ∃ hk : k < fields.size, fields[k].1 = f ∧
      ∀ j (hj : j < k), (fields[j]'(Nat.lt_trans hj hk)).1 ≠ f := by
  unfold fieldIdx? at h
  obtain ⟨hk, hp, hbefore⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨hk, by simpa using hp, fun j hj => ?_⟩
  have := hbefore j hj
  simpa using this

theorem StructFields.lookup_of_fieldIdx? (fields : Array (String × GoValue)) (f : String)
    (k : Nat) (h : fieldIdx? fields f = some k) :
    ∃ hk : k < fields.size, StructFields.lookup fields f = some fields[k].2 := by
  obtain ⟨hk, hname, hbefore⟩ := fieldIdx?_spec fields f k h
  refine ⟨hk, ?_⟩
  rw [StructFields.lookup_eq_find?]
  have hk' : k < fields.toList.length := by simpa using hk
  rw [List.find?_eq_of_first _ fields.toList k hk' (by simpa using hname)
    (fun j hj => by
      have := hbefore j hj
      simpa [Array.getElem_toList] using this)]
  simp

theorem StructFields.lookup_set_self (fields : Array (String × GoValue)) (f : String)
    (k : Nat) (hk : k < fields.size) (h : fieldIdx? fields f = some k) (v : GoValue) :
    StructFields.lookup (fields.set k (fields[k].1, v) hk) f = some v := by
  obtain ⟨_, hname, hbefore⟩ := fieldIdx?_spec fields f k h
  rw [StructFields.lookup_eq_find?, Array.toList_set]
  have hk' : k < fields.toList.length := by simpa using hk
  rw [List.find?_set_first _ fields.toList k hk' _
    (fun j hj => by
      have := hbefore j hj
      simpa [Array.getElem_toList] using this) (by simpa using hname)]
  rfl

theorem StructFields.lookup_set_ne (fields : Array (String × GoValue)) (f g : String)
    (k : Nat) (hk : k < fields.size) (h : fieldIdx? fields f = some k) (hfg : f ≠ g)
    (v : GoValue) :
    StructFields.lookup (fields.set k (fields[k].1, v) hk) g = StructFields.lookup fields g := by
  obtain ⟨_, hname, _⟩ := fieldIdx?_spec fields f k h
  have hne : (fields[k].1 == g) = false := by
    rw [hname]; simpa using hfg
  rw [StructFields.lookup_eq_find?, StructFields.lookup_eq_find?, Array.toList_set]
  have hk' : k < fields.toList.length := by simpa using hk
  rw [List.find?_set_of_neg _ fields.toList k hk' _ (by simpa [Array.getElem_toList] using hne) hne]

/-! ## `stubLoad` IS `loadLoc` (the leaf-first ↔ root-first bridge) -/

theorem readAt_append (v : GoValue) (p : List PathStep) (step : PathStep) :
    readAt ctx v (p ++ [step]) = (readAt ctx v p >>= fun x => readAt ctx x [step]) := by
  induction p generalizing v with
  | nil => simp [readAt, Bind.bind, Except.bind]
  | cons s rest ih =>
    simp only [List.cons_append, readAt]
    cases projectStep ctx v s with
    | error e => simp [Bind.bind, Except.bind]
    | ok w => simp only [Bind.bind, Except.bind]; exact ih w

theorem Loc.rootLoc_eq (l : Loc) : Loc.rootLoc l = .base (Loc.rootPath l).1 := by
  have h := Loc.rootPath_fst l
  unfold Loc.rootLoc
  rcases hx : (Loc.rootPath l).1 with ⟨i⟩
  rw [hx] at h
  simp only at h
  rw [h]

theorem stubLoad_eq_loadLoc (s : Store) : ∀ l : Loc, stubLoad ctx s l = loadLoc ctx s l := by
  intro l
  induction l with
  | base a =>
    obtain ⟨i⟩ := a
    simp only [stubLoad, loadLoc, Loc.rootPath, Loc.rootLoc, Loc.rootBase]
    split <;> simp_all [readAt]
  | field b tid f ih =>
    have hroot : (Loc.rootPath (.field b tid f)).1 = (Loc.rootPath b).1 := rfl
    have hpath : (Loc.rootPath (.field b tid f)).2 = (Loc.rootPath b).2 ++ [.field tid f] := rfl
    simp only [loadLoc]
    rw [← ih]
    simp only [stubLoad, hroot, hpath, Loc.rootLoc_eq, readAt_append]
    split
    · simp only [Bind.bind, Except.bind]
      split
      · rfl
      · rename_i w _
        cases w with
        | struct actualType fields =>
          simp only [readAt, projectStep, Bind.bind, Except.bind]
          by_cases hc : (actualType != tid && !structTagCompatible ctx actualType tid) = true
          · simp [hc, stuck, throw, throwThe, MonadExceptOf.throw]
          · have hc' : (actualType != tid && !structTagCompatible ctx actualType tid) = false := by
              simpa using hc
            simp only [hc', Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
            cases StructFields.lookup fields f <;>
              simp [pure, Except.pure, stuck, throw, throwThe, MonadExceptOf.throw, Bind.bind,
                Except.bind]
        | _ => simp [readAt, projectStep, Bind.bind, Except.bind, stuck, throw, throwThe,
                MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
  | index b i ih =>
    have hroot : (Loc.rootPath (.index b i)).1 = (Loc.rootPath b).1 := rfl
    have hpath : (Loc.rootPath (.index b i)).2 = (Loc.rootPath b).2 ++ [.index i] := rfl
    simp only [loadLoc]
    rw [← ih]
    simp only [stubLoad, hroot, hpath, Loc.rootLoc_eq, readAt_append]
    split
    · simp only [Bind.bind, Except.bind]
      split
      · rfl
      · rename_i w _
        cases w with
        | array values =>
          simp only [readAt, projectStep, Bind.bind, Except.bind]
          cases arrayGet values i <;> rfl
        | _ => simp [readAt, projectStep, Bind.bind, Except.bind, stuck, throw, throwThe,
                MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]
    · simp [Bind.bind, Except.bind, stuck, throw, throwThe, MonadExceptOf.throw]

/-! ## (a) The primitives commute at distinct positions -/

theorem Array.modify_comm {α : Type} (xs : Array α) {i j : Nat} (hij : i ≠ j) (f g : α → α) :
    (xs.modify i f).modify j g = (xs.modify j g).modify i f := by
  apply Array.ext
  · simp
  · intro k hk hk'
    simp only [Array.getElem_modify]
    by_cases hki : i = k <;> by_cases hkj : j = k <;> simp_all

theorem arrayIndexNat_spec {values : Array GoValue} {i : Int} {k : Nat}
    (h : arrayIndexNat values i = .ok k) : 0 ≤ i ∧ k = i.toNat ∧ k < values.size := by
  unfold arrayIndexNat at h
  by_cases hneg : i < 0
  · simp [hneg, indexOutOfRangePanic, panic, throw, throwThe, MonadExceptOf.throw,
      Bind.bind, Except.bind] at h
  · by_cases hlt : i.toNat < values.size
    · simp [hneg, hlt, Bind.bind, Except.bind, pure, Except.pure] at h
      subst h
      exact ⟨Int.not_lt.mp hneg, rfl, hlt⟩
    · simp [hneg, hlt, indexOutOfRangePanic, panic, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind, pure, Except.pure] at h

theorem arrayIndexNat_ok {values : Array GoValue} {i : Int} (h0 : 0 ≤ i)
    (hlt : i.toNat < values.size) : arrayIndexNat values i = .ok i.toNat := by
  unfold arrayIndexNat
  simp [Int.not_lt.mpr h0, hlt, Bind.bind, Except.bind, pure, Except.pure]

theorem arraySet_ok {values : Array GoValue} {i : Int} (h0 : 0 ≤ i)
    (hlt : i.toNat < values.size) (v : GoValue) :
    arraySet values i v = .ok (values.set i.toNat v hlt) := by
  unfold arraySet
  rw [arrayIndexNat_ok h0 hlt]
  simp [Array.getElem?_eq_getElem hlt, Array.set!, Array.setIfInBounds, hlt,
    Bind.bind, Except.bind, pure, Except.pure]

/-- `arraySet` at two DISTINCT in-range indices commutes — the array half
of the lemma pair obstruction 6 names. -/
theorem arraySet_comm (values : Array GoValue) {i j : Int} (hij : i ≠ j) (v w : GoValue)
    {a b : Array GoValue}
    (ha : arraySet values i v = .ok a) (hb : arraySet values j w = .ok b) :
    arraySet a j w = arraySet b i v := by
  unfold arraySet at ha hb
  simp only [bind_eq_ok] at ha hb
  obtain ⟨ki, hki, ha⟩ := ha
  obtain ⟨kj, hkj, hb⟩ := hb
  obtain ⟨hi0, rfl, hilt⟩ := arrayIndexNat_spec hki
  obtain ⟨hj0, rfl, hjlt⟩ := arrayIndexNat_spec hkj
  have hkij : i.toNat ≠ j.toNat := fun h => hij (by omega)
  simp only [Array.getElem?_eq_getElem hilt, pure_eq_ok, Except.ok.injEq] at ha
  simp only [Array.getElem?_eq_getElem hjlt, pure_eq_ok, Except.ok.injEq] at hb
  subst ha hb
  have hilt' : i.toNat < (values.set! j.toNat w).size := by simpa using hilt
  have hjlt' : j.toNat < (values.set! i.toNat v).size := by simpa using hjlt
  rw [arraySet_ok hj0 hjlt', arraySet_ok hi0 hilt']
  congr 1
  simp only [Array.set!, Array.setIfInBounds, hilt, hjlt, dite_true]
  exact Array.set_comm _ _ hkij

/-- The field update at two DISTINCT names commutes (the struct half of
the pair; the candidate's update is `Array.modify` at the name's
position, and the positions of distinct names are distinct). -/
theorem fieldModify_comm (fields : Array (String × GoValue)) {f g : String} (hfg : f ≠ g)
    {kf kg : Nat} (hf : fieldIdx? fields f = some kf) (hg : fieldIdx? fields g = some kg)
    (u w : GoValue → GoValue) :
    (fields.modify kf (fun (n, x) => (n, u x))).modify kg (fun (n, x) => (n, w x))
      = (fields.modify kg (fun (n, x) => (n, w x))).modify kf (fun (n, x) => (n, u x)) := by
  apply Array.modify_comm
  intro heq
  subst heq
  obtain ⟨_, hpf, _⟩ := fieldIdx?_spec fields f kf hf
  obtain ⟨_, hpg, _⟩ := fieldIdx?_spec fields g kf hg
  exact hfg (hpf.symm.trans hpg)

/-! ## (b) The leaf congruence, one `.index` depth and one `.field` depth -/

theorem isNormalListWith_iff {f : GoValue → Bool} :
    ∀ l : List GoValue, isNormalListWith f l = true ↔ ∀ x ∈ l, f x = true := by
  intro l
  induction l with
  | nil => simp [isNormalListWith]
  | cons x rest ih => simp [isNormalListWith, ih]

theorem isNormalListWith_set {f : GoValue → Bool} (values : Array GoValue) (k : Nat)
    (hk : k < values.size) (v : GoValue)
    (hall : isNormalListWith f values.toList = true) (hv : f v = true) :
    isNormalListWith f (values.set k v hk).toList = true := by
  rw [isNormalListWith_iff] at hall ⊢
  intro x hx
  rw [Array.toList_set] at hx
  rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
  · exact hall x hmem
  · exact hv

/-- ONE INDEX DEPTH: a normal array cell updated at one element by a value
normal at the element type is normal. -/
theorem isNormalForTyTy_array_set (atDefined : TypeIdx → GoValue → Bool)
    (length : Nat) (elem : Ty) (values : Array GoValue) (k : Nat) (hk : k < values.size)
    (v : GoValue)
    (hroot : isNormalForTyTy atDefined (.array length elem) (.array values) = true)
    (hleaf : isNormalForTyTy atDefined elem v = true) :
    isNormalForTyTy atDefined (.array length elem) (.array (values.set k v hk)) = true := by
  simp only [isNormalForTyTy, Bool.and_eq_true, decide_eq_true_eq] at hroot ⊢
  obtain ⟨hsize, hlist⟩ := hroot
  exact ⟨by simpa using hsize, isNormalListWith_set values k hk v hlist hleaf⟩

theorem isNormalFieldsWith_set {f : Ty → GoValue → Bool} :
    ∀ (defs : List FieldDef) (fields : List (String × GoValue)) (k : Nat)
      (name : String) (old v : GoValue),
      fields[k]? = some (name, old) →
      isNormalFieldsWith f defs fields = true →
      (∀ fd, defs[k]? = some fd → f fd.typ v = true) →
        isNormalFieldsWith f defs (fields.set k (name, v)) = true := by
  intro defs
  induction defs with
  | nil =>
    intro fields k name old v _ h _
    cases fields with
    | nil => simp [isNormalFieldsWith]
    | cons _ _ => simp [isNormalFieldsWith] at h
  | cons fd rest ih =>
    intro fields k name old v hk h hv
    cases fields with
    | nil => simp [isNormalFieldsWith] at h
    | cons fv fvs =>
      obtain ⟨fname, fval⟩ := fv
      simp only [isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hname, hval⟩, hrest⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp only [List.set, isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hname, hv fd rfl⟩, hrest⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [List.set, isNormalFieldsWith, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨hname, hval⟩, ih fvs k name old v hk hrest (fun fd' h' => hv fd' h')⟩

/-- ONE FIELD DEPTH: a normal struct cell (at defined type `i`, a struct
declaration) updated at field position `k` by a value normal at that
field's declared type is normal. Stated at the INDEX layer, where the
struct arm lives. -/
theorem isNormalForTyAt_struct_set (types : TypeEnv) (bound : Nat) (i : TypeIdx)
    (name : TypeId) (defs : Array FieldDef) (fields : Array (String × GoValue))
    (k : Nat) (hk : k < fields.size) (v : GoValue)
    (htab : types[i]? = some (name, .struct defs))
    (hroot : isNormalForTyAt types (bound + 1) i (.struct name fields) = true)
    (hleaf : ∀ fd, defs[k]? = some fd →
      isNormalForTyTy (isNormalForTyAt types bound) fd.typ v = true) :
    isNormalForTyAt types (bound + 1) i (.struct name (fields.set k (fields[k].1, v) hk)) = true := by
  simp only [isNormalForTyAt, htab, Bool.and_eq_true, decide_eq_true_eq] at hroot ⊢
  obtain ⟨⟨_, hsize⟩, hfields⟩ := hroot
  refine ⟨⟨trivial, by simpa using hsize⟩, ?_⟩
  have hk' : fields.toList[k]? = some (fields[k].1, fields[k].2) := by
    simp [List.getElem?_eq_getElem (show k < fields.toList.length by simpa using hk)]
  have := isNormalFieldsWith_set (f := isNormalForTyTy (isNormalForTyAt types bound))
    defs.toList fields.toList k fields[k].1 fields[k].2 v hk' hfields
    (fun fd h => hleaf fd (by simpa using h))
  simpa [Array.toList_set] using this

/-! ## (c) F1 / F2 — the disjoint-path frame laws, stated on the stub -/

/-- **F1 as chartered** (structural `ShadowKey.overlap`; conclusion =
agreement on successful loads, finding 2): a store at `l` is invisible
to every load at a non-overlapping `m`. REFUTED below (`counterexample`,
finding 1): structural non-overlap is not memory disjointness. -/
def F1 : Prop :=
  ∀ (s s' : Store) (l m : Loc) (v : GoValue),
    ShadowKey.overlap (.data l) (.data m) = false →
    stubStore ctx s l v = .ok s' →
    ∀ w, loadLoc ctx s' m = .ok w ↔ loadLoc ctx s m = .ok w

/-- **F2 as chartered**: two stores at non-overlapping paths commute —
equal stores (their traces, when S2 adds them, permute). -/
def F2 : Prop :=
  ∀ (s s₁ s₂ t₁ t₂ : Store) (l m : Loc) (v w : GoValue),
    ShadowKey.overlap (.data l) (.data m) = false →
    stubStore ctx s l v = .ok s₁ → stubStore ctx s₁ m w = .ok s₂ →
    stubStore ctx s m w = .ok t₁ → stubStore ctx t₁ l v = .ok t₂ →
    s₂ = t₂

/-- **F1 on the CANONICAL relation** — different roots, or canonically
disjoint paths under one root. PROVED (`f1_canon`, every depth). -/
def F1Canon : Prop :=
  ∀ (s s' : Store) (l m : Loc) (v : GoValue),
    ((Loc.rootPath l).1 ≠ (Loc.rootPath m).1 ∨ pathsDisjoint (Loc.rootPath l).2 (Loc.rootPath m).2) →
    stubStore ctx s l v = .ok s' →
    ∀ w, loadLoc ctx s' m = .ok w ↔ loadLoc ctx s m = .ok w

/-- **F2 on the CANONICAL relation** (stated; the S1/S2 proof obligation). -/
def F2Canon : Prop :=
  ∀ (s s₁ s₂ t₁ t₂ : Store) (l m : Loc) (v w : GoValue),
    ((Loc.rootPath l).1 ≠ (Loc.rootPath m).1 ∨ pathsDisjoint (Loc.rootPath l).2 (Loc.rootPath m).2) →
    stubStore ctx s l v = .ok s₁ → stubStore ctx s₁ m w = .ok s₂ →
    stubStore ctx s m w = .ok t₁ → stubStore ctx t₁ l v = .ok t₂ →
    s₂ = t₂

/-- Unfolding a successful struct-field write: the position, the sub-write. -/
theorem writeAt_field_ok {actual : TypeId} {fields : Array (String × GoValue)} {tid : TypeId}
    {f : String} {rest : List PathStep} {v root' : GoValue}
    (hw : writeAt ctx (.struct actual fields) (.field tid f :: rest) v = .ok root') :
    ∃ (k : Nat) (hk : k < fields.size) (old' : GoValue),
      fieldIdx? fields f = some k ∧ writeAt ctx fields[k].2 rest v = .ok old' ∧
      root' = .struct actual (fields.set k (fields[k].1, old') hk) := by
  simp only [writeAt] at hw
  split at hw
  · simp [stuck, throw, throwThe, MonadExceptOf.throw] at hw
  · split at hw
    · rename_i k hidx
      obtain ⟨hk, _, _⟩ := fieldIdx?_spec fields f k hidx
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hw
      obtain ⟨fields', hmod, rfl⟩ := hw
      obtain ⟨nv, hnv, rfl⟩ := (Array.modifyM_ok_iff fields k hk _ fields').mp hmod
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hnv
      obtain ⟨old', hold', rfl⟩ := hnv
      exact ⟨k, hk, old', hidx, hold', rfl⟩
    · simp [stuck, throw, throwThe, MonadExceptOf.throw] at hw

/-- Unfolding a successful array-element write. -/
theorem writeAt_index_ok {values : Array GoValue} {i : Int} {rest : List PathStep}
    {v root' : GoValue}
    (hw : writeAt ctx (.array values) (.index i :: rest) v = .ok root') :
    ∃ (h0 : 0 ≤ i) (hlt : i.toNat < values.size) (old' : GoValue),
      writeAt ctx values[i.toNat] rest v = .ok old' ∧
      root' = .array (values.set i.toNat old' hlt) := by
  simp only [writeAt, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hw
  obtain ⟨k, hk, values', hmod, rfl⟩ := hw
  obtain ⟨h0, rfl, hlt⟩ := arrayIndexNat_spec hk
  obtain ⟨old', hold', rfl⟩ := (Array.modifyM_ok_iff values i.toNat hlt _ values').mp hmod
  exact ⟨h0, hlt, old', hold', rfl⟩

/-- The write-side frame on VALUES: a root-first write along `pl` leaves
every SUCCESSFUL read along a canonically disjoint `pm` unchanged
(refusals stay refusals — their texts may embed the changed value). -/
theorem readAt_writeAt_disjoint :
    ∀ (pl pm : List PathStep) (root root' v : GoValue),
      pathsDisjoint pl pm →
      writeAt ctx root pl v = .ok root' →
      ∀ w, readAt ctx root' pm = .ok w ↔ readAt ctx root pm = .ok w := by
  intro pl
  induction pl with
  | nil => intro pm _ _ _ h _; exact absurd (List.nil_prefix) h.1
  | cons sl rl ih =>
    intro pm root root' v ⟨hlm, hml⟩ hw w
    cases pm with
    | nil => exact absurd List.nil_prefix hml
    | cons sm rm =>
      simp only [List.map_cons] at hlm hml
      by_cases hs : sl.canon = sm.canon
      · -- Same memory step: descend into the shared component.
        have hlm' : ¬ rl.map PathStep.canon <+: rm.map PathStep.canon :=
          fun h => hlm (List.cons_prefix_cons.mpr ⟨hs, h⟩)
        have hml' : ¬ rm.map PathStep.canon <+: rl.map PathStep.canon :=
          fun h => hml (List.cons_prefix_cons.mpr ⟨hs.symm, h⟩)
        cases sl with
        | field tid f =>
          cases sm with
          | index _ => simp [PathStep.canon] at hs
          | field tid' g =>
            simp only [PathStep.canon, Sum.inl.injEq] at hs
            subst hs
            cases root with
            | struct actual fields =>
              obtain ⟨k, hk, old', hidx, hold', rfl⟩ := writeAt_field_ok ctx hw
              have hlook := StructFields.lookup_set_self fields f k hk hidx old'
              obtain ⟨_, hlook0⟩ := StructFields.lookup_of_fieldIdx? fields f k hidx
              simp only [readAt, projectStep, hlook, hlook0]
              split
              · exact Iff.rfl
              · simp only [Bind.bind, Except.bind, pure, Except.pure]
                exact ih rm _ old' v ⟨hlm', hml'⟩ hold' w
            | _ => simp [writeAt, stuck, throw, throwThe, MonadExceptOf.throw] at hw
        | index i =>
          cases sm with
          | field _ _ => simp [PathStep.canon] at hs
          | index j =>
            simp only [PathStep.canon, Sum.inr.injEq] at hs
            subst hs
            cases root with
            | array values =>
              obtain ⟨h0, hlt, old', hold', rfl⟩ := writeAt_index_ok ctx hw
              simp only [readAt, projectStep, arrayGet, Bind.bind, Except.bind]
              rw [arrayIndexNat_ok h0 (by simpa using hlt), arrayIndexNat_ok h0 hlt]
              simp only [Array.getElem?_eq_getElem hlt,
                Array.getElem?_eq_getElem (show i.toNat < (values.set i.toNat old' hlt).size by
                  simpa using hlt), Array.getElem_set_self, pure, Except.pure]
              exact ih rm _ old' v ⟨hlm', hml'⟩ hold' w
            | _ => simp [writeAt, stuck, throw, throwThe, MonadExceptOf.throw] at hw
      · -- Different memory steps: the write happened in another component,
        -- or the read refuses on both sides (wrong base kind).
        cases sl with
        | field tid f =>
          cases root with
          | struct actual fields =>
            obtain ⟨k, hk, old', hidx, _, rfl⟩ := writeAt_field_ok ctx hw
            cases sm with
            | field tid' g =>
              have hfg : f ≠ g := fun h => hs (by simp [PathStep.canon, h])
              simp only [readAt, projectStep]
              rw [StructFields.lookup_set_ne fields f g k hk hidx hfg old']
            | index j =>
              simp [readAt, projectStep, Bind.bind, Except.bind, stuck, throw, throwThe,
                MonadExceptOf.throw]
          | _ => simp [writeAt, stuck, throw, throwThe, MonadExceptOf.throw] at hw
        | index i =>
          cases root with
          | array values =>
            obtain ⟨h0, hlt, old', _, rfl⟩ := writeAt_index_ok ctx hw
            cases sm with
            | field _ _ =>
              simp [readAt, projectStep, Bind.bind, Except.bind, stuck, throw, throwThe,
                MonadExceptOf.throw]
            | index j =>
              have hij : i ≠ j := fun h => hs (by simp [PathStep.canon, h])
              simp only [readAt, projectStep, arrayGet]
              cases hj : arrayIndexNat values j with
              | error e =>
                have : arrayIndexNat (values.set i.toNat old' hlt) j = .error e := by
                  unfold arrayIndexNat at hj ⊢
                  simpa using hj
                simp [this, hj, Bind.bind, Except.bind]
              | ok kj =>
                obtain ⟨hj0, rfl, hjlt⟩ := arrayIndexNat_spec hj
                have hne : i.toNat ≠ j.toNat := fun h => hij (by omega)
                rw [arrayIndexNat_ok hj0 (by simpa using hjlt)]
                simp only [Bind.bind, Except.bind, Array.getElem?_eq_getElem hjlt,
                  Array.getElem?_eq_getElem (show j.toNat < (values.set i.toNat old' hlt).size by
                    simpa using hjlt), pure, Except.pure]
                rw [Array.getElem_set_ne hlt _ hne]
          | _ => simp [writeAt, stuck, throw, throwThe, MonadExceptOf.throw] at hw

/-- **F1 PROVED on the canonical relation** (every depth): the cross-root
half is `Store.updateCell_lookup_ne` + `loadLoc_root_congr` (the pair
NPDRF.lean already has), the same-root half is `readAt_writeAt_disjoint`. -/
theorem f1_canon : F1Canon ctx := by
  intro s s' l m v hdis hst w
  by_cases hroot : (Loc.rootPath l).1 = (Loc.rootPath m).1
  · -- Same root: the paths are canonically disjoint.
    have hpaths : pathsDisjoint (Loc.rootPath l).2 (Loc.rootPath m).2 := by
      rcases hdis with h | h
      · exact absurd hroot h
      · exact h
    rw [← stubLoad_eq_loadLoc, ← stubLoad_eq_loadLoc]
    unfold stubStore at hst
    unfold stubLoad
    rw [← hroot]
    unfold Store.updateCell at hst
    split at hst
    · rename_i hi
      simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hst
      obtain ⟨cell', hcell', rfl⟩ := hst
      simp only [Heap.lookup, Array.getElem?_set_self hi, Array.getElem?_eq_getElem hi]
      cases hcell : s.heap[(Loc.rootPath l).1.id] with
      | value ty root =>
        rw [hcell] at hcell'
        simp only [bind_eq_ok] at hcell'
        obtain ⟨lt, _, v', _, hcell'⟩ := hcell'
        simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at hcell'
        obtain ⟨root', hroot', rfl⟩ := hcell'
        exact readAt_writeAt_disjoint ctx _ _ root root' v' hpaths hroot' w
      | mapPayload _ _ =>
        rw [hcell] at hcell'
        simp [stuck, throw, throwThe, MonadExceptOf.throw] at hcell'
      | chanPayload _ _ _ =>
        rw [hcell] at hcell'
        simp [stuck, throw, throwThe, MonadExceptOf.throw] at hcell'
    · simp [throw, throwThe, MonadExceptOf.throw] at hst
  · -- Cross-root: the stored cell is not the loaded root.
    rw [loadLoc_root_congr (σ₁ := s) (σ₂ := s')]
    rw [Loc.rootLoc_eq]
    unfold stubStore at hst
    exact Store.updateCell_lookup_ne hst (fun h => hroot (by injection h))

/-! ## The counterexample to F1 as chartered (structural overlap) -/

/-- Two declared struct types with identical field lists — the
tag-compatible pair triage L7 admits (`(*B)(p)` aliases an `A` cell). -/
def aliasTypes : TypeEnv :=
  #[(⟨"main.A"⟩, .struct #[⟨"f", .int .int, false⟩]),
    (⟨"main.B"⟩, .struct #[⟨"f", .int .int, false⟩])]

def aliasCtx : ProgramCtx := ProgramCtx.ofTables aliasTypes #[] #[] #[] #[]

/-- One cell: an `A` struct with `f = 0`. -/
def aliasStore : Store :=
  { heap := #[.value (.defined 0) (.struct ⟨"main.A"⟩ #[("f", .int 0 .int)])] }

def locA : Loc := .field (.base ⟨0⟩) ⟨"main.A"⟩ "f"
def locB : Loc := .field (.base ⟨0⟩) ⟨"main.B"⟩ "f"

-- The two keys are structurally NON-overlapping … (evaluates to `false`)
#eval ShadowKey.overlap (.data locA) (.data locB)
-- … yet a store through `locA` is visible through `locB`: evaluates to
-- `Except.ok (Except.ok (int 0), Except.ok (int 5))` — the load at `locB`
-- reads 0 before and 5 after, so `F1 aliasCtx` is false.
#eval (stubStore aliasCtx aliasStore locA (.int 5 .int)).map fun s' =>
  (loadLoc aliasCtx aliasStore locB, loadLoc aliasCtx s' locB)

/-! The refutation is WITNESSED BY EVALUATION, not kernel-checked: the stub's
`fieldIdx?` is `Array.findIdx?`, whose loop is well-founded and blocks
`decide`/`rfl` (probed in S0: `.tmp/probe/FindIdx.lean`). S1 DESIGN
CONSTRAINT recorded from this: the module's field-position search must be
STRUCTURAL (the de-WF recipe `Ops.lean` documents at `normalizeListWith`),
never `Array.findIdx?`, or the interpreter stops kernel-reducing. -/

end GoLean.GoCore.Machine
