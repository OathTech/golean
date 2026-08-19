import GoLeanProofs.Frame.NoPanic
import GoLeanProofs.Frame.ContOps

/-!
# The executable frame theorem, module 5: heap-operation simulation

The operations that read or write the heap, commuted across `FrameSim`:
`loadLoc`/`storeLoc` (the entire memory interface), the cell readers
(`mapEntries`/`chanCell`/`syncCell`), the call-protocol list operations
(`loadMany`/`storeMany`/`bindParams`/`allocDecls`/`pinResultLocs`), and
frame entry (`enterFrame` with `dynamicDispatch?`). Plus the generic
two-run `forIn` simulation (`forIn_sim`) the `for`-loop operations
compose through.

Style note: the loop/bind lemmas are applied in `refine` position so the
elaborated loop bodies unify against the goal (the `StructFields.set_congr`
pattern from `MachineSound.lean`); the loop bodies are never restated.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

/-! ## Generic two-run `forIn` simulation -/

/-- Pointwise `ForInStep` relation: same step kind, related payloads. -/
def StepSim {β β' : Type} (R : β → β' → Prop) :
    ForInStep β → ForInStep β' → Prop
  | .done x, .done y => R x y
  | .yield x, .yield y => R x y
  | _, _ => False

/-- Two `forIn` loops over pointwise-related index lists (the framed one
the `t`-image of the canonical one) with `R`-related accumulators and
`ExSim`-related bodies stay `ExSim`-related. -/
theorem forIn_sim {α α' β β' : Type} {t : α → α'} {R : β → β' → Prop}
    {f : α → β → Except GoError (ForInStep β)}
    {g : α' → β' → Except GoError (ForInStep β')} :
    ∀ {l : List α} {b : β} {b' : β'},
      R b b' →
      (∀ a ∈ l, ∀ x y, R x y → ExSim (StepSim R) (f a x) (g (t a) y)) →
      ExSim R (forIn l b f) (forIn (l.map t) b' g) := by
  intro l
  induction l with
  | nil =>
      intro b b' hb _
      simpa [List.forIn_nil] using ExSim.ok (R := R) hb
  | cons a as ih =>
      intro b b' hb hstep
      rw [List.map_cons, List.forIn_cons, List.forIn_cons]
      refine ExSim.bind (hstep a (by simp) b b' hb) ?_
      intro r r' hr
      cases r with
      | done x =>
          cases r' with
          | done y => exact ExSim.ok hr
          | yield y => exact absurd hr (by simp [StepSim])
      | yield x =>
          cases r' with
          | done y => exact absurd hr (by simp [StepSim])
          | yield y =>
              exact ih hr (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha'))

/-- Same-index-list corollary (loops over shared or loc-free data). -/
theorem forIn_sim_same {α β β' : Type} {R : β → β' → Prop}
    {f : α → β → Except GoError (ForInStep β)}
    {g : α → β' → Except GoError (ForInStep β')}
    {l : List α} {b : β} {b' : β'}
    (hb : R b b')
    (hstep : ∀ a ∈ l, ∀ x y, R x y → ExSim (StepSim R) (f a x) (g a y)) :
    ExSim R (forIn l b f) (forIn l b' g) := by
  have := forIn_sim (t := id) (f := f) (g := g) hb hstep
  simpa using this

/-! ## Struct-field table operations -/

private theorem foldl_option_ren {A B : Type} {t : A → B}
    {rv : GoValue → GoValue}
    {F : Option GoValue → A → Option GoValue}
    {G : Option GoValue → B → Option GoValue}
    (hFG : ∀ acc a, G (acc.map rv) (t a) = (F acc a).map rv) :
    ∀ (l : List A) (acc : Option GoValue),
      List.foldl G (acc.map rv) (l.map t) = (List.foldl F acc l).map rv := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a as ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, hFG]
      exact ih (F acc a)

theorem structFieldsLookup_ren (ρ : Nat → Nat)
    (fields : Array (String × GoValue)) (needle : String) :
    StructFields.lookup ((renameValueFields ρ fields.toList).toArray) needle
      = (StructFields.lookup fields needle).map (renameValue ρ) := by
  unfold StructFields.lookup
  dsimp only
  rw [renameValueFields_eq_map]
  rw [← Array.foldl_toList, ← Array.foldl_toList, List.toList_toArray]
  refine foldl_option_ren ?_ fields.toList none
  intro acc p
  obtain ⟨pn, pv⟩ := p
  cases acc with
  | some v => rfl
  | none =>
      by_cases hn : (pn == needle) = true
      · simp [hn]
      · simp [hn]

theorem structFieldsSet_sim (ρ : Nat → Nat)
    (fields : Array (String × GoValue)) (needle : String) (v : GoValue) :
    ExSim (fun out outF => outF = (renameValueFields ρ out.toList).toArray)
      (StructFields.set fields needle v)
      (StructFields.set ((renameValueFields ρ fields.toList).toArray) needle
        (renameValue ρ v)) := by
  unfold StructFields.set
  dsimp only
  refine ExSim.bind
    (R := fun (r r' : MProd Bool (Array (String × GoValue))) =>
      r'.fst = r.fst ∧ r'.snd = (renameValueFields ρ r.snd.toList).toArray)
    ?_ ?_
  · -- the loops
    rw [← Array.forIn_toList, ← Array.forIn_toList, List.toList_toArray,
      renameValueFields_eq_map]
    refine forIn_sim ⟨rfl, by simp [renameValueFields]⟩ ?_
    intro a _ x y hxy
    obtain ⟨an, av⟩ := a
    obtain ⟨hxy1, hxy2⟩ := hxy
    dsimp only
    by_cases hn : (an == needle) = true
    · rw [if_pos hn, if_pos hn]
      refine ExSim.ok ⟨rfl, ?_⟩
      simp [hxy2, renameValueFields_eq_map]
    · rw [if_neg hn, if_neg hn]
      refine ExSim.ok ⟨hxy1, ?_⟩
      simp [hxy2, renameValueFields_eq_map]
  · -- the post-loop check
    intro r r' hr
    obtain ⟨hr1, hr2⟩ := hr
    rw [hr1]
    by_cases hf : r.fst = true
    · rw [if_pos hf, if_pos hf]
      exact ExSim.ok hr2
    · rw [if_neg hf, if_neg hf]
      exact ExSim.stuck'

/-! ## Array element operations -/

theorem renamedArray_size (ρ : Nat → Nat) (values : Array GoValue) :
    ((renameValueList ρ values.toList).toArray).size = values.size := by
  simp [renameValueList_eq_map]

theorem renamedArray_getElem? (ρ : Nat → Nat) (values : Array GoValue) (n : Nat) :
    ((renameValueList ρ values.toList).toArray)[n]?
      = (values[n]?).map (renameValue ρ) := by
  simp [renameValueList_eq_map, ← Array.getElem?_toList]

theorem arrayIndexNat_ren (ρ : Nat → Nat) (values : Array GoValue) (i : Int) :
    arrayIndexNat ((renameValueList ρ values.toList).toArray) i
      = arrayIndexNat values i := by
  unfold arrayIndexNat
  rw [renamedArray_size]

theorem arrayGet_sim' (ρ : Nat → Nat) (values : Array GoValue) (i : Int) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (arrayGet values i)
      (arrayGet ((renameValueList ρ values.toList).toArray) i) := by
  unfold arrayGet
  rw [arrayIndexNat_ren]
  refine ExSim.bind (ExSim.refl _) ?_
  intro n n' hn
  subst hn
  rw [renamedArray_getElem?]
  cases values[n]? with
  | none =>
      simp only [Option.map_none]
      unfold indexOutOfRangePanic
      rw [renamedArray_size]
      split
      · exact ExSim.panic
      · exact ExSim.panic
  | some v => exact ExSim.ok rfl

theorem arraySet_sim' (ρ : Nat → Nat) (values : Array GoValue) (i : Int)
    (v : GoValue) :
    ExSim (fun out outF => outF = (renameValueList ρ out.toList).toArray)
      (arraySet values i v)
      (arraySet ((renameValueList ρ values.toList).toArray) i
        (renameValue ρ v)) := by
  unfold arraySet
  rw [arrayIndexNat_ren]
  refine ExSim.bind (ExSim.refl _) ?_
  intro n n' hn
  subst hn
  rw [renamedArray_getElem?]
  cases hv : values[n]? with
  | none =>
      simp only [Option.map_none]
      unfold indexOutOfRangePanic
      rw [renamedArray_size]
      split
      · exact ExSim.panic
      · exact ExSim.panic
  | some old =>
      simp only [Option.map_some]
      refine ExSim.bind (exSim_of_ren (coerceStoredValue_noPanic old v)
        (fun a ha => coerceStoredValue_ren ρ _ _ _ ha)) ?_
      intro a b hb
      subst hb
      refine ExSim.ok ?_
      rw [Array.set!, Array.set!]
      simp only [renameValueList_eq_map]
      rw [Array.toList_setIfInBounds]
      simp [List.map_set]

/-! ## `loadLoc` -/

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem loadLoc_sim (hS : FrameSim ρ na₀ na fr σ σF) :
    ∀ l : Loc, ExSim (fun v vF => vF = renameValue ρ v)
      (loadLoc σ l) (loadLoc σF (renameLoc ρ l)) := by
  intro l
  induction l with
  | base a =>
      rw [loadLoc, renameLoc]
      obtain ⟨i⟩ := a
      cases hl : Heap.lookup σ.heap (.base ⟨i⟩) with
      | none => exact ExSim.stuck'
      | some cell =>
          rw [loadLoc]
          have hf := hS.lookup_some (l := .base ⟨i⟩) hl
          rw [renameLoc] at hf
          rw [hf]
          exact ExSim.ok rfl
  | field b tid fname ihb =>
      rw [loadLoc, renameLoc, loadLoc]
      refine ExSim.bind ihb ?_
      intro v vF hvF
      subst hvF
      cases v
      case struct actual fields =>
          simp only [renameValue]
          -- the compat check reads only the types map (triage L7)
          rw [structTagCompatible_congr hS.types_eq]
          by_cases hne :
              (actual != tid && !structTagCompatible σ actual tid) = true
          · rw [if_pos hne]
            exact ExSim.stuck'
          · rw [if_neg hne, if_neg hne]
            rw [structFieldsLookup_ren]
            cases StructFields.lookup fields fname with
            | none => exact ExSim.stuck'
            | some fv => exact ExSim.ok rfl
      all_goals exact ExSim.stuck'
  | index b i ihb =>
      rw [loadLoc, renameLoc, loadLoc]
      refine ExSim.bind ihb ?_
      intro v vF hvF
      subst hvF
      cases v
      case array vs =>
          simp only [renameValue]
          exact arrayGet_sim' ρ vs i
      all_goals exact ExSim.stuck'


/-! ## `ExSim` wrappers for the pure walks -/

theorem defaultValue_sim {ρ : Nat → Nat} {σ σF : ExecState}
    (htypes : σF.types = σ.types) (ty : Ty) :
    ExSim (fun d dF => dF = renameValue ρ d)
      (defaultValue σ ty) (defaultValue σF ty) := by
  rw [defaultValue_congr htypes]
  cases hdv : defaultValue σ ty with
  | ok d => exact ExSim.ok (defaultValue_ren_id ρ hdv).symm
  | error e => cases e <;> first | exact ExSim.panic | trivial

theorem normalizeValueForTy_sim {ρ : Nat → Nat} {σ σF : ExecState}
    (htypes : σF.types = σ.types) (ty : Ty) (v : GoValue) :
    ExSim (fun r rF => rF = renameValue ρ r)
      (normalizeValueForTy σ ty v)
      (normalizeValueForTy σF ty (renameValue ρ v)) :=
  exSim_of_ren (normalizeValueForTy_noPanic σ ty v)
    (fun _ ha => normalizeValueForTy_ren ρ htypes ha)

theorem coerceStoredValue_sim (ρ : Nat → Nat) (old v : GoValue) :
    ExSim (fun r rF => rF = renameValue ρ r)
      (coerceStoredValue old v)
      (coerceStoredValue (renameValue ρ old) (renameValue ρ v)) :=
  exSim_of_ren (coerceStoredValue_noPanic old v)
    (fun _ ha => coerceStoredValue_ren ρ _ _ _ ha)

/-! ## `storeLoc` -/

section StateSim

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem storeLoc_sim (hS : FrameSim ρ na₀ na fr σ σF) :
    ∀ (l : Loc) (v : GoValue),
      ExSim (FrameSim ρ na₀ na fr)
        (storeLoc σ l v) (storeLoc σF (renameLoc ρ l) (renameValue ρ v)) := by
  intro l
  induction l generalizing σ σF hS with
  | base a =>
      intro v
      obtain ⟨i⟩ := a
      simp only [storeLoc, renameLoc]
      cases hl : Heap.lookup σ.heap (.base ⟨i⟩) with
      | some cell =>
          have hf := hS.lookup_some (l := .base ⟨i⟩) hl
          rw [renameLoc] at hf
          rw [hf]
          dsimp only
          rw [show (renameCell ρ cell).declaredTy = cell.declaredTy from rfl]
          cases hd : cell.declaredTy with
          | some ty =>
              dsimp only
              refine ExSim.bind (normalizeValueForTy_sim hS.types_eq ty v) ?_
              intro v' vF' hv'
              subst hv'
              exact ExSim.ok (hS.setBase i { declaredTy := some ty, value := v' })
          | none =>
              dsimp only
              refine ExSim.bind (coerceStoredValue_sim ρ cell.value v) ?_
              intro v' vF' hv'
              subst hv'
              exact ExSim.ok (hS.setBase i { declaredTy := none, value := v' })
      | none =>
          have hfn := hS.lookup_none_base (a := i) hl
          rw [hfn]
          dsimp only
          exact ExSim.ok (hS.setBase i { value := v })
  | field b tid fname ihb =>
      intro v
      simp only [storeLoc, renameLoc]
      refine ExSim.bind (loadLoc_sim hS b) ?_
      intro bv bvF hbv
      subst hbv
      cases bv
      case struct actual fields =>
        simp only [renameValue]
        rw [structTagCompatible_congr hS.types_eq]
        by_cases hne :
            (actual != tid && !structTagCompatible σ actual tid) = true
        · rw [if_pos hne]
          exact ExSim.stuck'
        · rw [if_neg hne, if_neg hne]
          simp only [pure_bind]
          refine ExSim.bind (structFieldsSet_sim ρ fields fname v) ?_
          intro upd updF hupdF
          subst hupdF
          exact ihb hS (.struct actual upd)
      all_goals exact ExSim.stuck'
  | index b i ihb =>
      intro v
      simp only [storeLoc, renameLoc]
      refine ExSim.bind (loadLoc_sim hS b) ?_
      intro bv bvF hbv
      subst hbv
      cases bv
      case array vs =>
        simp only [renameValue]
        refine ExSim.bind (arraySet_sim' ρ vs i v) ?_
        intro upd updF hupdF
        subst hupdF
        exact ihb hS (.array upd)
      all_goals exact ExSim.stuck'

/-! ## Cell readers -/

theorem mapEntries_sim (hS : FrameSim ρ na₀ na fr σ σF) (m : MapValue) :
    ExSim (fun o oF => oF = o.map (fun p =>
        (renameLoc ρ p.1, (renameValueEntries ρ p.2.toList).toArray)))
      (mapEntries σ m)
      (mapEntries σF { base := m.base.map (renameLoc ρ) }) := by
  simp only [mapEntries]
  cases m with
  | mk base =>
      cases base with
      | none => exact ExSim.ok rfl
      | some baseLoc =>
          simp only [Option.map_some]
          refine ExSim.bind (loadLoc_sim hS baseLoc) ?_
          intro v vF hvF
          subst hvF
          cases v
          case mapData es => exact ExSim.ok rfl
          all_goals exact ExSim.stuck'

theorem chanCell_sim (hS : FrameSim ρ na₀ na fr σ σF) (loc : Loc) :
    ExSim (fun c cF => cF = ((renameValueList ρ c.1.toList).toArray, c.2.1, c.2.2))
      (chanCell σ loc) (chanCell σF (renameLoc ρ loc)) := by
  simp only [chanCell]
  refine ExSim.bind (loadLoc_sim hS loc) ?_
  intro v vF hvF
  subst hvF
  cases v
  case chanData buf cap closed => exact ExSim.ok rfl
  all_goals exact ExSim.stuck'

theorem syncCell_sim (hS : FrameSim ρ na₀ na fr σ σF) (loc : Loc) :
    ExSim Eq (syncCell σ loc) (syncCell σF (renameLoc ρ loc)) := by
  simp only [syncCell]
  refine ExSim.bind (loadLoc_sim hS loc) ?_
  intro v vF hvF
  subst hvF
  cases v
  case syncData p => exact ExSim.ok rfl
  all_goals exact ExSim.stuck'

/-! ## Call-protocol list operations -/

theorem loadMany_sim (hS : FrameSim ρ na₀ na fr σ σF) :
    ∀ locs : List Loc,
      ExSim (fun vs vsF => vsF = renameValueList ρ vs)
        (loadMany σ locs) (loadMany σF (locs.map (renameLoc ρ))) := by
  intro locs
  induction locs with
  | nil => exact ExSim.ok rfl
  | cons l ls ih =>
      simp only [loadMany, List.map_cons]
      refine ExSim.bind (loadLoc_sim hS l) ?_
      intro v vF hvF
      subst hvF
      refine ExSim.bind ih ?_
      intro vs vsF hvsF
      subst hvsF
      exact ExSim.ok rfl

theorem storeMany_sim :
    ∀ (locs : List Loc) (vs : List GoValue) {σ σF : ExecState},
      FrameSim ρ na₀ na fr σ σF →
      ExSim (FrameSim ρ na₀ na fr)
        (storeMany σ locs vs)
        (storeMany σF (locs.map (renameLoc ρ)) (renameValueList ρ vs)) := by
  intro locs
  induction locs with
  | nil =>
      intro vs σ σF hS
      cases vs with
      | nil => exact ExSim.ok hS
      | cons v vs' => exact ExSim.stuck'
  | cons l ls ih =>
      intro vs σ σF hS
      cases vs with
      | nil => exact ExSim.stuck'
      | cons v vs' =>
          simp only [storeMany, List.map_cons, renameValueList]
          refine ExSim.bind (storeLoc_sim hS l v) ?_
          intro σ' σF' hS'
          exact ih vs' hS'

theorem pinResultLocs_ren (ρ : Nat → Nat) (env : LocalEnv) :
    ∀ (ps : List Param) {locs : List Loc},
      pinResultLocs env ps = .ok locs →
      pinResultLocs (renameEnv ρ env) ps = .ok (locs.map (renameLoc ρ)) := by
  intro ps
  induction ps with
  | nil =>
      intro locs h
      simp only [pinResultLocs, pure_eq_ok, Except.ok.injEq] at h
      subst h
      rfl
  | cons p rest ih =>
      intro locs h
      simp only [pinResultLocs] at h ⊢
      rw [localEnv_lookup_ren]
      cases hlk : LocalEnv.lookup env p.id with
      | none => rw [hlk] at h; simp at h
      | some loc =>
          rw [hlk] at h
          simp only [Option.map_some]
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
          obtain ⟨tail, htail, rfl⟩ := h
          simp only [bind_eq_ok, pure_eq_ok, Except.ok.injEq]
          exact ⟨_, ih htail, by simp⟩

theorem allocDecls_sim :
    ∀ (ps : List Param) (env : LocalEnv) {σ σF : ExecState},
      FrameSim ρ na₀ na fr σ σF →
      ExSim (fun (r : LocalEnv × ExecState) (rF : LocalEnv × ExecState) =>
          rF.1 = renameEnv ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
        (allocDecls env σ ps)
        (allocDecls (renameEnv ρ env) σF ps) := by
  intro ps
  induction ps with
  | nil =>
      intro env σ σF hS
      exact ExSim.ok ⟨rfl, hS⟩
  | cons p rest ih =>
      intro env σ σF hS
      simp only [allocDecls]
      refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq p.typ) ?_
      intro d dF hdF
      subst hdF
      have halloc : ExecState.alloc σF (renameValue ρ d) p.typ
          = (renameLoc ρ (ExecState.alloc σ d p.typ).1,
              (ExecState.alloc σF (renameValue ρ d) p.typ).2) := by
        rw [← hS.alloc_fst d p.typ]
      rw [halloc]
      rw [← localEnv_declare_ren]
      exact ih _ (hS.alloc_snd d p.typ)

theorem bindParams_sim :
    ∀ (ps : List Param) (vs : List GoValue) (env : LocalEnv) {σ σF : ExecState},
      FrameSim ρ na₀ na fr σ σF →
      ExSim (fun (r : LocalEnv × ExecState) (rF : LocalEnv × ExecState) =>
          rF.1 = renameEnv ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
        (bindParams env σ ps vs)
        (bindParams (renameEnv ρ env) σF ps (renameValueList ρ vs)) := by
  intro ps
  induction ps with
  | nil =>
      intro vs env σ σF hS
      cases vs with
      | nil => exact ExSim.ok ⟨rfl, hS⟩
      | cons v vs' => exact ExSim.stuck'
  | cons p rest ih =>
      intro vs env σ σF hS
      cases vs with
      | nil => exact ExSim.stuck'
      | cons v vs' =>
          simp only [bindParams, renameValueList]
          refine ExSim.bind (normalizeValueForTy_sim hS.types_eq p.typ v) ?_
          intro v' vF' hv'
          subst hv'
          have halloc : ExecState.alloc σF (renameValue ρ v') p.typ
              = (renameLoc ρ (ExecState.alloc σ v' p.typ).1,
                  (ExecState.alloc σF (renameValue ρ v') p.typ).2) := by
            rw [← hS.alloc_fst v' p.typ]
          rw [halloc]
          rw [← localEnv_declare_ren]
          exact ih vs' _ (hS.alloc_snd v' p.typ)

end StateSim


/-! ## Frame entry -/

theorem renamedArray_set! (ρ : Nat → Nat) (values : Array GoValue) (n : Nat)
    (v : GoValue) :
    ((renameValueList ρ values.toList).toArray).set! n (renameValue ρ v)
      = (renameValueList ρ ((values.set! n v)).toList).toArray := by
  rw [Array.set!, Array.set!]
  simp only [renameValueList_eq_map]
  rw [Array.toList_setIfInBounds]
  simp [List.map_set]

theorem pinResultLocs_noPanic : ∀ (ps : List Param) (env : LocalEnv),
    NoPanic (pinResultLocs env ps) := by
  intro ps
  induction ps with
  | nil => intro env; exact NoPanic.pure'
  | cons p rest ih =>
      intro env
      simp only [pinResultLocs]
      cases LocalEnv.lookup env p.id with
      | none => exact NoPanic.stuck'
      | some loc =>
          exact NoPanic.bind (ih env) fun _ => NoPanic.pure'

section FrameEntry

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem pinResultLocs_sim (env : LocalEnv) (ps : List Param) :
    ExSim (fun ls lsF => lsF = ls.map (renameLoc ρ))
      (pinResultLocs env ps) (pinResultLocs (renameEnv ρ env) ps) :=
  exSim_of_ren (pinResultLocs_noPanic ps env)
    (fun _ ha => pinResultLocs_ren ρ env ps ha)

theorem dynamicDispatch?_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (func : Func) (args : Array GoValue) :
    ExSim (fun o oF => oF = o.map (fun p =>
        (p.1, (renameValueList ρ p.2.toList).toArray)))
      (dynamicDispatch? σ func args)
      (dynamicDispatch? σF func ((renameValueList ρ args.toList).toArray)) := by
  simp only [dynamicDispatch?, methodInfoByFuncId?_congr hS.methods_eq,
    methodRecvInterfaceName?_congr hS.types_eq,
    concreteMethodForDynamic?_congr hS.types_eq hS.methods_eq,
    dynamicMethodSetRecorded_congr hS.types_eq hS.methodSets_eq,
    goTypeNameForMessage_congr hS.types_eq, hS.funcs_eq,
    renamedArray_getElem?]
  cases methodInfoByFuncId? σ func.id with
  | none => exact ExSim.ok rfl
  | some method =>
      dsimp only
      cases methodRecvInterfaceName? σ method with
      | none => exact ExSim.ok rfl
      | some iname =>
          dsimp only
          cases h0 : args[0]? with
          | none => exact ExSim.ok rfl
          | some v =>
              simp only [Option.map_some]
              cases v
              case interface dynTy inner =>
                simp only [renameValue]
                cases concreteMethodForDynamic? σ dynTy method.name with
                | some hit =>
                    obtain ⟨concrete, needsDeref⟩ := hit
                    dsimp only
                    cases findFunctionIn? σ.functions concrete.funcId with
                    | none => exact ExSim.stuck'
                    | some targetFunc =>
                        simp only [pure_bind]
                        cases needsDeref with
                        | true =>
                            simp only [if_true]
                            cases inner
                            case addr loc =>
                              simp only [renameValue]
                              refine ExSim.bind (loadLoc_sim hS loc) ?_
                              intro rv rvF hrvF
                              subst hrvF
                              refine ExSim.ok ?_
                              simp [renamedArray_set!, renameValueList_eq_map,
                                List.map_set]
                            case nil => exact ExSim.panic
                            all_goals exact ExSim.stuck'
                        | false =>
                            simp only [Bool.false_eq_true, if_false]
                            refine ExSim.ok ?_
                            simp [renamedArray_set!, renameValueList_eq_map,
                              List.map_set]
                | none =>
                    refine ExSim.skip ?_
                    intro m hm
                    split at hm <;> cases hm
              case nil => exact ExSim.panic
              all_goals exact ExSim.ok rfl

theorem findFunctionIn?_mem {funcs : Array Func} {fid : FuncId} {f : Func}
    (h : findFunctionIn? funcs fid = some f) : f ∈ funcs.toList := by
  unfold findFunctionIn? at h
  rw [← Array.foldl_toList] at h
  have hgen : ∀ (l : List Func) (acc : Option Func),
      List.foldl
        (fun found func =>
          match found with
          | some f => some f
          | none => if func.id == fid then some func else none)
        acc l = some f →
      acc = some f ∨ f ∈ l := by
    intro l
    induction l with
    | nil => intro acc hacc; exact Or.inl hacc
    | cons g gs ih =>
        intro acc hacc
        cases acc with
        | some f' =>
            cases ih _ hacc with
            | inl h' => exact Or.inl h'
            | inr h' => exact Or.inr (List.mem_cons_of_mem _ h')
        | none =>
            by_cases hg : (g.id == fid) = true
            · rw [List.foldl_cons] at hacc
              simp only [hg, if_true] at hacc
              cases ih _ hacc with
              | inl h' =>
                  simp only [Option.some.injEq] at h'
                  subst h'
                  exact Or.inr List.mem_cons_self
              | inr h' => exact Or.inr (List.mem_cons_of_mem _ h')
            · rw [List.foldl_cons] at hacc
              simp only [hg, if_false] at hacc
              cases ih _ hacc with
              | inl h' => cases h'
              | inr h' => exact Or.inr (List.mem_cons_of_mem _ h')
  cases hgen _ _ h with
  | inl h' => cases h'
  | inr h' => exact h'

/-- `dynamicDispatch?_sim` plus body-invariance of any dispatch target
(the target is drawn from the FUNCTION TABLE, whose bodies are
`ρ`-invariant by `bodies_inv`). -/
theorem dynamicDispatch?_sim' (hS : FrameSim ρ na₀ na fr σ σF)
    (func : Func) (args : Array GoValue) :
    ExSim (fun o oF => (oF = o.map (fun p =>
        (p.1, (renameValueList ρ p.2.toList).toArray)))
        ∧ ∀ tf ta, o = some (tf, ta) → renameStmt ρ tf.body = tf.body)
      (dynamicDispatch? σ func args)
      (dynamicDispatch? σF func ((renameValueList ρ args.toList).toArray)) := by
  have hbase := dynamicDispatch?_sim hS func args
  cases hd : dynamicDispatch? σ func args with
  | error e =>
      rw [hd] at hbase
      cases e
      case panic m =>
        rw [hbase.panic_inv rfl]
        exact ExSim.panic
      all_goals exact ExSim.skip fun m h => GoError.noConfusion h
  | ok o =>
      obtain ⟨oF, hoF, hrel⟩ := hbase.ok_inv hd
      rw [hoF]
      refine ExSim.ok ⟨hrel, ?_⟩
      intro tf ta hsome
      subst hsome
      -- the dispatch target came from findFunctionIn? on the table
      revert hd
      simp only [dynamicDispatch?]
      cases methodInfoByFuncId? σ func.id with
      | none => intro hd; simp [pure, Except.pure] at hd
      | some method =>
          dsimp only
          cases methodRecvInterfaceName? σ method with
          | none => intro hd; simp [pure, Except.pure] at hd
          | some iname =>
              dsimp only
              cases args[0]? with
              | none => intro hd; simp [pure, Except.pure] at hd
              | some v =>
                  cases v <;> intro hd <;>
                    first
                    | (simp [pure, Except.pure] at hd; done)
                    | skip
                  case interface dynTy inner =>
                    dsimp only at hd
                    cases hcm : concreteMethodForDynamic? σ dynTy method.name with
                    | none =>
                        rw [hcm] at hd
                        simp only [throw, throwThe, MonadExceptOf.throw] at hd
                        simp at hd
                    | some hit =>
                        obtain ⟨concrete, needsDeref⟩ := hit
                        rw [hcm] at hd
                        dsimp only at hd
                        cases hfind2 : findFunctionIn? σ.functions concrete.funcId with
                        | none =>
                            rw [hfind2] at hd
                            simp only [stuck_eq, Bind.bind, Except.bind] at hd
                            simp at hd
                        | some targetFunc =>
                            rw [hfind2] at hd
                            simp only [pure_bind] at hd
                            have htf : tf = targetFunc := by
                              cases needsDeref with
                              | true =>
                                  rw [if_pos rfl] at hd
                                  cases inner with
                                  | addr loc =>
                                      rw [bind_eq_ok] at hd
                                      obtain ⟨rv, hrv, hd2⟩ := hd
                                      simp only [pure, Except.pure,
                                        Except.ok.injEq, Option.some.injEq,
                                        Prod.mk.injEq] at hd2
                                      exact hd2.1.symm
                                  | nil =>
                                      simp [Bind.bind, Except.bind, throw,
                                        throwThe, MonadExceptOf.throw] at hd
                                  | _ =>
                                      simp [Bind.bind, Except.bind] at hd
                              | false =>
                                  rw [if_neg (by simp)] at hd
                                  simp only [pure, Except.pure,
                                    Except.ok.injEq, Option.some.injEq,
                                    Prod.mk.injEq] at hd
                                  exact hd.1.symm
                            rw [htf]
                            exact hS.bodies_inv targetFunc
                              (findFunctionIn?_mem hfind2)

theorem enterFrame_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (fid : FuncId) (args : List GoValue) :
    ExSim (fun (r rF : Func × LocalEnv × List Loc × ExecState) =>
        rF.1 = r.1 ∧ rF.2.1 = renameEnv ρ r.2.1
          ∧ rF.2.2.1 = r.2.2.1.map (renameLoc ρ)
          ∧ FrameSim ρ na₀ na fr r.2.2.2 rF.2.2.2
          ∧ renameStmt ρ r.1.body = r.1.body)
      (enterFrame σ fid args)
      (enterFrame σF fid (renameValueList ρ args)) := by
  simp only [enterFrame]
  rw [hS.funcs_eq]
  cases hfind : findFunctionIn? σ.functions fid with
  | none => exact ExSim.stuck'
  | some func =>
      simp only [pure_bind]
      rw [renameValueList_length]
      by_cases har : (func.args.size != args.length) = true
      · rw [if_pos har]
        exact ExSim.stuck'
      · simp only [if_neg har]
        have hddargs : (renameValueList ρ args).toArray
            = (renameValueList ρ (args.toArray).toList).toArray := by
          rw [List.toList_toArray]
        rw [hddargs]
        refine ExSim.bind (dynamicDispatch?_sim' hS func args.toArray) ?_
        intro o oF hoF
        obtain ⟨hoF, hbodies⟩ := hoF
        subst hoF
        cases o with
        | none =>
            have hnil : (renameEnv ρ [] : LocalEnv) = [] := rfl
            rw [← hnil]
            refine ExSim.bind (bindParams_sim func.args.toList args [] hS) ?_
            intro r1 r1F hr1
            obtain ⟨env1, σ1⟩ := r1
            obtain ⟨env1F, σ1F⟩ := r1F
            obtain ⟨henv1, hS1⟩ := hr1
            dsimp only at henv1 hS1 ⊢
            subst henv1
            refine ExSim.bind (allocDecls_sim func.results.toList env1 hS1) ?_
            intro r2 r2F hr2
            obtain ⟨env2, σ2⟩ := r2
            obtain ⟨env2F, σ2F⟩ := r2F
            obtain ⟨henv2, hS2⟩ := hr2
            dsimp only at henv2 hS2 ⊢
            subst henv2
            refine ExSim.bind (pinResultLocs_sim env2 func.results.toList) ?_
            intro ls lsF hls
            subst hls
            exact ExSim.ok ⟨rfl, rfl, rfl, hS2,
              hS.bodies_inv func (findFunctionIn?_mem hfind)⟩
        | some hit =>
            obtain ⟨tf, ta⟩ := hit
            dsimp only [Option.map_some]
            simp only [List.toList_toArray, renameValueList_length]
            by_cases har2 : (tf.args.size != ta.toList.length) = true
            · rw [if_pos har2]
              exact ExSim.stuck'
            · simp only [if_neg har2]
              have hnil : (renameEnv ρ [] : LocalEnv) = [] := rfl
              rw [← hnil]
              refine ExSim.bind (bindParams_sim tf.args.toList ta.toList [] hS) ?_
              intro r1 r1F hr1
              obtain ⟨env1, σ1⟩ := r1
              obtain ⟨env1F, σ1F⟩ := r1F
              obtain ⟨henv1, hS1⟩ := hr1
              dsimp only at henv1 hS1 ⊢
              subst henv1
              refine ExSim.bind (allocDecls_sim tf.results.toList env1 hS1) ?_
              intro r2 r2F hr2
              obtain ⟨env2, σ2⟩ := r2
              obtain ⟨env2F, σ2F⟩ := r2F
              obtain ⟨henv2, hS2⟩ := hr2
              dsimp only at henv2 hS2 ⊢
              subst henv2
              refine ExSim.bind (pinResultLocs_sim env2 tf.results.toList) ?_
              intro ls lsF hls
              subst hls
              exact ExSim.ok ⟨rfl, rfl, rfl, hS2, hbodies tf ta rfl⟩

end FrameEntry

end GoLean.Frame
