import GoLeanProofs.Frame.MachineRel

/-!
# The executable frame theorem: abort rendering, map-range machinery,
and the frame-entry step wrappers

* `renderPanicPayload`/`renderPanicHead` answer identically across the
  pair: every renderABLE payload shape is loc-free, the method-set
  consultations are table congruences, and the recovered-collapse check
  is structural equality (renaming-invariant by injectivity).
* The map-range snapshot/iteration helpers commute (the snapshot
  validation is `isNormalForTy`, renaming-invariant).
* `enterFrameStep`/`enterFrameDeferPanicking` lift `enterFrame_sim` to
  the configuration level, parameterized by the continuation builders.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

/-- The `stepFn` result relation: renamed configuration, related
states, IDENTICAL choice stream. -/
abbrev TripSim (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    Config × ExecState × Choices → Config × ExecState × Choices → Prop :=
  fun r rF => rF.1 = renameConfig ρ r.1
    ∧ FrameSim ρ na₀ na fr r.2.1 rF.2.1 ∧ rF.2.2 = r.2.2

section Tables

variable {σ σF : ExecState}

theorem hasNoArgStringMethod_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods)
    (hfuncs : σF.functions = σ.functions)
    (dynTy : Ty) (name : String) :
    hasNoArgStringMethod σF dynTy name = hasNoArgStringMethod σ dynTy name := by
  simp only [hasNoArgStringMethod,
    concreteMethodForDynamic?_congr htypes hmethods]
  cases concreteMethodForDynamic? σ dynTy name with
  | none => rfl
  | some hit =>
      simp only [concreteMethodSignature?_congr htypes hfuncs]

theorem panicPayloadIsRewritten_congr (htypes : σF.types = σ.types)
    (hmethods : σF.methods = σ.methods)
    (hfuncs : σF.functions = σ.functions) (dynTy : Ty) :
    panicPayloadIsRewritten σF dynTy = panicPayloadIsRewritten σ dynTy := by
  simp only [panicPayloadIsRewritten,
    hasNoArgStringMethod_congr htypes hmethods hfuncs]

end Tables

section Render

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem renderPanicPayload_ren (hS : FrameSim ρ na₀ na fr σ σF) :
    ∀ v : GoValue,
      renderPanicPayload σF (renameValue ρ v) = renderPanicPayload σ v := by
  intro v
  cases v
  case nil => rfl
  case interface t inner =>
      cases t <;> cases inner <;>
        simp [renameValue, renderPanicPayload,
          dynamicMethodSetRecorded_congr hS.types_eq hS.methodSets_eq,
          panicPayloadIsRewritten_congr hS.types_eq hS.methods_eq hS.funcs_eq]
  all_goals simp [renameValue, renderPanicPayload]

theorem renderPanicHead_ren (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (first : PanicEntry) (rest : List PanicEntry) :
    renderPanicHead σF (renameEntry ρ first) (renameChain ρ rest)
      = renderPanicHead σ first rest := by
  simp only [renderPanicHead, renameEntry, renderPanicPayload_ren hS]
  cases renderPanicPayload σ first.value with
  | none => rfl
  | some base =>
      simp only [Option.bind_some]
      cases hrec : first.recovered with
      | false => rfl
      | true =>
          simp only [if_pos rfl]
          cases rest with
          | nil => rfl
          | cons e es =>
              simp only [renameChain, List.map_cons]
              show (if (renameValue ρ e.value == renameValue ρ first.value) = true
                  then _ else _) = _
              rw [renameValue_eqb (hinj := hinj)]
              rfl

end Render

/-! ## Map-range machinery -/

section MapRange

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem map_fst_renameValueEntries (ρ : Nat → Nat) :
    ∀ l : List (GoValue × GoValue),
      (renameValueEntries ρ l).map (·.1) = renameValueList ρ (l.map (·.1)) := by
  intro l
  induction l with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      simp [renameValueEntries, renameValueList, ih]

/-- Range start renames pointwise (BUG-005 (L): base loc + start-key
set, replacing the retired snapshot sim). -/
theorem mapRangeStartSets_sim (hS : FrameSim ρ na₀ na fr σ σF) (v : GoValue) :
    ExSim (fun (bs bsF : Option Loc × Array GoValue) =>
        bsF.1 = bs.1.map (renameLoc ρ)
          ∧ bsF.2 = (renameValueList ρ bs.2.toList).toArray)
      (mapRangeStartSets σ v) (mapRangeStartSets σF (renameValue ρ v)) := by
  simp only [mapRangeStartSets]
  refine ExSim.bind (R := fun m mF =>
      mF = { base := m.base.map (renameLoc ρ) }) ?_ ?_
  · cases v
    case map m => exact ExSim.ok rfl
    all_goals exact ExSim.stuck'
  · intro m mF hmF
    subst hmF
    obtain ⟨base⟩ := m
    cases base with
    | none =>
        refine ExSim.ok ⟨rfl, ?_⟩
        simp [renameValueList]
    | some baseLoc =>
        simp only [Option.map_some]
        refine ExSim.bind (loadLoc_sim hS baseLoc) ?_
        intro w wF hwF
        subst hwF
        cases w
        case mapData es =>
            refine ExSim.ok ⟨rfl, ?_⟩
            simp only [renameValue, List.map_toArray, Array.toList_map,
              map_fst_renameValueEntries]
        all_goals exact ExSim.stuck'

/-- The live-cell load renames pointwise. -/
theorem mapIterLiveEntries_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (base : Option Loc) :
    ExSim (fun es esF => esF = (renameValueEntries ρ es.toList).toArray)
      (mapIterLiveEntries σ base)
      (mapIterLiveEntries σF (base.map (renameLoc ρ))) := by
  cases base with
  | none =>
      simp only [mapIterLiveEntries, Option.map_none]
      refine ExSim.ok ?_
      simp [renameValueEntries]
  | some l =>
      simp only [mapIterLiveEntries, Option.map_some]
      refine ExSim.bind (loadLoc_sim hS l) ?_
      intro w wF hwF
      subst hwF
      cases w
      case mapData es => exact ExSim.ok rfl
      all_goals exact ExSim.stuck'

theorem snapshotEntriesSelfNormalizedList_ren (ρ : Nat → Nat)
    (types : TypeEnv) (kt vt : Ty) :
    ∀ es : List (GoValue × GoValue),
      snapshotEntriesSelfNormalizedList types kt vt (renameValueEntries ρ es)
        = snapshotEntriesSelfNormalizedList types kt vt es := by
  intro es
  induction es with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨ek, ev⟩ := e
      simp [renameValueEntries, snapshotEntriesSelfNormalizedList,
        isNormalForTy_ren, ih]

/-- Key membership is renaming-invariant (Go map-key equality renames —
`valueEq_sim`). -/
theorem keyInKeyList_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (kt : Ty) (key : GoValue) :
    ∀ keys : List GoValue,
      ExSim Eq (keyInKeyList σ kt key keys)
        (keyInKeyList σF kt (renameValue ρ key) (renameValueList ρ keys)) := by
  intro keys
  induction keys with
  | nil => exact ExSim.ok rfl
  | cons p rest ih =>
      simp only [keyInKeyList, renameValueList]
      refine ExSim.bind (valueEq_sim hinj htypes kt p key) ?_
      intro b bF hb
      subst hb
      cases b
      · simpa using ih
      · exact ExSim.ok rfl

@[inherit_doc keyInKeyList_sim]
theorem keyInKeys_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (kt : Ty)
    (keys : Array GoValue) (key : GoValue) :
    ExSim Eq (keyInKeys σ kt keys key)
      (keyInKeys σF kt ((renameValueList ρ keys.toList).toArray)
        (renameValue ρ key)) := by
  simp only [keyInKeys, List.toList_toArray]
  exact keyInKeyList_sim hinj htypes kt key keys.toList

/-- The candidate filter renames pointwise. -/
theorem filterCandidateList_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (kt : Ty) (produced : Array GoValue) :
    ∀ es : List (GoValue × GoValue),
      ExSim (fun out outF => outF = renameValueEntries ρ out)
        (filterCandidateList σ kt produced es)
        (filterCandidateList σF kt
          ((renameValueList ρ produced.toList).toArray)
          (renameValueEntries ρ es)) := by
  intro es
  induction es with
  | nil => exact ExSim.ok rfl
  | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      simp only [filterCandidateList, renameValueEntries]
      refine ExSim.bind (keyInKeys_sim hinj htypes kt produced k) ?_
      intro b bF hb
      subst hb
      refine ExSim.bind ih ?_
      intro tail tailF htail
      subst htail
      cases b
      · exact ExSim.ok rfl
      · exact ExSim.ok rfl

/-- Pick-time candidates rename pointwise. -/
theorem mapIterCandidates_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (hS : FrameSim ρ na₀ na fr σ σF) (kt vt : Ty)
    (base : Option Loc) (produced : Array GoValue) :
    ExSim (fun es esF => esF = (renameValueEntries ρ es.toList).toArray)
      (mapIterCandidates σ kt vt base produced)
      (mapIterCandidates σF kt vt (base.map (renameLoc ρ))
        ((renameValueList ρ produced.toList).toArray)) := by
  simp only [mapIterCandidates]
  refine ExSim.bind (mapIterLiveEntries_sim hS base) ?_
  intro es esF hesF
  subst hesF
  refine ExSim.bind (R := fun out outF => outF = renameValueEntries ρ out)
    ?_ ?_
  · simpa [List.toList_toArray]
      using filterCandidateList_sim hinj hS.types_eq kt produced es.toList
  · intro out outF hout
    subst hout
    rw [show snapshotEntriesSelfNormalized σF.types kt vt
          (renameValueEntries ρ out).toArray
        = snapshotEntriesSelfNormalized σ.types kt vt out.toArray by
      simp only [snapshotEntriesSelfNormalized, hS.types_eq,
        List.toList_toArray, snapshotEntriesSelfNormalizedList_ren]]
    split
    · exact ExSim.ok rfl
    · exact ExSim.stuck'

/-- Mandatory-remains is renaming-invariant. -/
theorem mandatoryInList_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (kt : Ty) (start : Array GoValue) :
    ∀ cands : List (GoValue × GoValue),
      ExSim Eq (mandatoryInList σ kt start cands)
        (mandatoryInList σF kt ((renameValueList ρ start.toList).toArray)
          (renameValueEntries ρ cands)) := by
  intro cands
  induction cands with
  | nil => exact ExSim.ok rfl
  | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      simp only [mandatoryInList, renameValueEntries]
      refine ExSim.bind (keyInKeys_sim hinj htypes kt start k) ?_
      intro b bF hb
      subst hb
      cases b
      · simpa using ih
      · exact ExSim.ok rfl

@[inherit_doc mandatoryInList_sim]
theorem mapIterMandatoryRemains_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (kt : Ty)
    (cands : Array (GoValue × GoValue)) (start : Array GoValue) :
    ExSim Eq (mapIterMandatoryRemains σ kt cands start)
      (mapIterMandatoryRemains σF kt
        ((renameValueEntries ρ cands.toList).toArray)
        ((renameValueList ρ start.toList).toArray)) := by
  simp only [mapIterMandatoryRemains, List.toList_toArray]
  exact mandatoryInList_sim hinj htypes kt start cands.toList

/-- The delete-prune's set subtraction renames pointwise. -/
theorem removeKeyList_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (kt : Ty) (key : GoValue) :
    ∀ ks : List GoValue,
      ExSim (fun out outF => outF = renameValueList ρ out)
        (removeKeyList σ kt key ks)
        (removeKeyList σF kt (renameValue ρ key) (renameValueList ρ ks)) := by
  intro ks
  induction ks with
  | nil => exact ExSim.ok rfl
  | cons p rest ih =>
      simp only [removeKeyList, renameValueList]
      refine ExSim.bind ih ?_
      intro tail tailF htail
      subst htail
      refine ExSim.bind (valueEq_sim hinj htypes kt p key) ?_
      intro b bF hb
      subst hb
      cases b
      · exact ExSim.ok rfl
      · exact ExSim.ok rfl

/-- The per-key delete-prune commutes with renaming (BUG-005 (L)): the
frame-base test transfers by `renameLoc` injectivity, the set
subtraction by `valueEq_sim`. -/
theorem pruneIterFramesKey_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (htypes : σF.types = σ.types) (l : Loc) (key : GoValue) :
    ∀ k : Cont,
      ExSim (fun k1 k1F => k1F = renameCont ρ k1)
        (pruneIterFramesKey σ l key k)
        (pruneIterFramesKey σF (renameLoc ρ l) (renameValue ρ key)
          (renameCont ρ k)) := by
  intro k
  induction k <;> simp only [pruneIterFramesKey, renameCont]
  case stop => exact ExSim.ok rfl
  case mapIterK kv vv kt vt body base produced start env k ih =>
    refine ExSim.bind ih ?_
    intro k1 k1F hk1
    subst hk1
    have hbeq : (base.map (renameLoc ρ) == some (renameLoc ρ l))
        = (base == some l) := by
      simpa using renameOptLoc_beq hinj base (some l)
    rw [hbeq]
    split
    · refine ExSim.bind
        (by simpa [List.toList_toArray]
          using removeKeyList_sim hinj htypes kt key produced.toList) ?_
      intro p1 p1F hp1
      subst hp1
      refine ExSim.bind
        (by simpa [List.toList_toArray]
          using removeKeyList_sim hinj htypes kt key start.toList) ?_
      intro s1 s1F hs1
      subst hs1
      exact ExSim.ok (by simp only [renameCont])
    · exact ExSim.ok (by simp only [renameCont])
  all_goals
    (rename_i ih
     refine ExSim.bind ih ?_
     intro k1 k1F hk1
     subst hk1
     exact ExSim.ok (by simp only [renameCont]))

/-- `clear`'s prune commutes with renaming (pure). -/
theorem pruneIterFramesAll_ren
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (l : Loc) :
    ∀ k : Cont,
      pruneIterFramesAll (renameLoc ρ l) (renameCont ρ k)
        = renameCont ρ (pruneIterFramesAll l k) := by
  intro k
  induction k <;> simp only [pruneIterFramesAll, renameCont]
  case mapIterK kv vv kt vt body base produced start env k ih =>
    have hbeq : (base.map (renameLoc ρ) == some (renameLoc ρ l))
        = (base == some l) := by
      simpa using renameOptLoc_beq hinj base (some l)
    rw [hbeq]
    split <;> simp only [renameCont, ih] <;>
      simp [renameValueList]
  all_goals
    (try rename_i ih
     try rw [ih])

/-- `contAfterStmtOp` commutes with renaming: the two pruning ops
transfer through `valueAsMap`/`normalizeValueForTy`/the prune sims;
every other op is the identity on both sides. -/
theorem contAfterStmtOp_sim
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (hS : FrameSim ρ na₀ na fr σ σF)
    (op : StmtOp) (vs : List GoValue) (k : Cont) :
    ExSim (fun k1 k1F => k1F = renameCont ρ k1)
      (contAfterStmtOp σ op vs k)
      (contAfterStmtOp σF op (renameValueList ρ vs) (renameCont ρ k)) := by
  cases op <;> simp only [contAfterStmtOp] <;> try exact ExSim.ok rfl
  case mapDelete kt =>
    match vs with
    | [] => exact ExSim.ok rfl
    | [_] => exact ExSim.ok rfl
    | (_ :: _ :: _ :: _) => exact ExSim.ok rfl
    | [baseV, keyV] =>
        simp only [renameValueList]
        refine ExSim.bind (R := fun m mF =>
            mF = { base := m.base.map (renameLoc ρ) }) ?_ ?_
        · cases baseV
          case map m => exact ExSim.ok rfl
          all_goals exact ExSim.stuck'
        · intro m mF hm
          subst hm
          obtain ⟨base⟩ := m
          cases base with
          | none => exact ExSim.ok rfl
          | some l =>
              simp only [Option.map_some]
              refine ExSim.bind (normalizeValueForTy_sim hS.types_eq kt keyV) ?_
              intro nk nkF hnk
              subst hnk
              exact pruneIterFramesKey_sim hinj hS.types_eq l nk k
  case clearMap =>
    match vs with
    | [] => exact ExSim.ok rfl
    | (_ :: _ :: _) => exact ExSim.ok rfl
    | [baseV] =>
        simp only [renameValueList]
        refine ExSim.bind (R := fun m mF =>
            mF = { base := m.base.map (renameLoc ρ) }) ?_ ?_
        · cases baseV
          case map m => exact ExSim.ok rfl
          all_goals exact ExSim.stuck'
        · intro m mF hm
          subst hm
          obtain ⟨base⟩ := m
          cases base with
          | none => exact ExSim.ok rfl
          | some l =>
              simp only [Option.map_some]
              exact ExSim.ok (pruneIterFramesAll_ren hinj l k)

theorem bindIterVars_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (env : LocalEnv) (keyVar valVar : Option String) (kt vt : Ty)
    (key value : GoValue) :
    ExSim (fun (r rF : LocalEnv × ExecState) =>
        rF.1 = renameEnv ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
      (bindIterVars env σ keyVar valVar kt vt key value)
      (bindIterVars (renameEnv ρ env) σF keyVar valVar kt vt
        (renameValue ρ key) (renameValue ρ value)) := by
  have hval : ∀ (env1 : LocalEnv) {σ1 σ1F : ExecState},
      FrameSim ρ na₀ na fr σ1 σ1F →
      ExSim (fun (r rF : LocalEnv × ExecState) =>
          rF.1 = renameEnv ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
        (match valVar with
          | some name => do
            let vv ← normalizeValueForTy σ1 vt value
            pure (env1.declare name (σ1.alloc vv (some vt)).fst,
              (σ1.alloc vv (some vt)).snd)
          | none => pure (env1, σ1))
        (match valVar with
          | some name => do
            let vv ← normalizeValueForTy σ1F vt (renameValue ρ value)
            pure ((renameEnv ρ env1).declare name
                (σ1F.alloc vv (some vt)).fst,
              (σ1F.alloc vv (some vt)).snd)
          | none => pure (renameEnv ρ env1, σ1F)) := by
    intro env1 σ1 σ1F hS1
    cases valVar with
    | none => exact ExSim.ok ⟨rfl, hS1⟩
    | some vn =>
        refine ExSim.bind (normalizeValueForTy_sim hS1.types_eq vt value) ?_
        intro vv vvF hvvF
        subst hvvF
        have halloc : ExecState.alloc σ1F (renameValue ρ vv) (some vt)
            = (renameLoc ρ (ExecState.alloc σ1 vv (some vt)).1,
                (ExecState.alloc σ1F (renameValue ρ vv) (some vt)).2) := by
          rw [← hS1.alloc_fst vv (some vt)]
        rw [halloc]
        rw [← localEnv_declare_ren]
        exact ExSim.ok ⟨rfl, hS1.alloc_snd vv (some vt)⟩
  simp only [bindIterVars]
  cases keyVar with
  | none =>
      simp only [pure_bind]
      exact hval env hS
  | some kn =>
      refine ExSim.bind (normalizeValueForTy_sim hS.types_eq kt key) ?_
      intro kv kvF hkvF
      subst hkvF
      have halloc : ExecState.alloc σF (renameValue ρ kv) (some kt)
          = (renameLoc ρ (ExecState.alloc σ kv (some kt)).1,
              (ExecState.alloc σF (renameValue ρ kv) (some kt)).2) := by
        rw [← hS.alloc_fst kv (some kt)]
      rw [halloc]
      simp only [pure_bind]
      rw [← localEnv_declare_ren]
      exact hval _ (hS.alloc_snd kv (some kt))

end MapRange

/-! ## Frame-entry step wrappers -/

section FrameStep

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem enterFrameStep_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (fid : FuncId) (args : List GoValue)
    (mk mkF : Func → LocalEnv → List Loc → Config) (k : Cont) (ch : Choices)
    (hmk : ∀ f e ls, renameStmt ρ f.body = f.body →
        mkF f (renameEnv ρ e) (ls.map (renameLoc ρ))
          = renameConfig ρ (mk f e ls)) :
    ExSim (TripSim ρ na₀ na fr)
      (enterFrameStep σ fid args mk k ch)
      (enterFrameStep σF fid (renameValueList ρ args) mkF
        (renameCont ρ k) ch) := by
  simp only [enterFrameStep]
  cases henter : enterFrame σ fid args with
  | ok r =>
      obtain ⟨f, e, ls, σ'⟩ := r
      obtain ⟨rF, hrF, hrel⟩ := (enterFrame_sim hS fid args).ok_inv henter
      obtain ⟨fF, eF, lsF, σF'⟩ := rF
      obtain ⟨hf, he, hls, hS', hbody⟩ := hrel
      dsimp only at hf he hls hS' hbody
      subst hf he hls
      rw [hrF]
      exact ExSim.ok ⟨hmk _ _ _ hbody, hS', rfl⟩
  | error err =>
      cases err
      case panic m =>
          rw [(enterFrame_sim hS fid args).panic_inv henter]
          refine ExSim.ok ⟨?_, hS, rfl⟩
          simp [renameConfig, renameChain, renameEntry, runtimeErrorValue_ren]
      all_goals exact ExSim.skip fun m h => GoError.noConfusion h

theorem enterFrameDeferPanicking_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (fid : FuncId) (args : List GoValue)
    (mk mkF : Func → LocalEnv → Config) (chain : List PanicEntry)
    (krest : Cont) (ch : Choices)
    (hmk : ∀ f e, renameStmt ρ f.body = f.body →
        mkF f (renameEnv ρ e) = renameConfig ρ (mk f e)) :
    ExSim (TripSim ρ na₀ na fr)
      (enterFrameDeferPanicking σ fid args mk chain krest ch)
      (enterFrameDeferPanicking σF fid (renameValueList ρ args) mkF
        (renameChain ρ chain) (renameCont ρ krest) ch) := by
  simp only [enterFrameDeferPanicking]
  cases henter : enterFrame σ fid args with
  | ok r =>
      obtain ⟨f, e, ls, σ'⟩ := r
      obtain ⟨rF, hrF, hrel⟩ := (enterFrame_sim hS fid args).ok_inv henter
      obtain ⟨fF, eF, lsF, σF'⟩ := rF
      obtain ⟨hf, he, hls, hS', hbody⟩ := hrel
      dsimp only at hf he hls hS' hbody
      subst hf he hls
      rw [hrF]
      exact ExSim.ok ⟨by rw [hmk _ _ hbody], hS', rfl⟩
  | error err =>
      cases err
      case panic m =>
          rw [(enterFrame_sim hS fid args).panic_inv henter]
          refine ExSim.ok ⟨?_, hS, rfl⟩
          simp [renameConfig, renameChain, renameEntry, runtimeErrorValue_ren,
            List.map_append]
      all_goals exact ExSim.skip fun m h => GoError.noConfusion h

end FrameStep

end GoLean.Frame
