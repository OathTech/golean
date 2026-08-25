import GoLeanProofs.Frame.ShapeOps

/-!
# S-copies, part 2: the statement-op arms (`StmtOps`/`Ops2` mirrors)

Mechanical copies of `mapAssignValue_sim` / `applyStmtOpCore_sim` /
`storeTarget_sim` / `buildAppendBackingValue_sim` / `applyStmtOp_sim`
with the strengthened relation through `storeLoc_simS` and the
`FrameSimS` alloc pair, plus the weak files' PRIVATE value-level
helpers inlined verbatim (they are file-scoped upstream). See
`ShapeSim.lean` for the scaffold record.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

theorem list_eraseIdx_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a as ih =>
      intro i
      cases i with
      | zero => simp [List.eraseIdx]
      | succ n => simp only [List.map_cons, List.eraseIdx, ih]

theorem renEntries_size (ρ : Nat → Nat) (es : Array (GoValue × GoValue)) :
    ((renameValueEntries ρ es.toList).toArray).size = es.size := by
  simp [renameValueEntries_eq_map]

theorem renEntries_set! (ρ : Nat → Nat) (es : Array (GoValue × GoValue))
    (i : Nat) (k v : GoValue) :
    ((renameValueEntries ρ es.toList).toArray).set! i (renameValue ρ k, renameValue ρ v)
      = (renameValueEntries ρ (es.set! i (k, v)).toList).toArray := by
  rw [Array.set!, Array.set!]
  apply Array.toList_inj.mp
  simp [renameValueEntries_eq_map, Array.toList_setIfInBounds, List.map_set]

theorem renEntries_push (ρ : Nat → Nat) (es : Array (GoValue × GoValue))
    (k v : GoValue) :
    ((renameValueEntries ρ es.toList).toArray).push (renameValue ρ k, renameValue ρ v)
      = (renameValueEntries ρ (es.push (k, v)).toList).toArray := by
  apply Array.toList_inj.mp
  simp [renameValueEntries_eq_map]

theorem renEntries_eraseIdx! (ρ : Nat → Nat)
    (es : Array (GoValue × GoValue)) (i : Nat) :
    ((renameValueEntries ρ es.toList).toArray).eraseIdx! i
      = (renameValueEntries ρ (es.eraseIdx! i).toList).toArray := by
  unfold Array.eraseIdx!
  by_cases h : i < es.size
  · rw [dif_pos (by rw [renEntries_size]; exact h), dif_pos h]
    apply Array.toList_inj.mp
    rw [Array.toList_eraseIdx, Array.toList_eraseIdx]
    simp only [renameValueEntries_eq_map, List.toList_toArray]
    exact list_eraseIdx_map _ es.toList i
  · rw [dif_neg (by rw [renEntries_size]; exact h), dif_neg h]
    rfl

theorem renList_push (ρ : Nat → Nat) (vs : Array GoValue) (v : GoValue) :
    ((renameValueList ρ vs.toList).toArray).push (renameValue ρ v)
      = (renameValueList ρ (vs.push v).toList).toArray := by
  apply Array.toList_inj.mp
  simp [renameValueList_eq_map]

/-! ## `ExSim` forms of the shape coercions and slice validation -/

theorem valueAsInt_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim Eq (valueAsInt v) (valueAsInt (renameValue ρ v)) := by
  cases v with
  | int n k => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

theorem valueAsMap_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun m mF => mF = { base := m.base.map (renameLoc ρ) : MapValue })
      (valueAsMap v) (valueAsMap (renameValue ρ v)) := by
  cases v with
  | map m => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

theorem valueAsSlice_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun sl slF => slF = { sl with base := sl.base.map (renameLoc ρ) })
      (valueAsSlice v) (valueAsSlice (renameValue ρ v)) := by
  cases v with
  | slice sl => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

/-- Both runs' `validateSlice` calls relate: a canonical `ok` transfers
(`validateSlice_ren`), and a canonical error is never a panic. -/
theorem validateSlice_exsim (ρ : Nat → Nat) (sl : SliceValue) :
    ExSim (fun _ _ => True) (validateSlice sl)
      (validateSlice { sl with base := sl.base.map (renameLoc ρ) }) := by
  cases h : validateSlice sl with
  | ok u =>
      cases u
      rw [validateSlice_ren ρ h]
      exact ExSim.ok trivial
  | error e =>
      cases e with
      | panic m => exact absurd h (validateSlice_noPanic sl m ·)
      | _ => trivial

theorem renList_size (ρ : Nat → Nat) (l : List GoValue) :
    ((renameValueList ρ l).toArray).size = l.length := by
  simp [renameValueList_eq_map]



section
variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem mapAssignValue_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (kt vt : Ty) (baseV keyV valueV : GoValue) :
    ExSim (FrameSimS ρ na₀ na fr)
      (mapAssignValue σ kt vt baseV keyV valueV)
      (mapAssignValue σF kt vt (renameValue ρ baseV) (renameValue ρ keyV)
        (renameValue ρ valueV)) := by
  simp only [mapAssignValue]
  refine ExSim.bind (valueAsMap_sim ρ baseV) ?_
  intro m mF hmF
  subst hmF
  refine ExSim.bind (normalizeValueForTy_sim hS.types_eq kt keyV) ?_
  intro k kF hkF
  subst hkF
  refine ExSim.bind (normalizeValueForTy_sim hS.types_eq vt valueV) ?_
  intro v vF hvF
  subst hvF
  refine ExSim.bind (mapEntries_sim hS.toFrameSim m) ?_
  intro o oF hoF
  subst hoF
  cases o with
  | none => exact ExSim.panic
  | some p =>
      obtain ⟨baseLoc, entries⟩ := p
      simp only [Option.map_some]
      refine ExSim.bind (mapEntryIndex?_sim hinj hS.types_eq kt entries k true) ?_
      intro r r' hr
      subst hr
      cases r with
      | some i =>
          simp only [pure_bind]
          rw [renEntries_set!]
          exact storeLoc_simS hS baseLoc (.mapData (entries.set! i (k, v)))
      | none =>
          simp only [pure_bind]
          rw [renEntries_push]
          exact storeLoc_simS hS baseLoc (.mapData (entries.push (k, v)))

theorem applyStmtOpCore_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (op : StmtOp) (nt : Nat) (vs : List GoValue) :
    ExSim (FrameSimS ρ na₀ na fr)
      (applyStmtOpCore σ op nt vs)
      (applyStmtOpCore σF op nt (renameValueList ρ vs)) := by
  cases op with
  | newValue typ =>
      match vs with
      | [tv, value] =>
          simp only [applyStmtOpCore, renameValueList]
          refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
          intro loc locF hloc
          subst hloc
          have halloc : σF.alloc (renameValue ρ value) typ
              = (renameLoc ρ (σ.alloc value typ).1,
                  (σF.alloc (renameValue ρ value) typ).2) := by
            rw [← hS.alloc_fst value typ]
          rw [halloc]
          refine ExSim.bind (storeLoc_simS (hS.alloc_snd value typ) loc
            (.addr (σ.alloc value typ).1)) ?_
          intro σ' σF' hS'
          exact ExSim.ok hS'
      | [] => exact ExSim.stuck'
      | [_] => exact ExSim.stuck'
      | _ :: _ :: _ :: _ => exact ExSim.stuck'
  | makeSlice elem hasCap =>
      cases hasCap with
      | false =>
          match vs with
          | [tv, lenV] =>
              simp only [applyStmtOpCore, renameValueList, pure_bind]
              refine ExSim.bind (valueAsInt_sim ρ lenV) ?_
              intro lv lv' hlv
              subst hlv
              refine ExSim.bind (ExSim.refl (natFromNonnegativeInt
                "runtime error: makeslice: len out of range" lv)) ?_
              intro len len' hlen
              subst hlen
              refine ExSim.bind (ExSim.refl (natFromNonnegativeInt
                "runtime error: makeslice: cap out of range" lv)) ?_
              intro cap cap' hcap
              subst hcap
              refine ExSim.ite_congr (fun hc => ExSim.panic) (fun hc => ?_)
              refine ExSim.bind (exSim_of_ren
                (buildDefaultArrayValue_noPanic σ cap elem)
                (fun r h => buildDefaultArrayValue_ren ρ hS.types_eq h)) ?_
              intro backing backingF hb
              subst hb
              have halloc : σF.alloc (renameValue ρ backing) (some (.array cap elem))
                  = (renameLoc ρ (σ.alloc backing (some (.array cap elem))).1,
                      (σF.alloc (renameValue ρ backing) (some (.array cap elem))).2) := by
                rw [← hS.alloc_fst backing (some (.array cap elem))]
              rw [halloc]
              refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (storeLoc_simS
                (hS.alloc_snd backing (some (.array cap elem))) loc
                (.slice { base := some (σ.alloc backing (some (.array cap elem))).1,
                          offset := 0, len := len, cap := cap })) ?_
              intro σ' σF' hS'
              exact ExSim.ok hS'
          | [] => exact ExSim.stuck'
          | [_] => exact ExSim.stuck'
          | [_, _, _] => exact ExSim.stuck'
          | _ :: _ :: _ :: _ :: _ => exact ExSim.stuck'
      | true =>
          match vs with
          | [tv, lenV, capV] =>
              simp only [applyStmtOpCore, renameValueList, pure_bind]
              refine ExSim.bind (valueAsInt_sim ρ lenV) ?_
              intro lv lv' hlv
              subst hlv
              refine ExSim.bind (valueAsInt_sim ρ capV) ?_
              intro cv cv' hcv
              subst hcv
              refine ExSim.bind (ExSim.refl (natFromNonnegativeInt
                "runtime error: makeslice: len out of range" lv)) ?_
              intro len len' hlen
              subst hlen
              refine ExSim.bind (ExSim.refl (natFromNonnegativeInt
                "runtime error: makeslice: cap out of range" cv)) ?_
              intro cap cap' hcap
              subst hcap
              refine ExSim.ite_congr (fun hc => ExSim.panic) (fun hc => ?_)
              refine ExSim.bind (exSim_of_ren
                (buildDefaultArrayValue_noPanic σ cap elem)
                (fun r h => buildDefaultArrayValue_ren ρ hS.types_eq h)) ?_
              intro backing backingF hb
              subst hb
              have halloc : σF.alloc (renameValue ρ backing) (some (.array cap elem))
                  = (renameLoc ρ (σ.alloc backing (some (.array cap elem))).1,
                      (σF.alloc (renameValue ρ backing) (some (.array cap elem))).2) := by
                rw [← hS.alloc_fst backing (some (.array cap elem))]
              rw [halloc]
              refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
              intro loc locF hloc
              subst hloc
              refine ExSim.bind (storeLoc_simS
                (hS.alloc_snd backing (some (.array cap elem))) loc
                (.slice { base := some (σ.alloc backing (some (.array cap elem))).1,
                          offset := 0, len := len, cap := cap })) ?_
              intro σ' σF' hS'
              exact ExSim.ok hS'
          | [] => exact ExSim.stuck'
          | [_] => exact ExSim.stuck'
          | [_, _] => exact ExSim.stuck'
          | _ :: _ :: _ :: _ :: _ => exact ExSim.stuck'
  | makeMap hasSpace =>
      have hmapTail : ∀ tv : GoValue,
          (∀ {σ₁ σF₁ : ExecState}, FrameSimS ρ na₀ na fr σ₁ σF₁ →
            ExSim (FrameSimS ρ na₀ na fr)
              (do
                let loc ← valueAsLoc tv
                return ((← storeLoc (σ₁.alloc (.mapData #[])).2 loc
                  (.map { base := some (σ₁.alloc (.mapData #[])).1 }))))
              (do
                let loc ← valueAsLoc (renameValue ρ tv)
                return ((← storeLoc (σF₁.alloc (.mapData #[])).2 loc
                  (.map { base := some (σF₁.alloc (.mapData #[])).1 }))))) := by
        intro tv σ₁ σF₁ hS₁
        have hfst : (σF₁.alloc (.mapData #[]) none).1
            = renameLoc ρ (σ₁.alloc (.mapData #[]) none).1 :=
          hS₁.alloc_fst (.mapData #[]) none
        rw [hfst]
        refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
        intro loc locF hloc
        subst hloc
        refine ExSim.bind (storeLoc_simS (hS₁.alloc_snd (.mapData #[]) none) loc
          (.map { base := some (σ₁.alloc (.mapData #[]) none).1 })) ?_
        intro σ' σF' hS'
        exact ExSim.ok hS'
      cases hasSpace with
      | false =>
          match vs with
          | [tv] =>
              simp only [applyStmtOpCore, renameValueList, pure_bind]
              exact hmapTail tv hS
          | [] => exact ExSim.stuck'
          | [_, _] => exact ExSim.stuck'
          | _ :: _ :: _ :: _ => exact ExSim.stuck'
      | true =>
          match vs with
          | [tv, spaceV] =>
              simp only [applyStmtOpCore, renameValueList, pure_bind]
              refine ExSim.bind (valueAsInt_sim ρ spaceV) ?_
              intro sz sz' hsz
              subst hsz
              refine ExSim.bind (ExSim.refl (natFromNonnegativeInt
                "makemap: size out of range" sz)) ?_
              intro n n' hn
              subst hn
              exact hmapTail tv hS
          | [] => exact ExSim.stuck'
          | [_] => exact ExSim.stuck'
          | _ :: _ :: _ :: _ => exact ExSim.stuck'
  | makeChan hasCap =>
      have hchanTail : ∀ (tv : GoValue) (capacity : Nat),
          (∀ {σ₁ σF₁ : ExecState}, FrameSimS ρ na₀ na fr σ₁ σF₁ →
            ExSim (FrameSimS ρ na₀ na fr)
              (do
                let loc ← valueAsLoc tv
                return ((← storeLoc (σ₁.alloc (.chanData #[] capacity false)).2 loc
                  (.chan { base := some (σ₁.alloc (.chanData #[] capacity false)).1 }))))
              (do
                let loc ← valueAsLoc (renameValue ρ tv)
                return ((← storeLoc (σF₁.alloc (.chanData #[] capacity false)).2 loc
                  (.chan { base := some (σF₁.alloc (.chanData #[] capacity false)).1 }))))) := by
        intro tv capacity σ₁ σF₁ hS₁
        have hfst : (σF₁.alloc (.chanData #[] capacity false) none).1
            = renameLoc ρ (σ₁.alloc (.chanData #[] capacity false) none).1 :=
          hS₁.alloc_fst (.chanData #[] capacity false) none
        rw [hfst]
        refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
        intro loc locF hloc
        subst hloc
        refine ExSim.bind (storeLoc_simS
          (hS₁.alloc_snd (.chanData #[] capacity false) none) loc
          (.chan { base := some (σ₁.alloc (.chanData #[] capacity false) none).1 })) ?_
        intro σ' σF' hS'
        exact ExSim.ok hS'
      cases hasCap with
      | false =>
          match vs with
          | [tv] =>
              simp only [applyStmtOpCore, renameValueList, pure_bind]
              exact hchanTail tv 0 hS
          | [] => exact ExSim.stuck'
          | [_, _] => exact ExSim.stuck'
          | _ :: _ :: _ :: _ => exact ExSim.stuck'
      | true =>
          match vs with
          | [tv, capV] =>
              simp only [applyStmtOpCore, renameValueList, pure_bind]
              refine ExSim.bind (valueAsInt_sim ρ capV) ?_
              intro sz sz' hsz
              subst hsz
              refine ExSim.bind (ExSim.refl (natFromNonnegativeInt
                "makechan: size out of range" sz)) ?_
              intro capacity capacity' hcap
              subst hcap
              exact hchanTail tv capacity hS
          | [] => exact ExSim.stuck'
          | [_] => exact ExSim.stuck'
          | _ :: _ :: _ :: _ => exact ExSim.stuck'
  | mapAssign keyTy valueTy =>
      match vs with
      | [baseV, keyV, valueV] =>
          simp only [applyStmtOpCore, renameValueList]
          exact mapAssignValue_simS hS hinj keyTy valueTy baseV keyV valueV
      | [] => exact ExSim.stuck'
      | [_] => exact ExSim.stuck'
      | [_, _] => exact ExSim.stuck'
      | _ :: _ :: _ :: _ :: _ => exact ExSim.stuck'
  | appendSlice elem => exact ExSim.internal'
  | copySlice =>
      match vs with
      | [tv, dstV, srcV] =>
          simp only [applyStmtOpCore, renameValueList]
          refine ExSim.bind (valueAsSlice_sim ρ dstV) ?_
          intro dst dstF hdstF
          subst hdstF
          obtain ⟨db, doff, dlen, dcap⟩ := dst
          refine ExSim.bind (valueAsSlice_sim ρ srcV) ?_
          intro src srcF hsrcF
          subst hsrcF
          obtain ⟨sb, soff, slen, scap⟩ := src
          refine ExSim.bind (validateSlice_exsim ρ ⟨db, doff, dlen, dcap⟩) ?_
          intro _ _ _
          refine ExSim.bind (validateSlice_exsim ρ ⟨sb, soff, slen, scap⟩) ?_
          intro _ _ _
          simp only [Std.Legacy.Range.forIn_eq_forIn_range']
          -- the load loop: the framed accumulator is the renamed image
          refine ExSim.bind (forIn_sim_same
            (R := fun (v vF : Array GoValue) =>
              vF = (renameValueList ρ v.toList).toArray)
            (by simp [renameValueList]) ?_) ?_
          · intro a ha x y hxy
            subst hxy
            refine ExSim.bind (sliceIndexLoc_sim ρ ⟨sb, soff, slen, scap⟩
              (Int.ofNat a)) ?_
            intro l lF hlF
            subst hlF
            refine ExSim.bind (loadLoc_sim hS.toFrameSim l) ?_
            intro v vF hvF
            subst hvF
            exact ExSim.ok (renList_push ρ x v)
          · intro V VF hVF
            subst hVF
            -- the store loop: pairwise over the renamed values, the
            -- `i` counter riding the MProd state equal on both sides
            rw [← Array.forIn_toList, ← Array.forIn_toList]
            simp only [renameValueList_eq_map, List.toList_toArray]
            refine ExSim.bind (forIn_sim (t := renameValue ρ)
              (R := fun (p q : MProd ExecState Nat) =>
                FrameSimS ρ na₀ na fr p.fst q.fst ∧ p.snd = q.snd)
              ⟨hS, rfl⟩ ?_) ?_
            · intro a ha x y hxy
              obtain ⟨cx, ix⟩ := x
              obtain ⟨cy, iy⟩ := y
              obtain ⟨hc, hi⟩ := hxy
              dsimp only at hi hc
              cases hi
              refine ExSim.bind (sliceIndexLoc_sim ρ ⟨db, doff, dlen, dcap⟩
                (Int.ofNat ix)) ?_
              intro l lF hlF
              subst hlF
              refine ExSim.bind (storeLoc_simS hc l a) ?_
              intro cx' cy' hc'
              exact ExSim.ok ⟨hc', rfl⟩
            · intro st stF hst
              obtain ⟨c1, i1⟩ := st
              obtain ⟨c2, i2⟩ := stF
              obtain ⟨hc, hi⟩ := hst
              dsimp only at hi hc
              cases hi
              refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
              intro tloc tlocF htloc
              subst htloc
              refine ExSim.bind (storeLoc_simS hc tloc
                (.int (Int.ofNat (Nat.min dlen slen)))) ?_
              intro σ' σF' hS'
              exact ExSim.ok hS'
      | [] => exact ExSim.stuck'
      | [_] => exact ExSim.stuck'
      | [_, _] => exact ExSim.stuck'
      | _ :: _ :: _ :: _ :: _ => exact ExSim.stuck'
  | mapDelete keyTy =>
      match vs with
      | [baseV, keyV] =>
          simp only [applyStmtOpCore, renameValueList]
          refine ExSim.bind (valueAsMap_sim ρ baseV) ?_
          intro m mF hmF
          subst hmF
          refine ExSim.bind (normalizeValueForTy_sim hS.types_eq keyTy keyV) ?_
          intro k kF hkF
          subst hkF
          refine ExSim.bind (mapEntries_sim hS.toFrameSim m) ?_
          intro o oF hoF
          subst hoF
          cases o with
          | none =>
              refine ExSim.bind (checkKeyHashable_sim hS.types_eq k false false) ?_
              intro _ _ _
              exact ExSim.ok hS
          | some p =>
              obtain ⟨baseLoc, entries⟩ := p
              simp only [Option.map_some]
              refine ExSim.bind
                (mapEntryIndex?_sim hinj hS.types_eq keyTy entries k false) ?_
              intro r r' hr
              subst hr
              cases r with
              | some i =>
                  dsimp only
                  rw [renEntries_eraseIdx!]
                  refine ExSim.bind (storeLoc_simS hS baseLoc
                    (.mapData (entries.eraseIdx! i))) ?_
                  intro σ' σF' hS'
                  exact ExSim.ok hS'
              | none => exact ExSim.ok hS
      | [] => exact ExSim.stuck'
      | [_] => exact ExSim.stuck'
      | _ :: _ :: _ :: _ => exact ExSim.stuck'
  | clearMap =>
      match vs with
      | [baseV] =>
          simp only [applyStmtOpCore, renameValueList]
          refine ExSim.bind (valueAsMap_sim ρ baseV) ?_
          intro m mF hmF
          subst hmF
          refine ExSim.bind (mapEntries_sim hS.toFrameSim m) ?_
          intro o oF hoF
          subst hoF
          cases o with
          | none => exact ExSim.ok hS
          | some p =>
              obtain ⟨baseLoc, entries⟩ := p
              simp only [Option.map_some]
              refine ExSim.bind (storeLoc_simS hS baseLoc (.mapData #[])) ?_
              intro σ' σF' hS'
              exact ExSim.ok hS'
      | [] => exact ExSim.stuck'
      | _ :: _ :: _ => exact ExSim.stuck'
  | clearSlice elem =>
      match vs with
      | [baseV] =>
          simp only [applyStmtOpCore, renameValueList]
          refine ExSim.bind (valueAsSlice_sim ρ baseV) ?_
          intro sl slF hslF
          subst hslF
          obtain ⟨sbase, soff, slen, scap⟩ := sl
          refine ExSim.bind (validateSlice_exsim ρ ⟨sbase, soff, slen, scap⟩) ?_
          intro _ _ _
          refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq elem) ?_
          intro z zF hzF
          subst hzF
          simp only [Std.Legacy.Range.forIn_eq_forIn_range']
          refine ExSim.bind (forIn_sim_same hS ?_) ?_
          · intro a ha x y hxy
            refine ExSim.bind (sliceIndexLoc_sim ρ ⟨sbase, soff, slen, scap⟩
              (Int.ofNat a)) ?_
            intro l lF hlF
            subst hlF
            refine ExSim.bind (storeLoc_simS hxy l z) ?_
            intro x' y' hxy'
            exact ExSim.ok hxy'
          · intro x y hxy
            exact ExSim.ok hxy
      | [] => exact ExSim.stuck'
      | _ :: _ :: _ => exact ExSim.stuck'
  | sortSlice elem =>
      match vs with
      | [baseV] =>
          simp only [applyStmtOpCore, renameValueList]
          refine ExSim.bind (valueAsSlice_sim ρ baseV) ?_
          intro sl slF hslF
          subst hslF
          obtain ⟨sbase, soff, slen, scap⟩ := sl
          refine ExSim.bind (validateSlice_exsim ρ ⟨sbase, soff, slen, scap⟩) ?_
          intro _ _ _
          simp only [Std.Legacy.Range.forIn_eq_forIn_range']
          refine ExSim.bind (forIn_sim_same (R := Eq) rfl ?_) ?_
          · -- the load loop: accumulators stay EQUAL (loaded ints are
            -- loc-free, and the renamed load is forced to the same int)
            intro a ha x y hxy
            subst hxy
            refine ExSim.bind (sliceIndexLoc_sim ρ ⟨sbase, soff, slen, scap⟩
              (Int.ofNat a)) ?_
            intro l lF hlF
            subst hlF
            refine ExSim.bind (loadLoc_sim hS.toFrameSim l) ?_
            intro v vF hvF
            subst hvF
            cases v with
            | int n k => exact ExSim.ok rfl
            | _ => exact ExSim.stuck'
          · intro L L' hL
            subst hL
            refine ExSim.bind (forIn_sim_same hS ?_) ?_
            · -- the store-back loop: stored values are ints, renaming-inert
              intro a ha x y hxy
              cases (sortLe (fun a b => a.1 ≤ b.1) L.toList).toArray[a]? with
              | some p =>
                  obtain ⟨n, k⟩ := p
                  dsimp only
                  refine ExSim.bind (sliceIndexLoc_sim ρ ⟨sbase, soff, slen, scap⟩
                    (Int.ofNat a)) ?_
                  intro l lF hlF
                  subst hlF
                  refine ExSim.bind (storeLoc_simS hxy l (.int n k)) ?_
                  intro x' y' h'
                  exact ExSim.ok h'
              | none => exact ExSim.stuck'
            · intro x y hxy
              exact ExSim.ok hxy
      | [] => exact ExSim.stuck'
      | _ :: _ :: _ => exact ExSim.stuck'

end

section
variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

/-! ## `storeTarget` (phase 2, one target) -/

theorem storeTarget_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (r : TargetRef) (v : GoValue) :
    ExSim (FrameSimS ρ na₀ na fr)
      (storeTarget σ r v)
      (storeTarget σF (renameTargetRef ρ r) (renameValue ρ v)) := by
  cases r with
  | chain anchor idxs steps =>
      simp only [storeTarget, renameTargetRef]
      refine ExSim.bind (resolveChain_sim hS.toFrameSim steps anchor idxs) ?_
      intro cur curF hc
      subst hc
      refine ExSim.bind (valueAsLoc_sim ρ cur) ?_
      intro l lF hl
      subst hl
      exact storeLoc_simS hS l v
  | mapElem b k kt vt =>
      simp only [storeTarget, renameTargetRef]
      exact mapAssignValue_simS hS hinj kt vt b k v

/-! ## `buildAppendBackingValue` as an `ExSim` (the spill backing) -/

theorem buildAppendBackingValue_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (elem : Ty) (oldValues elemValues : Array GoValue) (newCap : Nat) :
    ExSim (fun v vF => vF = renameValue ρ v)
      (buildAppendBackingValue σ elem oldValues elemValues newCap)
      (buildAppendBackingValue σF elem
        ((renameValueList ρ oldValues.toList).toArray)
        ((renameValueList ρ elemValues.toList).toArray) newCap) := by
  unfold buildAppendBackingValue
  dsimp only
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  have harr : ((renameValueList ρ oldValues.toList).toArray
      ++ (renameValueList ρ elemValues.toList).toArray).toList
      = (oldValues ++ elemValues).toList.map (renameValue ρ) := by
    simp [renameValueList_eq_map]
  rw [harr]
  refine ExSim.bind (forIn_sim (t := renameValue ρ)
    (R := fun (v : Array GoValue) vF => vF = (renameValueList ρ v.toList).toArray)
    (by simp [renameValueList]) ?_) ?_
  · intro a ha x y hxy
    subst hxy
    refine ExSim.bind (normalizeValueForTy_sim hS.types_eq elem a) ?_
    intro nv nvF hnv
    subst hnv
    exact ExSim.ok (renList_push ρ x nv)
  · intro vs vsF h
    subst h
    simp only [renList_size, Array.length_toList]
    refine ExSim.ite_congr (fun _ => ExSim.stuck') (fun _ => ?_)
    simp only [pure_bind]
    rw [Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.forIn_eq_forIn_range']
    refine ExSim.bind (forIn_sim_same
      (R := fun (v : Array GoValue) vF =>
        vF = (renameValueList ρ v.toList).toArray) rfl ?_) ?_
    · intro i _ x y hxy
      subst hxy
      refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq elem) ?_
      intro d dF hd
      subst hd
      exact ExSim.ok (renList_push ρ x d)
    · intro vs2 vs2F h2
      subst h2
      exact ExSim.pure' (by simp [renameValue])

/-! ## `applyStmtOp` (the wide-op wrapper, `appendSlice` included) -/

theorem applyStmtOp_simS (hS : FrameSimS ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (ch : Choices) (op : StmtOp) (nt : Nat) (vs : List GoValue) :
    ExSim (fun (r rF : ExecState × Choices) =>
        FrameSimS ρ na₀ na fr r.1 rF.1 ∧ rF.2 = r.2)
      (applyStmtOp σ ch op nt vs)
      (applyStmtOp σF ch op nt (renameValueList ρ vs)) := by
  cases op
  case appendSlice elem =>
    match vs with
    | [tv, sliceV, elemsV] =>
        simp only [applyStmtOp, renameValueList]
        refine ExSim.bind (valueAsSlice_sim ρ sliceV) ?_
        intro sl slF hslF
        subst hslF
        obtain ⟨b, off, len, cap⟩ := sl
        refine ExSim.bind (valueAsSlice_sim ρ elemsV) ?_
        intro el elF helF
        subst helF
        obtain ⟨eb, eoff, elen, ecap⟩ := el
        refine ExSim.bind (validateSlice_exsim ρ ⟨b, off, len, cap⟩) ?_
        intro _ _ _
        refine ExSim.bind (validateSlice_exsim ρ ⟨eb, eoff, elen, ecap⟩) ?_
        intro _ _ _
        refine ExSim.bind (sliceVisibleValues_sim hS.toFrameSim ⟨eb, eoff, elen, ecap⟩) ?_
        intro ev evF hevF
        subst hevF
        refine ExSim.bind (valueAsLoc_sim ρ tv) ?_
        intro tloc tlocF htloc
        subst htloc
        have hsz : ((renameValueList ρ ev.toList).toArray).size = ev.size := by
          simp [renameValueList_eq_map]
        simp only [hsz]
        refine ExSim.ite_congr (fun hle => ?_) (fun hgt => ?_)
        · -- in place: pairwise store loop, `i` counter riding the MProd
          rw [← Array.forIn_toList, ← Array.forIn_toList]
          simp only [renameValueList_eq_map, List.toList_toArray]
          refine ExSim.bind (forIn_sim (t := renameValue ρ)
            (R := fun (p q : MProd ExecState Nat) =>
              FrameSimS ρ na₀ na fr p.fst q.fst ∧ p.snd = q.snd)
            ⟨hS, rfl⟩ ?_) ?_
          · intro a ha x y hxy
            obtain ⟨cx, ix⟩ := x
            obtain ⟨cy, iy⟩ := y
            obtain ⟨hc, hi⟩ := hxy
            dsimp only at hi hc
            cases hi
            cases b with
            | none => exact ExSim.stuck'
            | some base =>
                simp only [Option.map_some]
                refine ExSim.bind (storeLoc_simS hc
                  (.index base (Int.ofNat (off + len + ix))) a) ?_
                intro cx' cy' hc'
                exact ExSim.ok ⟨hc', rfl⟩
          · intro st stF hst
            obtain ⟨c1, i1⟩ := st
            obtain ⟨c2, i2⟩ := stF
            obtain ⟨hc, hi⟩ := hst
            dsimp only at hi hc
            cases hi
            refine ExSim.bind (storeLoc_simS hc tloc
              (.slice ⟨b, off, len + ev.size, cap⟩)) ?_
            intro σ' σF' hS'
            exact ExSim.pure' ⟨hS', rfl⟩
        · -- spill: same width, same choice; fresh backing at the renamed
          -- fresh address
          refine ExSim.bind (sliceVisibleValues_sim hS.toFrameSim ⟨b, off, len, cap⟩) ?_
          intro ov ovF hovF
          subst hovF
          rcases hcs : ch.consume (appendSpillWidth cap (len + ev.size))
            with ⟨extra, ch2⟩
          simp only [Choices.consumeAt_appendSpill, hcs]
          refine ExSim.bind (buildAppendBackingValue_simS hS elem ov ev
            (len + ev.size +
              (appendGrowthCap cap (len + ev.size) - (len + ev.size) + extra) %
                appendSpillWidth cap (len + ev.size))) ?_
          intro backing backingF hbF
          subst hbF
          generalize len + ev.size +
            (appendGrowthCap cap (len + ev.size) - (len + ev.size) + extra) %
              appendSpillWidth cap (len + ev.size) = ncap
          rw [hS.alloc_fst backing (some (.array ncap elem))]
          have hval : (GoValue.slice ⟨some (renameLoc ρ
                (σ.alloc backing (some (.array ncap elem))).1), 0,
                len + ev.size, ncap⟩)
              = renameValue ρ (.slice ⟨some
                ((σ.alloc backing (some (.array ncap elem))).1), 0,
                len + ev.size, ncap⟩) := by
            simp [renameValue]
          rw [hval]
          refine ExSim.bind
            (storeLoc_simS (hS.alloc_snd backing (some (.array ncap elem))) tloc
              (.slice ⟨some ((σ.alloc backing (some (.array ncap elem))).1), 0,
                len + ev.size, ncap⟩)) ?_
          intro σ' σF' hS'
          exact ExSim.pure' ⟨hS', rfl⟩
    | [] => exact ExSim.stuck'
    | [_] => exact ExSim.stuck'
    | [_, _] => exact ExSim.stuck'
    | _ :: _ :: _ :: _ :: _ => exact ExSim.stuck'
  all_goals (
    simp only [applyStmtOp]
    refine ExSim.bind (applyStmtOpCore_simS hS hinj _ nt vs) ?_
    intro s' sF' hS'
    exact ExSim.pure' ⟨hS', rfl⟩)

end

end GoLean.Frame
