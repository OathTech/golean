import GoLeanProofs.Frame.StmtOps
import GoLeanProofs.Frame.StrictOps

/-!
# The executable frame theorem: store-spine glue ops (build handoff §2)

The four apply-level commutation lemmas the remaining `stepFn_sim` arms
consume (handoff `docs/2026-08-13_frame-theorem-build-handoff.md` §2):

* `resolveChain_sim` — phase-2 chain replay (structural on the steps;
  `indexTargetLoc_sim` + `valueAsLoc_sim` at each step).
* `storeTarget_sim` — one phase-2 store (`resolveChain` + `storeLoc_sim`
  on the chain arm; `mapAssignValue_sim` on the map-element arm).
* `applyRhsOp_sim` — the comma-ok value source (`.vals` is pure;
  mapLookup/typeAssert through their commutation lemmas).
* `applyStmtOp_sim` — the wide-op wrapper: every non-append arm
  dispatches to `applyStmtOpCore_sim`; the `appendSlice` arm is proved
  here (in-place loop via `forIn_sim`, spill via
  `buildAppendBackingValue_sim` + the allocation combinators — the
  spill WIDTH is loc-free data, so the SAME choice is consumed and the
  streams stay equal).

The `private` shape-coercion `ExSim` forms replicate the (file-private)
copies in `StmtOps`/`StrictOps` — the file-local convention of the
helper layer.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

/-! ## Private shape-coercion copies -/

private theorem renList_size (ρ : Nat → Nat) (l : List GoValue) :
    ((renameValueList ρ l).toArray).size = l.length := by
  simp [renameValueList_eq_map]

private theorem renList_push (ρ : Nat → Nat) (vs : Array GoValue) (v : GoValue) :
    ((renameValueList ρ vs.toList).toArray).push (renameValue ρ v)
      = (renameValueList ρ (vs.push v).toList).toArray := by
  apply Array.toList_inj.mp
  simp [renameValueList_eq_map]

private theorem valueAsMap_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun m mF => mF = { base := m.base.map (renameLoc ρ) : MapValue })
      (valueAsMap v) (valueAsMap (renameValue ρ v)) := by
  cases v with
  | map m => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

private theorem valueAsSlice_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun sl slF => slF = { sl with base := sl.base.map (renameLoc ρ) })
      (valueAsSlice v) (valueAsSlice (renameValue ρ v)) := by
  cases v with
  | slice sl => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

private theorem validateSlice_exsim (ρ : Nat → Nat) (sl : SliceValue) :
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

private theorem typeAssertValue_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) (ty : Ty) :
    ExSim (fun (p pF : GoValue × Bool) => pF = (renameValue ρ p.1, p.2))
      (typeAssertValue σ v ty)
      (typeAssertValue σF (renameValue ρ v) ty) := by
  simp only [typeAssertValue]
  refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq ty) ?_
  intro d dF hdF
  subst hdF
  cases v <;> simp only [renameValue]
  case nil => exact ExSim.ok rfl
  case interface dynTy inner =>
      rw [resolveDefinedAliases_congr hS.types_eq]
      cases hres : resolveDefinedAliases σ ty
      case interface iname =>
          dsimp only
          rw [dynamicImplementsInterface_congr hS.types_eq hS.methods_eq
            hS.funcs_eq hS.methodSets_eq]
          refine ExSim.bind (ExSim.refl _) ?_
          intro b b' hb
          subst hb
          cases b
          · exact ExSim.ok rfl
          · exact ExSim.ok (by simp only [renameValue])
      all_goals (
        rw [canonicalTy_congr hS.types_eq]
        exact ExSim.ite_congr (fun _ => ExSim.ok rfl) (fun _ => ExSim.ok rfl))
  all_goals exact ExSim.unsupported'

/-! ## `resolveChain` (phase-2 chain replay) -/

theorem resolveChain_sim (hS : FrameSim ρ na₀ na fr σ σF) :
    ∀ (steps : List TargetStep) (cur : GoValue) (idxs : List GoValue),
      ExSim (fun v vF => vF = renameValue ρ v)
        (resolveChain σ cur steps idxs)
        (resolveChain σF (renameValue ρ cur) steps (renameValueList ρ idxs)) := by
  intro steps
  induction steps with
  | nil =>
      intro cur idxs
      cases idxs with
      | nil => exact ExSim.ok rfl
      | cons i t =>
          simp only [resolveChain, renameValueList]
          exact ExSim.stuck'
  | cons st rest ih =>
      intro cur idxs
      cases st with
      | index =>
          cases idxs with
          | nil =>
              simp only [resolveChain, renameValueList]
              exact ExSim.stuck'
          | cons i t =>
              simp only [resolveChain, renameValueList]
              refine ExSim.bind (indexTargetLoc_sim hS cur i) ?_
              intro l lF hl
              subst hl
              have h := ih (.addr l) t
              simp only [renameValue] at h
              exact h
      | field tid f =>
          simp only [resolveChain]
          refine ExSim.bind (valueAsLoc_sim ρ cur) ?_
          intro l lF hl
          subst hl
          have h := ih (.addr (.field l tid f)) idxs
          simp only [renameValue, renameLoc] at h
          exact h

/-! ## `storeTarget` (phase 2, one target) -/

theorem storeTarget_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (r : TargetRef) (v : GoValue) :
    ExSim (FrameSim ρ na₀ na fr)
      (storeTarget σ r v)
      (storeTarget σF (renameTargetRef ρ r) (renameValue ρ v)) := by
  cases r with
  | chain anchor idxs steps =>
      simp only [storeTarget, renameTargetRef]
      refine ExSim.bind (resolveChain_sim hS steps anchor idxs) ?_
      intro cur curF hc
      subst hc
      refine ExSim.bind (valueAsLoc_sim ρ cur) ?_
      intro l lF hl
      subst hl
      exact storeLoc_sim hS l v
  | mapElem b k kt vt =>
      simp only [storeTarget, renameTargetRef]
      exact mapAssignValue_sim hS hinj kt vt b k v

/-! ## `applyRhsOp` (the comma-ok value source) -/

theorem applyRhsOp_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (rop : RhsOp) (vs : List GoValue) :
    ExSim (fun vs' vsF => vsF = renameValueList ρ vs')
      (applyRhsOp σ rop vs) (applyRhsOp σF rop (renameValueList ρ vs)) := by
  cases rop with
  | vals => exact ExSim.pure' rfl
  | mapLookup kt vt =>
      match vs with
      | [baseV, keyV] =>
          simp only [applyRhsOp, renameValueList]
          refine ExSim.bind (valueAsMap_sim ρ baseV) ?_
          intro m mF hm
          subst hm
          refine ExSim.bind (normalizeValueForTy_sim hS.types_eq kt keyV) ?_
          intro k kF hk
          subst hk
          refine ExSim.bind (mapLookupValue_sim hS hinj m k kt vt) ?_
          intro p pF hp
          subst hp
          exact ExSim.pure' (by simp [renameValueList, renameValue])
      | [] => exact ExSim.stuck'
      | [_] => exact ExSim.stuck'
      | _ :: _ :: _ :: _ => exact ExSim.stuck'
  | typeAssert ty =>
      match vs with
      | [value] =>
          simp only [applyRhsOp, renameValueList]
          refine ExSim.bind (typeAssertValue_sim hS value ty) ?_
          intro p pF hp
          subst hp
          exact ExSim.pure' (by simp [renameValueList, renameValue])
      | [] => exact ExSim.stuck'
      | _ :: _ :: _ => exact ExSim.stuck'

/-! ## `buildAppendBackingValue` as an `ExSim` (the spill backing) -/

private theorem buildAppendBackingValue_sim (hS : FrameSim ρ na₀ na fr σ σF)
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

theorem applyStmtOp_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (ch : Choices) (op : StmtOp) (nt : Nat) (vs : List GoValue) :
    ExSim (fun (r rF : ExecState × Choices) =>
        FrameSim ρ na₀ na fr r.1 rF.1 ∧ rF.2 = r.2)
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
        refine ExSim.bind (sliceVisibleValues_sim hS ⟨eb, eoff, elen, ecap⟩) ?_
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
              FrameSim ρ na₀ na fr p.fst q.fst ∧ p.snd = q.snd)
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
                refine ExSim.bind (storeLoc_sim hc
                  (.index base (Int.ofNat (off + len + ix))) a) ?_
                intro cx' cy' hc'
                exact ExSim.ok ⟨hc', rfl⟩
          · intro st stF hst
            obtain ⟨c1, i1⟩ := st
            obtain ⟨c2, i2⟩ := stF
            obtain ⟨hc, hi⟩ := hst
            dsimp only at hi hc
            cases hi
            refine ExSim.bind (storeLoc_sim hc tloc
              (.slice ⟨b, off, len + ev.size, cap⟩)) ?_
            intro σ' σF' hS'
            exact ExSim.pure' ⟨hS', rfl⟩
        · -- spill: same width, same choice; fresh backing at the renamed
          -- fresh address
          refine ExSim.bind (sliceVisibleValues_sim hS ⟨b, off, len, cap⟩) ?_
          intro ov ovF hovF
          subst hovF
          rcases hcs : ch.consume (appendSpillWidth cap (len + ev.size))
            with ⟨extra, ch2⟩
          simp only [hcs]
          refine ExSim.bind (buildAppendBackingValue_sim hS elem ov ev
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
            (storeLoc_sim (hS.alloc_snd backing (some (.array ncap elem))) tloc
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
    refine ExSim.bind (applyStmtOpCore_sim hS hinj _ nt vs) ?_
    intro s' sF' hS'
    exact ExSim.pure' ⟨hS', rfl⟩)

end GoLean.Frame
