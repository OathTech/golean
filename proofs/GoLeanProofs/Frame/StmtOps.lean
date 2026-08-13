import GoLeanProofs.Frame.PanicFrame
import GoLeanProofs.Frame.Builders

/-!
# The executable frame theorem, module 6: wide-op simulation

The choices-free wide-op core (`applyStmtOpCore`) and its map-assign
helper (`mapAssignValue`) commute across `FrameSim`: canonical `.ok`
transfers to the framed run with the state relation preserved,
canonical panics transfer with the same (address-free) message, and
every other canonical error transfers vacuously.  Plus the panic-
freedom facts for the array builders and slice validation that lift
their ok-transfer (`_ren`) lemmas into `ExSim` positions.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

/-! ## Panic-freedom for the builders -/

theorem NoPanic.forIn' {α β : Type} {l : List α} {b : β}
    {f : α → β → Except GoError (ForInStep β)}
    (hf : ∀ a b', NoPanic (f a b')) : NoPanic (forIn l b f) := by
  induction l generalizing b with
  | nil =>
      rw [List.forIn_nil]
      exact NoPanic.pure'
  | cons a as ih =>
      rw [List.forIn_cons]
      refine NoPanic.bind (hf a b) fun s => ?_
      cases s with
      | done x => exact NoPanic.pure'
      | yield x => exact ih

private theorem defaultFieldsWith_noPanic {f : Ty → Except GoError GoValue}
    (hf : ∀ ty, NoPanic (f ty)) :
    ∀ l : List FieldDef, NoPanic (defaultFieldsWith f l) := by
  intro l
  induction l with
  | nil => exact NoPanic.pure'
  | cons fd rest ih =>
      simp only [defaultFieldsWith]
      exact NoPanic.bind (hf _) fun _ => NoPanic.bind ih fun _ => NoPanic.pure'

private theorem defaultValueFuel_noPanic :
    ∀ (fuel : Nat) (σ : ExecState) (ty : Ty),
      NoPanic (defaultValueFuel fuel σ ty) := by
  intro fuel
  induction fuel with
  | zero => intro σ ty; exact NoPanic.unsupported'
  | succ n ih =>
      intro σ ty
      cases ty with
      | array length elem =>
          simp only [defaultValueFuel]
          split
          · exact NoPanic.pure'
          · exact NoPanic.bind NoPanic.pure' fun _ =>
              NoPanic.bind (ih σ elem) fun _ => NoPanic.pure'
      | defined name =>
          simp only [defaultValueFuel]
          cases TypeEnv.lookup σ.types name with
          | none => exact NoPanic.unsupported'
          | some td =>
              cases td with
              | struct fields =>
                  exact NoPanic.map (defaultFieldsWith_noPanic (fun t => ih σ t) _)
              | alias target => exact ih σ target
              | defined target => exact ih σ target
              | interfaceDef ms => exact NoPanic.unsupported'
              | unsupported f => exact NoPanic.unsupported'
      | _ =>
          simp only [defaultValueFuel] <;>
            first
            | exact NoPanic.pure'
            | exact NoPanic.unsupported'

private theorem defaultValue_noPanic (σ : ExecState) (ty : Ty) :
    NoPanic (defaultValue σ ty) := by
  rw [defaultValue]
  exact defaultValueFuel_noPanic _ σ ty

theorem buildArrayValue_noPanic (σ : ExecState) (len : Nat) (elem : Ty)
    (args : Array (Int × GoValue)) : NoPanic (buildArrayValue σ len elem args) := by
  unfold buildArrayValue
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', ← Array.forIn_toList]
  refine NoPanic.bind (NoPanic.forIn' fun a b => ?_) fun values => ?_
  · exact NoPanic.bind (defaultValue_noPanic σ elem) fun _ =>
      NoPanic.bind NoPanic.pure' fun _ => NoPanic.pure'
  · refine NoPanic.bind (NoPanic.forIn' fun p st => ?_) fun st => NoPanic.pure'
    obtain ⟨key, value⟩ := p
    obtain ⟨seen, vals⟩ := st
    refine NoPanic.ite' ?_ ?_
    · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
    · refine NoPanic.bind NoPanic.pure' fun y => ?_
      refine NoPanic.ite' ?_ ?_
      · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
      · refine NoPanic.bind NoPanic.pure' fun y' => ?_
        dsimp only
        split
        · exact NoPanic.bind (normalizeValueForTy_noPanic σ elem value) fun nv =>
            NoPanic.bind (coerceStoredValue_noPanic _ nv) fun _ =>
              NoPanic.bind NoPanic.pure' fun _ => NoPanic.pure'
        · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha

theorem buildDefaultArrayValue_noPanic (σ : ExecState) (len : Nat) (elem : Ty) :
    NoPanic (buildDefaultArrayValue σ len elem) := by
  unfold buildDefaultArrayValue
  exact buildArrayValue_noPanic σ len elem #[]

theorem validateSlice_noPanic (sl : SliceValue) : NoPanic (validateSlice sl) := by
  simp only [validateSlice]
  refine NoPanic.ite' ?_ ?_
  · exact NoPanic.bind' NoPanic.stuck' fun a ha => by simp at ha
  · refine NoPanic.bind NoPanic.pure' fun y => ?_
    cases sl.base with
    | some b => exact NoPanic.pure'
    | none => exact NoPanic.ite' NoPanic.pure' NoPanic.stuck'

/-! ## Renamed-entry array bridges -/

private theorem list_eraseIdx_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a as ih =>
      intro i
      cases i with
      | zero => simp [List.eraseIdx]
      | succ n => simp only [List.map_cons, List.eraseIdx, ih]

private theorem renEntries_size (ρ : Nat → Nat) (es : Array (GoValue × GoValue)) :
    ((renameValueEntries ρ es.toList).toArray).size = es.size := by
  simp [renameValueEntries_eq_map]

private theorem renEntries_set! (ρ : Nat → Nat) (es : Array (GoValue × GoValue))
    (i : Nat) (k v : GoValue) :
    ((renameValueEntries ρ es.toList).toArray).set! i (renameValue ρ k, renameValue ρ v)
      = (renameValueEntries ρ (es.set! i (k, v)).toList).toArray := by
  rw [Array.set!, Array.set!]
  apply Array.toList_inj.mp
  simp [renameValueEntries_eq_map, Array.toList_setIfInBounds, List.map_set]

private theorem renEntries_push (ρ : Nat → Nat) (es : Array (GoValue × GoValue))
    (k v : GoValue) :
    ((renameValueEntries ρ es.toList).toArray).push (renameValue ρ k, renameValue ρ v)
      = (renameValueEntries ρ (es.push (k, v)).toList).toArray := by
  apply Array.toList_inj.mp
  simp [renameValueEntries_eq_map]

private theorem renEntries_eraseIdx! (ρ : Nat → Nat)
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

private theorem renList_push (ρ : Nat → Nat) (vs : Array GoValue) (v : GoValue) :
    ((renameValueList ρ vs.toList).toArray).push (renameValue ρ v)
      = (renameValueList ρ (vs.push v).toList).toArray := by
  apply Array.toList_inj.mp
  simp [renameValueList_eq_map]

/-! ## `ExSim` forms of the shape coercions and slice validation -/

private theorem valueAsInt_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim Eq (valueAsInt v) (valueAsInt (renameValue ρ v)) := by
  cases v with
  | int n k => exact ExSim.ok rfl
  | _ => exact ExSim.stuck'

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

/-- Both runs' `validateSlice` calls relate: a canonical `ok` transfers
(`validateSlice_ren`), and a canonical error is never a panic. -/
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

/-! ## The wide-op arms -/

section
variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

theorem mapAssignValue_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (kt vt : Ty) (baseV keyV valueV : GoValue) :
    ExSim (FrameSim ρ na₀ na fr)
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
  refine ExSim.bind (mapEntries_sim hS m) ?_
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
          exact storeLoc_sim hS baseLoc (.mapData (entries.set! i (k, v)))
      | none =>
          simp only [pure_bind]
          rw [renEntries_push]
          exact storeLoc_sim hS baseLoc (.mapData (entries.push (k, v)))

theorem applyStmtOpCore_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (op : StmtOp) (nt : Nat) (vs : List GoValue) :
    ExSim (FrameSim ρ na₀ na fr)
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
          refine ExSim.bind (storeLoc_sim (hS.alloc_snd value typ) loc
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
              refine ExSim.bind (storeLoc_sim
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
              refine ExSim.bind (storeLoc_sim
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
          (∀ {σ₁ σF₁ : ExecState}, FrameSim ρ na₀ na fr σ₁ σF₁ →
            ExSim (FrameSim ρ na₀ na fr)
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
        refine ExSim.bind (storeLoc_sim (hS₁.alloc_snd (.mapData #[]) none) loc
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
          (∀ {σ₁ σF₁ : ExecState}, FrameSim ρ na₀ na fr σ₁ σF₁ →
            ExSim (FrameSim ρ na₀ na fr)
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
        refine ExSim.bind (storeLoc_sim
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
          exact mapAssignValue_sim hS hinj keyTy valueTy baseV keyV valueV
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
            refine ExSim.bind (loadLoc_sim hS l) ?_
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
                FrameSim ρ na₀ na fr p.fst q.fst ∧ p.snd = q.snd)
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
              refine ExSim.bind (storeLoc_sim hc l a) ?_
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
              refine ExSim.bind (storeLoc_sim hc tloc
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
          refine ExSim.bind (mapEntries_sim hS m) ?_
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
                  refine ExSim.bind (storeLoc_sim hS baseLoc
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
          refine ExSim.bind (mapEntries_sim hS m) ?_
          intro o oF hoF
          subst hoF
          cases o with
          | none => exact ExSim.ok hS
          | some p =>
              obtain ⟨baseLoc, entries⟩ := p
              simp only [Option.map_some]
              refine ExSim.bind (storeLoc_sim hS baseLoc (.mapData #[])) ?_
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
            refine ExSim.bind (storeLoc_sim hxy l z) ?_
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
            refine ExSim.bind (loadLoc_sim hS l) ?_
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
                  refine ExSim.bind (storeLoc_sim hxy l (.int n k)) ?_
                  intro x' y' h'
                  exact ExSim.ok h'
              | none => exact ExSim.stuck'
            · intro x y hxy
              exact ExSim.ok hxy
      | [] => exact ExSim.stuck'
      | _ :: _ :: _ => exact ExSim.stuck'

end

end GoLean.Frame
