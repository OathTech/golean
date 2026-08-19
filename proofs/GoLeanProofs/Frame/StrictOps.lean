import GoLeanProofs.Frame.PanicFrame
import GoLeanProofs.Frame.Builders

/-!
# The executable frame theorem: strict-operator simulation

The whole strict-operator apply layer commuted across `FrameSim`:
`sliceVisibleValues`, `mapLookupValue`, `indexTargetLoc`, `applySlice`,
and `applyStrictOp` itself (every arm of the op table). Result relation
throughout: the framed value is the renamed canonical one and the
states stay `FrameSim`-related; canonical panics transfer with the SAME
message (bounds/nil-deref/divide-by-zero messages are int-only or
fixed; the typeAssert panic message is reachable only on nil/interface
operands, where `typeAssertPanicMessage_ren` applies); canonical
stuck/unsupported errors transfer vacuously.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

set_option linter.unusedSimpArgs false

section
variable {ρ : Nat → Nat} {na₀ na : Nat} {fr : Heap} {σ σF : ExecState}

/-! ## Generic `ExSim` utilities -/

/-- `ExSim.bind` with the canonical `.ok` hypothesis available in the
continuation (the typeAssert arm needs its ok-shape inversion). -/
private theorem exSim_bind_ok {α β γ δ : Type} {R : α → β → Prop}
    {S : γ → δ → Prop} {x : Except GoError α} {y : Except GoError β}
    {f : α → Except GoError γ} {g : β → Except GoError δ}
    (hxy : ExSim R x y)
    (hfg : ∀ a b, x = .ok a → R a b → ExSim S (f a) (g b)) :
    ExSim S (x >>= f) (y >>= g) := by
  cases x with
  | ok a =>
      cases y with
      | ok b => simpa [Bind.bind, Except.bind] using hfg a b rfl hxy
      | error e => exact absurd hxy (by simp [ExSim])
  | error e =>
      cases e with
      | panic m =>
          have hy : y = .error (.panic m) := hxy
          subst hy
          exact rfl
      | _ => trivial

/-- Same computation on both sides, ok-results fixed by the renaming. -/
private theorem exsim_ren_self (ρ : Nat → Nat) {x : Except GoError GoValue}
    (hok : ∀ v, x = .ok v → renameValue ρ v = v) :
    ExSim (fun a b => b = renameValue ρ a) x x := by
  cases x with
  | ok a => exact (hok a rfl).symm
  | error e => cases e <;> first | rfl | trivial

/-- Same-value transfer plus panic-freedom, at relation `Eq`. -/
private theorem exsim_eq_of_ren {α : Type} {x y : Except GoError α}
    (hnp : NoPanic x) (htr : ∀ a, x = .ok a → y = .ok a) : ExSim Eq x y := by
  cases x with
  | ok a => rw [htr a rfl]; exact ExSim.ok rfl
  | error e =>
      cases e with
      | panic m => exact absurd rfl (hnp m)
      | _ => trivial

/-- The do-guard shape (`if c then stuck/panic …` with the continuation
duplicated into both branches by the elaborator), same condition on
both runs. -/
private theorem exsim_stepSim_refl {β : Type}
    (x : Except GoError (ForInStep β)) : ExSim (StepSim Eq) x x := by
  refine (ExSim.refl x).weaken ?_
  intro a b h
  subst h
  cases a <;> exact rfl

/-- Package a value-level transfer into the `applyStrictOp` result pair
(state unchanged on both sides). -/
private theorem scalar_pair (hS : FrameSim ρ na₀ na fr σ σF)
    {x y : Except GoError GoValue}
    (h : ExSim (fun v vF => vF = renameValue ρ v) x y) :
    ExSim (fun (r rF : GoValue × ExecState) =>
        rF.1 = renameValue ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
      (x >>= fun v => pure (v, σ)) (y >>= fun v => pure (v, σF)) :=
  ExSim.bind h fun _ _ hb => ExSim.ok ⟨hb, hS⟩

/-! ## Renamed-array/entry bridges -/

private theorem renArr_size (vs : Array GoValue) :
    ((renameValueList ρ vs.toList).toArray).size = vs.size := by
  simp [renameValueList_eq_map]

private theorem renArr_push (vs : Array GoValue) (v : GoValue) :
    ((renameValueList ρ vs.toList).toArray).push (renameValue ρ v)
      = (renameValueList ρ (vs.push v).toList).toArray := by
  simp [renameValueList_eq_map]

private theorem renEntries_size (es : Array (GoValue × GoValue)) :
    ((renameValueEntries ρ es.toList).toArray).size = es.size := by
  simp [renameValueEntries_eq_map]

private theorem renEntries_getElem? (es : Array (GoValue × GoValue)) (i : Nat) :
    ((renameValueEntries ρ es.toList).toArray)[i]?
      = (es[i]?).map (fun p => (renameValue ρ p.1, renameValue ρ p.2)) := by
  simp [renameValueEntries_eq_map, ← Array.getElem?_toList]

/-! ## `valueAs*` coercion simulations -/

private theorem valueAsInt_sim (ρ : Nat → Nat) {v vF : GoValue}
    (h : vF = renameValue ρ v) :
    ExSim Eq (valueAsInt v) (valueAsInt vF) := by
  subst h
  cases v <;> simp only [renameValue] <;>
    first
    | exact ExSim.stuck'
    | exact ExSim.ok rfl

private theorem valueAsBool_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim Eq (valueAsBool v) (valueAsBool (renameValue ρ v)) := by
  cases v <;> simp only [renameValue] <;>
    first
    | exact ExSim.stuck'
    | exact ExSim.ok rfl

private theorem valueAsSlice_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun sl slF => slF = { sl with base := sl.base.map (renameLoc ρ) })
      (valueAsSlice v) (valueAsSlice (renameValue ρ v)) := by
  cases v <;> simp only [renameValue] <;>
    first
    | exact ExSim.stuck'
    | exact ExSim.ok rfl

private theorem valueAsMap_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun (m mF : MapValue) => mF = { base := m.base.map (renameLoc ρ) })
      (valueAsMap v) (valueAsMap (renameValue ρ v)) := by
  cases v <;> simp only [renameValue] <;>
    first
    | exact ExSim.stuck'
    | exact ExSim.ok rfl

/-! ## `validateSlice` (stuck-only) as a full `ExSim` fact -/

private theorem exsim_guard {α β : Type} {R : α → β → Prop} {c : Prop}
    [Decidable c] {m₁ m₂ : String} {x : Except GoError α}
    {y : Except GoError β} (h : ExSim R x y) :
    ExSim R
      (if c then (stuck m₁ : Except GoError PUnit) >>= fun _ => x
        else pure PUnit.unit >>= fun _ => x)
      (if c then (stuck m₂ : Except GoError PUnit) >>= fun _ => y
        else pure PUnit.unit >>= fun _ => y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact ExSim.stuck'
  · rw [if_neg hc, if_neg hc]
    exact h

private theorem validateSlice_exsim (ρ : Nat → Nat) (s : SliceValue) :
    ExSim (fun _ _ => True) (validateSlice s)
      (validateSlice { s with base := s.base.map (renameLoc ρ) }) := by
  obtain ⟨b, o, ln, cp⟩ := s
  simp only [validateSlice]
  refine exsim_guard ?_
  cases b with
  | none =>
      simp only [Option.map_none]
      exact ExSim.ite_congr (fun _ => ExSim.ok trivial) (fun _ => ExSim.stuck')
  | some l => exact ExSim.ok trivial

/-! ## `sliceVisibleValues` -/

theorem sliceVisibleValues_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (sl : SliceValue) :
    ExSim (fun vs vsF => vsF = (renameValueList ρ vs.toList).toArray)
      (sliceVisibleValues σ sl)
      (sliceVisibleValues σF { sl with base := sl.base.map (renameLoc ρ) }) := by
  obtain ⟨base, off, len, cap⟩ := sl
  simp only [sliceVisibleValues]
  refine ExSim.bind (validateSlice_exsim ρ ⟨base, off, len, cap⟩) ?_
  intro _ _ _
  refine ExSim.bind
    (R := fun vs vsF => vsF = (renameValueList ρ vs.toList).toArray) ?_ ?_
  · rw [Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.forIn_eq_forIn_range']
    refine forIn_sim_same (by simp [renameValueList]) ?_
    intro i _ x y hxy
    subst hxy
    refine ExSim.bind (sliceIndexLoc_sim ρ ⟨base, off, len, cap⟩ (Int.ofNat i)) ?_
    intro l lF hlF
    subst hlF
    refine ExSim.bind (loadLoc_sim hS l) ?_
    intro v vF hvF
    subst hvF
    exact ExSim.ok (renArr_push x v)
  · intro vs vsF h
    exact ExSim.ok h

/-! ## `mapLookupValue` -/

theorem mapLookupValue_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (m : MapValue) (key : GoValue) (kt vt : Ty) :
    ExSim (fun p pF => pF = (renameValue ρ p.1, p.2))
      (mapLookupValue σ m key kt vt)
      (mapLookupValue σF { base := m.base.map (renameLoc ρ) }
        (renameValue ρ key) kt vt) := by
  simp only [mapLookupValue]
  refine ExSim.bind (mapEntries_sim hS m) ?_
  intro o oF hoF
  subst hoF
  cases o with
  | none =>
      simp only [Option.map_none]
      refine ExSim.bind (checkKeyHashable_sim (ρ := ρ) hS.types_eq key false false) ?_
      intro _ _ _
      refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq vt) ?_
      intro d dF hdF
      subst hdF
      exact ExSim.ok rfl
  | some p =>
      obtain ⟨bl, entries⟩ := p
      simp only [Option.map_some]
      refine ExSim.bind (mapEntryIndex?_sim hinj hS.types_eq kt entries key false) ?_
      intro i i' hi
      subst hi
      cases i with
      | none =>
          refine ExSim.bind (defaultValue_sim (ρ := ρ) hS.types_eq vt) ?_
          intro d dF hdF
          subst hdF
          exact ExSim.ok rfl
      | some idx =>
          dsimp only
          rw [renEntries_getElem?]
          cases hidx : entries[idx]? with
          | none => exact ExSim.stuck'
          | some e =>
              obtain ⟨k1, v1⟩ := e
              simp only [Option.map_some]
              exact ExSim.ok rfl

/-! ## `indexTargetLoc` -/

theorem indexTargetLoc_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (b i : GoValue) :
    ExSim (fun l lF => lF = renameLoc ρ l)
      (indexTargetLoc σ b i)
      (indexTargetLoc σF (renameValue ρ b) (renameValue ρ i)) := by
  simp only [indexTargetLoc]
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n n' hn
  subst hn
  cases b <;> simp only [renameValue]
  case slice sl => exact sliceIndexLoc_sim ρ sl n
  case nil => exact ExSim.panic
  case addr l =>
      refine ExSim.bind (loadLoc_sim hS l) ?_
      intro v vF hvF
      subst hvF
      cases v <;> simp only [renameValue]
      case array vals =>
          rw [arrayIndexNat_ren]
          refine ExSim.bind (ExSim.refl _) ?_
          intro _ _ h
          subst h
          exact ExSim.ok rfl
      case slice sl => exact sliceIndexLoc_sim ρ sl n
      all_goals exact ExSim.stuck'
  all_goals exact ExSim.stuck'

/-! ## `applySlice` -/

theorem applySlice_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (b : GoValue) (lo hi : Int) (m : Option Int) :
    ExSim (fun (r rF : GoValue × ExecState) =>
        rF.1 = renameValue ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
      (applySlice σ b lo hi m)
      (applySlice σF (renameValue ρ b) lo hi m) := by
  simp only [applySlice]
  cases b <;> simp only [renameValue]
  case string gs => exact scalar_pair hS (stringSlice_ren_sim ρ gs lo hi m)
  case slice sl => exact scalar_pair hS (sliceFromSlice_sim ρ sl lo hi m)
  case addr l =>
      refine ExSim.bind (loadLoc_sim hS l) ?_
      intro v vF hvF
      subst hvF
      cases v <;> simp only [renameValue]
      case array vals =>
          rw [renArr_size]
          exact scalar_pair hS (sliceFromArray_sim ρ l vals.size lo hi m)
      case slice sl => exact scalar_pair hS (sliceFromSlice_sim ρ sl lo hi m)
      all_goals exact ExSim.stuck'
  case array vals => exact ExSim.unsupported'
  all_goals exact ExSim.stuck'

/-! ## Scalar operator helpers: panic-freedom, ok-shape, transfer

The int/float operator helpers error only with `stuck`/`unsupported`
and produce loc-free (`.int`/`.float`) ok-results, so their `ExSim`
facts follow from the `Compare.lean` ok-transfers with no value-shape
case explosion. -/

private theorem valueAsIntValue_noPanic (v : GoValue) :
    NoPanic (valueAsIntValue v) := by
  cases v <;> first | exact NoPanic.pure' | exact NoPanic.stuck'

private theorem intBinaryResult_noPanic (nm : String) (op : Int → Int → Int)
    (l r : GoValue) : NoPanic (intBinaryResult nm op l r) := by
  unfold intBinaryResult
  refine NoPanic.bind (valueAsIntValue_noPanic l) fun p => ?_
  split
  refine NoPanic.bind (valueAsIntValue_noPanic r) fun q => ?_
  split
  split
  · exact NoPanic.bind NoPanic.pure' fun _ => NoPanic.pure'
  · exact NoPanic.bind NoPanic.stuck' fun _ => NoPanic.pure'

private theorem intBinaryResult_ok (ρ : Nat → Nat) {nm : String}
    {op : Int → Int → Int} {l r v : GoValue}
    (h : intBinaryResult nm op l r = .ok v) : renameValue ρ v = v := by
  simp only [intBinaryResult, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, -, ⟨rv, rk⟩, -, h⟩ := h
  split at h
  · simp only [Bind.bind, Except.bind, Except.ok.injEq] at h
    subst h
    simp [renameValue]
  · simp [Bind.bind, Except.bind] at h

private theorem intBinaryResult_sim (ρ : Nat → Nat) {nm : String}
    {op : Int → Int → Int} {l r lF rF : GoValue}
    (hl : lF = renameValue ρ l) (hr : rF = renameValue ρ r) :
    ExSim (fun a b => b = renameValue ρ a)
      (intBinaryResult nm op l r) (intBinaryResult nm op lF rF) := by
  subst hl hr
  refine exSim_of_ren (intBinaryResult_noPanic nm op l r) ?_
  intro a ha
  rw [intBinaryResult_ren ρ ha, intBinaryResult_ok ρ ha]

private theorem intKindBitWidth_noPanic (nm : String) (k : IntKind) :
    NoPanic (intKindBitWidth nm k) := by
  unfold intKindBitWidth
  split
  · exact NoPanic.pure'
  · exact NoPanic.unsupported'

private theorem intKindUnsignedNat_noPanic (k : IntKind) (v : Int) :
    NoPanic (intKindUnsignedNat k v) := by
  unfold intKindUnsignedNat
  exact NoPanic.bind (intKindBitWidth_noPanic _ _) fun _ => NoPanic.pure'

private theorem intBitwiseBinaryResult_noPanic (nm : String)
    (op : Nat → Nat → Nat) (l r : GoValue) :
    NoPanic (intBitwiseBinaryResult nm op l r) := by
  unfold intBitwiseBinaryResult
  refine NoPanic.bind (valueAsIntValue_noPanic l) fun p => ?_
  split
  refine NoPanic.bind (valueAsIntValue_noPanic r) fun q => ?_
  split
  split
  · refine NoPanic.bind NoPanic.pure' fun kind => ?_
    refine NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => ?_
    exact NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => NoPanic.pure'
  · refine NoPanic.bind NoPanic.stuck' fun kind => ?_
    refine NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => ?_
    exact NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => NoPanic.pure'

private theorem intBitwiseBinaryResult_ok (ρ : Nat → Nat) {nm : String}
    {op : Nat → Nat → Nat} {l r v : GoValue}
    (h : intBitwiseBinaryResult nm op l r = .ok v) : renameValue ρ v = v := by
  simp only [intBitwiseBinaryResult, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, -, ⟨rv, rk⟩, -, h⟩ := h
  split at h
  · simp only [bind_eq_ok, Except.ok.injEq] at h
    obtain ⟨a, -, lb, -, rb, -, h⟩ := h
    subst h
    simp [renameValue]
  · simp [Bind.bind, Except.bind] at h

private theorem intBitwiseBinaryResult_sim (ρ : Nat → Nat) {nm : String}
    {op : Nat → Nat → Nat} (l r : GoValue) :
    ExSim (fun a b => b = renameValue ρ a)
      (intBitwiseBinaryResult nm op l r)
      (intBitwiseBinaryResult nm op (renameValue ρ l) (renameValue ρ r)) := by
  refine exSim_of_ren (intBitwiseBinaryResult_noPanic nm op l r) ?_
  intro a ha
  rw [intBitwiseBinaryResult_ren ρ ha, intBitwiseBinaryResult_ok ρ ha]

private theorem intBitClearResult_noPanic (l r : GoValue) :
    NoPanic (intBitClearResult l r) := by
  unfold intBitClearResult
  refine NoPanic.bind (valueAsIntValue_noPanic l) fun p => ?_
  split
  refine NoPanic.bind (valueAsIntValue_noPanic r) fun q => ?_
  split
  split
  · refine NoPanic.bind NoPanic.pure' fun kind => ?_
    refine NoPanic.bind (intKindBitWidth_noPanic _ _) fun _ => ?_
    refine NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => ?_
    exact NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => NoPanic.pure'
  · refine NoPanic.bind NoPanic.stuck' fun kind => ?_
    refine NoPanic.bind (intKindBitWidth_noPanic _ _) fun _ => ?_
    refine NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => ?_
    exact NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => NoPanic.pure'

private theorem intBitClearResult_ok (ρ : Nat → Nat) {l r v : GoValue}
    (h : intBitClearResult l r = .ok v) : renameValue ρ v = v := by
  simp only [intBitClearResult, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨⟨lv, lk⟩, -, ⟨rv, rk⟩, -, h⟩ := h
  split at h
  · simp only [bind_eq_ok, Except.ok.injEq] at h
    obtain ⟨a, -, bits, -, lb, -, rb, -, h⟩ := h
    subst h
    simp [renameValue]
  · simp [Bind.bind, Except.bind] at h

private theorem intBitClearResult_sim (ρ : Nat → Nat) (l r : GoValue) :
    ExSim (fun a b => b = renameValue ρ a)
      (intBitClearResult l r)
      (intBitClearResult (renameValue ρ l) (renameValue ρ r)) := by
  refine exSim_of_ren (intBitClearResult_noPanic l r) ?_
  intro a ha
  rw [intBitClearResult_ren ρ ha, intBitClearResult_ok ρ ha]

private theorem intBitNegResult_noPanic (v : GoValue) :
    NoPanic (intBitNegResult v) := by
  unfold intBitNegResult
  refine NoPanic.bind (valueAsIntValue_noPanic v) fun p => ?_
  split
  refine NoPanic.bind (intKindBitWidth_noPanic _ _) fun _ => ?_
  exact NoPanic.bind (intKindUnsignedNat_noPanic _ _) fun _ => NoPanic.pure'

private theorem intBitNegResult_ok (ρ : Nat → Nat) {x v : GoValue}
    (h : intBitNegResult x = .ok v) : renameValue ρ v = v := by
  simp only [intBitNegResult, bind_eq_ok, pure_eq_ok, Except.ok.injEq] at h
  obtain ⟨⟨v0, k0⟩, -, bits, -, vb, -, h⟩ := h
  subst h
  simp [renameValue]

private theorem intBitNegResult_sim (ρ : Nat → Nat) (v : GoValue) :
    ExSim (fun a b => b = renameValue ρ a)
      (intBitNegResult v) (intBitNegResult (renameValue ρ v)) := by
  refine exSim_of_ren (intBitNegResult_noPanic v) ?_
  intro a ha
  rw [intBitNegResult_ren ρ ha, intBitNegResult_ok ρ ha]

private theorem floatBinaryResult_ok (ρ : Nat → Nat) {nm : String}
    {op64 op32 : Nat → Nat → Nat} {l r v : GoValue}
    (h : floatBinaryResult nm op64 op32 l r = .ok v) : renameValue ρ v = v := by
  unfold floatBinaryResult at h
  split at h
  · split at h
    · split at h <;>
        (simp only [pure_eq_ok, Except.ok.injEq] at h
         subst h
         simp [renameValue])
    · simp at h
  · simp at h

/-! ## Ordering comparisons -/

private theorem floatCompareResult_noPanic (nm : String)
    (c64 c32 : Nat → Nat → Bool) (l r : GoValue) :
    NoPanic (floatCompareResult nm c64 c32 l r) := by
  unfold floatCompareResult
  split
  · split
    · split <;> exact NoPanic.pure'
    · exact NoPanic.stuck'
  · exact NoPanic.stuck'

private theorem valueLess_noPanic (l r : GoValue) : NoPanic (valueLess l r) := by
  unfold valueLess
  split
  · exact NoPanic.pure'
  · exact floatCompareResult_noPanic _ _ _ _ _
  · exact NoPanic.pure'
  · exact NoPanic.stuck'

private theorem valueAtMost_noPanic (l r : GoValue) :
    NoPanic (valueAtMost l r) := by
  unfold valueAtMost
  split
  · exact NoPanic.pure'
  · exact floatCompareResult_noPanic _ _ _ _ _
  · exact NoPanic.pure'
  · exact NoPanic.stuck'

private theorem valueGreater_noPanic (l r : GoValue) :
    NoPanic (valueGreater l r) := by
  unfold valueGreater
  split
  · exact NoPanic.pure'
  · exact floatCompareResult_noPanic _ _ _ _ _
  · exact NoPanic.pure'
  · exact NoPanic.stuck'

private theorem valueAtLeast_noPanic (l r : GoValue) :
    NoPanic (valueAtLeast l r) := by
  unfold valueAtLeast
  split
  · exact NoPanic.pure'
  · exact floatCompareResult_noPanic _ _ _ _ _
  · exact NoPanic.pure'
  · exact NoPanic.stuck'

private theorem valueLess_sim (ρ : Nat → Nat) {l r lF rF : GoValue}
    (hl : lF = renameValue ρ l) (hr : rF = renameValue ρ r) :
    ExSim Eq (valueLess l r) (valueLess lF rF) := by
  subst hl hr
  exact exsim_eq_of_ren (valueLess_noPanic l r) fun _ hb => valueLess_ren ρ hb

private theorem valueAtMost_sim (ρ : Nat → Nat) (l r : GoValue) :
    ExSim Eq (valueAtMost l r)
      (valueAtMost (renameValue ρ l) (renameValue ρ r)) :=
  exsim_eq_of_ren (valueAtMost_noPanic l r) fun _ hb => valueAtMost_ren ρ hb

private theorem valueGreater_sim (ρ : Nat → Nat) (l r : GoValue) :
    ExSim Eq (valueGreater l r)
      (valueGreater (renameValue ρ l) (renameValue ρ r)) :=
  exsim_eq_of_ren (valueGreater_noPanic l r) fun _ hb => valueGreater_ren ρ hb

private theorem valueAtLeast_sim (ρ : Nat → Nat) (l r : GoValue) :
    ExSim Eq (valueAtLeast l r)
      (valueAtLeast (renameValue ρ l) (renameValue ρ r)) :=
  exsim_eq_of_ren (valueAtLeast_noPanic l r) fun _ hb => valueAtLeast_ren ρ hb

/-! ## Convert result transfer (ok via the rename lemma; the
slice→array length-check PANIC — triage L2a, 2026-08-19 — via
`convertValueToTy_panic_ren`; the `_noPanic` lemma this section
carried is retired: the length check made it false, and the arm proof
now transfers each result class directly.) -/

/-! ## Panic-freedom of `defaultValue` -/

private theorem defaultFieldsWith_noPanic {f : Ty → Except GoError GoValue}
    (hf : ∀ ty, NoPanic (f ty)) :
    ∀ fds : List FieldDef, NoPanic (defaultFieldsWith f fds) := by
  intro fds
  induction fds with
  | nil => exact NoPanic.pure'
  | cons fd rest ih =>
      simp only [defaultFieldsWith]
      exact NoPanic.bind (hf fd.typ) fun _ =>
        NoPanic.bind ih fun _ => NoPanic.pure'

private theorem defaultValueFuel_noPanic (σ₀ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty), NoPanic (defaultValueFuel fuel σ₀ ty) := by
  intro fuel
  induction fuel with
  | zero => intro ty; exact NoPanic.unsupported'
  | succ n ih =>
      intro ty
      cases ty
      case array len elem =>
          simp only [defaultValueFuel]
          refine NoPanic.ite' NoPanic.pure' ?_
          exact NoPanic.bind NoPanic.pure' fun _ =>
            NoPanic.bind (ih elem) fun _ => NoPanic.pure'
      case defined name =>
          simp only [defaultValueFuel]
          split
          · exact NoPanic.map (defaultFieldsWith_noPanic (fun ty => ih ty) _)
          · exact ih _
          · exact ih _
          · exact NoPanic.unsupported'
          · exact NoPanic.unsupported'
          · exact NoPanic.unsupported'
      all_goals first | exact NoPanic.pure' | exact NoPanic.unsupported'

private theorem defaultValue_noPanic (σ₀ : ExecState) (ty : Ty) :
    NoPanic (defaultValue σ₀ ty) := by
  rw [defaultValue]
  exact defaultValueFuel_noPanic σ₀ _ ty

/-! ## Panic-freedom of the struct/array literal builders -/

private theorem buildStructFields_noPanic (σ₀ : ExecState) :
    ∀ (fds : List FieldDef) (vs : List GoValue),
      NoPanic (buildStructFields σ₀ fds vs) := by
  intro fds
  induction fds with
  | nil => intro vs; exact NoPanic.pure'
  | cons fd rest ih =>
      intro vs
      cases vs with
      | nil => exact NoPanic.pure'
      | cons v vrest =>
          simp only [buildStructFields]
          exact NoPanic.bind (normalizeValueForTy_noPanic σ₀ _ _) fun _ =>
            NoPanic.bind (ih vrest) fun _ => NoPanic.pure'

private theorem buildStructValueFuel_noPanic (σ₀ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty) (args : Array GoValue),
      NoPanic (buildStructValueFuel fuel σ₀ ty args) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty args
      rw [buildStructValueFuel.eq_def]
      split <;>
        first
        | exact NoPanic.unsupported'
        | (rename_i heq; exact absurd heq.symm (Nat.succ_ne_zero _))
  | succ n ih =>
      intro ty args
      rw [buildStructValueFuel.eq_def]
      split <;>
        first
        | exact NoPanic.unsupported'
        | (rename_i heq; exact absurd heq (Nat.succ_ne_zero _))
        | skip
      all_goals (
        rename_i heq
        injection heq with hfe
        subst hfe
        split
        · -- struct: size guard (join point), then the field builder
          split
          · exact NoPanic.bind NoPanic.stuck' fun _ =>
              NoPanic.map (buildStructFields_noPanic _ _ _)
          · exact NoPanic.bind NoPanic.pure' fun _ =>
              NoPanic.map (buildStructFields_noPanic _ _ _)
        · exact ih _ _
        · exact NoPanic.unsupported'
        · exact NoPanic.unsupported'
        · exact NoPanic.unsupported'
        · exact NoPanic.unsupported')

private theorem buildStructValue_noPanic (σ₀ : ExecState) (ty : Ty)
    (args : Array GoValue) : NoPanic (buildStructValue σ₀ ty args) := by
  rw [buildStructValue]
  exact buildStructValueFuel_noPanic σ₀ _ ty args

/-- Panic-decomposition of `bind` (the error-side sibling of
`bind_eq_ok`, stated for exactly the panic error). -/
private theorem bind_eq_panic {α β : Type} {x : Except GoError α}
    {f : α → Except GoError β} {m : String} :
    (x >>= f = .error (.panic m))
      ↔ (x = .error (.panic m) ∨ ∃ a, x = .ok a ∧ f a = .error (.panic m)) := by
  cases x with
  | ok a => simp [Bind.bind, Except.bind]
  | error e => simp [Bind.bind, Except.bind]

/-- A panicking list-`forIn` has a panicking body step. -/
private theorem forIn_panic {α β : Type}
    {f : α → β → Except GoError (ForInStep β)} {m : String} :
    ∀ {l : List α} {b : β}, forIn l b f = .error (.panic m) →
      ∃ a ∈ l, ∃ x, f a x = .error (.panic m) := by
  intro l
  induction l with
  | nil =>
      intro b h
      rw [List.forIn_nil] at h
      simp [pure, Except.pure] at h
  | cons a as ih =>
      intro b h
      rw [List.forIn_cons] at h
      rcases bind_eq_panic.mp h with h1 | ⟨r, -, h2⟩
      · exact ⟨a, by simp, b, h1⟩
      · cases r with
        | done x => simp [pure, Except.pure] at h2
        | yield x =>
            obtain ⟨a', ha', x', hx'⟩ := ih h2
            exact ⟨a', by simp [ha'], x', hx'⟩

private theorem buildArrayValue_noPanic (σ₀ : ExecState) (len : Nat)
    (elem : Ty) (args : Array (Int × GoValue)) :
    NoPanic (buildArrayValue σ₀ len elem args) := by
  intro m h
  unfold buildArrayValue at h
  simp only [bind_eq_panic] at h
  rcases h with h | ⟨vs₁, -, h⟩
  · -- default-fill loop
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
    obtain ⟨i, -, x, hx⟩ := forIn_panic h
    simp only [bind_eq_panic] at hx
    rcases hx with h1 | ⟨d, -, h2⟩
    · exact defaultValue_noPanic σ₀ elem m h1
    · simp [bind_eq_panic] at h2
  · -- keyed-entry loop (the final pure is pruned by the outer simp)
    rw [← Array.forIn_toList] at h
    rcases h with h | ⟨st, -, hfin⟩
    · obtain ⟨p, -, x, hx⟩ := forIn_panic h
      obtain ⟨key, value⟩ := p
      split at hx
      · simp [bind_eq_panic] at hx
      · simp only [bind_eq_panic, pure_eq_ok, Except.ok.injEq,
          reduceCtorEq, false_or, exists_eq_left'] at hx
        split at hx
        · simp [bind_eq_panic] at hx
        · simp only [bind_eq_panic, pure_eq_ok, Except.ok.injEq,
            reduceCtorEq, false_or, exists_eq_left'] at hx
          split at hx
          · simp [bind_eq_panic] at hx
            rcases hx with h1 | ⟨nv, -, h2⟩
            · exact normalizeValueForTy_noPanic σ₀ elem value m h1
            · exact coerceStoredValue_noPanic _ _ m h2
          · simp [bind_eq_panic] at hx
    · simp [pure, Except.pure] at hfin

/-! ## `typeAssertValue` simulation and ok-false inversion -/

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

private theorem typeAssertValue_ok_false {σ₀ : ExecState} {v : GoValue}
    {ty : Ty} {r : GoValue}
    (h : typeAssertValue σ₀ v ty = .ok (r, false)) :
    v = .nil ∨ ∃ t i, v = .interface t i := by
  cases v
  case nil => exact Or.inl rfl
  case interface t i => exact Or.inr ⟨t, i, rfl⟩
  all_goals (
    exfalso
    simp only [typeAssertValue, bind_eq_ok] at h
    obtain ⟨d, -, hbad⟩ := h
    simp at hbad)

/-! ## The `applyStrictOp` arms -/

/-- The result relation of `applyStrictOp_sim`, locally named. -/
private abbrev PairSim (ρ : Nat → Nat) (na₀ na : Nat) (fr : Heap) :
    GoValue × ExecState → GoValue × ExecState → Prop :=
  fun r rF => rF.1 = renameValue ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2

set_option maxHeartbeats 1600000 in
private theorem arm_add (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .add [l, r])
      (applyStrictOp σF .add [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  cases l
  case int a ka =>
      cases r <;>
        first
        | exact ExSim.stuck'
        | (simp only [renameValue]
           exact scalar_pair hS (exsim_ren_self ρ fun v hv => intBinaryResult_ok ρ hv))
  case float lb lk =>
      cases r <;>
        first
        | exact ExSim.stuck'
        | (simp only [renameValue]
           exact scalar_pair hS (exsim_ren_self ρ fun v hv => floatBinaryResult_ok ρ hv))
  case string sa =>
      cases r <;>
        first
        | exact ExSim.stuck'
        | (simp only [renameValue]
           exact ExSim.ok ⟨by simp only [renameValue], hS⟩)
  all_goals exact ExSim.stuck'

set_option maxHeartbeats 1600000 in
private theorem arm_sub (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .sub [l, r])
      (applyStrictOp σF .sub [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  cases l
  case float lb lk =>
      cases r <;> simp only [renameValue] <;>
        first
        | exact scalar_pair hS (exsim_ren_self ρ fun v hv => floatBinaryResult_ok ρ hv)
        | exact scalar_pair hS
            (intBinaryResult_sim ρ (by simp [renameValue]) (by simp [renameValue]))
  all_goals (
    simp only [renameValue]
    exact scalar_pair hS
      (intBinaryResult_sim ρ (by simp [renameValue]) rfl))

set_option maxHeartbeats 1600000 in
private theorem arm_mul (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .mul [l, r])
      (applyStrictOp σF .mul [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  cases l
  case float lb lk =>
      cases r <;> simp only [renameValue] <;>
        first
        | exact scalar_pair hS (exsim_ren_self ρ fun v hv => floatBinaryResult_ok ρ hv)
        | exact scalar_pair hS
            (intBinaryResult_sim ρ (by simp [renameValue]) (by simp [renameValue]))
  all_goals (
    simp only [renameValue]
    exact scalar_pair hS
      (intBinaryResult_sim ρ (by simp [renameValue]) rfl))

set_option maxHeartbeats 1600000 in
private theorem arm_div (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .div [l, r])
      (applyStrictOp σF .div [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  cases l <;>
    first
    | -- non-float rows: the default arm with `r` general
      (simp only [renameValue]
       refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
       intro d d' hd
       subst hd
       by_cases hz : (d == 0) = true
       · rw [if_pos hz, if_pos hz]
         exact ExSim.panic
       · rw [if_neg hz, if_neg hz]
         simp only [pure_bind]
         exact scalar_pair hS
           (intBinaryResult_sim ρ (by simp [renameValue]) rfl))
    | -- float row: split on r for the float×float arm
      (cases r <;> simp only [renameValue] <;>
        first
        | exact scalar_pair hS (exsim_ren_self ρ fun v hv => floatBinaryResult_ok ρ hv)
        | (refine ExSim.bind (valueAsInt_sim ρ (by simp [renameValue])) ?_
           intro d d' hd
           subst hd
           by_cases hz : (d == 0) = true
           · rw [if_pos hz, if_pos hz]
             exact ExSim.panic
           · rw [if_neg hz, if_neg hz]
             simp only [pure_bind]
             exact scalar_pair hS
               (intBinaryResult_sim ρ (by simp [renameValue]) (by simp [renameValue]))))

private theorem arm_mod (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .mod [l, r])
      (applyStrictOp σF .mod [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro d d' hd
  subst hd
  by_cases hz : (d == 0) = true
  · rw [if_pos hz, if_pos hz]
    exact ExSim.panic
  · rw [if_neg hz, if_neg hz]
    simp only [pure_bind]
    exact scalar_pair hS (intBinaryResult_sim ρ rfl rfl)

private theorem arm_shiftLeft (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .shiftLeft [l, r])
      (applyStrictOp σF .shiftLeft [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intShiftLeftResult_sim ρ l r)

private theorem arm_shiftRight (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .shiftRight [l, r])
      (applyStrictOp σF .shiftRight [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intShiftRightResult_sim ρ l r)

private theorem arm_bitAnd (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .bitAnd [l, r])
      (applyStrictOp σF .bitAnd [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intBitwiseBinaryResult_sim ρ l r)

private theorem arm_bitOr (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .bitOr [l, r])
      (applyStrictOp σF .bitOr [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intBitwiseBinaryResult_sim ρ l r)

private theorem arm_bitXor (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .bitXor [l, r])
      (applyStrictOp σF .bitXor [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intBitwiseBinaryResult_sim ρ l r)

private theorem arm_bitClear (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .bitClear [l, r])
      (applyStrictOp σF .bitClear [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intBitClearResult_sim ρ l r)

private theorem arm_bitNeg (hS : FrameSim ρ na₀ na fr σ σF) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .bitNeg [v])
      (applyStrictOp σF .bitNeg [renameValue ρ v]) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (intBitNegResult_sim ρ v)

private theorem arm_neg (hS : FrameSim ρ na₀ na fr σ σF) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .neg [v])
      (applyStrictOp σF .neg [renameValue ρ v]) := by
  simp only [applyStrictOp]
  cases v <;> simp only [renameValue] <;>
    first
    | exact ExSim.stuck'
    | exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_not (hS : FrameSim ρ na₀ na fr σ σF) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .not [v])
      (applyStrictOp σF .not [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsBool_sim ρ v) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_floatLit (hS : FrameSim ρ na₀ na fr σ σF)
    (num : Int) (den : Nat) (kind : FloatKind) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.floatLit num den kind) [])
      (applyStrictOp σF (.floatLit num den kind) []) := by
  simp only [applyStrictOp]
  by_cases hd : (den == 0) = true
  · rw [if_pos hd, if_pos hd]
    exact ExSim.stuck'
  · rw [if_neg hd, if_neg hd]
    exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_eq (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (ty : Ty) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.eqCmp ty) [l, r])
      (applyStrictOp σF (.eqCmp ty) [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueEq_sim hinj hS.types_eq ty l r) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_neq (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y) (ty : Ty) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.neqCmp ty) [l, r])
      (applyStrictOp σF (.neqCmp ty) [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueEq_sim hinj hS.types_eq ty l r) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_atMost (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .atMostCmp [l, r])
      (applyStrictOp σF .atMostCmp [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAtMost_sim ρ l r) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_atLeast (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .atLeastCmp [l, r])
      (applyStrictOp σF .atLeastCmp [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAtLeast_sim ρ l r) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_less (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .lessCmp [l, r])
      (applyStrictOp σF .lessCmp [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueLess_sim ρ rfl rfl) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_greater (hS : FrameSim ρ na₀ na fr σ σF) (l r : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .greaterCmp [l, r])
      (applyStrictOp σF .greaterCmp [renameValue ρ l, renameValue ρ r]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueGreater_sim ρ l r) ?_
  intro b b' hb
  subst hb
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_convert (hS : FrameSim ρ na₀ na fr σ σF)
    (ty : Ty) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.convert ty) [v])
      (applyStrictOp σF (.convert ty) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine scalar_pair hS ?_
  cases hx : convertValueToTy σ ty v with
  | ok a =>
      rw [convertValueToTy_ren ρ hS.types_eq hx]
      exact ExSim.ok rfl
  | error e =>
      cases e with
      | panic m =>
          -- The slice→array(-pointer) length check (triage L2a): the
          -- message embeds `len` and the target length only, both
          -- rename-invariant. `ExSim` at a canonical panic IS the
          -- framed-side equation, which is the transfer lemma verbatim.
          exact convertValueToTy_panic_ren ρ hS.types_eq hx
      | _ => trivial

private theorem arm_bytesFromString (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .bytesFromString [v])
      (applyStrictOp σF .bytesFromString [renameValue ρ v]) := by
  simp only [applyStrictOp]
  cases v <;> simp only [renameValue]
  case string gs =>
      have hb : renameValue ρ
          (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
          = .array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8) := by
        simp only [renameValue, renameValueList_eq_map, Array.toList_map,
          List.map_map]
        congr 1
        apply Array.toList_inj.mp
        simp [Function.comp_def, renameValue]
      have h1 : (σF.alloc
            (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
            (some (.array (gs.bytes.map fun b =>
              GoValue.int (Int.ofNat b.toNat) .uint8).size (.int .uint8)))).1
          = renameLoc ρ ((σ.alloc
            (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
            (some (.array (gs.bytes.map fun b =>
              GoValue.int (Int.ofNat b.toNat) .uint8).size (.int .uint8)))).1) := by
        have h := hS.alloc_fst
          (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
          (some (.array (gs.bytes.map fun b =>
            GoValue.int (Int.ofNat b.toNat) .uint8).size (.int .uint8)))
        rwa [hb] at h
      have h2 : FrameSim ρ na₀ na fr
          (σ.alloc
            (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
            (some (.array (gs.bytes.map fun b =>
              GoValue.int (Int.ofNat b.toNat) .uint8).size (.int .uint8)))).2
          (σF.alloc
            (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
            (some (.array (gs.bytes.map fun b =>
              GoValue.int (Int.ofNat b.toNat) .uint8).size (.int .uint8)))).2 := by
        have := hS.alloc_snd
          (.array (gs.bytes.map fun b => GoValue.int (Int.ofNat b.toNat) .uint8))
          (some (.array (gs.bytes.map fun b =>
            GoValue.int (Int.ofNat b.toNat) .uint8).size (.int .uint8)))
        rwa [hb] at this
      exact ExSim.ok ⟨by simp only [renameValue, Option.map_some, h1], h2⟩
  all_goals exact ExSim.stuck'

private theorem arm_stringFromByteSlice (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .stringFromByteSlice [v])
      (applyStrictOp σF .stringFromByteSlice [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsSlice_sim ρ v) ?_
  intro sl slF hslF
  subst hslF
  refine ExSim.bind (sliceVisibleValues_sim hS sl) ?_
  intro vs vsF hvsF
  subst hvsF
  refine ExSim.bind (R := Eq) ?_ ?_
  · rw [← Array.forIn_toList, ← Array.forIn_toList, List.toList_toArray,
      renameValueList_eq_map]
    refine forIn_sim (t := renameValue ρ) rfl ?_
    intro a _ x y hxy
    subst hxy
    cases a <;>
      first
      | exact ExSim.stuck'
      | (simp only [renameValue]; exact exsim_stepSim_refl _)
  · intro b b' hb
    subst hb
    exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_stringFromRune (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .stringFromRune [v])
      (applyStrictOp σF .stringFromRune [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n n' hn
  subst hn
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_runesFromString (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .runesFromString [v])
      (applyStrictOp σF .runesFromString [renameValue ρ v]) := by
  simp only [applyStrictOp]
  cases v <;> simp only [renameValue]
  case string gs =>
      have hb : renameValue ρ
          (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
          = .array ((runesOfString gs).map fun r => GoValue.int r .int32) := by
        simp only [renameValue, renameValueList_eq_map, Array.toList_map,
          List.map_map]
        congr 1
        apply Array.toList_inj.mp
        simp [Function.comp_def, renameValue]
      have h1 : (σF.alloc
            (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
            (some (.array ((runesOfString gs).map fun r =>
              GoValue.int r .int32).size (.int .int32)))).1
          = renameLoc ρ ((σ.alloc
            (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
            (some (.array ((runesOfString gs).map fun r =>
              GoValue.int r .int32).size (.int .int32)))).1) := by
        have h := hS.alloc_fst
          (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
          (some (.array ((runesOfString gs).map fun r =>
            GoValue.int r .int32).size (.int .int32)))
        rwa [hb] at h
      have h2 : FrameSim ρ na₀ na fr
          (σ.alloc
            (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
            (some (.array ((runesOfString gs).map fun r =>
              GoValue.int r .int32).size (.int .int32)))).2
          (σF.alloc
            (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
            (some (.array ((runesOfString gs).map fun r =>
              GoValue.int r .int32).size (.int .int32)))).2 := by
        have := hS.alloc_snd
          (.array ((runesOfString gs).map fun r => GoValue.int r .int32))
          (some (.array ((runesOfString gs).map fun r =>
            GoValue.int r .int32).size (.int .int32)))
        rwa [hb] at this
      exact ExSim.ok ⟨by simp only [renameValue, Option.map_some, h1], h2⟩
  all_goals exact ExSim.stuck'

private theorem arm_stringFromRuneSlice (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .stringFromRuneSlice [v])
      (applyStrictOp σF .stringFromRuneSlice [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsSlice_sim ρ v) ?_
  intro sl slF hslF
  subst hslF
  refine ExSim.bind (sliceVisibleValues_sim hS sl) ?_
  intro vs vsF hvsF
  subst hvsF
  refine ExSim.bind (R := Eq) ?_ ?_
  · rw [← Array.forIn_toList, ← Array.forIn_toList, List.toList_toArray,
      renameValueList_eq_map]
    refine forIn_sim (t := renameValue ρ) rfl ?_
    intro a _ x y hxy
    subst hxy
    cases a <;>
      first
      | exact ExSim.stuck'
      | (simp only [renameValue]; exact exsim_stepSim_refl _)
  · intro b b' hb
    subst hb
    exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_deref (hS : FrameSim ρ na₀ na fr σ σF)
    (ty : Ty) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.deref ty) [v])
      (applyStrictOp σF (.deref ty) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsLoc_sim ρ v) ?_
  intro l lF hl
  subst hl
  exact scalar_pair hS (loadLoc_sim hS l)

private theorem arm_fieldGet (hS : FrameSim ρ na₀ na fr σ σF)
    (tid : TypeId) (fname : String) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.fieldGet tid fname) [v])
      (applyStrictOp σF (.fieldGet tid fname) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  cases v <;> simp only [renameValue]
  case struct actual fields =>
      by_cases hne : (actual != tid) = true
      · rw [if_pos hne]
        exact ExSim.stuck'
      · rw [if_neg hne, if_neg hne]
        simp only [pure_bind]
        rw [structFieldsLookup_ren]
        cases StructFields.lookup fields fname with
        | none => exact ExSim.stuck'
        | some fv => exact ExSim.ok ⟨rfl, hS⟩
  all_goals exact ExSim.stuck'

private theorem arm_fieldAddr (hS : FrameSim ρ na₀ na fr σ σF)
    (tid : TypeId) (fname : String) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.fieldAddr tid fname) [v])
      (applyStrictOp σF (.fieldAddr tid fname) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsLoc_sim ρ v) ?_
  intro l lF hl
  subst hl
  exact ExSim.ok ⟨by simp only [renameValue, renameLoc], hS⟩

private theorem arm_addrOfDeref (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .addrOfDeref [v])
      (applyStrictOp σF .addrOfDeref [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsLoc_sim ρ v) ?_
  intro l lF hl
  subst hl
  exact ExSim.ok ⟨by simp only [renameValue, renameLoc], hS⟩

private theorem arm_structLit (hS : FrameSim ρ na₀ na fr σ σF)
    (ty : Ty) (vs : List GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.structLit ty) vs)
      (applyStrictOp σF (.structLit ty) (renameValueList ρ vs)) := by
  simp only [applyStrictOp]
  refine scalar_pair hS ?_
  refine exSim_of_ren (buildStructValue_noPanic σ ty vs.toArray) ?_
  intro a ha
  have := buildStructValue_ren ρ hS.types_eq (args := vs.toArray) ha
  simpa [List.toList_toArray] using this

private theorem arm_arrayLit (hS : FrameSim ρ na₀ na fr σ σF)
    (n : Nat) (elem : Ty) (keys : List Int) (vs : List GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.arrayLit n elem keys) vs)
      (applyStrictOp σF (.arrayLit n elem keys) (renameValueList ρ vs)) := by
  simp only [applyStrictOp]
  rw [renameValueList_length ρ vs]
  by_cases hlen : (keys.length != vs.length) = true
  · rw [if_pos hlen]
    exact ExSim.stuck'
  · rw [if_neg hlen, if_neg hlen]
    simp only [pure_bind]
    refine scalar_pair hS ?_
    refine exSim_of_ren (buildArrayValue_noPanic σ n elem (keys.zip vs).toArray) ?_
    intro a ha
    have harg : (keys.zip (renameValueList ρ vs)).toArray
        = renameValueEntriesKeyed ρ ((keys.zip vs).toArray) := by
      simp [renameValueEntriesKeyed, renameValueList_eq_map,
        List.zip_map_right, Function.comp_def, Prod.map]
    rw [harg]
    exact buildArrayValue_ren ρ hS.types_eq ha

private theorem arm_toInterface (hS : FrameSim ρ na₀ na fr σ σF)
    (tgt dyn : Ty) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.toInterface tgt dyn) [v])
      (applyStrictOp σF (.toInterface tgt dyn) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  rw [canonicalDynamicTy_congr hS.types_eq]
  refine ExSim.bind (ExSim.refl _) ?_
  intro t t' ht
  subst ht
  cases t <;>
    first
    | exact ExSim.ok ⟨rfl, hS⟩
    | exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_typeAssert (hS : FrameSim ρ na₀ na fr σ σF)
    (tgt : Ty) (srcTy : Option Ty) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.typeAssert tgt srcTy) [v])
      (applyStrictOp σF (.typeAssert tgt srcTy) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  refine exSim_bind_ok (typeAssertValue_sim hS v tgt) ?_
  intro p pF hok hrel
  subst hrel
  obtain ⟨r, ok⟩ := p
  cases ok
  case true => exact ExSim.ok ⟨rfl, hS⟩
  case false =>
      have hshape := typeAssertValue_ok_false hok
      rw [resolveDefinedAliases_congr hS.types_eq]
      rcases hshape with rfl | ⟨t, i, rfl⟩
      · -- nil operand
        have hmsg : ∀ ms, typeAssertPanicMessage σF .nil tgt srcTy ms
            = typeAssertPanicMessage σ .nil tgt srcTy ms := by
          intro ms
          simpa [renameValue] using
            typeAssertPanicMessage_ren ρ hS.types_eq (v := .nil)
              (tgt := tgt) (src := srcTy) (missing := ms) (Or.inl rfl)
        simp only [renameValue]
        cases hres : resolveDefinedAliases σ tgt <;>
          (refine ExSim.bind (ExSim.refl _) ?_
           intro ms ms' hms
           subst hms
           rw [hmsg ms]
           exact ExSim.panic)
      · -- interface operand
        have hmsg : ∀ ms,
            typeAssertPanicMessage σF (.interface t (renameValue ρ i)) tgt srcTy ms
              = typeAssertPanicMessage σ (.interface t i) tgt srcTy ms := by
          intro ms
          simpa [renameValue] using
            typeAssertPanicMessage_ren ρ hS.types_eq (v := .interface t i)
              (tgt := tgt) (src := srcTy) (missing := ms) (Or.inr ⟨t, i, rfl⟩)
        simp only [renameValue]
        cases hres : resolveDefinedAliases σ tgt
        case interface iname =>
            dsimp only
            rw [firstUnsatisfiedMethod?_congr hS.types_eq hS.methods_eq
              hS.funcs_eq hS.methodSets_eq]
            refine ExSim.bind (ExSim.refl _) ?_
            intro ms ms' hms
            subst hms
            rw [hmsg ms]
            exact ExSim.panic
        all_goals (
          refine ExSim.bind (ExSim.refl _) ?_
          intro ms ms' hms
          subst hms
          rw [hmsg ms]
          exact ExSim.panic)

private theorem arm_indexGet (hS : FrameSim ρ na₀ na fr σ σF)
    (b i : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .indexGet [b, i])
      (applyStrictOp σF .indexGet [renameValue ρ b, renameValue ρ i]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n n' hn
  subst hn
  cases b <;> simp only [renameValue]
  case array vals => exact scalar_pair hS (arrayGet_sim ρ vals n)
  case string gs => exact scalar_pair hS (stringByteGet_sim ρ gs n)
  case slice sl =>
      refine ExSim.bind (sliceIndexLoc_sim ρ sl n) ?_
      intro l lF hl
      subst hl
      exact scalar_pair hS (loadLoc_sim hS l)
  all_goals exact ExSim.stuck'

private theorem arm_indexAddr (hS : FrameSim ρ na₀ na fr σ σF)
    (b i : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .indexAddr [b, i])
      (applyStrictOp σF .indexAddr [renameValue ρ b, renameValue ρ i]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (indexTargetLoc_sim hS b i) ?_
  intro l lF hl
  subst hl
  exact ExSim.ok ⟨by simp only [renameValue], hS⟩

private theorem arm_mapGet (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (kt vt : Ty) (b i : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.mapGet kt vt) [b, i])
      (applyStrictOp σF (.mapGet kt vt) [renameValue ρ b, renameValue ρ i]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsMap_sim ρ b) ?_
  intro mp mpF hmp
  subst hmp
  refine ExSim.bind (normalizeValueForTy_sim hS.types_eq kt i) ?_
  intro k kF hk
  subst hk
  obtain ⟨mb⟩ := mp
  cases mb with
  | none =>
      simp only [Option.map_none]
      refine ExSim.bind (checkKeyHashable_sim (ρ := ρ) hS.types_eq k false false) ?_
      intro _ _ _
      exact scalar_pair hS (defaultValue_sim hS.types_eq vt)
  | some bl =>
      simp only [Option.map_some]
      refine ExSim.bind (loadLoc_sim hS bl) ?_
      intro w wF hw
      subst hw
      cases w <;> simp only [renameValue]
      case mapData entries =>
          refine ExSim.bind (mapEntryIndex?_sim hinj hS.types_eq kt entries k false) ?_
          intro o o' ho
          subst ho
          cases o with
          | none => exact scalar_pair hS (defaultValue_sim hS.types_eq vt)
          | some idx =>
              dsimp only
              rw [renEntries_getElem?]
              cases hidx : entries[idx]? with
              | none => exact ExSim.stuck'
              | some e =>
                  obtain ⟨k1, v1⟩ := e
                  simp only [Option.map_some]
                  exact ExSim.ok ⟨rfl, hS⟩
      all_goals exact ExSim.stuck'

private theorem arm_slice3 (hS : FrameSim ρ na₀ na fr σ σF)
    (b lo hi : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.sliceExpr false) [b, lo, hi])
      (applyStrictOp σF (.sliceExpr false)
        [renameValue ρ b, renameValue ρ lo, renameValue ρ hi]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n1 n1' h1
  subst h1
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n2 n2' h2
  subst h2
  exact applySlice_sim hS b n1 n2 none

private theorem arm_slice4 (hS : FrameSim ρ na₀ na fr σ σF)
    (b lo hi mx : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.sliceExpr true) [b, lo, hi, mx])
      (applyStrictOp σF (.sliceExpr true)
        [renameValue ρ b, renameValue ρ lo, renameValue ρ hi,
          renameValue ρ mx]) := by
  simp only [applyStrictOp]
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n1 n1' h1
  subst h1
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n2 n2' h2
  subst h2
  refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
  intro n3 n3' h3
  subst h3
  exact applySlice_sim hS b n1 n2 (some n3)

private theorem arm_length_body (hS : FrameSim ρ na₀ na fr σ σF) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.lengthOf none) [v])
      (applyStrictOp σF (.lengthOf none) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  cases v <;> simp only [renameValue]
  case string gs => exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  case addr l =>
      refine ExSim.bind (loadLoc_sim hS l) ?_
      intro w wF hw
      subst hw
      cases w <;> simp only [renameValue]
      case array vals =>
          rw [renArr_size]
          exact ExSim.ok ⟨by simp only [renameValue], hS⟩
      all_goals exact ExSim.unsupported'
  case array vals =>
      rw [renArr_size]
      exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  case slice sl =>
      obtain ⟨sb, so, sln, scp⟩ := sl
      refine ExSim.bind (validateSlice_exsim ρ ⟨sb, so, sln, scp⟩) ?_
      intro _ _ _
      exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  case map mp =>
      obtain ⟨mb⟩ := mp
      cases mb with
      | none => exact ExSim.ok ⟨by simp only [renameValue], hS⟩
      | some bl =>
          simp only [Option.map_some]
          refine ExSim.bind (loadLoc_sim hS bl) ?_
          intro w wF hw
          subst hw
          cases w <;> simp only [renameValue]
          case mapData es =>
              rw [renEntries_size]
              exact ExSim.ok ⟨by simp only [renameValue], hS⟩
          all_goals exact ExSim.stuck'
  case chan c =>
      obtain ⟨cb⟩ := c
      cases cb with
      | none => exact ExSim.ok ⟨by simp only [renameValue], hS⟩
      | some bl =>
          simp only [Option.map_some]
          refine ExSim.bind (loadLoc_sim hS bl) ?_
          intro w wF hw
          subst hw
          cases w <;> simp only [renameValue]
          case chanData buf cap closed =>
              rw [renArr_size]
              exact ExSim.ok ⟨by simp only [renameValue], hS⟩
          all_goals exact ExSim.stuck'
  all_goals exact ExSim.unsupported'

private theorem arm_length (hS : FrameSim ρ na₀ na fr σ σF)
    (typ : Option Ty) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.lengthOf typ) [v])
      (applyStrictOp σF (.lengthOf typ) [renameValue ρ v]) := by
  rcases typ with _ | ty
  · exact arm_length_body hS v
  · cases ty
    case pointer elem =>
        cases elem
        case array n e =>
            simp only [applyStrictOp]
            exact ExSim.ok ⟨by simp only [renameValue], hS⟩
        all_goals exact arm_length_body hS v
    all_goals exact arm_length_body hS v

private theorem arm_capacity_body (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.capacityOf none) [v])
      (applyStrictOp σF (.capacityOf none) [renameValue ρ v]) := by
  simp only [applyStrictOp]
  cases v <;> simp only [renameValue]
  case addr l =>
      refine ExSim.bind (loadLoc_sim hS l) ?_
      intro w wF hw
      subst hw
      cases w <;> simp only [renameValue]
      case array vals =>
          rw [renArr_size]
          exact ExSim.ok ⟨by simp only [renameValue], hS⟩
      all_goals exact ExSim.unsupported'
  case array vals =>
      rw [renArr_size]
      exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  case slice sl =>
      obtain ⟨sb, so, sln, scp⟩ := sl
      refine ExSim.bind (validateSlice_exsim ρ ⟨sb, so, sln, scp⟩) ?_
      intro _ _ _
      exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  case chan c =>
      obtain ⟨cb⟩ := c
      cases cb with
      | none => exact ExSim.ok ⟨by simp only [renameValue], hS⟩
      | some bl =>
          simp only [Option.map_some]
          refine ExSim.bind (loadLoc_sim hS bl) ?_
          intro w wF hw
          subst hw
          cases w <;> simp only [renameValue]
          case chanData buf cap closed =>
              exact ExSim.ok ⟨by simp only [renameValue], hS⟩
          all_goals exact ExSim.stuck'
  all_goals exact ExSim.unsupported'

private theorem arm_capacity (hS : FrameSim ρ na₀ na fr σ σF)
    (typ : Option Ty) (v : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.capacityOf typ) [v])
      (applyStrictOp σF (.capacityOf typ) [renameValue ρ v]) := by
  rcases typ with _ | ty
  · exact arm_capacity_body hS v
  · cases ty
    case pointer elem =>
        cases elem
        case array n e =>
            simp only [applyStrictOp]
            exact ExSim.ok ⟨by simp only [renameValue], hS⟩
        all_goals exact arm_capacity_body hS v
    all_goals exact arm_capacity_body hS v

private theorem arm_min (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) (vs : List GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .minOf (v :: vs))
      (applyStrictOp σF .minOf (renameValue ρ v :: renameValueList ρ vs)) := by
  simp only [applyStrictOp]
  have hfl : anyFloatOperand (renameValue ρ v :: renameValueList ρ vs)
      = anyFloatOperand (v :: vs) := by
    simpa [renameValueList] using anyFloatOperand_ren ρ (v :: vs)
  rw [hfl]
  by_cases hf : anyFloatOperand (v :: vs) = true
  · rw [if_pos hf, if_pos hf]
    exact ExSim.unsupported'
  · rw [if_neg hf, if_neg hf]
    refine ExSim.bind (R := fun b b' => b' = renameValue ρ b) ?_ ?_
    · rw [renameValueList_eq_map]
      refine forIn_sim rfl ?_
      intro w _ x y hxy
      subst hxy
      refine ExSim.bind (valueLess_sim ρ rfl rfl) ?_
      intro c c' hc
      subst hc
      cases c
      · exact ExSim.ok rfl
      · exact ExSim.ok rfl
    · intro b b' hb
      exact ExSim.ok ⟨hb, hS⟩

private theorem arm_max (hS : FrameSim ρ na₀ na fr σ σF)
    (v : GoValue) (vs : List GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .maxOf (v :: vs))
      (applyStrictOp σF .maxOf (renameValue ρ v :: renameValueList ρ vs)) := by
  simp only [applyStrictOp]
  have hfl : anyFloatOperand (renameValue ρ v :: renameValueList ρ vs)
      = anyFloatOperand (v :: vs) := by
    simpa [renameValueList] using anyFloatOperand_ren ρ (v :: vs)
  rw [hfl]
  by_cases hf : anyFloatOperand (v :: vs) = true
  · rw [if_pos hf, if_pos hf]
    exact ExSim.unsupported'
  · rw [if_neg hf, if_neg hf]
    refine ExSim.bind (R := fun b b' => b' = renameValue ρ b) ?_ ?_
    · rw [renameValueList_eq_map]
      refine forIn_sim rfl ?_
      intro w _ x y hxy
      subst hxy
      refine ExSim.bind (valueLess_sim ρ rfl rfl) ?_
      intro c c' hc
      subst hc
      cases c
      · exact ExSim.ok rfl
      · exact ExSim.ok rfl
    · intro b b' hb
      exact ExSim.ok ⟨hb, hS⟩

private theorem arm_runeAt (hS : FrameSim ρ na₀ na fr σ σF)
    (sv ov : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .runeAt [sv, ov])
      (applyStrictOp σF .runeAt [renameValue ρ sv, renameValue ρ ov]) := by
  simp only [applyStrictOp]
  cases sv <;> simp only [renameValue]
  case string gs =>
      refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
      intro n n' hn
      subst hn
      by_cases hneg : n < 0
      · rw [if_pos hneg]
        exact ExSim.stuck'
      · rw [if_neg hneg, if_neg hneg]
        simp only [pure_bind]
        exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  all_goals exact ExSim.stuck'

private theorem arm_runeSizeAt (hS : FrameSim ρ na₀ na fr σ σF)
    (sv ov : GoValue) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ .runeSizeAt [sv, ov])
      (applyStrictOp σF .runeSizeAt [renameValue ρ sv, renameValue ρ ov]) := by
  simp only [applyStrictOp]
  cases sv <;> simp only [renameValue]
  case string gs =>
      refine ExSim.bind (valueAsInt_sim ρ rfl) ?_
      intro n n' hn
      subst hn
      by_cases hneg : n < 0
      · rw [if_pos hneg]
        exact ExSim.stuck'
      · rw [if_neg hneg, if_neg hneg]
        simp only [pure_bind]
        exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  all_goals exact ExSim.stuck'

private theorem arm_defaultValueOf (hS : FrameSim ρ na₀ na fr σ σF) (ty : Ty) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.defaultValueOf ty) [])
      (applyStrictOp σF (.defaultValueOf ty) []) := by
  simp only [applyStrictOp]
  exact scalar_pair hS (defaultValue_sim hS.types_eq ty)

private theorem arm_nilLit (hS : FrameSim ρ na₀ na fr σ σF) (typ : Option Ty) :
    ExSim (PairSim ρ na₀ na fr)
      (applyStrictOp σ (.nilLit typ) [])
      (applyStrictOp σF (.nilLit typ) []) := by
  rcases typ with _ | ty
  · exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  · cases ty <;>
      first
      | exact ExSim.stuck'
      | exact ExSim.unsupported'
      | exact ExSim.ok ⟨by simp only [renameValue], hS⟩
      | (simp only [applyStrictOp]
         exact scalar_pair hS (defaultValue_sim hS.types_eq _))

/-! ## The whole op table -/

set_option maxHeartbeats 1600000 in
theorem applyStrictOp_sim (hS : FrameSim ρ na₀ na fr σ σF)
    (hinj : ∀ {x y : Nat}, ρ x = ρ y → x = y)
    (op : StrictOp) (vs : List GoValue) :
    ExSim (fun (r rF : GoValue × ExecState) =>
        rF.1 = renameValue ρ r.1 ∧ FrameSim ρ na₀ na fr r.2 rF.2)
      (applyStrictOp σ op vs)
      (applyStrictOp σF op (renameValueList ρ vs)) := by
  cases op with
  | add =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_add hS l r
      · exact ExSim.stuck'
  | sub =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_sub hS l r
      · exact ExSim.stuck'
  | mul =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_mul hS l r
      · exact ExSim.stuck'
  | div =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_div hS l r
      · exact ExSim.stuck'
  | mod =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_mod hS l r
      · exact ExSim.stuck'
  | shiftLeft =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_shiftLeft hS l r
      · exact ExSim.stuck'
  | shiftRight =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_shiftRight hS l r
      · exact ExSim.stuck'
  | bitAnd =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_bitAnd hS l r
      · exact ExSim.stuck'
  | bitOr =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_bitOr hS l r
      · exact ExSim.stuck'
  | bitXor =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_bitXor hS l r
      · exact ExSim.stuck'
  | bitClear =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_bitClear hS l r
      · exact ExSim.stuck'
  | bitNeg =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_bitNeg hS v
      · exact ExSim.stuck'
  | not =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_not hS v
      · exact ExSim.stuck'
  | neg =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_neg hS v
      · exact ExSim.stuck'
  | floatLit num den kind =>
      rcases vs with _ | ⟨x, t⟩
      · simp only [renameValueList]; exact arm_floatLit hS num den kind
      · exact ExSim.stuck'
  | eqCmp ty =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_eq hS hinj ty l r
      · exact ExSim.stuck'
  | neqCmp ty =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_neq hS hinj ty l r
      · exact ExSim.stuck'
  | atMostCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_atMost hS l r
      · exact ExSim.stuck'
  | atLeastCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_atLeast hS l r
      · exact ExSim.stuck'
  | lessCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_less hS l r
      · exact ExSim.stuck'
  | greaterCmp =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_greater hS l r
      · exact ExSim.stuck'
  | convert ty =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_convert hS ty v
      · exact ExSim.stuck'
  | bytesFromString =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_bytesFromString hS v
      · exact ExSim.stuck'
  | stringFromByteSlice =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_stringFromByteSlice hS v
      · exact ExSim.stuck'
  | stringFromRune =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_stringFromRune hS v
      · exact ExSim.stuck'
  | runesFromString =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_runesFromString hS v
      · exact ExSim.stuck'
  | stringFromRuneSlice =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_stringFromRuneSlice hS v
      · exact ExSim.stuck'
  | deref ty =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_deref hS ty v
      · exact ExSim.stuck'
  | fieldGet tid fname =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_fieldGet hS tid fname v
      · exact ExSim.stuck'
  | fieldAddr tid fname =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_fieldAddr hS tid fname v
      · exact ExSim.stuck'
  | addrOfDeref =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_addrOfDeref hS v
      · exact ExSim.stuck'
  | structLit ty => exact arm_structLit hS ty vs
  | arrayLit n elem keys => exact arm_arrayLit hS n elem keys vs
  | toInterface tgt dyn =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_toInterface hS tgt dyn v
      · exact ExSim.stuck'
  | typeAssert tgt srcTy =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_typeAssert hS tgt srcTy v
      · exact ExSim.stuck'
  | indexGet =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_indexGet hS l r
      · exact ExSim.stuck'
  | indexAddr =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_indexAddr hS l r
      · exact ExSim.stuck'
  | mapGet kt vt =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_mapGet hS hinj kt vt l r
      · exact ExSim.stuck'
  | sliceExpr hasMax =>
      cases hasMax
      · rcases vs with _ | ⟨b, _ | ⟨lo, _ | ⟨hi, _ | ⟨x, t⟩⟩⟩⟩
        · exact ExSim.stuck'
        · exact ExSim.stuck'
        · exact ExSim.stuck'
        · simp only [renameValueList]; exact arm_slice3 hS b lo hi
        · exact ExSim.stuck'
      · rcases vs with _ | ⟨b, _ | ⟨lo, _ | ⟨hi, _ | ⟨mx, _ | ⟨x, t⟩⟩⟩⟩⟩
        · exact ExSim.stuck'
        · exact ExSim.stuck'
        · exact ExSim.stuck'
        · exact ExSim.stuck'
        · simp only [renameValueList]; exact arm_slice4 hS b lo hi mx
        · exact ExSim.stuck'
  | lengthOf typ =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_length hS typ v
      · exact ExSim.stuck'
  | capacityOf typ =>
      rcases vs with _ | ⟨v, _ | ⟨x, t⟩⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_capacity hS typ v
      · exact ExSim.stuck'
  | defaultValueOf ty =>
      rcases vs with _ | ⟨x, t⟩
      · simp only [renameValueList]; exact arm_defaultValueOf hS ty
      · exact ExSim.stuck'
  | nilLit typ =>
      rcases vs with _ | ⟨x, t⟩
      · simp only [renameValueList]; exact arm_nilLit hS typ
      · exact ExSim.stuck'
  | funcValOf fid => exact ExSim.ok ⟨by simp only [renameValue], hS⟩
  | minOf =>
      rcases vs with _ | ⟨v, t⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_min hS v t
  | maxOf =>
      rcases vs with _ | ⟨v, t⟩
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_max hS v t
  | runeAt =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_runeAt hS l r
      · exact ExSim.stuck'
  | runeSizeAt =>
      rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, t⟩⟩⟩
      · exact ExSim.stuck'
      · exact ExSim.stuck'
      · simp only [renameValueList]; exact arm_runeSizeAt hS l r
      · exact ExSim.stuck'

end

end GoLean.Frame
