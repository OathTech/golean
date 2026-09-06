import GoLean.GoCore.Ops

/-! A bounded BUG-090 design spike. No production caller uses this module.
The fast operation is total on raw states; its refinement theorem has a
local backing-array premise, independently stated by integer range/tag.
It performs no runtime scan of the old array. -/

namespace GoLean.GoCore.ByteStorePrototype

/-- A canonical byte, independently of the normalizer's implementation. -/
def ByteNormal (v : GoValue) : Prop :=
  ∃ z : Int, v = .int z .uint8 ∧ 0 ≤ z ∧ z < 256

/-- Only this backing array is constrained. No whole-state invariant,
type-environment validity, alias exclusion, or incoming-value premise. -/
def BackingNormal (n : Nat) (values : Array GoValue) : Prop :=
  values.size = n ∧ ∀ v ∈ values.toList, ByteNormal v

def normalizeByte (v : GoValue) : Except Stop GoValue :=
  match v with
  | .int z _ => .ok (.int (z % 256) .uint8)
  | other => stuck s!"expected uint8 value, got {repr other}"

theorem normalizeByte_eq (state : ExecState) (v : GoValue) :
    normalizeByte v = normalizeValueForTy state (.int .uint8) v := by
  cases v <;> rfl

theorem normalizeByte_self {v : GoValue} (h : ByteNormal v) :
    normalizeByte v = .ok v := by
  obtain ⟨z, rfl, hz, hz'⟩ := h
  simp [normalizeByte, Int.emod_eq_of_lt hz hz']

theorem normalizeByte_normal {v w : GoValue}
    (h : normalizeByte v = .ok w) : ByteNormal w := by
  cases v <;> simp [normalizeByte, stuck] at h
  next z kind =>
    subst w
    exact ⟨z % 256, rfl, Int.emod_nonneg z (by decide),
      Int.emod_lt_of_pos z (by decide)⟩

theorem normalizeList_self (f : GoValue → Except Stop GoValue)
    (xs : List GoValue) (h : ∀ x ∈ xs, f x = .ok x) :
    normalizeListWith f xs = .ok xs.toArray := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp [normalizeListWith, hx, ht, Bind.bind, Except.bind, pure, Except.pure]

/-- Updating one member of a fixed-point list requires normalizing only the
new member, including its precise error. Old normal members cannot fail. -/
theorem normalizeList_set (f : GoValue → Except Stop GoValue)
    (xs : List GoValue) (h : ∀ x ∈ xs, f x = .ok x)
    (i : Nat) (hi : i < xs.length) (v : GoValue) :
    normalizeListWith f (xs.set i v) = (do
      let w ← f v
      pure ((xs.set i w).toArray)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, f y = .ok y := fun y hy => h y (by simp [hy])
    cases i with
    | zero =>
      simp [normalizeListWith, normalizeList_self f xs ht]
      cases f v <;> simp [Bind.bind, Except.bind, Functor.map, Except.map]
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simp [normalizeListWith, hx, ih ht i hi', Bind.bind, Except.bind,
        pure, Except.pure]
      cases f v <;> simp

theorem normalizeArray_set (state : ExecState) {n : Nat}
    {values : Array GoValue} (h : BackingNormal n values)
    (i : Nat) (hi : i < values.size) (v : GoValue) :
    normalizeValueForTy state (.array n (.int .uint8))
        (.array (values.set! i v)) = (do
      let w ← normalizeByte v
      pure (.array (values.set! i w))) := by
  have hf : ∀ x ∈ values.toList,
      normalizeValueForTyTy (normalizeValueForTyAt state.types state.types.size)
        (.int .uint8) x = .ok x := by
    intro x hx
    exact (normalizeByte_eq state x).symm.trans (normalizeByte_self (h.2 x hx))
  simp only [normalizeValueForTy, normalizeValueForTyTy, Array.size_set!, h.1,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [Array.set!, Array.toList_setIfInBounds,
    normalizeList_set _ _ hf i (by simpa using hi)]
  have hn : normalizeValueForTyTy (normalizeValueForTyAt state.types state.types.size)
      (.int .uint8) v = normalizeByte v := (normalizeByte_eq state v).symm
  rw [hn]
  cases normalizeByte v <;> simp [Bind.bind, Except.bind, pure, Except.pure,
    Functor.map, Except.map, Array.set!]
  apply Array.toList_inj.mp
  simp

/-- Same bounds check and error text/order as `arraySet`; normalize only
the incoming element after the bounds check succeeds. -/
def setByte (values : Array GoValue) (index : Int) (v : GoValue) :
    Except Stop (Array GoValue) := do
  let i ← arrayIndexNat values index
  match values[i]? with
  | some _ =>
      let w ← normalizeByte v
      pure (values.set! i w)
  | none => indexOutOfRangePanic index values.size

/-- A candidate fast branch with an explicit fallback for other cell shapes.
Calling this on non-normal byte arrays is outside the refinement theorem;
the function does not silently check or assume a whole-state invariant. -/
def storeByteElement (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) : Except Stop ExecState :=
  match Heap.lookup state.heap (.base a) with
  | some (.value (.array n (.int .uint8)) (.array values)) => do
      let updated ← setByte values index v
      state.updateCell a (fun _ => .ok (.value (.array n (.int .uint8)) (.array updated)))
  | _ => storeLoc state (.index (.base a) index) v

theorem storeByteElement_eq_storeLoc (state : ExecState) (a : Addr)
    (index : Int) (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values)))
    (hn : BackingNormal n values) :
    storeByteElement state a index v = storeLoc state (.index (.base a) index) v := by
  have ha := Heap.lookup_lt hc
  have hget : state.heap[a.id]'ha =
      .value (.array n (.int .uint8)) (.array values) := by
    exact (Array.getElem?_eq_some_iff.mp hc).2
  simp only [storeByteElement, hc, storeLoc, loadLoc, arraySet, setByte,
    Bind.bind, Except.bind, pure, Except.pure]
  cases hi : arrayIndexNat values index with
  | error e => rfl
  | ok i =>
    simp only []
    cases hg : values[i]? with
    | none =>
      by_cases hz : index < 0 <;>
        simp only [indexOutOfRangePanic, hz, ↓reduceIte, panic] <;> rfl
    | some old =>
      have hib : i < values.size := (Array.getElem?_eq_some_iff.mp hg).1
      simp only [ExecState.updateCell, ha, ↓reduceDIte, hget]
      rw [normalizeArray_set state hn i hib v]
      cases normalizeByte v <;> rfl

theorem arrayIndexNat_ok {values : Array GoValue} {index : Int} {i : Nat}
    (h : arrayIndexNat values index = .ok i) :
    0 ≤ index ∧ i = index.toNat ∧ i < values.size := by
  unfold arrayIndexNat at h
  split at h
  · simp only [indexOutOfRangePanic, show index < 0 by assumption, ↓reduceIte] at h
    change Except.error _ = Except.ok i at h
    cases h
  · rename_i hn
    simp only [pure, Except.pure] at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst i
      exact ⟨by omega, rfl, by assumption⟩
    · simp [indexOutOfRangePanic, panic, hn] at h

theorem setByte_result {values updated : Array GoValue} {index : Int} {v : GoValue}
    (h : setByte values index v = .ok updated) :
    ∃ w, 0 ≤ index ∧ index.toNat < values.size ∧
      normalizeByte v = .ok w ∧ updated = values.set! index.toNat w := by
  unfold setByte at h
  cases hi : arrayIndexNat values index with
  | error e => simp [hi, Bind.bind, Except.bind] at h
  | ok i =>
    obtain ⟨hz, rfl, hib⟩ := arrayIndexNat_ok hi
    simp only [hi, Bind.bind, Except.bind] at h
    rw [Array.getElem?_eq_getElem hib] at h
    cases hw : normalizeByte v with
    | error e => simp [hw] at h
    | ok w =>
      simp [hw, pure, Except.pure] at h
      exact ⟨w, hz, hib, rfl, h.symm⟩

theorem backingNormal_set {n : Nat} {values : Array GoValue}
    (h : BackingNormal n values) (i : Nat) {w : GoValue} (hw : ByteNormal w) :
    BackingNormal n (values.set! i w) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro x hx
  rw [Array.set!, Array.toList_setIfInBounds] at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h.2 x hx
  · exact hw

/-- Successful stores return the reusable local certificate. It is erased
proof data; establishing it does not run a normality scan in this function. -/
theorem setByte_preserves {n : Nat} {values updated : Array GoValue}
    {index : Int} {v : GoValue} (hn : BackingNormal n values)
    (h : setByte values index v = .ok updated) : BackingNormal n updated := by
  obtain ⟨w, _, _, hw, rfl⟩ := setByte_result h
  exact backingNormal_set hn _ (normalizeByte_normal hw)

theorem setByte_untouched {values updated : Array GoValue} {index : Int} {v : GoValue}
    (h : setByte values index v = .ok updated) (j : Nat) (hj : index.toNat ≠ j) :
    updated[j]? = values[j]? := by
  obtain ⟨w, _, _, _, rfl⟩ := setByte_result h
  exact Array.getElem?_setIfInBounds_ne hj

theorem storeByteElement_result (state : ExecState) (a : Addr)
    (index : Int) (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values)))
    (hn : BackingNormal n values) {state' : ExecState}
    (hs : storeByteElement state a index v = .ok state') :
    ∃ updated, setByte values index v = .ok updated ∧ BackingNormal n updated ∧
      state' = { state with heap := (state.heap.set a.id
        (.value (.array n (.int .uint8)) (.array updated)) (Heap.lookup_lt hc)) } := by
  simp only [storeByteElement, hc, Bind.bind, Except.bind] at hs
  cases hu : setByte values index v with
  | error e => simp [hu] at hs
  | ok updated =>
    simp [hu, ExecState.updateCell, Heap.lookup_lt hc, Functor.map, Except.map] at hs
    exact ⟨updated, rfl, setByte_preserves hn hu, hs.symm⟩

theorem storeByteElement_untouched_cell (state : ExecState) (a : Addr)
    (index : Int) (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values)))
    (hn : BackingNormal n values) {state' : ExecState}
    (hs : storeByteElement state a index v = .ok state')
    (j : Nat) (hj : a.id ≠ j) : state'.heap[j]? = state.heap[j]? := by
  obtain ⟨updated, _, _, rfl⟩ := storeByteElement_result state a index v hc hn hs
  simp [hj]

def NormalBackingAt (state : ExecState) (a : Addr) (n : Nat) : Prop :=
  ∃ values, Heap.lookup state.heap (.base a) =
    some (.value (.array n (.int .uint8)) (.array values)) ∧ BackingNormal n values

theorem storeByteElement_preserves {state state' : ExecState} {a : Addr} {n : Nat}
    (h : NormalBackingAt state a n) (index : Int) (v : GoValue)
    (hs : storeByteElement state a index v = .ok state') : NormalBackingAt state' a n := by
  obtain ⟨values, hc, hn⟩ := h
  obtain ⟨updated, _, hn', rfl⟩ := storeByteElement_result state a index v hc hn hs
  exact ⟨updated, by simp [Heap.lookup, Heap.lookup_lt hc], hn'⟩

/-- The certificate is a Prop field: it is erased at runtime. No stored
second array and no executable normality check are needed to thread it. -/
def storeCertifiedByteElement {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n })
    (index : Int) (v : GoValue) : Except Stop { s : ExecState // NormalBackingAt s a n } :=
  match hs : storeByteElement state.val a index v with
  | .error e => .error e
  | .ok state' => .ok ⟨state', storeByteElement_preserves state.property index v hs⟩

theorem storeCertifiedByteElement_eq_storeLoc {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n }) (index : Int) (v : GoValue) :
    (storeCertifiedByteElement state index v).map Subtype.val =
      storeLoc state.val (.index (.base a) index) v := by
  obtain ⟨values, hc, hn⟩ := state.property
  rw [← storeByteElement_eq_storeLoc state.val a index v hc hn]
  unfold storeCertifiedByteElement
  split <;> rename_i result hr <;> exact hr.symm

namespace Challenges

def bytes : Array GoValue := #[.int 0 .uint8, .int 255 .uint8]

/-- The unrelated cell has the wrong shape for its declared type. The
premise deliberately permits this raw malformed state. -/
def rawState : ExecState :=
  { heap := #[.value (.array 2 (.int .uint8)) (.array bytes),
              .value (.int .uint8) (.bool true)] }

theorem rawState_normal : NormalBackingAt rawState ⟨0⟩ 2 := by
  refine ⟨bytes, rfl, rfl, ?_⟩
  intro v hv
  simp [bytes] at hv
  rcases hv with rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  · exact ⟨255, rfl, by decide, by decide⟩

theorem arbitrary_raw_incoming (i : Int) (v : GoValue) :
    storeByteElement rawState ⟨0⟩ i v = storeLoc rawState (.index (.base ⟨0⟩) i) v := by
  obtain ⟨values, hc, hn⟩ := rawState_normal
  exact storeByteElement_eq_storeLoc _ _ _ _ hc hn

theorem mismatched_tag_and_negative_wrap :
    storeByteElement rawState ⟨0⟩ 0 (.int (-1) .int) =
      .ok { rawState with heap :=
        #[.value (.array 2 (.int .uint8)) (.array #[.int 255 .uint8, .int 255 .uint8]),
          .value (.int .uint8) (.bool true)] } := by rfl

theorem oversized_wrap :
    setByte bytes 1 (.int 258 (.unbounded "raw")) =
      .ok #[.int 0 .uint8, .int 2 .uint8] := by rfl

theorem negative_bounds_before_invalid_value :
    storeByteElement rawState ⟨0⟩ (-1) (.bool true) =
      .error (.panic "runtime error: index out of range [-1]") := by rfl

theorem high_bounds_before_invalid_value :
    storeByteElement rawState ⟨0⟩ 2 (.bool true) =
      .error (.panic "runtime error: index out of range [2] with length 2") := by rfl

theorem in_bounds_invalid_value :
    storeByteElement rawState ⟨0⟩ 1 (.bool true) =
      stuck s!"expected uint8 value, got {repr (.bool true : GoValue)}" := by rfl

theorem zero_length_backing : BackingNormal 0 #[] := by
  exact ⟨rfl, by simp⟩

theorem zero_length_bounds :
    setByte #[] 0 (.int 0 .uint8) =
      .error (.panic "runtime error: index out of range [0] with length 0") := by rfl

/-- A malformed old element at the overwritten position is outside the
premise, even if this individual ordinary store could repair it. -/
theorem non_normal_byte_excluded : ¬ BackingNormal 1 #[.int 256 .uint8] := by
  intro h
  obtain ⟨z, heq, _, hz⟩ := h.2 (.int 256 .uint8) (by simp)
  cases heq
  omega

theorem wrong_length_excluded : ¬ BackingNormal 3 bytes := by
  intro h
  have := h.1
  contradiction

def nonNormalState : ExecState :=
  { heap := #[.value (.array 2 (.int .uint8))
    (.array #[.int 256 .uint8, .int 0 .uint8])] }

/-- The normality premise is necessary. An untouched noncanonical byte is
renormalized by ordinary root storage, but deliberately not by this branch. -/
theorem no_unrestricted_refinement :
    storeByteElement nonNormalState ⟨0⟩ 1 (.int 1 .uint8) ≠
      storeLoc nonNormalState (.index (.base ⟨0⟩) 1) (.int 1 .uint8) := by
  intro h
  have he := congrArg (fun result => result.toOption.map
    (fun state => state.heap[0]?)) h
  change some (some (HeapCell.value (.array 2 (.int .uint8))
      (.array #[.int 256 .uint8, .int 1 .uint8]))) =
    some (some (HeapCell.value (.array 2 (.int .uint8))
      (.array #[.int 0 .uint8, .int 1 .uint8]))) at he
  have ha : (#[.int 256 .uint8, .int 1 .uint8] : Array GoValue) =
      #[.int 0 .uint8, .int 1 .uint8] := by injection he with he; injection he with he; injection he with _ he; injection he
  have hf := congrArg (fun a : Array GoValue => a[0]?) ha
  simp at hf

end Challenges

end GoLean.GoCore.ByteStorePrototype
