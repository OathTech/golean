import GoLean.GoCore.Ops

/-! Exact byte-array store implementation lemmas. See
`docs/2026-09-06_byte-append-runtime.md` for provenance and scope. -/

namespace GoLean.GoCore.ByteArrayStore

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




/-- Bounded consuming variant. `modifyM` releases the old heap-cell slot
before running its callback in Lean's standard compiled implementation.
Other root shapes fail visibly; the certificate excludes these branches. -/
def consumeByteElement (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) : Except Stop ExecState :=
  match state with
  | ⟨types, functions, methods, methodSets, typeDisplays, heap⟩ => do
    if a.id < heap.size then
      let heap ← heap.modifyM a.id fun
        | .value (.array n (.int .uint8)) (.array values) => do
          let updated ← setByte values index v
          pure (.value (.array n (.int .uint8)) (.array updated))
        | _ => stuck "byte-store prototype: expected a declared byte-array root"
      pure ⟨types, functions, methods, methodSets, typeDisplays, heap⟩
    else stuck s!"unbound GoCore heap location: {repr (Loc.base a)}"

theorem consumeByteElement_eq (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values))) :
    consumeByteElement state a index v = storeByteElement state a index v := by
  have ha := Heap.lookup_lt hc
  have hget := (Array.getElem?_eq_some_iff.mp hc).2
  cases state with
  | mk types functions methods methodSets typeDisplays heap =>
    simp only [consumeByteElement, ha, ↓reduceIte, Array.modifyM, ↓reduceDIte,
      hget, storeByteElement, hc]
    cases setByte values index v <;>
      simp [ExecState.updateCell, ha, Bind.bind, Except.bind, pure, Except.pure]

theorem consumeByteElement_eq_storeLoc (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values)))
    (hn : BackingNormal n values) :
    consumeByteElement state a index v = storeLoc state (.index (.base a) index) v :=
  (consumeByteElement_eq state a index v hc).trans
    (storeByteElement_eq_storeLoc state a index v hc hn)

def consumeCertifiedByteElement {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n })
    (index : Int) (v : GoValue) : Except Stop { s : ExecState // NormalBackingAt s a n } :=
  match hs : consumeByteElement state.val a index v with
  | .error e => .error e
  | .ok state' => .ok ⟨state', by
    obtain ⟨values, hc, hn⟩ := state.property
    exact storeByteElement_preserves state.property index v
      ((consumeByteElement_eq state.val a index v hc).symm.trans hs)⟩

theorem consumeCertifiedByteElement_eq_storeLoc {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n }) (index : Int) (v : GoValue) :
    (consumeCertifiedByteElement state index v).map Subtype.val =
      storeLoc state.val (.index (.base a) index) v := by
  obtain ⟨values, hc, hn⟩ := state.property
  rw [← consumeByteElement_eq_storeLoc state.val a index v hc hn]
  unfold consumeCertifiedByteElement
  split <;> rename_i result hr <;> exact hr.symm




/-- Tail-recursive normalization. It preserves left-to-right failure order
and uses ordinary `Array.push`, with no compiler override. -/
def normalizeListAcc (f : GoValue → Except Stop GoValue) :
    List GoValue → Array GoValue → Except Stop (Array GoValue)
  | [], acc => .ok acc
  | value :: rest, acc => do
      let value ← f value
      normalizeListAcc f rest (acc.push value)

theorem normalizeListAcc_eq (f : GoValue → Except Stop GoValue)
    (xs : List GoValue) (acc : Array GoValue) :
    normalizeListAcc f xs acc = (normalizeListWith f xs).map (acc ++ ·) := by
  induction xs generalizing acc with
  | nil => simp [normalizeListAcc, normalizeListWith, pure, Except.pure, Except.map]
  | cons x xs ih =>
    simp only [normalizeListAcc, normalizeListWith]
    cases hx : f x with
    | error e => rfl
    | ok y =>
      simp only [Bind.bind, Except.bind]
      rw [ih]
      cases ht : normalizeListWith f xs <;>
        simp only [Except.map, pure, Except.pure,
          Array.push_eq_append, Array.append_assoc]

theorem normalizeListAcc_empty_eq (f : GoValue → Except Stop GoValue)
    (xs : List GoValue) : normalizeListAcc f xs #[] = normalizeListWith f xs := by
  rw [normalizeListAcc_eq]
  cases normalizeListWith f xs <;> simp [Except.map]

theorem normalizeListByte_result {xs : List GoValue} {values : Array GoValue}
    (h : normalizeListWith normalizeByte xs = .ok values) :
    values.size = xs.length ∧ ∀ v ∈ values.toList, ByteNormal v := by
  induction xs generalizing values with
  | nil =>
    simp [normalizeListWith, pure, Except.pure] at h
    subst values
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    cases hx : normalizeByte x with
    | error e => simp [normalizeListWith, hx, Bind.bind, Except.bind] at h
    | ok y =>
      cases ht : normalizeListWith normalizeByte xs with
      | error e => simp [normalizeListWith, hx, ht, Bind.bind, Except.bind] at h
      | ok tail =>
        have hp := ih ht
        simp [normalizeListWith, hx, ht, Bind.bind, Except.bind, pure, Except.pure] at h
        subst values
        refine ⟨by simp [hp.1]; omega, ?_⟩
        intro v hv
        simp only [Array.toList_append, List.mem_append] at hv
        simp only [List.mem_singleton] at hv
        rcases hv with rfl | hv
        · exact normalizeByte_normal hx
        · exact hp.2 v hv

/-- Ordinary byte-array normalization with an equivalent linear builder. -/
def normalizeByteBacking (n : Nat) (values : Array GoValue) :
    Except Stop (Array GoValue) := do
  if values.size != n then
    stuck s!"array value length mismatch: expected {n}, got {values.size}"
  normalizeListAcc normalizeByte values.toList #[]

theorem normalizeByteBacking_eq (state : ExecState) (n : Nat)
    (values : Array GoValue) :
    (normalizeByteBacking n values).map GoValue.array =
      normalizeValueForTy state (.array n (.int .uint8)) (.array values) := by
  simp only [normalizeByteBacking, normalizeValueForTy, normalizeValueForTyTy]
  split
  · rfl
  · rw [normalizeListAcc_empty_eq]
    have hf : normalizeValueForTyTy
        (normalizeValueForTyAt state.types state.types.size) (.int .uint8) =
        normalizeByte := by
      funext v
      exact (normalizeByte_eq state v).symm
    rw [hf]
    rfl

theorem normalizeByteBacking_normal {n : Nat} {values updated : Array GoValue}
    (h : normalizeByteBacking n values = .ok updated) : BackingNormal n updated := by
  unfold normalizeByteBacking at h
  split at h
  · simp [stuck, Bind.bind, Except.bind] at h
  · rename_i hn
    rw [normalizeListAcc_empty_eq] at h
    have hp := normalizeListByte_result h
    exact ⟨by simpa using hp.1.trans (by simpa using hn), hp.2⟩

/-- First successful byte store establishes its local certificate by the
ordinary normalization itself. The initial backing need not be normal. -/
def firstByteElement (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) : Except Stop ExecState :=
  match Heap.lookup state.heap (.base a) with
  | some (.value (.array n (.int .uint8)) (.array values)) => do
      let updated ← arraySet values index v
      let normalized ← normalizeByteBacking n updated
      state.updateCell a (fun _ =>
        .ok (.value (.array n (.int .uint8)) (.array normalized)))
  | _ => storeLoc state (.index (.base a) index) v

theorem firstByteElement_eq_storeLoc (state : ExecState) (a : Addr)
    (index : Int) (v : GoValue) :
    firstByteElement state a index v = storeLoc state (.index (.base a) index) v := by
  unfold firstByteElement
  split
  · rename_i n values hc
    have ha := Heap.lookup_lt hc
    have hget := (Array.getElem?_eq_some_iff.mp hc).2
    simp only [storeLoc, loadLoc, hc, Bind.bind, Except.bind, pure, Except.pure]
    cases hs : arraySet values index v with
    | error e => rfl
    | ok updated =>
      simp only [ExecState.updateCell, ha, ↓reduceDIte, hget]
      rw [← normalizeByteBacking_eq]
      cases normalizeByteBacking n updated <;> rfl
  · rfl

theorem firstByteElement_normal (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) {n : Nat} {values : Array GoValue} {state' : ExecState}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values)))
    (hs : firstByteElement state a index v = .ok state') :
    NormalBackingAt state' a n := by
  simp only [firstByteElement, hc, Bind.bind, Except.bind] at hs
  cases hu : arraySet values index v with
  | error e => simp [hu] at hs
  | ok updated =>
    cases hn : normalizeByteBacking n updated with
    | error e => simp [hu, hn] at hs
    | ok normalized =>
      simp [hu, hn, Bind.bind, Except.bind, ExecState.updateCell,
        Heap.lookup_lt hc, pure, Except.pure] at hs
      subst state'
      exact ⟨normalized, by simp [Heap.lookup, Heap.lookup_lt hc],
        normalizeByteBacking_normal hn⟩

/-- The existing in-place append loop, made independently callable. -/
def appendValuesOriginal (state : ExecState) (slice : SliceValue)
    (values : Array GoValue) : Except Stop ExecState := do
  let mut current := state
  let mut i := 0
  for value in values do
    match slice.base with
    | some base =>
        current ← storeLoc current
          (.index base (Int.ofNat (slice.offset + slice.len + i))) value
        i := i + 1
    | none => stuck s!"cannot append {values.size} element(s) into nil slice in place"
  pure current

def appendListOriginal (base : Option Loc) (start total : Nat) :
    List GoValue → ExecState → Nat → Except Stop ExecState
  | [], state, _ => .ok state
  | value :: rest, state, i => do
      match base with
      | some base =>
          let state ← storeLoc state (.index base (Int.ofNat (start + i))) value
          appendListOriginal (some base) start total rest state (i + 1)
      | none => stuck s!"cannot append {total} element(s) into nil slice in place"

def certifiedByteList {a : Addr} {n : Nat} (start : Nat) :
    List GoValue → { s : ExecState // NormalBackingAt s a n } → Nat →
      Except Stop ExecState
  | [], state, _ => .ok state.val
  | value :: rest, state, i => do
      let state ← consumeCertifiedByteElement state (Int.ofNat (start + i)) value
      certifiedByteList start rest state (i + 1)

theorem certifiedByteList_eq {a : Addr} {n : Nat} (start total : Nat)
    (values : List GoValue) (state : { s : ExecState // NormalBackingAt s a n })
    (i : Nat) : certifiedByteList start values state i =
      appendListOriginal (some (.base a)) start total values state.val i := by
  induction values generalizing state i with
  | nil => rfl
  | cons v vs ih =>
    simp only [certifiedByteList, appendListOriginal]
    rw [← consumeCertifiedByteElement_eq_storeLoc state]
    cases consumeCertifiedByteElement state (Int.ofNat (start + i)) v with
    | error e => rfl
    | ok state' => exact ih state' (i + 1)

/-- One ordinary successful normalization establishes normality; the
remaining element stores carry its erased certificate. Any raw state not
having this direct declared root keeps the entire original loop. -/
def appendListFast (base : Option Loc) (start total : Nat)
    (values : List GoValue) (state : ExecState) (i : Nat) : Except Stop ExecState :=
  match values, base with
  | value :: rest, some (.base a) =>
      match hc : Heap.lookup state.heap (.base a) with
      | some (.value (.array _n (.int .uint8)) (.array _)) =>
          match hs : firstByteElement state a (Int.ofNat (start + i)) value with
          | .error e => .error e
          | .ok state' =>
              certifiedByteList start rest
                ⟨state', firstByteElement_normal state a _ value hc hs⟩ (i + 1)
      | _ => appendListOriginal base start total values state i
  | _, _ => appendListOriginal base start total values state i

theorem appendListFast_eq (base : Option Loc) (start total : Nat)
    (values : List GoValue) (state : ExecState) (i : Nat) :
    appendListFast base start total values state i =
      appendListOriginal base start total values state i := by
  unfold appendListFast
  split
  · split
    · rename_i value rest a n backing hc
      simp only [appendListOriginal]
      rw [← firstByteElement_eq_storeLoc]
      split
      · rename_i e hs
        rw [hs]
        rfl
      · rename_i state' hs
        simp only [hs, Bind.bind, Except.bind]
        exact certifiedByteList_eq start total rest _ (i + 1)
    · rfl
  · rfl

def appendValuesFast (state : ExecState) (slice : SliceValue)
    (values : Array GoValue) : Except Stop ExecState :=
  appendListFast slice.base (slice.offset + slice.len) values.size values.toList state 0

theorem appendListOriginal_forIn (base : Option Loc) (start total : Nat)
    (values : List GoValue) (state : ExecState) (i : Nat) :
    appendListOriginal base start total values state i = (do
      let (state, _) ← forIn values (state, i) fun value (state, i) => do
        match base with
        | some base =>
            let state ← storeLoc state (.index base (Int.ofNat (start + i))) value
            pure (.yield (state, i + 1))
        | none =>
            stuck s!"cannot append {total} element(s) into nil slice in place"
            pure (.yield (state, i))
      pure state) := by
  induction values generalizing state i with
  | nil => rfl
  | cons v vs ih =>
    simp only [appendListOriginal, List.forIn_cons]
    cases base with
    | none => rfl
    | some base =>
      simp only []
      cases hs : storeLoc state (.index base (Int.ofNat (start + i))) v with
      | error e => simp [Bind.bind, Except.bind]
      | ok state' =>
          simpa only [hs, Bind.bind, Except.bind, pure, Except.pure] using ih state' (i + 1)

theorem appendValuesFast_eq (state : ExecState) (slice : SliceValue)
    (values : Array GoValue) :
    appendValuesFast state slice values = appendValuesOriginal state slice values := by
  unfold appendValuesFast
  rw [appendListFast_eq, appendListOriginal_forIn, Array.forIn_toList]
  unfold appendValuesOriginal
  rfl


end GoLean.GoCore.ByteArrayStore
