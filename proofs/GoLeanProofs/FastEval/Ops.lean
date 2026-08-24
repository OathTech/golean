import GoLeanProofs.FastEval.Heap
import GoLeanProofs.FastEval.Congr

/-!
# FastEval — the fast state and the three heap primitives, with their
one-directional sims (campaign Arc 2, U4; design
`docs/2026-08-22_fasteval-design.md` §3)

`ExecStateF` replaces only the heap representation; `γF` is the
abstraction. UNTRUSTED METHOD — never in any statement closure.

The two structural rules every mirror below follows (the design's §2):
- **one-directional**: `<f>F … = .ok r → <f> (γF σF) … = .ok (γ-image r)`;
  arms the twin run does not exercise are FAIL-CLOSED STUBS whose sim
  cases are vacuous;
- **lazy view**: pure (non-heap) helpers are called at `γF σF` itself —
  kernel projection laziness means they never force the `γH` dump, and
  the sim's two sides share the call syntactically.
-/

namespace GoLean.FastEval

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- The fast machine state: `ExecState` with the heap re-represented.
Field-for-field otherwise. -/
structure ExecStateF where
  types : TypeEnv := []
  functions : Array Func := #[]
  methods : Array MethodInfo := #[]
  methodSets : Array MethodSetRecord := #[]
  heapT : HeapT := .leaf
  nextAddr : Nat := 0

/-- THE ABSTRACTION at state level. -/
def γF (σF : ExecStateF) : ExecState :=
  { types := σF.types, functions := σF.functions, methods := σF.methods
    methodSets := σF.methodSets, heap := γH σF.heapT σF.nextAddr
    nextAddr := σF.nextAddr }

/-! ## The O(1) context image (P2R ctx refactor, slice 3)

`γF`'s COMPILED construction strictly materializes the `γH` heap dump —
O(cells) per call (the P2R strictness discovery). Every def-side call
of a static-table-only helper therefore runs at `ctxF σF` instead: the
same tables and frontier, EMPTY heap, O(1) to construct. The `_ctx`
lemmas rewrite those calls back to the `γF` spelling inside the sims
(`FastEval/Congr.lean` supplies the congruences; the table fields of
`ctxF σF` and `γF σF` are definitionally equal, so every hypothesis is
`rfl`). UNTRUSTED METHOD — never in any statement closure. -/

def ctxF (σF : ExecStateF) : ExecState :=
  { types := σF.types, functions := σF.functions, methods := σF.methods
    methodSets := σF.methodSets, heap := [], nextAddr := σF.nextAddr }

theorem ctxF_types (σF : ExecStateF) : (ctxF σF).types = (γF σF).types := rfl
theorem ctxF_functions (σF : ExecStateF) :
    (ctxF σF).functions = (γF σF).functions := rfl

theorem structTagCompatible_ctx (σF : ExecStateF) :
    structTagCompatible (ctxF σF) = structTagCompatible (γF σF) :=
  structTagCompatible_congr rfl
theorem normalizeValueForTy_ctx (σF : ExecStateF) :
    normalizeValueForTy (ctxF σF) = normalizeValueForTy (γF σF) :=
  normalizeValueForTy_congr rfl
theorem defaultValue_ctx (σF : ExecStateF) :
    defaultValue (ctxF σF) = defaultValue (γF σF) :=
  funext fun ty => GoLean.Frame.defaultValue_congr (σF := ctxF σF) (σ := γF σF) rfl ty
theorem valueEq_ctx (σF : ExecStateF) :
    valueEq (ctxF σF) = valueEq (γF σF) :=
  valueEq_congr rfl
theorem checkKeyHashable_ctx (σF : ExecStateF) :
    checkKeyHashable (ctxF σF) = checkKeyHashable (γF σF) :=
  checkKeyHashable_congr rfl
theorem mapEntryIndex?_ctx (σF : ExecStateF) (keyTy : Ty)
    (entries : Array (GoValue × GoValue)) (key : GoValue) (isInsert : Bool) :
    mapEntryIndex? (ctxF σF) keyTy entries key isInsert
      = mapEntryIndex? (γF σF) keyTy entries key isInsert :=
  mapEntryIndex?_congr (σ' := ctxF σF) (σ := γF σF) rfl keyTy entries key isInsert
theorem convertValueToTy_ctx (σF : ExecStateF) :
    convertValueToTy (ctxF σF) = convertValueToTy (γF σF) :=
  convertValueToTy_congr rfl
theorem typeAssertValue_ctx (σF : ExecStateF) :
    typeAssertValue (ctxF σF) = typeAssertValue (γF σF) :=
  typeAssertValue_congr rfl rfl rfl rfl
theorem buildStructValue_ctx (σF : ExecStateF) :
    buildStructValue (ctxF σF) = buildStructValue (γF σF) :=
  buildStructValue_congr rfl
theorem buildArrayValue_ctx (σF : ExecStateF) :
    buildArrayValue (ctxF σF) = buildArrayValue (γF σF) :=
  buildArrayValue_congr rfl
theorem buildDefaultArrayValue_ctx (σF : ExecStateF) :
    buildDefaultArrayValue (ctxF σF) = buildDefaultArrayValue (γF σF) :=
  buildDefaultArrayValue_congr rfl
theorem buildAppendBackingValue_ctx (σF : ExecStateF) :
    buildAppendBackingValue (ctxF σF) = buildAppendBackingValue (γF σF) :=
  buildAppendBackingValue_congr rfl
theorem keyInKeys_ctx (σF : ExecStateF) :
    keyInKeys (ctxF σF) = keyInKeys (γF σF) :=
  keyInKeys_congr rfl
theorem filterCandidateList_ctx (σF : ExecStateF) :
    filterCandidateList (ctxF σF) = filterCandidateList (γF σF) :=
  filterCandidateList_congr rfl
theorem mapIterMandatoryRemains_ctx (σF : ExecStateF) :
    mapIterMandatoryRemains (ctxF σF) = mapIterMandatoryRemains (γF σF) :=
  mapIterMandatoryRemains_congr rfl
theorem canonicalDynamicTy_ctx (σF : ExecStateF) :
    canonicalDynamicTy (ctxF σF) = canonicalDynamicTy (γF σF) :=
  funext fun ty => GoLean.Frame.canonicalDynamicTy_congr (σF := ctxF σF) (σ := γF σF) rfl ty
theorem methodInfoByFuncId?_ctx (σF : ExecStateF) :
    methodInfoByFuncId? (ctxF σF) = methodInfoByFuncId? (γF σF) :=
  funext fun fid => GoLean.Frame.methodInfoByFuncId?_congr (σF := ctxF σF) (σ := γF σF) rfl fid
theorem methodRecvInterfaceName?_ctx (σF : ExecStateF) :
    methodRecvInterfaceName? (ctxF σF) = methodRecvInterfaceName? (γF σF) :=
  funext fun m => GoLean.Frame.methodRecvInterfaceName?_congr (σF := ctxF σF) (σ := γF σF) rfl m
theorem concreteMethodForDynamic?_ctx (σF : ExecStateF) :
    concreteMethodForDynamic? (ctxF σF) = concreteMethodForDynamic? (γF σF) :=
  funext fun dynTy => funext fun name =>
    GoLean.Frame.concreteMethodForDynamic?_congr (σF := ctxF σF) (σ := γF σF)
      rfl rfl dynTy name

/-! ## The three primitives, mirrored -/

/-- `loadLoc`, fast. The frontier guard (`a.id < nextAddr`) is what
makes the `.ok` answer transportable without any carried invariant —
beyond-frontier and hole reads refuse (stubs; the twin run performs
neither). -/
def loadLocF (σF : ExecStateF) : Loc → Except GoError GoValue
  | .base a =>
      if a.id < σF.nextAddr then
        match σF.heapT.get a.id with
        | some cell => return cell.value
        | none => stuck "fastEval-stub: hole read below frontier"
      else stuck "fastEval-stub: read beyond frontier"
  | .field base typeId fieldName => do
      match ← loadLocF σF base with
      | .struct actualType fields =>
          if actualType != typeId && !structTagCompatible (ctxF σF) actualType typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          match StructFields.lookup fields fieldName with
          | some value => return value
          | none => stuck s!"unknown GoCore struct field: {fieldName}"
      | other => stuck s!"expected struct base for field load, got {repr other}"
  | .index base index => do
      match ← loadLocF σF base with
      | .array values => arrayGet values index
      | other => stuck s!"expected array base for index load, got {repr other}"

/-- `storeLoc`, fast. The create-on-missing arm of the original is a
STUB here (it would break the ascending-dump abstraction; the run
never writes an unallocated base — `alloc` is the only creator). -/
def storeLocF (σF : ExecStateF) : Loc → GoValue → Except GoError ExecStateF
  | .base a, value =>
      if a.id < σF.nextAddr then
        match σF.heapT.get a.id with
        | some cell => do
            let value ←
              match cell.declaredTy with
              | some ty => normalizeValueForTy (ctxF σF) ty value
              | none => coerceStoredValue cell.value value
            return { σF with heapT := σF.heapT.set a.id { cell with value } }
        | none => stuck "fastEval-stub: hole store below frontier"
      else stuck "fastEval-stub: store beyond frontier (create-on-missing unmirrored)"
  | .field base typeId fieldName, value => do
      match ← loadLocF σF base with
      | .struct actualType fields =>
          if actualType != typeId && !structTagCompatible (ctxF σF) actualType typeId then
            stuck s!"expected struct {typeId.key}, got struct {actualType.key}"
          let updated ← StructFields.set fields fieldName value
          storeLocF σF base (.struct actualType updated)
      | other => stuck s!"expected struct base for field store, got {repr other}"
  | .index base index, value => do
      match ← loadLocF σF base with
      | .array values => storeLocF σF base (.array (← arraySet values index value))
      | other => stuck s!"expected array base for index store, got {repr other}"

/-- `ExecState.alloc`, fast — total (allocation cannot fail). -/
def allocF (σF : ExecStateF) (value : GoValue) (typ : Option Ty := none) :
    Loc × ExecStateF :=
  (Loc.base ⟨σF.nextAddr⟩,
   { σF with heapT := σF.heapT.set σF.nextAddr { declaredTy := typ, value }
             nextAddr := σF.nextAddr + 1 })

/-! ## The sims -/

/-- The base-cell read fact underneath both sims. -/
theorem γF_lookup_of_get {σF : ExecStateF} {a : Addr} {cell : HeapCell}
    (hlt : a.id < σF.nextAddr) (hget : σF.heapT.get a.id = some cell) :
    Heap.lookup (γF σF).heap (Loc.base a) = some cell := by
  show Heap.lookup (γH σF.heapT σF.nextAddr) (Loc.base ⟨a.id⟩) = some cell
  rw [γH_lookup]
  simp [hlt, hget]

/-! ### Slow-side arm equations (hypothesis-conditioned, the StepKit
style): each reduces the original's base arm under known scrutinees.
The proof pattern of record (U4 template): `simp only [<def>, <scrutinee
equations>]` unfolds the definition AND iota-reduces its matches, then
`rfl` closes the join-point/bind plumbing. -/

theorem loadLoc_base_eq {σ : ExecState} {a : Addr} {cell : HeapCell}
    (hl : Heap.lookup σ.heap (Loc.base a) = some cell) :
    loadLoc σ (Loc.base a) = .ok cell.value := by
  simp only [loadLoc, hl]; rfl

theorem storeLoc_base_typed_eq {σ : ExecState} {a : Addr} {cell : HeapCell}
    {ty : Ty} (v : GoValue)
    (hl : Heap.lookup σ.heap (Loc.base a) = some cell)
    (hd : cell.declaredTy = some ty) :
    storeLoc σ (Loc.base a) v =
      (normalizeValueForTy σ ty v).bind fun value =>
        .ok { σ with heap := Heap.set σ.heap (Loc.base a) { cell with value } } := by
  simp only [storeLoc, hl, hd]; rfl

theorem storeLoc_base_untyped_eq {σ : ExecState} {a : Addr} {cell : HeapCell}
    (v : GoValue)
    (hl : Heap.lookup σ.heap (Loc.base a) = some cell)
    (hd : cell.declaredTy = none) :
    storeLoc σ (Loc.base a) v =
      (coerceStoredValue cell.value v).bind fun value =>
        .ok { σ with heap := Heap.set σ.heap (Loc.base a) { cell with value } } := by
  simp only [storeLoc, hl, hd]; rfl

theorem loadLocF_ok {σF : ExecStateF} :
    ∀ {loc : Loc} {v : GoValue},
    loadLocF σF loc = .ok v → loadLoc (γF σF) loc = .ok v := by
  intro loc
  induction loc with
  | base a =>
      intro v h
      unfold loadLocF at h
      split at h
      case isTrue hlt =>
        split at h
        case h_1 cell hget =>
            rw [loadLoc_base_eq (γF_lookup_of_get hlt hget)]
            exact h
        case h_2 => simp at h
      case isFalse => simp at h
  | field base typeId fieldName ih =>
      intro v h
      unfold loadLocF at h
      try simp only [structTagCompatible_ctx] at h
      unfold loadLoc
      cases hb : loadLocF σF base with
      | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
      | ok bv =>
          rw [hb] at h
          rw [ih hb]
          simp only [Bind.bind, Except.bind] at h ⊢
          exact h
  | index base index ih =>
      intro v h
      unfold loadLocF at h
      try simp only [structTagCompatible_ctx] at h
      unfold loadLoc
      cases hb : loadLocF σF base with
      | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
      | ok bv =>
          rw [hb] at h
          rw [ih hb]
          simp only [Bind.bind, Except.bind] at h ⊢
          exact h

/-- The base-arm state image: the fast store's heap update abstracts to
the slow one's. -/
theorem γF_store_image {σF : ExecStateF} {a : Addr} (hlt : a.id < σF.nextAddr)
    (cell : HeapCell) :
    γF { σF with heapT := σF.heapT.set a.id cell } =
      { γF σF with heap := Heap.set (γF σF).heap (Loc.base a) cell } := by
  unfold γF
  simp only [ExecState.mk.injEq, and_true, true_and]
  exact γH_set _ _ _ a.id hlt

theorem storeLocF_ok {σF : ExecStateF} :
    ∀ {loc : Loc} {v : GoValue} {σF' : ExecStateF},
    storeLocF σF loc v = .ok σF' →
    storeLoc (γF σF) loc v = .ok (γF σF') := by
  intro loc
  induction loc with
  | base a =>
      intro v σF' h
      unfold storeLocF at h
      simp only [normalizeValueForTy_ctx] at h
      split at h
      case isTrue hlt =>
        split at h
        case h_1 cell hget =>
          split at h <;> rename_i hd
          case h_1 ty =>
              rw [storeLoc_base_typed_eq v (γF_lookup_of_get hlt hget) hd]
              cases hn : normalizeValueForTy (γF σF) ty v with
              | error e => rw [hn] at h; simp [Bind.bind, Except.bind] at h
              | ok v' =>
                  rw [hn] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure,
                    Except.ok.injEq] at h ⊢
                  rw [← h, γF_store_image hlt]
          case h_2 =>
              rw [storeLoc_base_untyped_eq v (γF_lookup_of_get hlt hget) hd]
              cases hn : coerceStoredValue cell.value v with
              | error e => rw [hn] at h; simp [Bind.bind, Except.bind] at h
              | ok v' =>
                  rw [hn] at h
                  simp only [Bind.bind, Except.bind, pure, Except.pure,
                    Except.ok.injEq] at h ⊢
                  rw [← h, γF_store_image hlt]
        case h_2 => simp at h
      case isFalse => simp at h
  | field base typeId fieldName ih =>
      intro v σF' h
      unfold storeLocF at h
      try simp only [structTagCompatible_ctx] at h
      unfold storeLoc
      cases hb : loadLocF σF base with
      | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
      | ok bv =>
          rw [hb] at h
          rw [loadLocF_ok hb]
          simp only [Bind.bind, Except.bind] at h ⊢
          cases bv
          case struct actualType fields =>
            simp only [] at h ⊢
            split at h <;> rename_i hguard
            · simp at h
            · rw [if_neg hguard]
              cases hs : StructFields.set fields fieldName v with
              | error e => rw [hs] at h; simp [Bind.bind, Except.bind] at h
              | ok updated =>
                  rw [hs] at h
                  simp only [Bind.bind, Except.bind] at h ⊢
                  exact ih h
          all_goals simp_all
  | index base index ih =>
      intro v σF' h
      unfold storeLocF at h
      try simp only [structTagCompatible_ctx] at h
      unfold storeLoc
      cases hb : loadLocF σF base with
      | error e => rw [hb] at h; simp [Bind.bind, Except.bind] at h
      | ok bv =>
          rw [hb] at h
          rw [loadLocF_ok hb]
          simp only [Bind.bind, Except.bind] at h ⊢
          cases bv
          case array values =>
            simp only [] at h ⊢
            cases hs : arraySet values index v with
            | error e => rw [hs] at h; simp [Bind.bind, Except.bind] at h
            | ok arr =>
                rw [hs] at h
                simp only [Bind.bind, Except.bind] at h ⊢
                exact ih h
          all_goals simp_all

theorem allocF_loc (σF : ExecStateF) (v : GoValue) (ty : Option Ty) :
    (allocF σF v ty).1 = (ExecState.alloc (γF σF) v ty).1 := rfl

theorem allocF_state (σF : ExecStateF) (v : GoValue) (ty : Option Ty) :
    γF (allocF σF v ty).2 = (ExecState.alloc (γF σF) v ty).2 := by
  unfold allocF ExecState.alloc ExecState.freshLoc γF
  simp only [ExecState.mk.injEq, and_true, true_and]
  exact (γH_slow_alloc _ _ _).symm

end GoLean.FastEval
