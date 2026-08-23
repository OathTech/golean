import GoLeanProofs.FastEval.Heap

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

open GoLean GoLean.GoCore

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
          if actualType != typeId && !structTagCompatible (γF σF) actualType typeId then
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
              | some ty => normalizeValueForTy (γF σF) ty value
              | none => coerceStoredValue cell.value value
            return { σF with heapT := σF.heapT.set a.id { cell with value } }
        | none => stuck "fastEval-stub: hole store below frontier"
      else stuck "fastEval-stub: store beyond frontier (create-on-missing unmirrored)"
  | .field base typeId fieldName, value => do
      match ← loadLocF σF base with
      | .struct actualType fields =>
          if actualType != typeId && !structTagCompatible (γF σF) actualType typeId then
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
