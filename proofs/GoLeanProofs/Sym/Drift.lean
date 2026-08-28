import GoLeanProofs.Sym.Conc

/-!
# Drift/commutation HELPER LAYER — mirror ⇒ machine (WP arc slice 4)

STATUS (phase 1, 2026-08-18): the per-helper commutation layer over ANY
sound interpretation (log JC-4) — the shared substrate for BOTH gated
theorems:

- THE DRIFT THEOREM (`stepFn'_concrete_agrees`, charter
  `docs/2026-08-16_wp-arc-charter.md:80-83`, embedding-mediated per
  ruled OQ3): the master ~200-arm success-only walk of `stepFn'`
  against `stepFn` at the concrete interpretation. NOT YET STATED in
  this module — the walk is the phase-2 continuation (this session
  landed the helper layer below plus the SPIKE's fragment-restricted
  step transport, `Sym/SpikeKadane.lean:spikeStep_sound`, which
  build-gates the spike fragment's arms TODAY). The park record with
  the remaining-arm inventory: `docs/wp-arc-log/s4.md`.
- The symbolic step-commutation (the refinement theorem's per-step
  half): the same walk at `symInterp ρ`; phase 2 composes it through
  the window driver.

Landed here, all success-only (`… = .ok r → machine = .ok (conc r)`;
quit outcomes assert nothing — `ExSim`'s success-steps-only
precedent): the `concV` collapse forms; the class-B projection lemmas;
heap lookup/set/alloc; the coerce fuel walk; the normalize fuel walk;
`StructFields` lookup/set (the generic `forIn_conc` loop transport);
array get/set; `loadLoc'`/`storeLoc'`/`loadMany'`; defaults; the
comparison family; `intBinaryResult'`; `seqCont'`/`contHeadLabel'`/
`pushDefer'`.
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine

variable {D : ScalarDom} {I : Interp D}

/-! ## Collapse lemmas: `concV` on aggregate constructors

The definition recurses through `attach` (termination); these restate
each aggregate equation in plain-`map` form — the working shapes every
commutation lemma rewrites with. -/

@[simp] theorem concV_unit : concV I .unit = .unit := by simp [concV]
@[simp] theorem concV_bool (b : D.BoolR) :
    concV I (.bool b) = .bool (I.boolV b) := by simp [concV]
@[simp] theorem concV_int (v : D.IntR) (kind : IntKind) :
    concV I (.int v kind) = .int (I.intV v) kind := by simp [concV]
@[simp] theorem concV_float (bits : Nat) (kind : FloatKind) :
    concV I (.float bits kind) = .float bits kind := by simp [concV]
@[simp] theorem concV_string (s : GoString) :
    concV I (.string s) = .string s := by simp [concV]
@[simp] theorem concV_addr (loc : Loc) :
    concV I (.addr loc) = .addr loc := by simp [concV]
@[simp] theorem concV_nil : concV I .nil = .nil := by simp [concV]
@[simp] theorem concV_interface (dynTy : Ty) (inner : Value D) :
    concV I (.interface dynTy inner) = .interface dynTy (concV I inner) := by
  simp [concV]
@[simp] theorem concV_struct (tid : TypeId) (fields : Array (String × Value D)) :
    concV I (.struct tid fields)
      = .struct tid (fields.map (fun (name, v) => (name, concV I v))) := by
  simp only [concV]
  congr 1
  exact Array.attach_map_val _ (fun (p : String × Value D) => (p.fst, concV I p.snd))
@[simp] theorem concV_array (values : Array (Value D)) :
    concV I (.array values) = .array (values.map (concV I)) := by
  simp only [concV]
  congr 1
  exact Array.attach_map_val _ _
@[simp] theorem concV_slice (sv : SliceValue) :
    concV I (.slice sv) = .slice sv := by simp [concV]
@[simp] theorem concV_map (mv : MapValue) :
    concV I (.map mv) = .map mv := by simp [concV]
@[simp] theorem concV_mapData (entries : Array (Value D × Value D)) :
    concV I (.mapData entries)
      = .mapData (entries.map (fun (k, v) => (concV I k, concV I v))) := by
  simp only [concV]
  congr 1
  exact Array.attach_map_val _ (fun (p : Value D × Value D) => (concV I p.fst, concV I p.snd))
@[simp] theorem concV_chan (cv : ChanValue) :
    concV I (.chan cv) = .chan cv := by simp [concV]
@[simp] theorem concV_chanData (buf : Array (Value D)) (capacity : Nat)
    (closed : Bool) :
    concV I (.chanData buf capacity closed)
      = .chanData (buf.map (concV I)) capacity closed := by
  simp only [concV]
  congr 1
  exact Array.attach_map_val _ _
@[simp] theorem concV_funcVal (fid : FuncId) (captured : List (Value D)) :
    concV I (.funcVal fid captured)
      = .funcVal fid (captured.map (concV I)) := by
  simp only [concV]
  congr 1
  exact List.attach_map_val
@[simp] theorem concV_syncData (p : SyncPrim) :
    concV I (.syncData p) = .syncData p := by simp [concV]

/-! ## Projection commutation (Group A: the class-B census, transported)

Success-only throughout (`… = .ok r → machine = .ok (conc r)`): quit
outcomes assert nothing. -/

theorem asIntAt_conc (hI : I.Sound) {q : QuitSite} {v : Value D} {n : Int}
    (h : v.asIntAt q = .ok n) : valueAsInt (concV I v) = .ok n := by
  cases v <;> simp_all [Value.asIntAt, valueAsInt, quit]
  next payload kind =>
    cases htoi : D.toInt? payload with
    | none => rw [htoi] at h; exact absurd h (by simp)
    | some m =>
        rw [htoi] at h
        cases h
        exact hI.toInt? _ _ htoi

theorem asIntR_conc {v : Value D} {r : D.IntR} {kind : IntKind}
    (h : v.asIntR = .ok (r, kind)) :
    valueAsIntValue (concV I v) = .ok (I.intV r, kind) := by
  cases v <;> simp_all [Value.asIntR, valueAsIntValue, quit]

theorem asBoolAt_conc (hI : I.Sound) {q : QuitSite} {v : Value D} {b : Bool}
    (h : v.asBoolAt q = .ok b) : valueAsBool (concV I v) = .ok b := by
  cases v <;> simp_all [Value.asBoolAt, valueAsBool, quit]
  next payload =>
    cases htob : D.toBool? payload with
    | none => rw [htob] at h; exact absurd h (by simp)
    | some m =>
        rw [htob] at h
        cases h
        exact hI.toBool? _ _ htob

theorem asLoc_conc {v : Value D} {loc : Loc} (h : v.asLoc = .ok loc) :
    valueAsLoc (concV I v) = .ok loc := by
  cases v <;> simp_all [Value.asLoc, valueAsLoc, quit]

theorem asSlice_conc {v : Value D} {sv : SliceValue} (h : v.asSlice = .ok sv) :
    valueAsSlice (concV I v) = .ok sv := by
  cases v <;> simp_all [Value.asSlice, valueAsSlice, quit]

theorem asMap_conc {v : Value D} {mv : MapValue} (h : v.asMap = .ok mv) :
    valueAsMap (concV I v) = .ok mv := by
  cases v <;> simp_all [Value.asMap, valueAsMap, quit]

theorem deferrable_conc {v : Value D} {b : Bool} (h : v.deferrable = .ok b) :
    deferrableCallee (concV I v) = b := by
  cases v <;> simp_all [Value.deferrable, deferrableCallee, quit]

/-! ## Heap commutation (Group B) -/

theorem lookup_conc (h : Heap D) (loc : Loc) :
    GoCore.Heap.lookup (concHeap I h) loc
      = (Heap.lookup h loc).map (concCell I) := by
  induction h with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨l, cell⟩ := hd
      by_cases hl : (l == loc) = true
      · simp [concHeap, GoCore.Heap.lookup, Heap.lookup, hl]
      · simp [concHeap, GoCore.Heap.lookup, Heap.lookup, hl] at ih ⊢
        simpa [concHeap] using ih

theorem set_conc (h : Heap D) (loc : Loc) (cell : HeapCell D) :
    GoCore.Heap.set (concHeap I h) loc (concCell I cell)
      = concHeap I (Heap.set h loc cell) := by
  induction h with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨l, old⟩ := hd
      by_cases hl : (l == loc) = true
      · simp [concHeap, GoCore.Heap.set, Heap.set, hl]
      · simp [concHeap, GoCore.Heap.set, Heap.set, hl] at ih ⊢
        simpa [concHeap] using ih

theorem freshLoc_conc (σ : ExecState) (s : State D) :
    (concS I σ s).freshLoc
      = ((s.freshLoc).1, concS I σ (s.freshLoc).2) := rfl

theorem alloc_conc (σ : ExecState) (s : State D) (v : Value D)
    (ty : Option Ty) :
    (concS I σ s).alloc (concV I v) ty
      = ((s.alloc v ty).1, concS I σ (s.alloc v ty).2) := by
  have hset := set_conc (I := I) s.heap (.base ⟨s.nextAddr⟩)
    (.mk ty v)
  simp only [concCell] at hset
  simp only [ExecState.alloc, State.alloc, ExecState.freshLoc, State.freshLoc,
    concS, hset]

/-! ## Value-walk commutation (Group D) -/

/-- Coerce commutation (untyped-cell stores), fuel-indexed. -/
theorem coerceFuel_conc (hI : I.Sound) :
    ∀ (fuel : Nat) (old new out : Value D),
      coerceStoredValueFuel' fuel old new = .ok out →
      coerceStoredValue (concV I old) (concV I new) = .ok (concV I out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro old new out h
      simp only [coerceStoredValueFuel', quit] at h
      cases h
  | succ fuel ih =>
      have harr : ∀ (olds news : List (Value D)) (out : Array (Value D)),
          coerceListWith' (coerceStoredValueFuel' fuel) olds news = .ok out →
          coerceArray (olds.map (concV I)) (news.map (concV I))
            = .ok (out.map (concV I)) := by
        intro olds
        induction olds with
        | nil =>
            intro news out h
            cases news <;>
              simp_all [coerceListWith', coerceArray]
        | cons ov orest ihl =>
            intro news out h
            cases news with
            | nil => simp_all [coerceListWith', coerceArray]
            | cons nv nrest =>
                simp only [coerceListWith', bind_eq_ok] at h
                obtain ⟨head, hhead, tail, htail, hout⟩ := h
                cases hout
                simp only [List.map_cons, coerceArray, bind_eq_ok]
                exact ⟨_, ih _ _ _ hhead, _, ihl _ _ htail, by simp⟩
      have hstr : ∀ (olds news : List (String × Value D))
          (out : Array (String × Value D)),
          coerceFieldsWith' (coerceStoredValueFuel' fuel) olds news = .ok out →
          coerceStruct (olds.map (fun p => (p.1, concV I p.2)))
              (news.map (fun p => (p.1, concV I p.2)))
            = .ok (out.map (fun p => (p.1, concV I p.2))) := by
        intro olds
        induction olds with
        | nil =>
            intro news out h
            cases news <;>
              simp_all [coerceFieldsWith', coerceStruct]
        | cons ov orest ihl =>
            intro news out h
            obtain ⟨oname, ovalue⟩ := ov
            cases news with
            | nil => simp_all [coerceFieldsWith', coerceStruct]
            | cons nv nrest =>
                obtain ⟨nname, nvalue⟩ := nv
                simp only [coerceFieldsWith'] at h
                by_cases hn : (oname != nname) = true
                · rw [if_pos hn] at h
                  exact absurd h (by simp [quit, Bind.bind, Except.bind])
                · rw [if_neg hn] at h
                  simp only [pure_bind, bind_eq_ok] at h
                  obtain ⟨head, hhead, tail, htail, hout⟩ := h
                  cases hout
                  simp only [List.map_cons, coerceStruct]
                  rw [if_neg (by simpa using hn)]
                  simp only [pure_bind, bind_eq_ok]
                  exact ⟨_, ih _ _ _ hhead, _, ihl _ _ htail, by simp⟩
      intro old new out h
      cases old <;> cases new <;>
        simp only [coerceStoredValueFuel', quit] at h <;>
        first
          | (cases h; done)
          | (cases h; simp [coerceStoredValue]; done)
          | skip
      all_goals try (cases h; done)
      -- int/int
      case succ.int.int =>
        rename_i v kind value kind1
        cases h
        simp [coerceStoredValue, hI.norm]
      -- float/float
      case succ.float.float =>
        rename_i bits kind bits1 k
        by_cases hk : (k == kind) = true
        · rw [if_pos hk] at h
          cases h
          simp only [concV_float, coerceStoredValue]
          rw [if_pos hk]
          rfl
        · rw [if_neg hk] at h
          exact absurd h (by simp)
      -- array/array
      case succ.array.array =>
        rename_i oldValues newValues
        by_cases hsz : (oldValues.size != newValues.size) = true
        · rw [if_pos hsz] at h
          exact absurd h (by simp)
        · rw [if_neg hsz] at h
          rcases hok : coerceListWith' (coerceStoredValueFuel' fuel)
              oldValues.toList newValues.toList with _ | arr
          · rw [hok] at h
            exact absurd h (by simp [Functor.map, Except.map])
          · rw [hok] at h
            simp only [Functor.map, Except.map] at h
            cases h
            have := harr _ _ _ hok
            simp only [concV_array, coerceStoredValue]
            rw [if_neg (by simp_all)]
            simp only [Array.toList_map] at this ⊢
            rw [this]
            simp [Functor.map, Except.map]
      -- struct/struct
      case succ.struct.struct =>
        rename_i oldType oldFields newType newFields
        by_cases hty : (oldType != newType) = true
        · rw [if_pos hty] at h
          exact absurd h (by simp)
        · rw [if_neg hty] at h
          by_cases hsz : (oldFields.size != newFields.size) = true
          · rw [if_pos hsz] at h
            exact absurd h (by simp)
          · rw [if_neg hsz] at h
            rcases hok : coerceFieldsWith' (coerceStoredValueFuel' fuel)
                oldFields.toList newFields.toList with _ | arr
            · rw [hok] at h
              exact absurd h (by simp [Functor.map, Except.map])
            · rw [hok] at h
              simp only [Functor.map, Except.map] at h
              cases h
              have := hstr _ _ _ hok
              simp only [concV_struct, coerceStoredValue]
              rw [if_neg (by simp_all), if_neg (by simp_all)]
              simp only [Array.toList_map] at this ⊢
              rw [this]
              simp [Functor.map, Except.map]

@[inherit_doc coerceFuel_conc]
theorem coerce_conc (hI : I.Sound) {old new out : Value D}
    (h : coerceStoredValue' old new = .ok out) :
    coerceStoredValue (concV I old) (concV I new) = .ok (concV I out) :=
  coerceFuel_conc hI _ old new out h

/-! ## Normalization commutation -/

theorem normalizeListWith_conc {f : Value D → M (Value D)}
    {g : GoValue → Except GoError GoValue}
    (hf : ∀ v out, f v = .ok out → g (concV I v) = .ok (concV I out)) :
    ∀ (l : List (Value D)) (arr : Array (Value D)),
      normalizeListWith' f l = .ok arr →
      normalizeListWith g (l.map (concV I)) = .ok (arr.map (concV I)) := by
  intro l
  induction l with
  | nil =>
      intro arr h
      simp only [normalizeListWith'] at h
      cases h
      simp [normalizeListWith]
  | cons v rest ihl =>
      intro arr h
      simp only [normalizeListWith', bind_eq_ok] at h
      obtain ⟨head, hhead, tail, htail, hout⟩ := h
      cases hout
      simp only [List.map_cons, normalizeListWith, bind_eq_ok]
      exact ⟨_, hf _ _ hhead, _, ihl _ htail, by simp⟩

/-- Normalization commutation: a successful mirror normalize at `ty`
transports to the machine's, at the SAME fuel, for EVERY state (the
mirror refutes the `.defined` arms, the only state consumers). -/
theorem normalizeFuel_conc (hI : I.Sound) (σ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty) (v out : Value D),
      normalizeValueForTyFuel' fuel ty v = .ok out →
      normalizeValueForTyFuel fuel σ ty (concV I v) = .ok (concV I out) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v out h
      simp only [normalizeValueForTyFuel', quit] at h
      cases h
  | succ fuel ih =>
      intro ty v out h
      cases ty <;> cases v <;>
        simp only [normalizeValueForTyFuel', quit] at h <;>
        first
          | (cases h; done)
          | (cases h; simp [normalizeValueForTyFuel]; done)
          | skip
      all_goals try (cases h; done)
      case succ.int.int =>
        rename_i kind payload kind1
        cases h
        simp [normalizeValueForTyFuel, hI.norm]
      case succ.float.float =>
        rename_i kind bits k
        by_cases hk : (k == kind) = true
        · rw [if_pos hk] at h
          cases h
          simp only [concV_float, normalizeValueForTyFuel]
          rw [if_pos hk]
          rfl
        · rw [if_neg hk] at h
          cases h
      case succ.array.array =>
        rename_i length elem values
        by_cases hsz : (values.size != length) = true
        · rw [if_pos hsz] at h
          cases h
        · rw [if_neg hsz] at h
          rcases hok : normalizeListWith' (normalizeValueForTyFuel' fuel elem)
              values.toList with _ | arr
          · rw [hok] at h
            exact absurd h (by simp [Functor.map, Except.map])
          · rw [hok] at h
            simp only [Functor.map, Except.map] at h
            cases h
            have := normalizeListWith_conc (fun v out hv => ih elem v out hv)
              values.toList arr hok
            simp only [concV_array, normalizeValueForTyFuel]
            rw [if_neg (by simp_all)]
            simp only [Array.toList_map] at this ⊢
            rw [this]
            simp [Functor.map, Except.map]
      case succ.sync.syncData =>
        rename_i kind p
        by_cases hp : (p.kind == kind) = true
        · rw [if_pos hp] at h
          cases h
          simp only [concV_syncData, normalizeValueForTyFuel]
          rw [if_pos hp]
          rfl
        · rw [if_neg hp] at h
          cases h

@[inherit_doc normalizeFuel_conc]
theorem normalize_conc (hI : I.Sound) (σ : ExecState) {ty : Ty}
    {v out : Value D} (h : normalizeValueForTy' ty v = .ok out) :
    normalizeValueForTy σ ty (concV I v) = .ok (concV I out) := by
  simp only [normalizeValueForTy]
  exact normalizeFuel_conc hI σ _ ty v out h

/-! ## Heap access commutation -/

private theorem foldl_option_conc {A B : Type} {t : A → B}
    {F : Option (Value D) → A → Option (Value D)}
    {G : Option GoValue → B → Option GoValue}
    (hFG : ∀ acc a, G (acc.map (concV I)) (t a) = (F acc a).map (concV I)) :
    ∀ (l : List A) (acc : Option (Value D)),
      List.foldl G (acc.map (concV I)) (l.map t)
        = (List.foldl F acc l).map (concV I) := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a as ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, hFG]
      exact ih (F acc a)

theorem structLookup_conc (fields : Array (String × Value D))
    (needle : String) :
    StructFields.lookup (fields.map (fun p => (p.1, concV I p.2))) needle
      = (StructFields.lookup' fields needle).map (concV I) := by
  unfold StructFields.lookup StructFields.lookup'
  dsimp only
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map]
  refine foldl_option_conc ?_ fields.toList none
  intro acc p
  obtain ⟨pn, pv⟩ := p
  cases acc with
  | some v => rfl
  | none =>
      by_cases hn : (pn == needle) = true
      · simp [hn]
      · simp [hn]

theorem arrayIndexNat'_conc {n : Nat} {i : Int} {j : Nat}
    (h : arrayIndexNat' n i = .ok j) (vs : Array GoValue) (hsz : vs.size = n) :
    arrayIndexNat vs i = .ok j := by
  simp only [arrayIndexNat', quit] at h
  by_cases hneg : i < 0
  · rw [if_pos hneg] at h
    cases h
  · rw [if_neg hneg] at h
    by_cases hlt : i.toNat < n
    · rw [if_pos hlt] at h
      cases h
      simp only [arrayIndexNat, hsz]
      rw [if_neg hneg, if_pos hlt]
      rfl
    · rw [if_neg hlt] at h
      cases h

/-! ## Generic loop transport (the `forIn` shape of every mirrored
op-table `for` loop) -/

/-- Step-outcome transport for `forIn` bodies. -/
inductive StepConc (R : β → β' → Prop) : ForInStep β → ForInStep β' → Prop
  | done {x y} : R x y → StepConc R (.done x) (.done y)
  | yield {x y} : R x y → StepConc R (.yield x) (.yield y)

/-- Transport a successful mirror `forIn` over a list to the machine's
`forIn` over the element-mapped list, along a state relation `R`. -/
theorem forIn_conc {A B β β' : Type} {R : β → β' → Prop} {t : A → B}
    {f : A → β → M (ForInStep β)}
    {g : B → β' → Except GoError (ForInStep β')} :
    ∀ {l : List A} {x : β} {y : β'}, R x y →
      (∀ a ∈ l, ∀ x y, R x y → ∀ st, f a x = .ok st →
        ∃ st', g (t a) y = .ok st' ∧ StepConc R st st') →
      ∀ {out : β}, forIn l x f = .ok out →
        ∃ out', forIn (l.map t) y g = .ok out' ∧ R out out' := by
  intro l
  induction l with
  | nil =>
      intro x y hR _ out h
      simp only [List.forIn_nil] at h
      cases h
      exact ⟨y, by simp, hR⟩
  | cons a as ih =>
      intro x y hR hstep out h
      simp only [List.forIn_cons, bind_eq_ok] at h
      obtain ⟨st, hst, hrest⟩ := h
      obtain ⟨st', hst', hcorr⟩ :=
        hstep a (List.mem_cons_self) x y hR st hst
      cases hcorr with
      | done hR' =>
          simp only [pure, Except.pure] at hrest
          cases hrest
          refine ⟨_, ?_, hR'⟩
          simp only [List.map_cons, List.forIn_cons, hst', bind_eq_ok]
          exact ⟨_, rfl, by simp [pure, Except.pure]⟩
      | yield hR' =>
          obtain ⟨out', hout', hRout⟩ := ih hR'
            (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')) hrest
          refine ⟨out', ?_, hRout⟩
          simp only [List.map_cons, List.forIn_cons, hst', bind_eq_ok]
          exact ⟨_, rfl, hout'⟩

/-- The machine-side loop body of `StructFields.set`, named so the
`forIn` transport's `g` instantiation is first-order. -/
-- 4.32.2: the do-desugar's loop state is now `(out, found) : _ × Bool`
-- in declaration order (was `MProd Bool (Array _)`), and the junk
-- `pure PUnit.unit` binds are gone — this named body mirrors it exactly.
private def setLoopG (needle : String) (w : GoValue)
    (b : String × GoValue) (y : Array (String × GoValue) × Bool) :
    Except GoError (ForInStep (Array (String × GoValue) × Bool)) :=
  if (b.fst == needle) = true then
    pure (ForInStep.yield (y.fst.push (b.fst, w), true))
  else
    pure (ForInStep.yield (y.fst.push (b.fst, b.snd), y.snd))

/-- Struct-field replacement commutation (the first `forIn` transport
consumer; the loop relation is equality-to-image). -/
theorem structSet_conc {fields : Array (String × Value D)} {needle : String}
    {v : Value D} {out : Array (String × Value D)}
    (h : StructFields.set' fields needle v = .ok out) :
    StructFields.set (fields.map (fun p => (p.1, concV I p.2))) needle
        (concV I v)
      = .ok (out.map (fun p => (p.1, concV I p.2))) := by
  unfold StructFields.set' at h
  unfold StructFields.set
  dsimp only at h ⊢
  rw [← Array.forIn_toList] at h
  rw [← Array.forIn_toList, Array.toList_map]
  simp only [bind_eq_ok] at h ⊢
  obtain ⟨r, hloop, hfin⟩ := h
  refine ⟨⟨r.fst.map (fun p => (p.1, concV I p.2)), r.snd⟩, ?_, ?_⟩
  · have hstep : ∀ a ∈ fields.toList,
        ∀ (x : Array (String × Value D) × Bool)
          (y : Array (String × GoValue) × Bool),
        y = ⟨x.fst.map (fun p => (p.1, concV I p.2)), x.snd⟩ →
        ∀ st, ((if (a.fst == needle) = true then
                 pure (ForInStep.yield
                   ((x.fst.push (a.fst, v), true) :
                     Array (String × Value D) × Bool))
               else
                 pure (ForInStep.yield
                   ((x.fst.push (a.fst, a.snd), x.snd) :
                     Array (String × Value D) × Bool))) :
                 M (ForInStep (Array (String × Value D) × Bool)))
               = .ok st →
          ∃ st', setLoopG needle (concV I v)
                   ((fun p => (p.1, concV I p.2)) a) y = .ok st' ∧
            StepConc (fun m m' =>
              m' = ⟨m.fst.map (fun p => (p.1, concV I p.2)), m.snd⟩) st st' := by
      intro a _ x y hR st hst
      obtain ⟨xs, xf⟩ := x
      subst hR
      unfold setLoopG
      by_cases hn : (a.fst == needle) = true
      · rw [if_pos hn] at hst
        rw [if_pos hn]
        simp only [pure, Except.pure] at hst ⊢
        cases hst
        exact ⟨_, rfl, .yield (by simp)⟩
      · rw [if_neg hn] at hst
        rw [if_neg hn]
        simp only [pure, Except.pure] at hst ⊢
        cases hst
        exact ⟨_, rfl, .yield (by simp)⟩
    obtain ⟨out', hout', hR⟩ := forIn_conc
      (R := fun (m : Array (String × Value D) × Bool)
            (m' : Array (String × GoValue) × Bool) =>
              m' = ⟨m.fst.map (fun p => (p.1, concV I p.2)), m.snd⟩)
      (t := fun p => (p.1, concV I p.2)) (y := ⟨#[], false⟩)
      (g := setLoopG needle (concV I v))
      (by simp) hstep hloop
    rw [hR] at hout'
    exact hout'
  · obtain ⟨rs, rf⟩ := r
    dsimp only at hfin ⊢
    by_cases hf : rf = true
    · rw [if_pos hf] at hfin
      simp only [pure, Except.pure] at hfin
      cases hfin
      rw [if_pos hf]
      rfl
    · rw [if_neg hf] at hfin
      exact absurd hfin (by simp [quit])

/-! ## Array-cell and heap-location access commutation -/

theorem arrayGet_conc {values : Array (Value D)} {i : Int} {v : Value D}
    (h : arrayGet' values i = .ok v) :
    arrayGet (values.map (concV I)) i = .ok (concV I v) := by
  simp only [arrayGet', bind_eq_ok, quit] at h
  obtain ⟨j, hj, h2⟩ := h
  rcases hv : values[j]? with _ | val
  · rw [hv] at h2
    cases h2
  · rw [hv] at h2
    cases h2
    simp only [arrayGet, bind_eq_ok]
    refine ⟨j, arrayIndexNat'_conc hj _ (by simp), ?_⟩
    rw [Array.getElem?_map, hv]
    rfl

theorem arraySet_conc (hI : I.Sound) {values : Array (Value D)} {i : Int}
    {v : Value D} {out : Array (Value D)}
    (h : arraySet' values i v = .ok out) :
    arraySet (values.map (concV I)) i (concV I v)
      = .ok (out.map (concV I)) := by
  simp only [arraySet', bind_eq_ok, quit] at h
  obtain ⟨j, hj, h2⟩ := h
  rcases hv : values[j]? with _ | old
  · rw [hv] at h2
    cases h2
  · rw [hv] at h2
    simp only [bind_eq_ok] at h2
    obtain ⟨cv, hcv, h3⟩ := h2
    cases h3
    simp only [arraySet, bind_eq_ok]
    refine ⟨j, arrayIndexNat'_conc hj _ (by simp), ?_⟩
    rw [Array.getElem?_map, hv]
    simp only [Option.map, bind_eq_ok]
    refine ⟨_, coerce_conc hI hcv, ?_⟩
    have hjlt : j < values.size := by
      simp only [arrayIndexNat', quit] at hj
      by_cases hneg : i < 0
      · rw [if_pos hneg] at hj; cases hj
      · rw [if_neg hneg] at hj
        by_cases hlt : i.toNat < values.size
        · rw [if_pos hlt] at hj; cases hj; exact hlt
        · rw [if_neg hlt] at hj; cases hj
    simp [Array.set!, Array.setIfInBounds, hjlt, Array.map_set]

-- `quit` below is load-bearing for uniform simp progress across the
-- 18-way value case split (removing it changes which branches fail);
-- the unused-arg lint false-flags it (s1 gotcha (b)).
set_option linter.unusedSimpArgs false in
theorem loadLoc_conc (σ : ExecState) {s : State D} :
    ∀ {loc : Loc} {v : Value D}, loadLoc' s loc = .ok v →
      loadLoc (concS I σ s) loc = .ok (concV I v) := by
  intro loc
  induction loc with
  | base a =>
      intro v h
      simp only [loadLoc', quit] at h
      rcases hq : Heap.lookup s.heap (.base a) with _ | cell
      · rw [hq] at h
        cases h
      · rw [hq] at h
        cases cell with
        | atom a' => cases h
        | mk dty cv =>
            cases h
            simp only [loadLoc, concS]
            rw [lookup_conc, hq]
            rfl
  | field base tid fname ih =>
      intro v h
      simp only [loadLoc', bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [loadLoc, bind_eq_ok]
      refine ⟨concV I bv, ih hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next actual fields =>
        simp only [concV_struct]
        by_cases hty : (actual != tid) = true
        · rw [if_pos hty] at h2
          cases h2
        · rw [if_neg hty] at h2
          have hty2 : ¬(actual != tid
              && !structTagCompatible (concS I σ s) actual tid) = true := by
            simp only [Bool.not_eq_true] at hty
            simp [hty]
          rw [if_neg hty2]
          rcases hf : StructFields.lookup' fields fname with _ | value
          · rw [hf] at h2
            cases h2
          · rw [hf] at h2
            cases h2
            rw [structLookup_conc, hf]
            rfl
  | index base i ih =>
      intro v h
      simp only [loadLoc', bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [loadLoc, bind_eq_ok]
      refine ⟨concV I bv, ih hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next values =>
        simp only [concV_array]
        exact arrayGet_conc h2

-- `quit` below is load-bearing for uniform simp progress across the
-- 18-way value case split (removing it changes which branches fail);
-- the unused-arg lint false-flags it (s1 gotcha (b)).
set_option linter.unusedSimpArgs false in
theorem storeLoc_conc (hI : I.Sound) (σ : ExecState) {s : State D} :
    ∀ {loc : Loc} {v : Value D} {s' : State D}, storeLoc' s loc v = .ok s' →
      storeLoc (concS I σ s) loc (concV I v) = .ok (concS I σ s') := by
  intro loc
  induction loc with
  | base a =>
      intro v s' h
      simp only [storeLoc', quit] at h
      rcases hq : Heap.lookup s.heap (.base a) with _ | cell
      · rw [hq] at h
        cases h
        simp only [storeLoc, concS]
        rw [lookup_conc, hq]
        simp only [Option.map]
        rw [show ({ value := concV I v } : GoCore.HeapCell)
              = concCell I (.mk none v) from rfl, set_conc]
        rfl
      · rw [hq] at h
        rcases cell with ⟨dty, oldv⟩ | ca
        case atom => cases h
        cases dty with
        | none =>
            simp only [bind_eq_ok] at h
            obtain ⟨nv, hnv, h2⟩ := h
            cases h2
            simp only [storeLoc, concS]
            rw [lookup_conc, hq]
            simp only [Option.map, concCell, bind_eq_ok]
            refine ⟨concV I nv, coerce_conc hI hnv, ?_⟩
            rw [show ({ declaredTy := none, value := concV I nv } : GoCore.HeapCell)
                  = concCell I (.mk none nv) from rfl,
              set_conc]
            rfl
        | some ty =>
            simp only [bind_eq_ok] at h
            obtain ⟨nv, hnv, h2⟩ := h
            cases h2
            simp only [storeLoc, concS]
            rw [lookup_conc, hq]
            simp only [Option.map, concCell, bind_eq_ok]
            refine ⟨concV I nv, normalize_conc hI (concS I σ s) hnv, ?_⟩
            rw [show ({ declaredTy := some ty, value := concV I nv } : GoCore.HeapCell)
                  = concCell I (.mk (some ty) nv) from rfl,
              set_conc]
            rfl
  | field base tid fname ih =>
      intro v s' h
      simp only [storeLoc', bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [storeLoc, bind_eq_ok]
      refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next actual fields =>
        simp only [concV_struct]
        by_cases hty : (actual != tid) = true
        · rw [if_pos hty] at h2
          cases h2
        · rw [if_neg hty] at h2
          have hty2 : ¬(actual != tid
              && !structTagCompatible (concS I σ s) actual tid) = true := by
            simp only [Bool.not_eq_true] at hty
            simp [hty]
          rw [if_neg hty2]
          simp only [bind_eq_ok] at h2
          obtain ⟨updated, hupd, h3⟩ := h2
          simp only [pure_bind, bind_eq_ok]
          refine ⟨_, structSet_conc hupd, ?_⟩
          have := ih h3
          simpa [concV_struct] using this
  | index base i ih =>
      intro v s' h
      simp only [storeLoc', bind_eq_ok, quit] at h
      obtain ⟨bv, hbv, h2⟩ := h
      simp only [storeLoc, bind_eq_ok]
      refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
      cases bv <;> simp only [quit] at h2 <;> try (cases h2; done)
      next values =>
        simp only [concV_array]
        simp only [bind_eq_ok] at h2
        obtain ⟨updated, hupd, h3⟩ := h2
        simp only [bind_eq_ok]
        refine ⟨_, arraySet_conc hI hupd, ?_⟩
        have := ih h3
        simpa [concV_array] using this

theorem loadMany_conc (σ : ExecState) {s : State D} :
    ∀ {locs : List Loc} {vs : List (Value D)}, loadMany' s locs = .ok vs →
      loadMany (concS I σ s) locs = .ok (vs.map (concV I)) := by
  intro locs
  induction locs with
  | nil =>
      intro vs h
      simp only [loadMany'] at h
      cases h
      simp [loadMany]
  | cons loc rest ih =>
      intro vs h
      simp only [loadMany', bind_eq_ok] at h
      obtain ⟨v, hv, tail, htail, hout⟩ := h
      cases hout
      simp only [loadMany, bind_eq_ok]
      exact ⟨_, loadLoc_conc σ hv, _, ih htail, by simp⟩

/-! ## Defaults, comparisons, control glue -/

theorem defaultFuel_conc (hI : I.Sound) (σ : ExecState) :
    ∀ (fuel : Nat) (ty : Ty) (v : Value D),
      defaultValueFuel' fuel ty = .ok v →
      defaultValueFuel fuel σ ty = .ok (concV I v) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ty v h
      simp only [defaultValueFuel', quit] at h
      cases h
  | succ fuel ih =>
      intro ty v h
      cases ty <;>
        simp only [defaultValueFuel', quit] at h <;>
        first
          | (cases h; done)
          | (cases h; simp [defaultValueFuel, hI.litB, hI.litI]; done)
          | skip
      case array length elem =>
        by_cases hlen : (length == 0) = true
        · rw [if_pos hlen] at h
          cases h
          simp only [defaultValueFuel]
          rw [if_pos hlen]
          simp
        · rw [if_neg hlen] at h
          simp only [bind_eq_ok] at h
          obtain ⟨ed, hed, hout⟩ := h
          cases hout
          simp only [defaultValueFuel]
          rw [if_neg hlen]
          simp only [pure_bind, bind_eq_ok]
          exact ⟨_, ih _ _ hed, by simp [concV_array, Array.map_replicate]⟩

/-- Default-value commutation at the seeded fuel. -/
theorem default_conc (hI : I.Sound) (σ : ExecState) {ty : Ty} {v : Value D}
    (h : defaultValue' ty = .ok v) : defaultValue σ ty = .ok (concV I v) := by
  simp only [defaultValue]
  exact defaultFuel_conc hI σ _ ty v h

theorem floatCompare_conc {cmp64 cmp32 : Nat → Nat → Bool} {lb : Nat}
    {lk : FloatKind} {rb : Nat} {rk : FloatKind} {b : Bool} (name : String)
    (h : floatCompareResult' cmp64 cmp32 lb lk rb rk = .ok b) :
    floatCompareResult name cmp64 cmp32 (.float lb lk) (.float rb rk)
      = .ok b := by
  simp only [floatCompareResult', quit] at h
  by_cases hk : (lk == rk) = true
  · rw [if_pos hk] at h
    cases lk <;> cases rk <;> simp_all [floatCompareResult]
  · rw [if_neg hk] at h
    cases h

theorem valueLess_conc (hI : I.Sound) {l r : Value D} {b : D.BoolR}
    (h : valueLess' l r = .ok b) :
    valueLess (concV I l) (concV I r) = .ok (I.boolV b) := by
  cases l <;> cases r <;>
    simp only [valueLess', quit, bind_eq_ok] at h <;>
    try (cases h; done)
  case int.int lv lkind rv rkind =>
    cases h
    simp [valueLess, hI.ltI]
  case float.float lb lk rb rk =>
    obtain ⟨bb, hbb, hout⟩ := h
    cases hout
    simp only [concV_float, valueLess]
    rw [floatCompare_conc _ hbb]
    simp [hI.litB]
  case string.string ls rs =>
    cases h
    simp [valueLess, hI.litB]

theorem valueAtMost_conc (hI : I.Sound) {l r : Value D} {b : D.BoolR}
    (h : valueAtMost' l r = .ok b) :
    valueAtMost (concV I l) (concV I r) = .ok (I.boolV b) := by
  cases l <;> cases r <;>
    simp only [valueAtMost', quit, bind_eq_ok] at h <;>
    try (cases h; done)
  case int.int lv lkind rv rkind =>
    cases h
    simp [valueAtMost, hI.leI]
  case float.float lb lk rb rk =>
    obtain ⟨bb, hbb, hout⟩ := h
    cases hout
    simp only [concV_float, valueAtMost]
    rw [floatCompare_conc _ hbb]
    simp [hI.litB]
  case string.string ls rs =>
    cases h
    simp [valueAtMost, hI.litB]

theorem valueGreater_conc (hI : I.Sound) {l r : Value D} {b : D.BoolR}
    (h : valueGreater' l r = .ok b) :
    valueGreater (concV I l) (concV I r) = .ok (I.boolV b) := by
  cases l <;> cases r <;>
    simp only [valueGreater', quit, bind_eq_ok] at h <;>
    try (cases h; done)
  case int.int lv lkind rv rkind =>
    cases h
    simp [valueGreater, hI.ltI]
  case float.float lb lk rb rk =>
    obtain ⟨bb, hbb, hout⟩ := h
    cases hout
    simp only [concV_float, valueGreater]
    rw [floatCompare_conc _ hbb]
    simp [hI.litB]
  case string.string ls rs =>
    cases h
    simp [valueGreater, hI.litB]

theorem valueAtLeast_conc (hI : I.Sound) {l r : Value D} {b : D.BoolR}
    (h : valueAtLeast' l r = .ok b) :
    valueAtLeast (concV I l) (concV I r) = .ok (I.boolV b) := by
  cases l <;> cases r <;>
    simp only [valueAtLeast', quit, bind_eq_ok] at h <;>
    try (cases h; done)
  case int.int lv lkind rv rkind =>
    cases h
    simp [valueAtLeast, hI.leI]
  case float.float lb lk rb rk =>
    obtain ⟨bb, hbb, hout⟩ := h
    cases hout
    simp only [concV_float, valueAtLeast]
    rw [floatCompare_conc _ hbb]
    simp [hI.litB]
  case string.string ls rs =>
    cases h
    simp [valueAtLeast, hI.litB]

theorem intBinaryResult_conc (hI : I.Sound) {opD : D.IntR → D.IntR → D.IntR}
    {opZ : Int → Int → Int} {name : String}
    (hop : ∀ a b, I.intV (opD a b) = opZ (I.intV a) (I.intV b))
    {l r out : Value D} (h : intBinaryResult' opD l r = .ok out) :
    intBinaryResult name opZ (concV I l) (concV I r) = .ok (concV I out) := by
  simp only [intBinaryResult', bind_eq_ok, quit] at h
  obtain ⟨⟨lv, lkind⟩, hl, ⟨rv, rkind⟩, hr, h2⟩ := h
  rcases hcomp : IntKind.compatibleResult lkind rkind with _ | kind
  · rw [hcomp] at h2
    cases h2
  · rw [hcomp] at h2
    cases h2
    simp only [intBinaryResult, bind_eq_ok]
    exact ⟨_, asIntR_conc hl, _, asIntR_conc hr,
      by rw [hcomp]; simp [hI.norm, hop, Bind.bind, Except.bind]⟩

theorem seqCont_conc (ss : List Stmt) (env : LocalEnv) (k : Cont D) :
    seqCont ss env (concK I k) = concK I (seqCont' ss env k) := by
  cases k <;> simp only [seqCont, seqCont', concK]
  next rest env' k' =>
    by_cases henv : env' = env
    · rw [if_pos henv, if_pos henv]
      simp [concK]
    · rw [if_neg henv, if_neg henv]
      simp [concK]

theorem contHeadLabel_conc (k : Cont D) :
    contHeadLabel (concK I k) = contHeadLabel' k := by
  cases k <;> simp [contHeadLabel, contHeadLabel', concK]

theorem pushDefer_conc (cv : Value D) (args : List (Value D)) :
    ∀ (k : Cont D),
      pushDefer (concV I cv, args.map (concV I)) (concK I k)
        = (pushDefer' (cv, args) k).map (concK I) := by
  intro k
  induction k <;> simp_all [pushDefer, pushDefer', concK]
  all_goals
    (rename_i ih
     cases hpd : pushDefer' (cv, args) _ <;>
       simp_all [Option.map])
  all_goals simp [concK]

/-! ## Commutation leaves: the slice/bounds/index family (loop-free
layer-2 helpers; WP arc s4 deliverable 5, first tranche) -/

theorem checkSliceBounds_conc {limit : Nat} {low high : Int}
    {p : Nat × Nat} (name : String)
    (h : checkSliceBounds' limit low high = .ok p) :
    checkSliceBounds name limit low high = .ok p := by
  simp only [checkSliceBounds', quit] at h
  by_cases h1 : high < 0
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : high > limit
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : low < 0
      · rw [if_pos h3] at h; cases h
      · rw [if_neg h3] at h
        by_cases h4 : low > high
        · rw [if_pos h4] at h; cases h
        · rw [if_neg h4] at h
          cases h
          simp only [checkSliceBounds]
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          rfl

theorem checkSliceBounds3_conc {max : Nat} {low high : Int}
    {p : Nat × Nat} (h : checkSliceBounds3' max low high = .ok p) :
    checkSliceBounds3 max low high = .ok p := by
  simp only [checkSliceBounds3', quit] at h
  by_cases h1 : high < 0
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : high > max
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : low < 0
      · rw [if_pos h3] at h; cases h
      · rw [if_neg h3] at h
        by_cases h4 : low > high
        · rw [if_pos h4] at h; cases h
        · rw [if_neg h4] at h
          cases h
          simp only [checkSliceBounds3]
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
          rfl

theorem checkSliceMax_conc {limit : Nat} {max : Int} {m : Nat}
    (name : String) (h : checkSliceMax' limit max = .ok m) :
    checkSliceMax name limit max = .ok m := by
  simp only [checkSliceMax', quit] at h
  by_cases h1 : max < 0
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : max > limit
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      cases h
      simp only [checkSliceMax]
      rw [if_neg h1, if_neg h2]
      rfl

theorem validateSlice_conc {sl : SliceValue}
    (h : validateSlice' sl = .ok ()) :
    validateSlice sl = .ok () := by
  simp only [validateSlice', quit] at h
  by_cases h1 : sl.len > sl.cap
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    simp only [validateSlice]
    rw [if_neg h1]
    rcases hb : sl.base with _ | b
    · rw [hb] at h
      by_cases h2 : (sl.offset == 0 && sl.len == 0 && sl.cap == 0) = true
      · rw [if_pos h2] at h
        rw [if_pos h2]
        rfl
      · rw [if_neg h2] at h
        cases h
    · rw [hb] at h
      rfl

theorem sliceIndexLoc_conc {sl : SliceValue} {i : Int} {loc : Loc}
    (h : sliceIndexLoc' sl i = .ok loc) :
    sliceIndexLoc sl i = .ok loc := by
  simp only [sliceIndexLoc', quit] at h
  rcases hval : validateSlice' sl with e | u
  · rw [hval] at h
    cases h
  · rw [hval] at h
    obtain ⟨⟩ := u
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    by_cases hneg : i < 0
    · rw [if_pos hneg] at h
      cases h
    · rw [if_neg hneg] at h
      by_cases hlt : i.toNat < sl.len
      · rw [if_pos hlt] at h
        rcases hb : sl.base with _ | b
        · rw [hb] at h
          cases h
        · rw [hb] at h
          cases h
          simp only [sliceIndexLoc, Bind.bind, Except.bind]
          rw [validateSlice_conc hval]
          dsimp only
          rw [if_neg hneg]
          simp only [pure, Except.pure]
          rw [if_pos hlt, hb]
      · rw [if_neg hlt] at h
        cases h

theorem sliceFromSlice_conc {sl : SliceValue} {low high : Int}
    {max : Option Int} {v : Value D}
    (h : sliceFromSlice' sl low high max = .ok v) :
    sliceFromSlice sl low high max = .ok (concV I v) := by
  simp only [sliceFromSlice'] at h
  rcases hval : validateSlice' sl with e | u
  · rw [hval] at h
    cases h
  · rw [hval] at h
    obtain ⟨⟩ := u
    simp only [Bind.bind, Except.bind] at h
    cases max with
    | none =>
        dsimp only at h
        rcases hp : checkSliceBounds' sl.cap low high with e | ⟨lo, hi⟩
        · rw [hp] at h
          cases h
        · rw [hp] at h
          cases h
          simp only [sliceFromSlice, Bind.bind, Except.bind]
          rw [validateSlice_conc hval]
          dsimp only
          rw [checkSliceBounds_conc "capacity" hp]
          simp
    | some m =>
        dsimp only at h
        rcases hm : checkSliceMax' sl.cap m with e | mm
        · rw [hm] at h
          cases h
        · rw [hm] at h
          dsimp only at h
          rcases hp : checkSliceBounds3' mm low high with e | ⟨lo, hi⟩
          · rw [hp] at h
            cases h
          · rw [hp] at h
            cases h
            simp only [sliceFromSlice, Bind.bind, Except.bind]
            rw [validateSlice_conc hval]
            dsimp only
            rw [checkSliceMax_conc "capacity" hm]
            dsimp only
            rw [checkSliceBounds3_conc hp]
            simp

theorem sliceFromArray_conc {base : Loc} {length : Nat} {low high : Int}
    {max : Option Int} {v : Value D}
    (h : sliceFromArray' base length low high max = .ok v) :
    sliceFromArray base length low high max = .ok (concV I v) := by
  simp only [sliceFromArray'] at h
  cases max with
  | none =>
      dsimp only at h
      rcases hp : checkSliceBounds' length low high with e | ⟨lo, hi⟩
      · rw [hp] at h
        cases h
      · rw [hp] at h
        cases h
        simp only [sliceFromArray, Bind.bind, Except.bind]
        rw [checkSliceBounds_conc "length" hp]
        simp
  | some m =>
      dsimp only at h
      rcases hm : checkSliceMax' length m with e | mm
      · rw [hm] at h
        cases h
      · simp only [hm, Bind.bind, Except.bind] at h
        rcases hp : checkSliceBounds3' mm low high with e | ⟨lo, hi⟩
        · simp only [hp] at h
          cases h
        · simp only [hp] at h
          cases h
          simp only [sliceFromArray, Bind.bind, Except.bind]
          rw [checkSliceMax_conc "length" hm]
          dsimp only
          rw [checkSliceBounds3_conc hp]
          simp

theorem stringSlice_conc {str : GoString} {low high : Int}
    {max : Option Int} {v : Value D}
    (h : stringSlice' str low high max = .ok v) :
    stringSlice str low high max = .ok (concV I v) := by
  simp only [stringSlice', quit] at h
  by_cases hm : max.isSome
  · rw [if_pos hm] at h
    exact absurd h (by simp [Bind.bind, Except.bind])
  · rw [if_neg hm] at h
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    rcases hp : checkSliceBounds' str.length low high with e | ⟨lo, hi⟩
    · rw [hp] at h
      cases h
    · rw [hp] at h
      cases h
      simp only [stringSlice, Bind.bind, Except.bind]
      rw [if_neg hm]
      simp only [pure, Except.pure]
      rw [checkSliceBounds_conc "length" hp]
      dsimp only
      simp

theorem stringByteGet_conc (hI : I.Sound) {str : GoString} {i : Int}
    {v : Value D} (h : stringByteGet' str i = .ok v) :
    stringByteGet str i = .ok (concV I v) := by
  simp only [stringByteGet', quit, Bind.bind, Except.bind, pure,
    Except.pure] at h
  by_cases hneg : i < 0
  · rw [if_pos hneg] at h
    cases h
  · rw [if_neg hneg] at h
    rcases hb : str.byte? i.toNat with _ | byte
    · rw [hb] at h
      cases h
    · rw [hb] at h
      cases h
      simp only [stringByteGet, Bind.bind, Except.bind, pure, Except.pure]
      rw [if_neg hneg]
      try dsimp only
      rw [hb]
      simp [hI.litI]

theorem applySlice_conc (σ : ExecState) {s : State D}
    {b : Value D} {low high : Int} {max : Option Int} {v : Value D}
    (h : applySlice' s b low high max = .ok v) :
    applySlice (concS I σ s) (concV I b) low high max
      = .ok (concV I v, concS I σ s) := by
  cases b <;> simp only [applySlice'] at h <;> try (cases h; done)
  case string str =>
    simp only [concV_string, applySlice, bind_eq_ok]
    exact ⟨_, stringSlice_conc h, rfl⟩
  case slice sl =>
    simp only [concV_slice, applySlice, bind_eq_ok]
    exact ⟨_, sliceFromSlice_conc h, rfl⟩
  case addr baseLoc =>
    simp only [bind_eq_ok] at h
    obtain ⟨bv, hbv, h2⟩ := h
    simp only [concV_addr, applySlice, bind_eq_ok]
    refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
    cases bv <;> try (cases h2; done)
    · next values =>
        simp only [concV_array, bind_eq_ok]
        rw [show (values.map (concV I)).size = values.size by simp]
        exact ⟨_, sliceFromArray_conc h2, rfl⟩
    · next sl =>
        simp only [concV_slice, bind_eq_ok]
        exact ⟨_, sliceFromSlice_conc h2, rfl⟩

theorem indexTargetLoc_conc (hI : I.Sound) (σ : ExecState) {s : State D}
    {b i : Value D} {loc : Loc}
    (h : indexTargetLoc' s b i = .ok loc) :
    indexTargetLoc (concS I σ s) (concV I b) (concV I i) = .ok loc := by
  simp only [indexTargetLoc', bind_eq_ok, quit] at h
  obtain ⟨iv, hiv, h2⟩ := h
  simp only [indexTargetLoc, bind_eq_ok]
  refine ⟨iv, asIntAt_conc hI hiv, ?_⟩
  cases b <;> try (cases h2; done)
  case slice sl =>
    simp only [concV_slice]
    exact sliceIndexLoc_conc h2
  case addr baseLoc =>
    simp only [bind_eq_ok] at h2
    obtain ⟨bv, hbv, h3⟩ := h2
    simp only [concV_addr, bind_eq_ok]
    refine ⟨concV I bv, loadLoc_conc σ hbv, ?_⟩
    cases bv <;> try (cases h3; done)
    · next values =>
        simp only [concV_array]
        simp only [bind_eq_ok] at h3
        obtain ⟨j, hj, h4⟩ := h3
        cases h4
        simp only [bind_eq_ok]
        exact ⟨j, arrayIndexNat'_conc hj _ (by simp), rfl⟩
    · next sl =>
        simp only [concV_slice]
        exact sliceIndexLoc_conc h3

end GoLean.Sym
