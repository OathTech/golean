import GoLeanProofs.Examples.WordFreq.Build
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.MapMem

/-!
# WordFreq — the shim's byte scan

The `goleanShimStringsFields` frame: prologue, the per-byte scan loop
over the FAMILY text (pure ASCII: letters `97`–`99`, separators
`32`/`9`), and the exit delivering the `[]string` of the family's
one-letter words into `words`.

**Placement discipline**: the front (cells 0–30) is concrete; every
scan-loop allocation (per-byte `w`/`c`, the long letter path's
`c1`/`c2`, per-append `$c16`/`$c17` and backings) is at a symbolic
address past it, and the `out` backing's address and capacity are
CHOICE-dependent (`append`'s spill path consumes a capacity choice),
so the loop state carries the backing through the `ScanBack` invariant
and the iteration/loop lemmas quantify `∃ k, b, cap, D, na, ch'`.

-- GAP-WITNESS: `[]string` slice vocabulary (make / append /
-- element store / visible-values at STRING elements) — `SliceMem` is
-- `[]uint64`-only; the conditioned facts below are what a
-- string-slice kit module would open with (2nd element family after
-- `SliceMem`'s; promotion candidate).
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Heap-split helpers (iteration cells as an explicit suffix) -/

theorem lookup_c1of1 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0)]) (.base ⟨na⟩) = some c0 := by
  rw [lookup_append_right (hD na (Nat.le_refl _))]
  exact lookup_singleton_self

theorem lookup_c1of2 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1)])
      (.base ⟨na⟩) = some c0 := by
  rw [lookup_append_right (hD na (by omega))]
  simp [Heap.lookup]

theorem lookup_c2of2 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1)])
      (.base ⟨na + 1⟩) = some c1 := by
  rw [lookup_append_right (hD (na + 1) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
  simp [Heap.lookup]

theorem lookup_c2of4 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)])
      (.base ⟨na + 1⟩) = some c1 := by
  rw [lookup_append_right (hD (na + 1) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
  simp [Heap.lookup]

theorem lookup_c3of3 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 : HeapCell} :
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2)]) (.base ⟨na + 2⟩) = some c2 := by
  rw [lookup_append_right (hD (na + 2) (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ na + 2)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ na + 2))]
  simp [Heap.lookup]

/-- Setting the LAST cell of a 2-cell suffix. -/
theorem set_c2of2 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c1' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1)])
        (.base ⟨na + 1⟩) c1'
      = D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1')] := by
  rw [set_append_right (hD (na + 1) (by omega))]
  simp [Heap.set, base_beq_false (by omega : na ≠ na + 1)]

theorem set_c1of1 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c0' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0)]) (.base ⟨na⟩) c0'
      = D ++ [(.base ⟨na⟩, c0')] := by
  rw [set_append_right (hD na (Nat.le_refl _))]
  exact congrArg _ set_singleton_self

theorem set_c3of3 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c2' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2)]) (.base ⟨na + 2⟩) c2'
      = D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
          (.base ⟨na + 2⟩, c2')] := by
  rw [set_append_right (hD (na + 2) (by omega))]
  simp [Heap.set, base_beq_false (by omega : na ≠ na + 2),
    base_beq_false (by omega : na + 1 ≠ na + 2)]

theorem set_c4of4 {D : Heap} {na : Nat} (hD : DeadFrom D na)
    {c0 c1 c2 c3 c3' : HeapCell} :
    Heap.set (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
        (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)]) (.base ⟨na + 3⟩) c3'
      = D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
          (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3')] := by
  rw [set_append_right (hD (na + 3) (by omega))]
  simp [Heap.set, base_beq_false (by omega : na ≠ na + 3),
    base_beq_false (by omega : na + 1 ≠ na + 3),
    base_beq_false (by omega : na + 2 ≠ na + 3)]

/-- `DeadFrom` after appending 4 fresh cells. -/
theorem DeadFrom.push4 {dead : Heap} {na : Nat} {c0 c1 c2 c3 : HeapCell}
    (h : DeadFrom dead na) :
    DeadFrom (dead ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),
      (.base ⟨na + 2⟩, c2), (.base ⟨na + 3⟩, c3)]) (na + 4) := by
  intro x hx
  rw [lookup_append_right (h x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : na + 3 ≠ x))]
  rfl

-- (`DeadFrom.set_below`, formerly here, is StepKit's `DeadFrom.set`
-- since WP arc s2 item 1; call sites re-pointed.)

/-! ## The `[]string` conditioned op facts (KIT-GAP block, see the
module docstring) -/

/-- The default `[n]string` backing at a SYMBOLIC length: `n` empty
strings. -/
theorem buildDefaultArrayValue_str (σ : ExecState) (n : Nat) :
    buildDefaultArrayValue σ n tStr
      = .ok (.array (List.replicate n (.string GoString.empty)).toArray) := by
  simp only [buildDefaultArrayValue, buildArrayValue,
    Std.Legacy.Range.forIn_eq_forIn_range', Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show ([:n] : Std.Legacy.Range).size = n from by
    simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := n) (n := n) (j := 0)
    (b := (#[] : Array GoValue))
    (Q := fun i acc =>
      acc = (List.replicate i (GoValue.string GoString.empty)).toArray)
    (out := fun _ acc => acc.push (.string GoString.empty))
    (res := (List.replicate n (GoValue.string GoString.empty)).toArray)
    ?hfill (by omega) (by simp) (by intro b' h; rw [h, Nat.zero_add])]
  · rfl
  · case hfill =>
      intro i acc hi hacc
      refine ⟨by simp [defaultValue, defaultValueFuel, typeResolutionFuel],
        ?_⟩
      rw [hacc, List.replicate_succ']
      simp [← List.toArray_replicate]

/-- `make([]string, 1, 1)` at a freshly-declared nil-slice target: the
one-slot backing (an empty string) at the allocator, the handle stored
over the target. -/
theorem applyStmtOp_makeSlice_str11 {σ : ExecState} {t : Nat}
    {ch : Choices}
    (hlook : Heap.lookup σ.heap (.base ⟨t⟩) = some slsNil)
    (ht : t ≠ σ.nextAddr) :
    applyStmtOp σ ch (.makeSlice tStr true) 1
      [.addr (.base ⟨t⟩), .int 1 .int, .int 1 .int]
      = .ok ({ σ with
          heap := Heap.set
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)
            (.base ⟨t⟩) ⟨some tSlS, slsVal σ.nextAddr 0 1 1⟩,
          nextAddr := σ.nextAddr + 1 }, ch) := by
  have hlook2 : Heap.lookup
      (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
        ⟨some (.array 1 tStr), .array #[.string GoString.empty]⟩)
      (.base ⟨t⟩) = some slsNil := by
    rw [Machine.Heap.lookup_set_ne
      (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega
        : (Loc.base ⟨σ.nextAddr⟩ : Loc) ≠ .base ⟨t⟩)]
    exact hlook
  simp only [applyStmtOp, applyStmtOpCore, Bind.bind, Except.bind, pure,
    Except.pure, valueAsInt]
  rw [show natFromNonnegativeInt
      "runtime error: makeslice: len out of range" (1 : Int) = .ok 1
      from rfl,
    show natFromNonnegativeInt
      "runtime error: makeslice: cap out of range" (1 : Int) = .ok 1
      from rfl]
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    show ¬ ((1 : Nat) < (1 : Nat)) from by omega, if_false,
    ExecState.alloc, ExecState.freshLoc, valueAsLoc]
  rw [show buildDefaultArrayValue σ 1 tStr
      = .ok (.array #[.string GoString.empty]) from by
    rw [buildDefaultArrayValue_str]
    rfl]
  simp only [storeLoc, hlook2, Bind.bind, Except.bind, pure, Except.pure]
  rw [show normalizeValueForTy
      { σ with
        heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
          (⟨some (.array 1 tStr),
            .array #[.string GoString.empty]⟩ : HeapCell),
        nextAddr := σ.nextAddr + 1 } tSlS (slsVal σ.nextAddr 0 1 1)
      = .ok (slsVal σ.nextAddr 0 1 1) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]]

/-- The element store `$c16[0] = <string>` through the index-chain
target over a 1-slot backing. -/
theorem storeTarget_c16 {σ : ExecState} {e : Nat} {v0 : GoString}
    {w : GoString}
    (hlook : Heap.lookup σ.heap (.base ⟨e⟩)
      = some ⟨some (.array 1 tStr), .array #[.string v0]⟩) :
    storeTarget σ (.chain (slsVal e 0 1 1) [.int 0 .int] [.index])
      (.string w)
      = .ok { σ with
          heap := Heap.set σ.heap (.base ⟨e⟩)
            ⟨some (.array 1 tStr), .array #[.string w]⟩ } := by
  simp only [storeTarget, resolveChain, indexTargetLoc, valueAsInt,
    Bind.bind, Except.bind, pure, Except.pure]
  rw [show sliceIndexLoc ⟨some (.base ⟨e⟩), 0, 1, 1⟩ ((0 : Int))
      = .ok (.index (.base ⟨e⟩) 0) from by
    have := GoLean.Iris.sliceIndexLoc_prefix (sta := ⟨e⟩) (n := 1)
      (cap := 1) (j := 0) (by omega) (by omega)
    simpa using this]
  simp only [valueAsLoc, Bind.bind, Except.bind, pure, Except.pure]
  simp only [storeLoc, loadLoc, hlook, Bind.bind, Except.bind, pure,
    Except.pure, arraySet]
  with_unfolding_all rfl

/-- Element-wise normalization by the identity is the identity. -/
theorem normalizeListWith_pure :
    ∀ l : List GoValue,
    normalizeListWith (fun x => (Except.ok x : Except GoError GoValue)) l
      = .ok l.toArray := by
  intro l
  induction l with
  | nil => rfl
  | cons v rest ih =>
      simp only [normalizeListWith, Bind.bind, Except.bind, pure,
        Except.pure] at ih ⊢
      rw [ih]
      simp

/-- Normalizing a string backing array at its declared type is the
identity (symbolic length). -/
theorem normalize_strArr (σ : ExecState) (fs : List (List UInt8))
    (cap : Nat) (hle : fs.length ≤ cap) :
    normalizeValueForTy σ (.array cap tStr) (strArr fs cap)
      = .ok (strArr fs cap) := by
  have hlen : ((fs.map (fun f => GoValue.string (gs f)))
      ++ List.replicate (cap - fs.length)
        (GoValue.string GoString.empty)).length = cap := by
    simp
    omega
  simp only [normalizeValueForTy, strArr]
  rw [show typeResolutionFuel = 1023 + 1 from rfl]
  simp only [normalizeValueForTyFuel]
  rw [show (((fs.map (fun f => GoValue.string (gs f)))
      ++ List.replicate (cap - fs.length)
        (GoValue.string GoString.empty)).toArray.size != cap) = false from by
    simp only [List.size_toArray, hlen]
    simp]
  simp only [Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [normalizeListWith_pure]
  rw [show (List.map (fun f => GoValue.string (gs f)) fs
      ++ List.replicate (cap - fs.length)
        (GoValue.string GoString.empty)).toArray
      = (⟨List.map (fun f => GoValue.string (gs f)) fs
          ++ List.replicate (cap - fs.length)
            (GoValue.string GoString.empty)⟩ : Array GoValue) from by
    apply Array.toList_inj.mp
    simp]
  rfl

/-- The visible values of the `out` slice: the field strings
(symbolic length; `forIn_range'_inv` engine). -/
theorem sliceVisibleValues_str {σ : ExecState} {b : Nat}
    {fs : List (List UInt8)} {cap : Nat}
    (hlook : Heap.lookup σ.heap (.base ⟨b⟩) = some (strArrCell fs cap))
    (hle : fs.length ≤ cap) :
    sliceVisibleValues σ ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩
      = .ok (fs.map (fun f => GoValue.string (gs f))).toArray := by
  simp only [sliceVisibleValues, validateSlice, Bind.bind, Except.bind,
    pure, Except.pure, if_neg (show ¬ fs.length > cap from by omega),
    Std.Legacy.Range.forIn_eq_forIn_range']
  rw [show ([:fs.length] : Std.Legacy.Range).size = fs.length from by
    simp [Std.Legacy.Range.size]]
  rw [GoLean.Iris.forIn_range'_inv (N := fs.length) (n := fs.length)
    (j := 0) (b := (#[] : Array GoValue))
    (Q := fun i acc =>
      acc = ((fs.take i).map (fun f => GoValue.string (gs f))).toArray)
    (out := fun i acc => acc.push (.string (gs (fs.getD i []))))
    (res := (fs.map (fun f => GoValue.string (gs f))).toArray)
    ?hfill (by omega) (by simp)
    (by intro b' hb'; rw [hb', Nat.zero_add, List.take_length])]
  case hfill =>
      intro i acc hi hacc
      constructor
      · have harr : ((⟨List.map (fun f => GoValue.string (gs f)) fs
              ++ List.replicate (cap - fs.length)
                (GoValue.string GoString.empty)⟩ : Array GoValue))[i]?
            = some (GoValue.string (gs (fs.getD i []))) := by
          rw [show ((⟨List.map (fun f => GoValue.string (gs f)) fs
              ++ List.replicate (cap - fs.length)
                (GoValue.string GoString.empty)⟩ : Array GoValue))[i]?
              = (List.map (fun f => GoValue.string (gs f)) fs
              ++ List.replicate (cap - fs.length)
                (GoValue.string GoString.empty))[i]?
            from List.getElem?_toArray]
          rw [List.getElem?_append_left (by simpa using hi),
            List.getElem?_map, List.getElem?_eq_getElem hi]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        have hidx : arrayIndexNat
            (⟨List.map (fun f => GoValue.string (gs f)) fs
              ++ List.replicate (cap - fs.length)
                (GoValue.string GoString.empty)⟩ : Array GoValue)
            (Int.ofNat i) = .ok i := by
          simp only [arrayIndexNat, Int.ofNat_eq_natCast, Bind.bind,
            Except.bind, pure, Except.pure]
          rw [if_neg (by omega : ¬ (((i : Nat) : Int) < 0)),
            Int.toNat_natCast,
            if_pos (show i < (⟨List.map (fun f => GoValue.string (gs f)) fs
                ++ List.replicate (cap - fs.length)
                  (GoValue.string GoString.empty)⟩ : Array GoValue).size
              from by
                simp only [List.size_toArray, List.length_append,
                  List.length_map, List.length_replicate]
                omega)]
        rw [show sliceIndexLoc ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩
            (Int.ofNat i) = .ok (.index (.base ⟨b⟩) (Int.ofNat i)) from by
          simpa using GoLean.Iris.sliceIndexLoc_prefix (sta := ⟨b⟩)
            (n := fs.length) (cap := cap) (j := i) hi hle]
        simp only [Bind.bind, Except.bind, pure, Except.pure, loadLoc,
          hlook, strArr, arrayGet, hidx, harr]
      · rw [hacc, GoLean.MapMem.take_succ_getD hi (d := [])]
        simp

/-- **The `append(out, $c16...)` IN-PLACE fact** (`len < cap`): the
element lands in the backing at index `len`, the handle's length
bumps, NO choice is consumed. -/
theorem applyStmtOp_append_str_inplace {σ : ExecState} {t b e : Nat}
    {fs : List (List UInt8)} {cap : Nat} {f : List UInt8} {ch : Choices}
    (hb : Heap.lookup σ.heap (.base ⟨b⟩) = some (strArrCell fs cap))
    (he : Heap.lookup σ.heap (.base ⟨e⟩)
      = some ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)
    (ht : Heap.lookup (Heap.set σ.heap (.base ⟨b⟩)
        (strArrCell (fs ++ [f]) cap)) (.base ⟨t⟩) = some slsNil)
    (hlt : fs.length < cap) :
    applyStmtOp σ ch (.appendSlice tStr) 1
      [.addr (.base ⟨t⟩), slsVal b 0 fs.length cap, slsVal e 0 1 1]
      = .ok ({ σ with
          heap := Heap.set
            (Heap.set σ.heap (.base ⟨b⟩) (strArrCell (fs ++ [f]) cap))
            (.base ⟨t⟩)
            ⟨some tSlS, slsVal b 0 (fs.length + 1) cap⟩ }, ch) := by
  have hvis : sliceVisibleValues σ ⟨some (.base ⟨e⟩), 0, 1, 1⟩
      = .ok #[.string (gs f)] := by
    have := sliceVisibleValues_str (σ := σ) (b := e) (fs := [f]) (cap := 1)
      (by simpa [strArrCell, strArr] using he) (by simp)
    simpa using this
  -- WP arc s2 item 3: the applyStmtOp unfolding replaced by the kit's
  -- `SliceMem.applyStmtOp_append1_inplace` (applied at the end).
  have hstore : storeLoc σ ((Loc.base ⟨b⟩).index
        (Int.ofNat (0 + fs.length + 0))) (GoValue.string (gs f))
      = .ok (wSt σ
          (Heap.set σ.heap (.base ⟨b⟩) (strArrCell (fs ++ [f]) cap))
          σ.nextAddr) := by
    simp only [storeLoc, loadLoc, hb, Bind.bind, Except.bind, pure,
      Except.pure]
    simp only [strArr]
    have hset : arraySet
        (⟨List.map (fun f => GoValue.string (gs f)) fs
          ++ List.replicate (cap - fs.length)
            (GoValue.string GoString.empty)⟩ : Array GoValue)
        (Int.ofNat (0 + fs.length + 0)) (GoValue.string (gs f))
        = .ok (⟨List.map (fun f => GoValue.string (gs f)) (fs ++ [f])
            ++ List.replicate (cap - (fs ++ [f]).length)
              (GoValue.string GoString.empty)⟩ : Array GoValue) := by
      have hrep : List.replicate (cap - fs.length)
          (GoValue.string GoString.empty)
          = GoValue.string GoString.empty
            :: List.replicate (cap - fs.length - 1)
              (GoValue.string GoString.empty) := by
        rw [show cap - fs.length = (cap - fs.length - 1) + 1 from by omega]
        rfl
      have hgetl : ((⟨List.map (fun f => GoValue.string (gs f)) fs
          ++ List.replicate (cap - fs.length)
            (GoValue.string GoString.empty)⟩ : Array GoValue))[fs.length]?
          = some (GoValue.string GoString.empty) := by
        rw [show ((⟨List.map (fun f => GoValue.string (gs f)) fs
            ++ List.replicate (cap - fs.length)
              (GoValue.string GoString.empty)⟩ : Array GoValue))[fs.length]?
            = (List.map (fun f => GoValue.string (gs f)) fs
            ++ List.replicate (cap - fs.length)
              (GoValue.string GoString.empty))[fs.length]?
          from List.getElem?_toArray]
        rw [hrep, show fs.length
            = (List.map (fun f => GoValue.string (gs f)) fs).length from by
          simp]
        exact GoLean.Iris.list_getElem?_middle _ _ _
      have hidx : arrayIndexNat
          (⟨List.map (fun f => GoValue.string (gs f)) fs
            ++ List.replicate (cap - fs.length)
              (GoValue.string GoString.empty)⟩ : Array GoValue)
          (Int.ofNat (0 + fs.length + 0)) = .ok fs.length := by
        simp only [arrayIndexNat, Int.ofNat_eq_natCast, Bind.bind,
          Except.bind, pure, Except.pure, Nat.zero_add, Nat.add_zero]
        rw [if_neg (by omega : ¬ (((fs.length : Nat) : Int) < 0)),
          Int.toNat_natCast,
          if_pos (show fs.length
              < (⟨List.map (fun f => GoValue.string (gs f)) fs
                ++ List.replicate (cap - fs.length)
                  (GoValue.string GoString.empty)⟩ : Array GoValue).size
            from by
              simp only [List.size_toArray, List.length_append,
                List.length_map, List.length_replicate]
              omega)]
      simp only [arraySet, hidx, Bind.bind, Except.bind, pure,
        Except.pure, hgetl]
      rw [show coerceStoredValue (GoValue.string GoString.empty)
          (GoValue.string (gs f)) = .ok (.string (gs f)) from rfl]
      show Except.ok
          ((⟨List.map (fun f => GoValue.string (gs f)) fs
            ++ List.replicate (cap - fs.length)
              (GoValue.string GoString.empty)⟩ : Array GoValue).set!
            fs.length (GoValue.string (gs f))) = _
      apply congrArg
      apply Array.toList_inj.mp
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
        List.toList_toArray]
      rw [hrep, show fs.length
          = (List.map (fun f => GoValue.string (gs f)) fs).length from by
        simp]
      rw [GoLean.Iris.list_set_middle]
      simp only [List.map_append, List.map_cons, List.map_nil,
        List.length_append, List.length_cons, List.length_nil]
      rw [show cap - (fs.length + (0 + 1)) = cap - fs.length - 1 from by
        omega]
      simp
    simp only [hset, Bind.bind, Except.bind, pure, Except.pure]
    rw [show GoValue.array
        (⟨List.map (fun f => GoValue.string (gs f)) (fs ++ [f])
          ++ List.replicate (cap - (fs ++ [f]).length)
            (GoValue.string GoString.empty)⟩ : Array GoValue)
        = strArr (fs ++ [f]) cap from rfl]
    rw [normalize_strArr σ (fs ++ [f]) cap (by simp; omega)]
  exact SliceMem.applyStmtOp_append1_inplace (elem := tStr)
    (by omega) (Nat.le_refl 1) hvis hstore
    (by
      simp only [storeLoc]
      rw [show Heap.lookup (wSt σ
          (Heap.set σ.heap (.base ⟨b⟩) (strArrCell (fs ++ [f]) cap))
          σ.nextAddr).heap (.base ⟨t⟩) = some slsNil from ht]
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [show normalizeValueForTy (wSt σ
          (Heap.set σ.heap (.base ⟨b⟩) (strArrCell (fs ++ [f]) cap))
          σ.nextAddr) tSlS (slsVal b 0 (fs.length + 1) cap)
          = .ok (slsVal b 0 (fs.length + 1) cap) from by
        simp [normalizeValueForTy, normalizeValueForTyFuel,
          typeResolutionFuel]])


-- (`forIn_push_generic`, formerly here, fed only the builder below —
-- deleted with its forIn fight in WP arc s2 item 3.)

/-- The spill path's fresh backing: old values, the new element, and
empty-string padding to the chosen capacity. -/
theorem buildAppendBackingValue_str (σ : ExecState)
    (fs : List (List UInt8)) (f : List UInt8) (newCap : Nat)
    (h : fs.length + 1 ≤ newCap) :
    buildAppendBackingValue σ tStr
      (fs.map (fun x => GoValue.string (gs x))).toArray
      #[.string (gs f)] newCap
      = .ok (strArr (fs ++ [f]) newCap) := by
  -- WP arc s2 item 3: the forIn fight replaced by the kit's generic
  -- builder closed form (string values self-normalize).
  have h := SliceMem.buildAppendBackingValue_of_norm (σ := σ)
    (elem := tStr)
    (l₁ := fs.map (fun x => GoValue.string (gs x)))
    (l₂ := [GoValue.string (gs f)]) (newCap := newCap)
    (d := .string GoString.empty)
    (fun x _ => by with_unfolding_all rfl)
    (by with_unfolding_all rfl)
    (by simpa using h)
  rw [show buildAppendBackingValue σ tStr
      (fs.map (fun x => GoValue.string (gs x))).toArray
      #[.string (gs f)] newCap
    = buildAppendBackingValue σ tStr
      ⟨fs.map (fun x => GoValue.string (gs x))⟩
      ⟨[GoValue.string (gs f)]⟩ newCap from rfl]
  rw [h]
  congr 2
  simp [strArr, List.map_append, List.map_replicate]

/-- **The `append(out, $c16...)` SPILL fact** (`len = cap`): one choice
consumed, a fresh backing is allocated at the current
allocator with the appended values and empty-string padding to the
chosen capacity, and the handle stored over the target points at it.
The capacity is Skolemized: `∃ newCap ∈ [len+1, …]` — its exact value
is the choice-dependent envelope member. -/
theorem applyStmtOp_append_str_spill {σ : ExecState} {t b e : Nat}
    {fs : List (List UInt8)} {cap : Nat} {f : List UInt8} {ch : Choices}
    (hb : Heap.lookup σ.heap (.base ⟨b⟩) = some (strArrCell fs cap))
    (he : Heap.lookup σ.heap (.base ⟨e⟩)
      = some ⟨some (.array 1 tStr), .array #[.string (gs f)]⟩)
    (ht : Heap.lookup σ.heap (.base ⟨t⟩) = some slsNil)
    (htna : t ≠ σ.nextAddr)
    (heq : fs.length = cap) :
    ∃ (newCap : Nat) (ch' : Choices), fs.length + 1 ≤ newCap ∧
    applyStmtOp σ ch (.appendSlice tStr) 1
      [.addr (.base ⟨t⟩), slsVal b 0 fs.length cap, slsVal e 0 1 1]
      = .ok (wSt σ
          (Heap.set
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              (strArrCell (fs ++ [f]) newCap))
            (.base ⟨t⟩)
            ⟨some tSlS, slsVal σ.nextAddr 0 (fs.length + 1) newCap⟩)
          (σ.nextAddr + 1), ch') := by
  have hvis : sliceVisibleValues σ ⟨some (.base ⟨e⟩), 0, 1, 1⟩
      = .ok #[.string (gs f)] := by
    have := sliceVisibleValues_str (σ := σ) (b := e) (fs := [f]) (cap := 1)
      (by simpa [strArrCell, strArr] using he) (by simp)
    simpa using this
  have hvisOld : sliceVisibleValues σ
      ⟨some (.base ⟨b⟩), 0, fs.length, cap⟩
      = .ok (fs.map (fun x => GoValue.string (gs x))).toArray :=
    sliceVisibleValues_str hb (by omega)
  -- WP arc s2 item 3: the applyStmtOp unfolding and the realized
  -- capacity replaced by the kit's envelope existential
  -- `SliceMem.applyStmtOp_append1_spill_ex`.
  obtain ⟨newCap, ch', h1, -, happly⟩ :=
    SliceMem.applyStmtOp_append1_spill_ex (σ := σ) (elem := tStr)
      (tloc := .base ⟨t⟩) (bb := .base ⟨b⟩) (off := 0)
      (len := fs.length) (cap := cap)
      (eb := .base ⟨e⟩) (eoff := 0) (elen := 1) (ecap := 1)
      (w := .string (gs f))
      (old := (fs.map (fun x => GoValue.string (gs x))).toArray)
      (bk := fun nc => strArr (fs ++ [f]) nc)
      (σT := fun nc => wSt σ
          (Heap.set
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              (strArrCell (fs ++ [f]) nc))
            (.base ⟨t⟩)
            ⟨some tSlS, slsVal σ.nextAddr 0 (fs.length + 1) nc⟩)
          (σ.nextAddr + 1))
      (ch := ch)
      (by omega) (by omega) (Nat.le_refl 1) hvis hvisOld
      (fun nc hnc => buildAppendBackingValue_str σ fs f nc hnc)
      (fun nc hnc => by
        have hlook2 : Heap.lookup
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              (strArrCell (fs ++ [f]) nc)) (.base ⟨t⟩)
            = some slsNil := by
          rw [Machine.Heap.lookup_set_ne
            (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega
              : (Loc.base ⟨σ.nextAddr⟩ : Loc) ≠ .base ⟨t⟩)]
          exact ht
        simp only [storeLoc, hlook2, Bind.bind, Except.bind, pure,
          Except.pure]
        rw [show ∀ σ' : ExecState, normalizeValueForTy σ' tSlS
            (slsVal σ.nextAddr 0 (fs.length + 1) nc)
            = .ok (slsVal σ.nextAddr 0 (fs.length + 1) nc) from
          fun σ' => by
            simp [normalizeValueForTy, normalizeValueForTyFuel,
              typeResolutionFuel]])
  exact ⟨newCap, ch', h1, happly⟩

/-! ## The scan loop's environments and continuations -/

def scScope : Scope :=
  [("inField", .base ⟨29⟩), ("start", .base ⟨28⟩), ("i", .base ⟨27⟩),
   ("out", .base ⟨26⟩), ("$c15", .base ⟨24⟩)]
def scEnvS : LocalEnv := [scScope, shimFrameScope]
def scEnv : LocalEnv := [[("$forFirst", .base ⟨30⟩)], scScope, shimFrameScope]
def scEnvC : LocalEnv := [] :: scEnv

def scTailIf : Stmt :=
  .ifThenElse (.var "inField") goleanShimStringsFieldsFunc.scTailAppend
    (.seqn #[])
def scResSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "out"), .returnStmt]
def scHeadTail : Cont :=
  .seq [] scEnv (.seq [scTailIf, scResSeqn] scEnvS shimFrameK)
def scHeadCfg : Config :=
  .exec (.while (.boolLit true) goleanShimStringsFieldsFunc.scWhileBody)
    scEnv scHeadTail
def scLoopK : Cont :=
  .loop (.boolLit true) goleanShimStringsFieldsFunc.scWhileBody scEnv
    scHeadTail
def scCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt scEnvC
    (.seq [goleanShimStringsFieldsFunc.scByteBlock] scEnvC scLoopK)
def scPostBody : Cont := .seq [] scEnvC scLoopK
/-- The byte block's pushed scope. -/
def scEnvB0 : LocalEnv := [] :: scEnvC
/-- `w` declared at the iteration cell. -/
def scEnvB (a : Nat) : LocalEnv := [("w", .base ⟨a⟩)] :: scEnvC
/-- `c` declared after it. -/
def scEnvBC (a : Nat) : LocalEnv :=
  [("c", .base ⟨a + 1⟩), ("w", .base ⟨a⟩)] :: scEnvC

/-- The `c := s[i]` seqn (named for segment statements). -/
def scSeqnC : Stmt :=
  .seqn #[.initialization { id := "c", typ := tU8 },
          .assign (.var "c") (.indexGet (.var "s") (.var "i"))]
/-- The `w > 0` branch statement. -/
def scIfW : Stmt :=
  .ifThenElse (.greaterCmp (.var "w") (.intLit 0 .int))
    goleanShimStringsFieldsFunc.scSepArm
    goleanShimStringsFieldsFunc.scLetterArm

/-! ## The scan state family -/

/-- The scan-phase state: concrete 31-cell front (the `out` handle at
`(b, 0, |fs|, cap)`), the debris-and-backing region `D` past it. -/
abbrev scSt (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (iv sv2 : Int)
    (fv ffv : Bool) (D : Heap) (na : Nat) : ExecState :=
  wSt σ (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv ffv
    ++ D) na

/-! ## Raw segments — prologue and dispatch -/

/-- `wordFreq` prologue: body start → the shim call's argument
delivered. 8 steps. -/
theorem wf_pro_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (ch : Choices) :
    stepFnIter 8 (wSt σ (wHeapWF nv sv qv bnv bsv l q biv) 21)
      (.exec wordFreqFunc.body wfFrameEnv wfFrameK) ch
      = .ok (.retV (.string (gs l)) shimCallK0,
          wSt σ (wHeapWords nv sv qv bnv bsv l q biv) 22, ch) := by
  with_unfolding_all rfl

/-- The shim prologue: `$c15 := make([]string, 0, 0)` (backing at the
CONCRETE cell 25), `out := $c15`, `i := 0`, `start := 0`,
`inField := false`, the first-pass flag → the scan loop head. 79
steps. -/
theorem sc_pro_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (ch : Choices) :
    stepFnIter 79 (wSt σ (wHeapShim nv sv qv bnv bsv l q biv) 24)
      (.exec goleanShimStringsFieldsFunc.body shimFrameEnv shimFrameK) ch
      = .ok (scHeadCfg,
          scSt σ nv sv qv bnv bsv l q biv 25 0 [] 0 0 false true [] 31,
          ch) := by
  with_unfolding_all rfl

/-- Scan dispatch, first pass: flag write, the exit test delivered. 27
steps. -/
theorem sc_A0_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat)
    (fs : List (List UInt8)) (iv sv2 : Int) (fv : Bool) (D : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 27
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv true D na)
      scHeadCfg ch
      = .ok (.retV (.bool (decide (iv < (l.length : Int)))) scCmpK,
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na,
          ch) := by
  with_unfolding_all rfl

/-- Scan dispatch, later passes. 20 steps. -/
theorem sc_A1_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat)
    (fs : List (List UInt8)) (iv sv2 : Int) (fv : Bool) (D : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 20
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na)
      scHeadCfg ch
      = .ok (.retV (.bool (decide (iv < (l.length : Int)))) scCmpK,
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na,
          ch) := by
  with_unfolding_all rfl

/-! ## The byte-block prefix (`w := 0; c := s[i]`), composed -/

/-- Test true → the `w` initialization point. 7 steps. -/
theorem sc_P1_raw (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat)
    (fs : List (List UInt8)) (iv sv2 : Int) (fv : Bool) (D : Heap)
    (na : Nat) (ch : Choices) :
    stepFnIter 7
      (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na)
      (.retV (.bool true) scCmpK) ch
      = .ok (.exec (.initialization { id := "w", typ := tInt }) scEnvB0
            (.seq [.assign (.var "w") (.intLit 0 .int), scSeqnC,
              goleanShimStringsFieldsFunc.scClassify, scIfW] scEnvB0
              scPostBody),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na,
          ch) := by
  with_unfolding_all rfl

/-- The `w := 0` (default) allocation step at the iteration cell. -/
theorem sc_step_initW (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat)
    (fs : List (List UInt8)) (iv sv2 : Int) (fv : Bool) (D : Heap)
    (na : Nat) (rest : List Stmt) (k : Cont) (ch : Choices)
    (hna : 31 ≤ na) (hD : DeadFrom D na) :
    stepFn (scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na)
      (.exec (.initialization { id := "w", typ := tInt }) scEnvB0
        (.seq rest scEnvB0 k)) ch
      = .ok (.next (.seq rest (scEnvB na) k),
          scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false
            (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) (na + 1),
          ch) := by
  have h := stepFn_init_seq
    (σ := scSt σ nv sv qv bnv bsv l q biv b cap fs iv sv2 fv false D na)
    (p := { id := "w", typ := tInt }) (rest := rest) (env := scEnvB0)
    (k := k) (ch := ch) (v := .int 0 .int)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show Heap.set (wHeapScan nv sv qv bnv bsv l q biv b fs.length cap
        iv sv2 fv false ++ D) (.base ⟨na⟩) ⟨some tInt, .int 0 .int⟩
      = wHeapScan nv sv qv bnv bsv l q biv b fs.length cap iv sv2 fv false
        ++ (D ++ [(.base ⟨na⟩, ⟨some tInt, .int 0 .int⟩)]) from by
    rw [set_append_right (lookup_wHeapScan_none nv sv qv bnv bsv l q biv
        b fs.length cap iv sv2 fv false (by omega)),
      set_fresh (hD na (Nat.le_refl na))]] at h
  exact h

/-! ## CONTINUED IN `Scan2.lean` (W3, 2026-08-16)

The byte-block prefix composition (`sc_prefix`), the four classify
composites, the letter/skip arms, the append tail and the
state-abstract spill step now live in `Scan2.lean` (split for
elaboration budget), all green. The close-arm COMPOSITE and everything
after it (iterations, loop, exit, `scan_phase`) are parked — see the
PARKED BOUNDARY at the end of `Scan2.lean` for the authoritative
continuation plan and the elaboration-performance analysis, and
`.tmp/e5-drafts/w3-close-arm-draft.lean` for the drafted composite. -/

end GoLean.Examples.WordFreq
