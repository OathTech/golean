import GoLean.GoCore.MachineSound

/-!
# Slice-in-memory vocabulary + the executable slice-op facts
(verified-examples slice 2b, 2026-08-13; design note
`docs/2026-08-12_example-spec-form.md` §9a)

The corpus vocabulary for a Go `[]uint64` input living in memory:
`sliceCells` (the backing cell) and `sliceVal` (the handle the program
receives), exactly as §9a specifies — offset 0, cap = len pinned for
v1 (sub-slice generality is a recorded 2b+ option, not widened here).

Placement decision (recorded): §9a proposed this vocabulary "in the
Reverse example module or a small shared module under `Examples/`"; it
lives HERE, at the shared `GoLeanProofs` top level, because the WP law
layer (`Laws/Slice.lean`) discharges its premises through the same
executable facts and `Laws/*` must not import target-specific
`Examples/*` modules (layering doctrine 2026-08-01: general
infrastructure stays separated from target-specific infrastructure).

Beside the vocabulary: the EXECUTABLE slice-operation facts — what
`applyStrictOp`/`storeTarget` compute at slice operands, conditioned on
the bounds/normal-form hypotheses. These are the shared discharge
lemmas for (a) the WP slice laws' premises and (b) the direct
machine-step segments of the reverse exemplar. No Iris here: this
module is statement-side-safe.
-/

namespace GoLean.SliceMem

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## §9a: the input-in-memory vocabulary -/

/-- The heap representation of a Go `[]uint64` holding `xs`: one
backing cell at `base` with the array of wrapped values. The slice
HANDLE the program receives is `sliceVal xs base` — base pointer,
offset 0, length and capacity `xs.length`. -/
def sliceCells (xs : List Int) (base : Nat) : Heap :=
  [(.base ⟨base⟩,
    ⟨some (.array xs.length (.int .uint64)),
     .array ⟨xs.map (fun v => .int v .uint64)⟩⟩)]

def sliceVal (xs : List Int) (base : Nat) : GoValue :=
  .slice ⟨some (.base ⟨base⟩), 0, xs.length, xs.length⟩

/-- **Sortedness, first-order and readable** (shared spec vocabulary,
verified-examples slice 2c): every earlier position holds a value ≤
every later position. Used as binary search's precondition and
insertion sort's postcondition — ONE definition so the gallery's
"sorted" means one thing. On the abstract `List Int`, like everything
in this vocabulary; `getD _ 0` is the house total-read idiom (the
domain condition `j < xs.length` makes the default irrelevant). -/
def Sorted (xs : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length → xs.getD i 0 ≤ xs.getD j 0

/-! ## Machine-integer normal forms -/

/-- A `uint64` value in Go range is its own normal form. -/
theorem unorm_of_range {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 64) :
    IntKind.normalize .uint64 v = v := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed]
  simp only [Bool.false_eq_true, if_false]
  omega

/-- A signed-`int` value in Go range is its own normal form. -/
theorem inorm_of_range {v : Int} (h0 : -(2 ^ 63) ≤ v) (h1 : v < 2 ^ 63) :
    IntKind.normalize .int v = v := by
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, if_true]
  split <;> omega

/-- The `Nat`-cast corner of `inorm_of_range` (loop counters). -/
theorem inorm_nat_of_lt {x : Nat} (h : x < 2 ^ 63) :
    IntKind.normalize .int (x : Int) = (x : Int) :=
  inorm_of_range (by omega) (by exact_mod_cast h)

/-- The `Nat`-cast corner of `unorm_of_range` (consolidation slice
2026-08-13: promoted from per-example privates, P3). -/
theorem unorm_nat_of_lt {x : Nat} (h : x < 2 ^ 64) :
    IntKind.normalize .uint64 (x : Int) = (x : Int) :=
  unorm_of_range (by omega) (by exact_mod_cast h)

/-- Wrapped uint64 addition of two `Nat`-cast values (promoted, P3). -/
theorem unorm_add_nat (a b : Nat) :
    IntKind.normalize .uint64 ((a : Int) + (b : Int))
      = (((a + b) % 2 ^ 64 : Nat) : Int) := by
  rw [show ((a : Int) + (b : Int)) = ((a + b : Nat) : Int) from by omega]
  simp [IntKind.normalize, IntKind.bits?, IntKind.signed]

/-! ## The executable slice-op facts -/

theorem validateSlice_ok {b : Loc} {off len cap : Nat} (hcap : len ≤ cap) :
    validateSlice ⟨some b, off, len, cap⟩ = .ok () := by
  simp [validateSlice, Nat.not_lt.mpr hcap, Bind.bind, Except.bind]

/-- The element location of `s[i]` at an in-bounds `Nat` index. -/
theorem sliceIndexLoc_ok {b : Loc} {off len cap i : Nat}
    (hcap : len ≤ cap) (hi : i < len) :
    sliceIndexLoc ⟨some b, off, len, cap⟩ (i : Nat) =
      .ok (.index b (Int.ofNat (off + i))) := by
  simp only [sliceIndexLoc, validateSlice_ok hcap, Bind.bind, Except.bind,
    pure, Except.pure, Int.toNat_natCast, Int.ofNat_eq_natCast]
  rw [if_neg (by omega)]
  simp [hi]

/-- `s[i]` (the `indexGet` strict-op application) at a slice handle:
loads the backing array through the owned cell and returns the
element. Bounds check at EVALUATION (the expression-position check). -/
theorem applyStrictOp_indexGet_slice {σ : ExecState} {a : Addr}
    {dty : Option Ty} {off len cap i : Nat} {ik : IntKind}
    {vs : Array GoValue} {w : GoValue}
    (hlook : Heap.lookup σ.heap (.base a) = some ⟨dty, .array vs⟩)
    (hcap : len ≤ cap) (hi : i < len)
    (hget : vs[off + i]? = some w) :
    applyStrictOp σ .indexGet
      [.slice ⟨some (.base a), off, len, cap⟩, .int (i : Nat) ik]
      = .ok (w, σ) := by
  have hsz : off + i < vs.size := by
    cases Nat.lt_or_ge (off + i) vs.size with
    | inl h => exact h
    | inr h => rw [Array.getElem?_eq_none h] at hget; cases hget
  simp only [applyStrictOp, valueAsInt, pure, Except.pure,
    sliceIndexLoc_ok hcap hi, loadLoc, hlook, arrayGet, arrayIndexNat,
    Bind.bind, Except.bind, Int.ofNat_eq_natCast, Int.toNat_natCast]
  rw [if_neg (by omega)]
  rw [if_pos hsz]
  simp [hget]

/-- `len(s)` at a slice handle is the handle's length — state-free
(the handle carries its length; no heap read). Stated at the
slice-annotated form the frontend emits for `len` over `[]T`. -/
theorem applyStrictOp_len_slice {σ : ExecState} {b : Loc}
    {off len cap : Nat} {elem : Ty}
    (hcap : len ≤ cap) :
    applyStrictOp σ (.lengthOf (some (.slice elem)))
      [.slice ⟨some b, off, len, cap⟩]
      = .ok (.int (len : Nat) .int, σ) := by
  simp only [applyStrictOp, validateSlice_ok (b := b) hcap]
  rfl

/-- The slice expression `(&arr)[lo:hi]` over a pointer-to-array base:
the handle via `sliceFromArray` (the driver-seed shape: `lo = 0`,
`hi = L = the array's length`). -/
theorem applyStrictOp_sliceExpr_array {σ : ExecState} {a : Addr}
    {dty : Option Ty} {ik ik' : IntKind} {vs : Array GoValue} {L : Nat}
    (hlook : Heap.lookup σ.heap (.base a) = some ⟨dty, .array vs⟩)
    (hsz : vs.size = L) :
    applyStrictOp σ (.sliceExpr false)
      [.addr (.base a), .int 0 ik, .int (L : Nat) ik']
      = .ok (.slice ⟨some (.base a), 0, L, L⟩, σ) := by
  simp only [applyStrictOp, valueAsInt, applySlice, loadLoc, hlook,
    sliceFromArray, checkSliceBounds, Bind.bind, Except.bind, pure,
    Except.pure, hsz]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  simp

/-! ### The uint64 element-store fact

The store side normalizes the whole backing array against the cell's
declared type, so the fact is stated at the `[]uint64` fragment: a
backing list of in-range values stays itself elementwise, and the
stored element lands wrapped (in-range: unchanged). -/

theorem normalizeListWith_u64 {σ : ExecState} {fuel : Nat}
    (hf : 0 < fuel)
    (l : List Int) (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) :
    normalizeListWith (normalizeValueForTyFuel fuel σ (.int .uint64))
      (l.map (fun v => .int v .uint64))
      = .ok ⟨l.map (fun v => .int v .uint64)⟩ := by
  match fuel, hf with
  | f + 1, _ =>
    induction l with
    | nil => simp [normalizeListWith]
    | cons v rest ih =>
        have hv := hl v (by simp)
        have hrest := ih (fun w hw => hl w (by simp [hw]))
        simp [normalizeListWith, normalizeValueForTyFuel,
          unorm_of_range hv.1 hv.2, hrest, Bind.bind, Except.bind]

/-- Membership in `List.set` comes from the new element or the old
list. -/
private theorem mem_of_mem_set {l : List Int} {i : Nat} {w v : Int}
    (h : v ∈ l.set i w) : v = w ∨ v ∈ l := by
  induction l generalizing i with
  | nil => simp [List.set] at h
  | cons x rest ih =>
      cases i with
      | zero =>
          simp only [List.set, List.mem_cons] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (by simp [h])
      | succ n =>
          simp only [List.set, List.mem_cons] at h
          rcases h with h | h
          · exact .inr (by simp [h])
          · rcases ih h with h | h
            · exact .inl h
            · exact .inr (by simp [h])

/-- **The phase-2 element store through an index-chain target**
(`s[i] = w` on `[]uint64`): `storeTarget` replays the chain — the
bounds check fires HERE, at store time (BUG-029) — and the write lands
in the BACKING cell: the array with element `off + i` set. The cell's
declared array type re-normalizes the array on store; on the in-range
`[]uint64` fragment that is the identity, which is what the range
hypotheses are for. -/
theorem storeTarget_slice_u64 {σ : ExecState} {a : Addr}
    {off len cap i n : Nat} {ik : IntKind} {l : List Int} {w : Int}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨some (.array n (.int .uint64)),
              .array ⟨l.map (fun v => .int v .uint64)⟩⟩)
    (hcap : len ≤ cap) (hi : i < len)
    (hsz : off + i < l.length) (hn : l.length = n)
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64)
    (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget σ
      (.chain (.slice ⟨some (.base a), off, len, cap⟩) [.int (i : Nat) ik]
        [.index])
      (.int w .uint64)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨some (.array n (.int .uint64)),
           .array ⟨(l.set (off + i) w).map (fun v => .int v .uint64)⟩⟩) } := by
  have hglist : l[off + i]? = some (l[off + i]'hsz) :=
    List.getElem?_eq_getElem hsz
  have hset : ∀ v ∈ l.set (off + i) w, 0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_of_mem_set hv with rfl | hv
    · exact hw
    · exact hl v hv
  have harrset : arraySet (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
      (Int.ofNat (off + i)) (.int w .uint64)
      = .ok ⟨(l.set (off + i) w).map (fun v => .int v .uint64)⟩ := by
    have hidx : ((off + i : Nat) : Int).toNat = off + i := by omega
    simp only [arraySet, arrayIndexNat, Bind.bind, Except.bind,
      Int.ofNat_eq_natCast, hidx]
    rw [if_neg (by omega), if_pos (by simpa using hsz)]
    simp [hglist, coerceStoredValue, unorm_of_range hw.1 hw.2,
      Array.set!, pure, Except.pure]
  have hnorm : normalizeValueForTy σ (.array n (.int .uint64))
      (.array ⟨(l.set (off + i) w).map (fun v => .int v .uint64)⟩)
      = .ok (.array ⟨(l.set (off + i) w).map (fun v => .int v .uint64)⟩) := by
    rw [normalizeValueForTy, typeResolutionFuel]
    simp only [normalizeValueForTyFuel]
    rw [if_neg (by simp [hn])]
    have hlist := normalizeListWith_u64 (σ := σ) (fuel := 1023) (by omega)
      (l.set (off + i) w) hset
    simp only [List.map_set] at hlist
    simp [hlist, Bind.bind, Except.bind, Functor.map, Except.map]
  simp only [storeTarget, resolveChain, indexTargetLoc, valueAsInt,
    valueAsLoc, sliceIndexLoc_ok hcap hi, Bind.bind, Except.bind, storeLoc,
    loadLoc, hlook, harrset, hnorm, pure, Except.pure]

/-! ### The ARRAY-local element store (phase-2 slice 1, 2026-08-14)

The S3 relational harness style returns its observed data as a
fixed-cap Go ARRAY, so it needs the array-typed-local analogue of
`storeTarget_slice_u64`: `a[i] = w` where `a` is an array-typed LOCAL,
not a slice handle. The target is then an ADDRESS-rooted chain
(`.addr (.base a)`, from the frontend's `.indexAddr (.ref x)`), so
`indexTargetLoc` takes its `.addr` arm — load the base array,
bounds-check, yield `Loc.index base i` — and `storeLoc` at a `.index`
loc `arraySet`s and re-stores at the base, where the declared array
type re-normalizes. Same tail as `storeTarget_slice_u64`, different
root.

Promoted from `Examples/MinMax/HarnessR.lean`'s in-module copies (form
note §12) now that the second consumer exists —
`Examples/WordCount/HarnessR.lean`'s `words[i] = w[i]` copy loop — and
generalized from minmax's cap-8 form to arbitrary `N`. Both consumers
are retrofitted in the promotion commit and are its fixture witnesses;
minmax keeps a thin cap-8 alias so its own statements are untouched. -/

/-- Normalizing an in-range uint64 list at an array type is the
identity — the side condition of every array-valued store. -/
theorem normalizeValueForTy_arr_u64 {σ : ExecState} {N : Nat} {lp : List Int}
    (hlen : lp.length = N) (hl : ∀ v ∈ lp, 0 ≤ v ∧ v < 2 ^ 64) :
    normalizeValueForTy σ (.array N (.int .uint64))
        (.array ⟨lp.map (fun v => .int v .uint64)⟩)
      = .ok (.array ⟨lp.map (fun v => .int v .uint64)⟩) := by
  rw [normalizeValueForTy, typeResolutionFuel]
  simp only [normalizeValueForTyFuel]
  rw [if_neg (by simp [hlen])]
  have hlist := normalizeListWith_u64 (σ := σ) (fuel := 1023) (by omega) lp hl
  simp [hlist, Bind.bind, Except.bind, Functor.map, Except.map]

/-- **The element store through an ADDRESS-rooted index chain**
(`a[i] = w` on an array-typed `[N]uint64` local). -/
theorem storeTarget_arrayLocal_u64 {σ : ExecState} {a : Addr} {N i : Nat}
    {ik : IntKind} {l : List Int} {w : Int}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨some (.array N (.int .uint64)),
              .array ⟨l.map (fun v => .int v .uint64)⟩⟩)
    (hi : i < l.length) (hn : l.length = N)
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) (hw : 0 ≤ w ∧ w < 2 ^ 64) :
    storeTarget σ (.chain (.addr (.base a)) [.int (i : Nat) ik] [.index])
        (.int w .uint64)
      = .ok { σ with
          heap := Heap.set σ.heap (.base a)
            ⟨some (.array N (.int .uint64)),
             .array ⟨(l.set i w).map (fun v => .int v .uint64)⟩⟩ } := by
  have hsize : (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue).size
      = l.length := by simp
  have hglist : l[i]? = some (l[i]'hi) := List.getElem?_eq_getElem hi
  have hset : ∀ v ∈ l.set i w, 0 ≤ v ∧ v < 2 ^ 64 := by
    intro v hv
    rcases mem_of_mem_set hv with rfl | hv
    · exact hw
    · exact hl v hv
  have hidxn : arrayIndexNat (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
      ((i : Nat) : Int) = .ok i := by
    simp only [arrayIndexNat, Bind.bind, Except.bind]
    rw [if_neg (by omega), Int.toNat_natCast,
      if_pos (by simpa [hsize] using hi)]
    rfl
  have harrset : arraySet (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)
      ((i : Nat) : Int) (.int w .uint64)
      = .ok ⟨(l.set i w).map (fun v => .int v .uint64)⟩ := by
    simp only [arraySet, Bind.bind, Except.bind, hidxn]
    simp [hglist, coerceStoredValue, unorm_of_range hw.1 hw.2,
      Array.set!, pure, Except.pure]
  have hnorm : normalizeValueForTy σ (.array N (.int .uint64))
      (.array ⟨(l.set i w).map (fun v => .int v .uint64)⟩)
      = .ok (.array ⟨(l.set i w).map (fun v => .int v .uint64)⟩) :=
    normalizeValueForTy_arr_u64 (by rw [List.length_set]; exact hn) hset
  simp only [storeTarget, resolveChain, indexTargetLoc, valueAsInt,
    valueAsLoc, Bind.bind, Except.bind, storeLoc, loadLoc, hlook, hidxn,
    harrset, hnorm, pure, Except.pure]

/-! ## Slice-value plumbing (consolidation slice 2026-08-13: promoted
from 4–5 per-example private copies, ledger row P2) -/

/-- Reading the mapped-to-`GoValue` backing at an in-range index. -/
theorem getElem?_mapU (l : List Int) (k : Nat) (hk : k < l.length) :
    (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[k]?
      = some (.int (l.getD k 0) .uint64) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

/-- The house total-read idiom hits a member at an in-range index. -/
theorem getD_mem {xs : List Int} {k : Nat} (hk : k < xs.length) :
    xs.getD k 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

/-- Membership after a `set` is the new value or an old member. -/
theorem mem_set_of_mem {l : List Int} {i : Nat} {w v : Int}
    (h : v ∈ l.set i w) : v = w ∨ v ∈ l := by
  induction l generalizing i with
  | nil => simp [List.set] at h
  | cons x rest ih =>
      cases i with
      | zero =>
          simp only [List.set, List.mem_cons] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr (by simp [h])
      | succ n =>
          simp only [List.set, List.mem_cons] at h
          rcases h with h | h
          · exact .inr (by simp [h])
          · rcases ih h with h | h
            · exact .inl h
            · exact .inr (by simp [h])

/-- An all-int backing array owns no locations. -/
theorem locSup_mapU (l : List Int) :
    GoValue.locSup (.array ⟨l.map (fun v => .int v .uint64)⟩) = 0 := by
  show goValueListSup (l.map (fun v => .int v .uint64)) = 0
  induction l with
  | nil => rfl
  | cons v rest ih => simpa [goValueListSup, GoValue.locSup] using ih

/-- The integer `<` strict-op fact (both operand kinds free: the
machine compares the `Int` payloads; promoted from the MinMax
private, second consumer the placement-generic wordcount loop). -/
theorem applyStrictOp_lessCmp_int {σ : ExecState} {a b : Int}
    {k k' : IntKind} :
    applyStrictOp σ .lessCmp [.int a k, .int b k']
      = .ok (.bool (decide (a < b)), σ) := rfl

/-- **The `%` executable fact** (promoted from Gcd/WordCount privates):
uint64 `%` at a positive divisor is Nat `%`, wrapped nowhere — the
divide-by-zero check is the one data-dependent branch. -/
theorem applyStrictOp_mod_u64 {σ : ExecState} {a b : Nat}
    (hb : 0 < b) (hb64 : b < 2 ^ 64) :
    applyStrictOp σ .mod [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a % b : Nat) : Int) .uint64, σ) := by
  have hbne : (((b : Nat) : Int) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]
    omega
  have htmod : Int.tmod (a : Int) (b : Int) = ((a % b : Nat) : Int) := rfl
  have hnorm : IntKind.normalize .uint64 ((a % b : Nat) : Int)
      = ((a % b : Nat) : Int) :=
    unorm_nat_of_lt (by
      have : a % b < b := Nat.mod_lt _ hb
      omega)
  simp only [applyStrictOp, valueAsInt, hbne, intBinaryResult,
    valueAsIntValue, htmod, IntKind.compatibleResult,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure, Except.pure]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl,
    if_true, hnorm]

end GoLean.SliceMem
