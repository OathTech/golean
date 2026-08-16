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

## PUBLIC API — the sealed interface (phase-2 slice 2, 2026-08-14;
the brick-wp W6 convention adapted to Lean 4)

**What consumers may depend on** (and nothing else):

* statement-adjacent vocabulary: `sliceCells`, `sliceVal`, `Sorted`;
* machine-integer normal forms: `unorm_of_range`, `inorm_of_range`,
  `inorm_nat_of_lt`, `unorm_nat_of_lt`, `unorm_add_nat`, and (WP arc
  s1 lift 1, 2026-08-16) `unorm_nat`, `unorm_mul_nat`,
  `intKind_normalize_idem`, plus the kind-generic pair
  `normalize_of_range_unsigned`/`normalize_of_range_signed`;
* the executable op facts, each conditioned on exactly its
  bounds/range hypotheses: `applyStrictOp_indexGet_slice`,
  `applyStrictOp_len_slice`, `applyStrictOp_sliceExpr_array`,
  `applyStrictOp_lessCmp_int`, `applyStrictOp_mod_u64`, and (WP arc
  s1 lift 1) the completed integer family `applyStrictOp_mul_u64`,
  `applyStrictOp_div_u64`, `applyStrictOp_add_u64`,
  `applyStrictOp_sub_int`, `applyStrictOp_eqCmp_int`,
  `applyStrictOp_neqCmp_int`, `applyStrictOp_atMostCmp`,
  `applyStrictOp_not`, `applyStrictOp_convert_u64`;
  `storeTarget_slice_u64`, `storeTarget_arrayLocal_u64`,
  `normalizeValueForTy_arr_u64`;
* slice-value plumbing: `getElem?_mapU`, `getD_mem`,
  `mem_set_of_mem`, `locSup_mapU`;
* the setup family + copy prefix (GAP-P2 lift, 2026-08-15):
  `familyMod`, `prefixPad`, with `familyMod_length`/`_range`/
  `familyModZ_range`/`_succ`/`_set`/`_getD` and `prefixPad_zero`/
  `_length`/`_range`/`prefixPad_familyMod_set`/`prefixPad_full`.

**Internal** (`private` — spelling may change without notice):
`validateSlice_ok`, `sliceIndexLoc_ok`, `normalizeListWith_u64` — the
decomposition steps of the public store/index facts. Consumers state
their needs against the PUBLIC facts' hypothesis shapes, never against
how a fact is discharged internally.

**The API discipline** (C2 decoupling rule, harness-style scoping
note: spec-style adapters are thin layers over a style-neutral core —
they depend on APIs, not internals):

1. Everything here is UNTRUSTED METHOD except the three vocabulary
   defs, and even those enter a headline only under the §11 statement
   closure rules — a kit lemma NAME never appears in a headline
   statement (form note §12b).
2. Additions follow the active-abstraction loop (form note §12):
   ≥2 consumers retrofitted in the lifting commit, measured deltas.
   Single-consumer shapes stay private copies in their example module.
3. Lean has no Rocq-style opaque `Module Type` ascription: `private`
   hides names but does not seal definitional transparency. The seal
   is therefore name-level + this contract; the statement layer has
   its own frozen closure and gate (statement-TCB).
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

/-- Wrapped uint64 normalization of a bare `Nat` cast — the setup/LCG
families' own wrap, no range hypothesis. (WP arc s1 lift 1: lifted
from SIX per-example copies — dotprod `unorm_nat`, bubble `unorm_nat`,
fib's private `unorm_nat`, minmax `unorm_nat_wrap`, isort + selsort
`unorm_nat_mod` — all byte-identical statements.) -/
theorem unorm_nat (x : Nat) :
    IntKind.normalize .uint64 ((x : Nat) : Int)
      = ((x % 2 ^ 64 : Nat) : Int) := by
  simp [IntKind.normalize, IntKind.bits?, IntKind.signed]

/-- Wrapped uint64 multiplication of two `Nat`-cast values — the
WRAPPING counterpart of `unorm_add_nat` (`applyStrictOp_mul_u64` below
is the no-wrap conditioned form; when `*`/`+` ride inside
`with_unfolding_all rfl` segments only this normalization identity is
consumed — the dotprod negative finding, g1.md §GAP-A1-wrap). -/
theorem unorm_mul_nat (a b : Nat) :
    IntKind.normalize .uint64 ((a : Int) * (b : Int))
      = ((a * b % 2 ^ 64 : Nat) : Int) := by
  rw [show (a : Int) * (b : Int) = ((a * b : Nat) : Int) from by
    push_cast; rfl]
  exact unorm_nat (a * b)

/-- `IntKind.normalize` is idempotent — the fact behind discharging
store re-normalizations to zero hypotheses. (WP arc s1 lift 1, the C4
resolution: lifted OUT of `HeapBridge` — whose closure pulls the whole
Iris layer — into this Iris-free module, so footprint-style example
closures can consume it without importing a proof-device layer;
`HeapBridge.intKind_normalize_idem` now delegates here, and fibmemo's
local uint64 copy (`unorm_idem`) is deleted.) -/
theorem intKind_normalize_idem (kind : IntKind) (v : Int) :
    kind.normalize (kind.normalize v) = kind.normalize v := by
  cases kind <;> simp [IntKind.normalize, IntKind.bits?, IntKind.signed] <;>
    (repeat' split) <;> omega

/-! ### Kind-generic normal forms (WP arc s1 lift 1)

One lemma per signedness covers every `uint*`/`int*` in-range identity
at once — the class strrev/wordfreq re-derived at `.int32`
(`i32norm_of_range`) and kadane at `.int64` (`inorm64_of_range`).
`bits?`/`signed` are forced by the kind: instantiate with `rfl`, e.g.
`normalize_of_range_signed (bits := 63) rfl rfl h0 h1` at `.int64`.
The signed form's width is spelled `bits + 1` so the half-range
hypotheses are `-(2^bits) ≤ v < 2^bits` with no degenerate-width
side condition. -/

/-- A value of an UNSIGNED kind inside `[0, 2^bits)` is its own
normal form. -/
theorem normalize_of_range_unsigned {k : IntKind} {bits : Nat} {v : Int}
    (hb : k.bits? = some bits) (hs : k.signed = false)
    (h0 : 0 ≤ v) (h1 : v < 2 ^ bits) :
    IntKind.normalize k v = v := by
  simp only [IntKind.normalize, hb, hs, Bool.false_eq_true, if_false]
  exact Int.emod_eq_of_lt h0 h1

/-- A value of a SIGNED kind of width `bits + 1` inside
`[-(2^bits), 2^bits)` is its own normal form. -/
theorem normalize_of_range_signed {k : IntKind} {bits : Nat} {v : Int}
    (hb : k.bits? = some (bits + 1)) (hs : k.signed = true)
    (h0 : -(2 ^ bits) ≤ v) (h1 : v < 2 ^ bits) :
    IntKind.normalize k v = v := by
  have hpos : (0 : Int) < 2 ^ bits := by
    have := Nat.two_pow_pos bits
    exact_mod_cast this
  have hps : (2 : Int) ^ (bits + 1) = 2 ^ bits * 2 := Int.pow_succ 2 bits
  simp only [IntKind.normalize, hb, hs, if_true, Nat.add_sub_cancel]
  by_cases hv : 0 ≤ v
  · have hmod : v % 2 ^ (bits + 1) = v := Int.emod_eq_of_lt hv (by omega)
    rw [hmod, if_neg (by omega)]
  · have hmod : v % 2 ^ (bits + 1) = v + 2 ^ (bits + 1) := by
      have h' := Int.add_mul_emod_self_left v (2 ^ (bits + 1)) 1
      rw [Int.mul_one] at h'
      rw [← h']
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hmod, if_pos (by omega)]
    omega

/-! ## The executable slice-op facts -/

private theorem validateSlice_ok {b : Loc} {off len cap : Nat} (hcap : len ≤ cap) :
    validateSlice ⟨some b, off, len, cap⟩ = .ok () := by
  simp [validateSlice, Nat.not_lt.mpr hcap, Bind.bind, Except.bind]

/-- The element location of `s[i]` at an in-bounds `Nat` index. -/
private theorem sliceIndexLoc_ok {b : Loc} {off len cap i : Nat}
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

private theorem normalizeListWith_u64 {σ : ExecState} {fuel : Nat}
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

/-- Membership after a `set` is the new value or an old member.
(Hoisted from the slice-value plumbing section, phase-2 slice 2: the
store facts below use it, and the module carried a `private` verbatim
duplicate `mem_of_mem_set` — deduplicated as part of the API seal.) -/
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
    rcases mem_set_of_mem hv with rfl | hv
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
    rcases mem_set_of_mem hv with rfl | hv
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

/-! ## The integer executable-op family, completed (WP arc s1 lift 1,
2026-08-16)

The A1/A2 consolidation note (g1.md §Unit G1.3b): the integer
executable-op facts land as ONE family rather than singly, so the
fixture cost is paid once. Lifted from the landed per-example copies —
powmod (`mul`, `div`), dedup (`div`, `eqCmp`, `neqCmp`, `sub`,
`convert`), sieve (`mul`, `add`, `atMostCmp`, `not`), rle (`div`),
dotprod's docstring cite of `mul` — each statement byte-identical to
its copies (rle's `div` had an extra unused `b < 2^64` hypothesis;
the kit form is the two-hypothesis powmod/dedup shape). -/

/-- uint64 `*` below the wrap threshold (wrapping form: the
`unorm_mul_nat` normalization identity above). -/
theorem applyStrictOp_mul_u64 {σ : ExecState} {a b : Nat}
    (h : a * b < 2 ^ 64) :
    applyStrictOp σ .mul [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a * b : Nat) : Int) .uint64, σ) := by
  have hraw : applyStrictOp σ .mul [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int (IntKind.normalize .uint64 ((a : Int) * (b : Int))) .uint64, σ) := rfl
  have hc : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by push_cast; rfl
  rw [hraw, ← hc, unorm_nat_of_lt h]

/-- uint64 `/` at a positive divisor (`a / b ≤ a` is the range
argument, where `%` got its range from `< b`). -/
theorem applyStrictOp_div_u64 {σ : ExecState} {a b : Nat}
    (hb : 0 < b) (ha : a < 2 ^ 64) :
    applyStrictOp σ .div [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a / b : Nat) : Int) .uint64, σ) := by
  have hbne : (((b : Nat) : Int) == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Int.natCast_eq_zero]; omega
  have htdiv : Int.tdiv (a : Int) (b : Int) = ((a / b : Nat) : Int) := rfl
  have hnorm : IntKind.normalize .uint64 ((a / b : Nat) : Int) = ((a / b : Nat) : Int) :=
    unorm_nat_of_lt (by have := Nat.div_le_self a b; omega)
  simp only [applyStrictOp, valueAsInt, hbne, intBinaryResult,
    valueAsIntValue, htdiv, IntKind.compatibleResult,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure, Except.pure]
  simp only [show (IntKind.uint64 == IntKind.uint64) = true from rfl, if_true, hnorm]

/-- uint64 `+` below the wrap threshold (wrapping form:
`unorm_add_nat`). -/
theorem applyStrictOp_add_u64 {σ : ExecState} {a b : Nat}
    (h : a + b < 2 ^ 64) :
    applyStrictOp σ .add [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int ((a + b : Nat) : Int) .uint64, σ) := by
  have hraw : applyStrictOp σ .add [.int (a : Int) .uint64, .int (b : Int) .uint64]
      = .ok (.int (IntKind.normalize .uint64 ((a : Int) + (b : Int))) .uint64, σ) := rfl
  have hc : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by push_cast; rfl
  rw [hraw, ← hc, unorm_nat_of_lt h]

/-- Signed-int `-` on in-range `Nat`-cast operands (the `k - 1` of a
guard; parameterized by what the landed witnesses vary — dedup's is
the only shape, `a - 1`). -/
theorem applyStrictOp_sub_int {σ : ExecState} {a : Nat}
    (ha : 1 ≤ a) (ha2 : a < 2 ^ 63) :
    applyStrictOp σ .sub [.int (a : Int) .int, .int (1 : Int) .int]
      = .ok (.int ((a - 1 : Nat) : Int) .int, σ) := by
  have hraw : applyStrictOp σ .sub [.int (a : Int) .int, .int (1 : Int) .int]
      = .ok (.int (IntKind.normalize .int ((a : Int) - 1)) .int, σ) := rfl
  rw [hraw, show ((a : Int) - 1) = ((a - 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt (by omega)]

/-- The `==` executable fact at integer operands — `valueEq` at an int
type is payload `BEq` (note `with_unfolding_all`: plain `rfl` does not
close `valueEq`, the dedup finding). -/
theorem applyStrictOp_eqCmp_int {σ : ExecState} {a b : Int}
    {k k1 k2 : IntKind} :
    applyStrictOp σ (.eqCmp (.int k)) [.int a k1, .int b k2]
      = .ok (.bool (a == b), σ) := by with_unfolding_all rfl

/-- The `!=` executable fact at integer operands. -/
theorem applyStrictOp_neqCmp_int {σ : ExecState} {a b : Int}
    {k k1 k2 : IntKind} :
    applyStrictOp σ (.neqCmp (.int k)) [.int a k1, .int b k2]
      = .ok (.bool (!(a == b)), σ) := by with_unfolding_all rfl

/-- `<=` on ints compares the payloads, state-free (mirror of
`applyStrictOp_lessCmp_int`). -/
theorem applyStrictOp_atMostCmp {σ : ExecState} {a b : Int}
    {k k' : IntKind} :
    applyStrictOp σ .atMostCmp [.int a k, .int b k']
      = .ok (.bool (decide (a ≤ b)), σ) := rfl

/-- `!` on a delivered bool, state-free. -/
theorem applyStrictOp_not {σ : ExecState} {b : Bool} :
    applyStrictOp σ .not [.bool b] = .ok (.bool (!b), σ) := rfl

/-- `uint64(x)` conversion of an in-range value is the identity on the
payload. -/
theorem applyStrictOp_convert_u64 {σ : ExecState} {a : Nat} {k : IntKind}
    (ha : a < 2 ^ 64) :
    applyStrictOp σ (.convert (.int .uint64)) [.int (a : Int) k]
      = .ok (.int ((a : Nat) : Int) .uint64, σ) := by
  have hraw : applyStrictOp σ (.convert (.int .uint64)) [.int (a : Int) k]
      = .ok (.int (IntKind.normalize .uint64 (a : Int)) .uint64, σ) := rfl
  rw [hraw, unorm_nat_of_lt ha]

/-! ## The modular setup family + the zero-padded prefix (Gallery
Campaign kit-gap closure GAP-P2, 2026-08-15)

`familyMod k n seed` — the harness setup family `v[i] = seed + i % k`,
wrapped at uint64 — and `prefixPad`, the copy loop's "family prefix,
zero tail" invariant list, lifted from the verbatim per-example copies
(`wcFamily`/`wcPre`, `histFamily`/`histPre`; both landed consumers
keep their pinned names as one-line delegations). The wrap is part of
the family BY DESIGN, so the family covers wrap-boundary seeds.
(MinMax's `mmFamily` is a DIFFERENT formula (`seed + i`, no modulus)
and designated statement vocabulary — deliberately not touched.) -/

/-- The modular setup family: `fam[i] = (seed + i % k) % 2^64`. -/
def familyMod (k n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i % k) % 2 ^ 64 : Nat) : Int))

theorem familyMod_length (k n seed : Nat) :
    (familyMod k n seed).length = n := by
  simp [familyMod]

theorem familyMod_range (k n seed : Nat) :
    ∀ v ∈ familyMod k n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [familyMod, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  have : (seed + i % k) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

/-- The family prefix with a zero tail stays in uint64 range. -/
theorem familyModZ_range {k n seed i : Nat} :
    ∀ v ∈ familyMod k i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact familyMod_range k i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem familyMod_succ (k i seed : Nat) :
    familyMod k (i + 1) seed
      = familyMod k i seed ++ [(((seed + i % k) % 2 ^ 64 : Nat) : Int)] := by
  simp [familyMod, List.range_succ]

/-- One setup store advances the family prefix. -/
theorem familyMod_set {k n seed i : Nat} (hi : i < n) :
    (familyMod k i seed ++ List.replicate (n - i) 0).set i
        (((seed + i % k) % 2 ^ 64 : Nat) : Int)
      = familyMod k (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (familyMod k i seed).length = i := familyMod_length k i seed
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, familyMod_succ]
  simp

/-- The family's element at an in-range index. -/
theorem familyMod_getD {k n seed m : Nat} (hm : m < n) :
    (familyMod k n seed).getD m 0
      = (((seed + m % k) % 2 ^ 64 : Nat) : Int) := by
  rw [familyMod, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-- The copy loop's array invariant: the family prefix after `m`
steps, the rest still the array's zero default (cap `cap`). -/
def prefixPad (fam : Nat → Nat → List Int) (cap m seed : Nat) :
    List Int :=
  fam m seed ++ List.replicate (cap - m) 0

theorem prefixPad_zero {fam : Nat → Nat → List Int} {cap seed : Nat}
    (h0 : fam 0 seed = []) :
    prefixPad fam cap 0 seed = List.replicate cap 0 := by
  simp [prefixPad, h0]

theorem prefixPad_length {fam : Nat → Nat → List Int}
    {cap m seed : Nat} (hlen : (fam m seed).length = m) (hm : m ≤ cap) :
    (prefixPad fam cap m seed).length = cap := by
  rw [prefixPad, List.length_append, hlen, List.length_replicate]
  omega

theorem prefixPad_range {fam : Nat → Nat → List Int}
    {cap m seed : Nat} (hr : ∀ v ∈ fam m seed, 0 ≤ v ∧ v < 2 ^ 64) :
    ∀ v ∈ prefixPad fam cap m seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hr v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

/-- One copy store advances the prefix (the `familyMod` instance). -/
theorem prefixPad_familyMod_set {k cap seed m : Nat} (hm : m < cap) :
    (prefixPad (familyMod k) cap m seed).set m
        (((seed + m % k) % 2 ^ 64 : Nat) : Int)
      = prefixPad (familyMod k) cap (m + 1) seed :=
  familyMod_set hm

/-- The copy loop's terminal list IS the family zero-padded to the
cap. -/
theorem prefixPad_full {fam : Nat → Nat → List Int}
    {cap n seed : Nat} (hlen : (fam n seed).length = n) :
    prefixPad fam cap n seed
      = fam n seed ++ List.replicate (cap - (fam n seed).length) 0 := by
  rw [prefixPad, hlen]

/-! ## The swap surgery + count algebra (WP arc s1 lift 3, 2026-08-16)

Pure `List Int` algebra every swap-based subject re-derives, lifted
verbatim from `Examples/SelectionSort/Pure.lean`'s GAP-WITNESS block
(consumers: selsort, bubble — whose `bstepL` swap arm IS
`swapList l (i-1) i`; isort's `bubbleState_swap` is the same surgery
in `bubbleState`-structural clothing and stays local, recorded). -/

theorem getD_set_self {l : List Int} {k : Nat} {w : Int}
    (hk : k < l.length) : (l.set k w).getD k 0 = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_pos rfl,
    if_pos hk]
  rfl

theorem getD_set_ne {l : List Int} {k j : Nat} {w : Int}
    (h : k ≠ j) : (l.set k w).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, if_neg h,
    List.getD_eq_getElem?_getD]

/-- The additive counting law of one `set` (no `Nat` subtraction). -/
theorem count_set_add (v w : Int) :
    ∀ (l : List Int) (k : Nat), k < l.length →
    (l.set k w).count v + (if l.getD k 0 = v then 1 else 0)
      = l.count v + (if w = v then 1 else 0) := by
  intro l
  induction l with
  | nil => intro k hk; simp at hk
  | cons x rest ih =>
      intro k hk
      cases k with
      | zero =>
          simp only [List.set_cons_zero, List.count_cons, List.getD_cons_zero,
            beq_iff_eq]
          omega
      | succ kk =>
          have hkk : kk < rest.length := by simpa using hk
          have ih' := ih kk hkk
          simp only [List.set_cons_succ, List.count_cons,
            List.getD_cons_succ, beq_iff_eq]
          omega

/-- The machine's two stores, in the machine's order: `s[i] := old
s[m]`, then `s[m] := old s[i]` (both right-hand sides were read before
either store). At `m = i` this is a no-op on the list. -/
def swapList (l : List Int) (i m : Nat) : List Int :=
  (l.set i (l.getD m 0)).set m (l.getD i 0)

theorem swapList_length (l : List Int) (i m : Nat) :
    (swapList l i m).length = l.length := by
  simp [swapList]

theorem getD_swapList_fst {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length) :
    (swapList l i m).getD i 0 = l.getD m 0 := by
  by_cases him : m = i
  · subst him
    rw [swapList, getD_set_self (by simpa using hi)]
  · rw [swapList, getD_set_ne him, getD_set_self hi]

theorem getD_swapList_snd {l : List Int} {i m : Nat}
    (hm : m < l.length) :
    (swapList l i m).getD m 0 = l.getD i 0 :=
  getD_set_self (by simpa using hm)

theorem getD_swapList_other {l : List Int} {i m k : Nat}
    (hki : k ≠ i) (hkm : k ≠ m) :
    (swapList l i m).getD k 0 = l.getD k 0 := by
  rw [swapList, getD_set_ne (fun h => hkm h.symm),
    getD_set_ne (fun h => hki h.symm)]

/-- **Swapping preserves every count** — the permutation half of any
sort invariant, first-order. -/
theorem count_swapList (v : Int) {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length) :
    (swapList l i m).count v = l.count v := by
  have h1 := count_set_add v (l.getD i 0) (l.set i (l.getD m 0)) m
    (by simpa using hm)
  have h2 := count_set_add v (l.getD m 0) l i hi
  have hgm : (l.set i (l.getD m 0)).getD m 0 = l.getD m 0 := by
    by_cases him : i = m
    · subst him; exact getD_set_self hi
    · exact getD_set_ne him
  rw [hgm] at h1
  rw [show ((l.set i (l.getD m 0)).set m (l.getD i 0)) = swapList l i m
    from rfl] at h1
  by_cases ha : l.getD m 0 = v <;> by_cases hb : l.getD i 0 = v <;>
    simp [ha, hb] at h1 h2 ⊢ <;> omega

/-- The range invariant survives a swap (values only move). -/
theorem range_swapList {l : List Int} {i m : Nat}
    (hi : i < l.length) (hm : m < l.length)
    (hr : ∀ x ∈ l, 0 ≤ x ∧ x < 2 ^ 64) :
    ∀ x ∈ swapList l i m, 0 ≤ x ∧ x < 2 ^ 64 := by
  intro x hx
  rw [swapList] at hx
  rcases mem_set_of_mem hx with rfl | hx
  · exact hr _ (getD_mem hi)
  · rcases mem_set_of_mem hx with rfl | hx
    · exact hr _ (getD_mem hm)
    · exact hr x hx

/-! ## The generic setup families (WP arc s1 lift 2, 2026-08-16)

Three layers, each pre-drafted in the campaign ledger (g1.md, the
lane-B kit-gap lists + GAP-P2b/c/d):

* `familyZ (g : Nat → Int) (n)` — the fully generic map-over-range
  family, `g` the per-index element. The SIGNED carrier (kadane's
  `kadFamVal` family, dotprod's unwrapped `dpFamB`) and the base the
  other two layers' facts delegate to. `padZ` is its zero-padded
  prefix (an `Int`-elementwise `prefixPad`), with the two-store
  mid-list helper (`padZ_set_any`) GAP-P2c asked for.
* `familyF (f : Nat → Nat) (n seed)` — the drafted uint64 shape
  `v[i] = (seed + f i) % 2^64`: `familyMod k = familyF (· % k)`,
  twosum/dotprod-A/reverse/minmax/stack/queue = `familyF id` (the
  six-affine-copy family, GAP-P2b), rle = `familyF (· / 3)`, dedup =
  `familyF (· / 2)` (GAP-P2d).
* `familyOf (step : Nat → Nat) (n seed)` — the iterated-step family
  (`iterStep`); the sorts' LCG becomes an instance. -/

/-- The fully generic setup family: `fam[i] = g i`. -/
def familyZ (g : Nat → Int) (n : Nat) : List Int :=
  (List.range n).map g

theorem familyZ_length (g : Nat → Int) (n : Nat) :
    (familyZ g n).length = n := by
  simp [familyZ]

/-- Membership characterization — the generic scaffold every
family-specific range fact discharges through. -/
theorem familyZ_mem {g : Nat → Int} {n : Nat} {v : Int}
    (hv : v ∈ familyZ g n) : ∃ i, i < n ∧ v = g i := by
  simp only [familyZ, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact ⟨i, hi, rfl⟩

theorem familyZ_succ (g : Nat → Int) (i : Nat) :
    familyZ g (i + 1) = familyZ g i ++ [g i] := by
  simp [familyZ, List.range_succ]

/-- One setup store advances the family prefix. -/
theorem familyZ_set {g : Nat → Int} {n i : Nat} (hi : i < n) :
    (familyZ g i ++ List.replicate (n - i) 0).set i (g i)
      = familyZ g (i + 1) ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (familyZ g i).length = i := familyZ_length g i
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, familyZ_succ]
  simp

/-- The family's element at an in-range index. -/
theorem familyZ_getD {g : Nat → Int} {n m : Nat} (hm : m < n) :
    (familyZ g n).getD m 0 = g m := by
  rw [familyZ, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hm)]
  simp

/-- The zero-padded prefix of a generic family (the `Int`-elementwise
`prefixPad`). -/
def padZ (g : Nat → Int) (cap m : Nat) : List Int :=
  familyZ g m ++ List.replicate (cap - m) 0

theorem padZ_zero (g : Nat → Int) (cap : Nat) :
    padZ g cap 0 = List.replicate cap 0 := by
  simp [padZ, familyZ]

theorem padZ_length {g : Nat → Int} {cap m : Nat} (hm : m ≤ cap) :
    (padZ g cap m).length = cap := by
  rw [padZ, List.length_append, familyZ_length, List.length_replicate]
  omega

/-- One padded-prefix store advances the prefix. -/
theorem padZ_set {g : Nat → Int} {cap m : Nat} (hm : m < cap) :
    (padZ g cap m).set m (g m) = padZ g cap (m + 1) := by
  exact familyZ_set hm

/-- Storing an ARBITRARY value at the prefix boundary — the two-store
mid-list helper (GAP-P2c): the first store of an odd-index pair lands
`w`, the second rewrites it to `g m` (`padZ_set` from the mid list
via `List.set_set`, or directly by this at `w := g m`). -/
theorem padZ_set_any {g : Nat → Int} {cap m : Nat} (w : Int)
    (hm : m < cap) :
    (padZ g cap m).set m w
      = familyZ g m ++ (w :: List.replicate (cap - (m + 1)) 0) := by
  have hlen : (familyZ g m).length = m := familyZ_length g m
  have hnm : cap - m = (cap - (m + 1)) + 1 := by omega
  rw [padZ, List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero]

/-- Every member is in range when every element is (the generic range
transport for `padZ` — zero must satisfy the bound, as it does for
every landed window). -/
theorem padZ_range {g : Nat → Int} {cap m : Nat} {lo hi : Int}
    (hg : ∀ i, i < m → lo ≤ g i ∧ g i ≤ hi)
    (h0 : lo ≤ 0 ∧ (0 : Int) ≤ hi) :
    ∀ v ∈ padZ g cap m, lo ≤ v ∧ v ≤ hi := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨i, hi', rfl⟩ := familyZ_mem hv
    exact hg i hi'
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    exact h0

/-! ### `familyF` — the index-function uint64 family (the exact
drafted shape, g1.md §THE KIT-GAP LIST (twosum)/(rle)) -/

/-- The index-function setup family: `fam[i] = (seed + f i) % 2^64`. -/
def familyF (f : Nat → Nat) (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + f i) % 2 ^ 64 : Nat) : Int))

/-- `familyMod` IS the `· % k` instance (definitional). -/
theorem familyMod_eq_familyF (k : Nat) : familyMod k = familyF (· % k) :=
  rfl

theorem familyF_length (f : Nat → Nat) (n seed : Nat) :
    (familyF f n seed).length = n := by
  simp [familyF]

theorem familyF_range (f : Nat → Nat) (n seed : Nat) :
    ∀ v ∈ familyF f n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := familyZ_mem (g := fun i =>
    (((seed + f i) % 2 ^ 64 : Nat) : Int)) hv
  have : (seed + f i) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

/-- The family prefix with a zero tail stays in uint64 range. -/
theorem familyFZ_range {f : Nat → Nat} {n seed i : Nat} :
    ∀ v ∈ familyF f i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact familyF_range f i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem familyF_succ (f : Nat → Nat) (i seed : Nat) :
    familyF f (i + 1) seed
      = familyF f i seed ++ [(((seed + f i) % 2 ^ 64 : Nat) : Int)] :=
  familyZ_succ _ i

/-- One setup store advances the family prefix. -/
theorem familyF_set {f : Nat → Nat} {n seed i : Nat} (hi : i < n) :
    (familyF f i seed ++ List.replicate (n - i) 0).set i
        (((seed + f i) % 2 ^ 64 : Nat) : Int)
      = familyF f (i + 1) seed ++ List.replicate (n - (i + 1)) 0 :=
  familyZ_set hi

/-- The family's element at an in-range index. -/
theorem familyF_getD {f : Nat → Nat} {n seed m : Nat} (hm : m < n) :
    (familyF f n seed).getD m 0
      = (((seed + f m) % 2 ^ 64 : Nat) : Int) :=
  familyZ_getD hm

/-- One copy store advances the prefix (the `familyF` instance of
`prefixPad_familyMod_set`). -/
theorem prefixPad_familyF_set {f : Nat → Nat} {cap seed m : Nat}
    (hm : m < cap) :
    (prefixPad (familyF f) cap m seed).set m
        (((seed + f m) % 2 ^ 64 : Nat) : Int)
      = prefixPad (familyF f) cap (m + 1) seed :=
  familyF_set hm

/-! ### `familyOf` — the iterated-step family (the LCG shape) -/

/-- Iterate a step function `k` times from `x` (structurally the
sorts' `lcgStep`, step-function generic). -/
def iterStep (step : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => step (iterStep step k x)

/-- Every positive iterate of a range-preserving step is in range. -/
theorem iterStep_lt {step : Nat → Nat} {k x : Nat}
    (hs : ∀ y, step y < 2 ^ 64) (hk : 0 < k) :
    iterStep step k x < 2 ^ 64 := by
  cases k with
  | zero => omega
  | succ k => exact hs _

/-- The iterated-step setup family: `fam[i]` is the `(i+1)`-th
iterate of `step` from `seed`. -/
def familyOf (step : Nat → Nat) (n seed : Nat) : List Int :=
  (List.range n).map (fun i => ((iterStep step (i + 1) seed : Nat) : Int))

theorem familyOf_length (step : Nat → Nat) (n seed : Nat) :
    (familyOf step n seed).length = n := by
  simp [familyOf]

theorem familyOf_range {step : Nat → Nat} (hs : ∀ y, step y < 2 ^ 64)
    (n seed : Nat) :
    ∀ v ∈ familyOf step n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := familyZ_mem (g := fun i =>
    ((iterStep step (i + 1) seed : Nat) : Int)) hv
  have := iterStep_lt (k := i + 1) (x := seed) hs (by omega)
  omega

/-- The family prefix with a zero tail stays in uint64 range. -/
theorem familyOfZ_range {step : Nat → Nat} (hs : ∀ y, step y < 2 ^ 64)
    {n seed i : Nat} :
    ∀ v ∈ familyOf step i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact familyOf_range hs i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

theorem familyOf_succ (step : Nat → Nat) (i seed : Nat) :
    familyOf step (i + 1) seed
      = familyOf step i seed
          ++ [((iterStep step (i + 1) seed : Nat) : Int)] :=
  familyZ_succ _ i

/-- One setup store advances the family prefix. -/
theorem familyOf_set {step : Nat → Nat} {n seed i : Nat} (hi : i < n) :
    (familyOf step i seed ++ List.replicate (n - i) 0).set i
        ((iterStep step (i + 1) seed : Nat) : Int)
      = familyOf step (i + 1) seed ++ List.replicate (n - (i + 1)) 0 :=
  familyZ_set hi

/-- The family's element at an in-range index. -/
theorem familyOf_getD {step : Nat → Nat} {n seed m : Nat} (hm : m < n) :
    (familyOf step n seed).getD m 0
      = ((iterStep step (m + 1) seed : Nat) : Int) :=
  familyZ_getD hm

/-! ### `takePad` — the copy-OUT prefix over COMPUTED data (the exact
drafted shape, g1.md §THE KIT-GAP LIST (selsort); the bubble list's
`prefixPadL` is this same shape) -/

/-- The copy-out loop's invariant list: the first `m` elements of the
(computed, symbolic) source `l`, zero-padded to `cap`. -/
def takePad (l : List Int) (cap m : Nat) : List Int :=
  l.take m ++ List.replicate (cap - m) 0

theorem takePad_zero (l : List Int) (cap : Nat) :
    takePad l cap 0 = List.replicate cap 0 := by
  simp [takePad]

theorem takePad_length {l : List Int} {cap m : Nat}
    (hm : m ≤ cap) (hl : m ≤ l.length) :
    (takePad l cap m).length = cap := by
  rw [takePad, List.length_append, List.length_take, List.length_replicate]
  omega

theorem takePad_range {l : List Int} {cap m : Nat}
    (hl : ∀ v ∈ l, 0 ≤ v ∧ v < 2 ^ 64) :
    ∀ v ∈ takePad l cap m, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hl v (List.mem_of_mem_take hv)
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

/-- One copy-out store advances the prefix. (Stated at the weakest
hypotheses the two landed consumers need — `m` in the source and in
the cap; the ledger's drafted `m < n → l.length = n → n ≤ cap` form
follows by `omega`.) -/
theorem takePad_set {l : List Int} {cap m : Nat}
    (hml : m < l.length) (hcap : m < cap) :
    (takePad l cap m).set m (l.getD m 0) = takePad l cap (m + 1) := by
  have hltake : (l.take m).length = m := by
    rw [List.length_take]; omega
  have hnm : cap - m = (cap - (m + 1)) + 1 := by omega
  have htake : l.take (m + 1) = l.take m ++ [l.getD m 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hml]
    simp [List.take_add_one (l := l) (i := m)]
  rw [takePad, List.set_append_right _ _ (by omega), hltake,
    Nat.sub_self, hnm, List.replicate_succ, List.set_cons_zero,
    takePad, htake]
  simp

/-- The copy-out loop's terminal list IS the source zero-padded to
the cap. -/
theorem takePad_full {l : List Int} {cap n : Nat} (hlen : l.length = n) :
    takePad l cap n = l ++ List.replicate (cap - n) 0 := by
  rw [takePad, List.take_of_length_le (by omega)]

end GoLean.SliceMem
