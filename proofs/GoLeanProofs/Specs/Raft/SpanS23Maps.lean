import GoLeanProofs.Specs.Raft.SpanS1

/-!
# The two S23 map fragments + the data code (A4d-SM2 items 1-2)

`main.twin.apply` touches two maps `MapMem` does not cover
(the SM1 boundary-stop's priced residue, `docs/campaign-arc4d-log.md`):

1. **`nd.got` — `map[string]bool`** (`got[data] = true`): the
   STRING-KEYED sibling of `MapMem`'s uint64 fragment. Model:
   `List (GoString × Bool)` with `sIdxOf?`/`setks`; machine encoding
   `toEntriesS`; the one op the span performs is the assignment
   (`mapAssignValue_toEntriesS`). Built in the MapMem reuse pattern —
   one scan engine + one op lemma, NOT a re-derived map theory.
   PROMOTABLE: the fragment is target-independent (wordfreq-class
   examples are the recorded latent second consumers); it lives here
   per the lane's location rule and the §7 one-consumer test — the
   promotion target is `GoLeanProofs/StrMapMem.lean` beside `MapMem`.
2. **`t.byIndex` — `map[uint64]main.slot`** (comma-ok lookup +
   insert-if-absent): STRUCT-VALUED, so the value normalizations run
   at the DEFINED slot type (the U23 table-footprint class). Model:
   `List (Int × SlotA)` with `bIdxOf?`/`bget?`; `slotFs` +
   `normalize_slotFs` are the `twinFs` pattern verbatim (3 fields);
   `slotDecl_pinned` anchors the declaration to the pinned table.
   The generic key scan (`scanV_generic`) is shared by parameterizing
   over the VALUE encoder — values are opaque to the scan.
3. **`encGS` — the injective data code**: the model's `AEv.data` is a
   `Nat` (`NativeCheckerBridge.AEv`); the machine's datum is a
   `GoString`. `encGS` (base-257 with digits 1..256) is injective
   with `encGS s = 0 ↔ s` empty, so the machine's string comparisons
   and the empty-payload branch are EXACTLY the model's Nat
   comparisons at the projection. The T1 assembly may rename data
   values through any injection; `encGS_inj` is what makes that
   transport sound (the assembly-seam note in the walk module).

LINEAGE: data refinement (abstraction function + operation
commutation) — MapMem's own lineage, at two new payload types.
-/

namespace GoLean.RaftSeam.SpanS23

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.RaftSeam.UtoaSpan (twinSt)
open GoLean.RaftSeam.SpanCells
open GoLean.StringMem (gs)

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

-- The unusedSimpArgs linter false-flags `letFun` (mapEntryIndex?) —
-- removing it breaks the proof (verified 2026-08-26); the same
-- suppression `MapMem.lean` carries, for the same reason.
set_option linter.unusedSimpArgs false

/-! ## 1. The injective data code -/

/-- Base-257 code over the byte list, digits `1..256` (so the empty
string — and only it — codes to `0`). -/
def encB : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 1 + 257 * encB rest

/-- The `GoString` data code. -/
def encGS (s : GoString) : Nat := encB s.bytes.toList

theorem encB_inj : ∀ l r : List UInt8, encB l = encB r → l = r
  | [], [], _ => rfl
  | [], b :: r, h => by
    exfalso
    simp only [encB] at h
    omega
  | a :: l, [], h => by
    exfalso
    simp only [encB] at h
    omega
  | a :: l, b :: r, h => by
    simp only [encB] at h
    have ha : a.toNat < 256 := a.toNat_lt
    have hb : b.toNat < 256 := b.toNat_lt
    have hab : a.toNat = b.toNat ∧ encB l = encB r := by omega
    have h1 : a = b := UInt8.toNat_inj.mp hab.1
    have h2 : l = r := encB_inj l r hab.2
    rw [h1, h2]

theorem encGS_inj {l r : GoString} (h : encGS l = encGS r) : l = r := by
  obtain ⟨⟨lb⟩⟩ := l
  obtain ⟨⟨rb⟩⟩ := r
  have h2 := encB_inj lb rb h
  subst h2
  rfl

theorem encB_eq_zero_iff : ∀ l : List UInt8, encB l = 0 ↔ l = [] := by
  intro l
  cases l with
  | nil => simp [encB]
  | cons b rest =>
    simp only [encB]
    constructor
    · intro h; omega
    · intro h; cases h

theorem encGS_eq_zero_iff (s : GoString) :
    encGS s = 0 ↔ s = GoString.empty := by
  obtain ⟨⟨lb⟩⟩ := s
  rw [show encGS ⟨⟨lb⟩⟩ = encB lb from rfl, encB_eq_zero_iff]
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; rfl

/-- The derived `GoString` `BEq` decides propositional equality (the
derived instance is field-wise; `Array UInt8` is lawful). -/
theorem gsBeq_iff_eq {l r : GoString} : (l == r) = true ↔ l = r := by
  obtain ⟨lb⟩ := l
  obtain ⟨rb⟩ := r
  show (lb == rb) = true ↔ _
  rw [beq_iff_eq]
  constructor
  · intro h; rw [h]
  · intro h; cases h; rfl

/-- The machine's string `==` IS the model's code `==` — the S2
data-comparison transport (injectivity both ways). -/
theorem gsBeq_encGS (l r : GoString) :
    (l == r) = (encGS l == encGS r) := by
  by_cases h : l = r
  · rw [h, gsBeq_iff_eq.mpr rfl, beq_self_eq_true]
  · have h1 : (l == r) = false := by
      cases hb : (l == r)
      · rfl
      · exact absurd (gsBeq_iff_eq.mp hb) h
    have h2 : (encGS l == encGS r) = false := by
      cases hb : (encGS l == encGS r)
      · rfl
      · exact absurd (encGS_inj (beq_iff_eq.mp hb)) h
    rw [h1, h2]

/-! ## 2. The string-keyed fragment (`nd.got`) -/

/-- First index of key `d` (the machine's scan order; Bool-flavored
`==` matching the machine's `valueEq` verbatim — strings' `==` is
propositional equality by `gsBeq_iff_eq`). -/
def sIdxOf? : List (GoString × Bool) → GoString → Option Nat
  | [], _ => none
  | (k, _) :: rest, d =>
      if k == d then some 0 else (sIdxOf? rest d).map (· + 1)

/-- Update the first occurrence, or append — `mapAssignValue`'s
update-or-insert on the entry list. -/
def setks : List (GoString × Bool) → GoString → Bool → List (GoString × Bool)
  | [], d, b => [(d, b)]
  | (k, c) :: rest, d, b =>
      if k == d then (k, b) :: rest else (k, c) :: setks rest d b

/-- The machine encoding: insertion-ordered `mapData` entries. -/
def toEntriesS (kvs : List (GoString × Bool)) : Array (GoValue × GoValue) :=
  ⟨kvs.map (fun kv => (.string kv.1, .bool kv.2))⟩

theorem valueEq_string (σ : ExecState) (l r : GoString) :
    valueEq σ .string (.string l) (.string r) = .ok (l == r) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]

theorem checkKeyHashable_string (σ : ExecState) (d : GoString)
    (b ne : Bool) :
    checkKeyHashable σ (.string d) b ne = .ok () := by
  simp [checkKeyHashable, valueHashability]

/-- The key-scan loop over the string entries (the `MapMem`
`scan_generic` engine at string keys). -/
theorem scanS_generic {d : GoString}
    (f : GoValue × GoValue → MProd (Option (Option Nat)) Nat →
      Except GoError (ForInStep (MProd (Option (Option Nat)) Nat)))
    (hf : ∀ (k : GoString) (v : GoValue)
      (r : MProd (Option (Option Nat)) Nat),
      f (.string k, v) r
        = .ok (if k == d then .done ⟨some (some r.snd), r.snd⟩
               else .yield ⟨none, r.snd + 1⟩)) :
    ∀ (kvs : List (GoString × Bool)) (i : Nat),
    (forIn (m := Except GoError) (toEntriesS kvs)
      (⟨none, i⟩ : MProd (Option (Option Nat)) Nat) f)
      = pure (match sIdxOf? kvs d with
        | some j => ⟨some (some (j + i)), j + i⟩
        | none => ⟨none, i + kvs.length⟩) := by
  intro kvs
  induction kvs with
  | nil => intro i; simp [toEntriesS, sIdxOf?]
  | cons kv rest ih =>
    intro i
    obtain ⟨k, c⟩ := kv
    simp only [toEntriesS, List.map_cons, ← Array.forIn_toList] at ih ⊢
    rw [List.forIn_cons, hf]
    cases hk : (k == d) with
    | true =>
      rw [if_pos rfl]
      simp [sIdxOf?, hk, Bind.bind, Except.bind]
    | false =>
      rw [if_neg Bool.false_ne_true]
      simp only [sIdxOf?, hk, if_neg Bool.false_ne_true, Bind.bind,
        Except.bind]
      rw [ih (i + 1)]
      cases hidx : sIdxOf? rest d with
      | none =>
        simp only [Option.map_none, List.length_cons]
        rw [show i + 1 + rest.length = i + (rest.length + 1) from by
          omega]
      | some j =>
        simp only [Option.map_some]
        rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The machine's key scan over the string entry list is the model's
first-index scan. -/
theorem mapEntryIndex?_toEntriesS (σ : ExecState)
    (kvs : List (GoString × Bool)) (d : GoString) (b : Bool) :
    mapEntryIndex? σ .string (toEntriesS kvs) (.string d) b
      = .ok (sIdxOf? kvs d) := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.string d) b (!(toEntriesS kvs).isEmpty)
      = .ok () from checkKeyHashable_string ..]
  simp only [letFun]
  rw [scanS_generic (d := d) _ ?hf kvs 0]
  case hf =>
    intro k v r
    simp only [valueEq_string, Bind.bind, Except.bind]
    cases hk : (k == d) <;> simp
  cases h : sIdxOf? kvs d
    <;> simp [Bind.bind, Except.bind, pure, Except.pure]

private theorem sIdxOf?_none_setks {kvs : List (GoString × Bool)}
    {d : GoString} (h : sIdxOf? kvs d = none) (b : Bool) :
    kvs ++ [(d, b)] = setks kvs d b := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, c⟩ := kv
    simp only [sIdxOf?] at h
    by_cases hk : (k == d) = true
    · simp [hk] at h
    · rw [Bool.not_eq_true] at hk
      simp only [hk] at h
      simp only [List.cons_append, setks, hk]
      exact congrArg _
        (ih (by cases hidx : sIdxOf? rest d <;> simp [hidx] at h ⊢))

private theorem sIdxOf?_some_setks {kvs : List (GoString × Bool)}
    {d : GoString} {j : Nat} (h : sIdxOf? kvs d = some j) (b : Bool) :
    kvs.set j (d, b) = setks kvs d b := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
    obtain ⟨k, c⟩ := kv
    simp only [sIdxOf?] at h
    by_cases hk : (k == d) = true
    · simp only [hk, if_true, Option.some.injEq] at h
      cases h
      have hkd : k = d := gsBeq_iff_eq.mp hk
      subst hkd
      show (k, b) :: rest = _
      simp [setks, hk]
    · rw [Bool.not_eq_true] at hk
      simp only [hk] at h
      cases hidx : sIdxOf? rest d with
      | none => simp [hidx] at h
      | some j' =>
        simp only [hidx, Option.map_some] at h
        cases h
        simp only [List.set, setks, hk]
        exact congrArg _ (ih hidx)

private theorem toEntriesS_setks {kvs : List (GoString × Bool)}
    {d : GoString} {b : Bool} :
    (match sIdxOf? kvs d with
      | some i => (toEntriesS kvs).set! i (.string d, .bool b)
      | none => (toEntriesS kvs).push (.string d, .bool b))
      = toEntriesS (setks kvs d b) := by
  cases hidx : sIdxOf? kvs d with
  | none =>
    show (toEntriesS kvs).push _ = _
    apply Array.toList_inj.mp
    simp [toEntriesS, ← sIdxOf?_none_setks hidx b]
  | some j =>
    show (toEntriesS kvs).set! j _ = _
    apply Array.toList_inj.mp
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
      toEntriesS, ← sIdxOf?_some_setks hidx b, List.map_set]

/-- **The got-map write** (`got[data] = true`, and any
`map[string]bool` element assignment): `mapAssignValue`'s
update-or-append on the string entry list is `setks`. String keys and
bool values normalize as identities (no normalizer arm matches —
measured off the definition, the `twinFs` observation). -/
theorem mapAssignValue_toEntriesS {σ : ExecState} {a : Addr}
    {kvs : List (GoString × Bool)} {d : GoString} {b : Bool}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntriesS kvs)⟩) :
    mapAssignValue σ .string .bool
      (.map ⟨some (.base a)⟩) (.string d) (.bool b)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (toEntriesS (setks kvs d b))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ .string (.string d) = .ok (.string d)
    from by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel]]
  rw [show normalizeValueForTy σ .bool (.bool b) = .ok (.bool b)
    from by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel]]
  simp only [mapEntries, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_toEntriesS]
  cases hidx : sIdxOf? kvs d with
  | some j =>
    show storeLoc σ (.base a)
      (.mapData ((toEntriesS kvs).set! j (.string d, .bool b))) = _
    rw [show (toEntriesS kvs).set! j
        ((.string d : GoValue), (.bool b : GoValue))
        = toEntriesS (setks kvs d b) from by
      have h := toEntriesS_setks (kvs := kvs) (d := d) (b := b)
      rw [hidx] at h
      exact h]
    simp only [storeLoc, hlook, coerceStoredValue, Bind.bind,
      Except.bind, pure, Except.pure]
  | none =>
    show storeLoc σ (.base a)
      (.mapData ((toEntriesS kvs).push (.string d, .bool b))) = _
    rw [show (toEntriesS kvs).push
        ((.string d : GoValue), (.bool b : GoValue))
        = toEntriesS (setks kvs d b) from by
      have h := toEntriesS_setks (kvs := kvs) (d := d) (b := b)
      rw [hidx] at h
      exact h]
    simp only [storeLoc, hlook, coerceStoredValue, Bind.bind,
      Except.bind, pure, Except.pure]

/-! ## 3. The slot vocabulary (`main.slot`) -/

/-- A slot's abstract payload: (term, data, node). -/
abbrev SlotA := Nat × GoString × Nat

/-- The slot struct's field array at the pinned declaration's order. -/
def slotFs (t : Int) (d : GoString) (n : Int) : Array (String × GoValue) :=
  #[("term", .int t .uint64), ("data", .string d),
    ("node", .int n .uint64)]

/-- The slot struct value at an abstract payload. -/
def slotV (s : SlotA) : GoValue :=
  .struct ⟨"main.slot"⟩ (slotFs (s.1 : Int) s.2.1 (s.2.2 : Int))

/-- The slot declaration, spelled. -/
def slotDecl : Array FieldDef :=
  #[⟨"term", .int .uint64, false⟩, ⟨"data", .string, false⟩,
    ⟨"node", .int .uint64, false⟩]

/-- **PIN**: the type table's `main.slot` IS the spelled declaration
(`artifacts/probe/applyprobe.out`). -/
theorem slotDecl_pinned :
    TypeEnv.lookup twinTypes ⟨"main.slot"⟩ = some (.struct slotDecl) := by
  kernel_rfl

/-- The whole-slot normalization identity at in-range counters (raw
form at the destructured state; the `normalize_twinFs` pattern). -/
theorem normalize_slotFs {σ : ExecState}
    (htypes : σ.types = twinTypes) {t n : Int} {d : GoString}
    (ht0 : 0 ≤ t) (ht1 : t < 2 ^ 64)
    (hn0 : 0 ≤ n) (hn1 : n < 2 ^ 64) :
    normalizeValueForTy σ (.defined ⟨"main.slot"⟩)
        (.struct ⟨"main.slot"⟩ (slotFs t d n))
      = .ok (.struct ⟨"main.slot"⟩ (slotFs t d n)) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    have hraw : normalizeValueForTy
        ⟨twinTypes, functions, methods, methodSets, heap, nextAddr⟩
        (.defined ⟨"main.slot"⟩)
        (.struct ⟨"main.slot"⟩ (slotFs t d n))
        = .ok (.struct ⟨"main.slot"⟩
            (slotFs (IntKind.normalize .uint64 t) d
              (IntKind.normalize .uint64 n))) := by
      kernel_rfl
    rw [hraw, GoLean.SliceMem.unorm_of_range ht0 ht1,
      GoLean.SliceMem.unorm_of_range hn0 hn1]

/-- The slot zero value at the twin tables (the comma-ok miss
payload). -/
theorem defaultValue_slot {σ : ExecState}
    (htypes : σ.types = twinTypes) :
    defaultValue σ (.defined ⟨"main.slot"⟩)
      = .ok (.struct ⟨"main.slot"⟩ (slotFs 0 GoString.empty 0)) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    kernel_rfl

/-- The zero slot's abstract payload. -/
abbrev zeroSlot : SlotA := (0, GoString.empty, 0)

theorem slotV_zero : slotV zeroSlot = .struct ⟨"main.slot"⟩
    (slotFs 0 GoString.empty 0) := rfl

/-- The slot literal builder at the twin tables: in-range payloads
build the spelled struct (`buildStructValue` normalizes field-wise;
identity at these arms). -/
theorem buildStructValue_slot {σ : ExecState}
    (htypes : σ.types = twinTypes) {t n : Int} {d : GoString}
    (ht0 : 0 ≤ t) (ht1 : t < 2 ^ 64)
    (hn0 : 0 ≤ n) (hn1 : n < 2 ^ 64) :
    buildStructValue σ (.defined ⟨"main.slot"⟩)
        #[.int t .uint64, .string d, .int n .uint64]
      = .ok (.struct ⟨"main.slot"⟩ (slotFs t d n)) := by
  cases σ with
  | mk types functions methods methodSets heap nextAddr =>
    simp only at htypes
    subst htypes
    have hraw : buildStructValue
        ⟨twinTypes, functions, methods, methodSets, heap, nextAddr⟩
        (.defined ⟨"main.slot"⟩)
        #[.int t .uint64, .string d, .int n .uint64]
        = .ok (.struct ⟨"main.slot"⟩
            (slotFs (IntKind.normalize .uint64 t) d
              (IntKind.normalize .uint64 n))) := by
      kernel_rfl
    rw [hraw, GoLean.SliceMem.unorm_of_range ht0 ht1,
      GoLean.SliceMem.unorm_of_range hn0 hn1]

/-! ## 4. The slot-valued fragment (`t.byIndex`) -/

/-- First index of key `w` (machine scan order). -/
def bIdxOf? : List (Int × SlotA) → Int → Option Nat
  | [], _ => none
  | (k, _) :: rest, w =>
      if k = w then some 0 else (bIdxOf? rest w).map (· + 1)

/-- First-match slot lookup. -/
def bget? : List (Int × SlotA) → Int → Option SlotA
  | [], _ => none
  | (k, s) :: rest, w => if k = w then some s else bget? rest w

/-- The machine encoding of the byIndex list. -/
def toEntriesB (kvs : List (Int × SlotA)) : Array (GoValue × GoValue) :=
  ⟨kvs.map (fun kv => (.int kv.1 .uint64, slotV kv.2))⟩

private theorem valueEq_u64 (σ : ExecState) (l r : Int) :
    valueEq σ (.int .uint64) (.int l .uint64) (.int r .uint64)
      = .ok (l == r) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]

/-- The key-scan loop over the slot entries: values are OPAQUE to the
scan, so the engine is `MapMem.scan_generic`'s proof at the slot
encoding. -/
theorem scanB_generic {w : Int}
    (f : GoValue × GoValue → MProd (Option (Option Nat)) Nat →
      Except GoError (ForInStep (MProd (Option (Option Nat)) Nat)))
    (hf : ∀ (k : Int) (v : GoValue)
      (r : MProd (Option (Option Nat)) Nat),
      f (.int k .uint64, v) r
        = .ok (if k = w then .done ⟨some (some r.snd), r.snd⟩
               else .yield ⟨none, r.snd + 1⟩)) :
    ∀ (kvs : List (Int × SlotA)) (i : Nat),
    (forIn (m := Except GoError) (toEntriesB kvs)
      (⟨none, i⟩ : MProd (Option (Option Nat)) Nat) f)
      = pure (match bIdxOf? kvs w with
        | some j => ⟨some (some (j + i)), j + i⟩
        | none => ⟨none, i + kvs.length⟩) := by
  intro kvs
  induction kvs with
  | nil => intro i; simp [toEntriesB, bIdxOf?]
  | cons kv rest ih =>
    intro i
    obtain ⟨k, s⟩ := kv
    simp only [toEntriesB, List.map_cons, ← Array.forIn_toList] at ih ⊢
    rw [List.forIn_cons, hf]
    by_cases hk : k = w
    · simp [hk, bIdxOf?, Bind.bind, Except.bind]
    · simp only [if_neg hk, bIdxOf?, Bind.bind, Except.bind]
      rw [ih (i + 1)]
      cases hidx : bIdxOf? rest w with
      | none =>
        simp only [Option.map_none, List.length_cons]
        rw [show i + 1 + rest.length = i + (rest.length + 1) from by
          omega]
      | some j =>
        simp only [Option.map_some]
        rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The machine's key scan over the slot entry list is the model's
first-index scan. -/
theorem mapEntryIndex?_toEntriesB (σ : ExecState)
    (kvs : List (Int × SlotA)) (w : Int) (b : Bool) :
    mapEntryIndex? σ (.int .uint64) (toEntriesB kvs)
        (.int w .uint64) b
      = .ok (bIdxOf? kvs w) := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.int w .uint64) b
      (!(toEntriesB kvs).isEmpty) = .ok () from by
    simp [checkKeyHashable, valueHashability]]
  simp only [letFun]
  rw [scanB_generic (w := w) _ ?hf kvs 0]
  case hf =>
    intro k v r
    simp only [valueEq_u64, Bind.bind, Except.bind]
    by_cases hk : k = w
    · simp [hk]
    · have hkb : (k == w) = false := by simpa using hk
      simp [hkb, hk]
  cases h : bIdxOf? kvs w
    <;> simp [Bind.bind, Except.bind, pure, Except.pure]

theorem bIdxOf?_none_bget? {kvs : List (Int × SlotA)} {w : Int}
    (h : bIdxOf? kvs w = none) : bget? kvs w = none := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k, s⟩ := kv
    simp only [bIdxOf?] at h
    by_cases hk : k = w
    · simp [hk] at h
    · simp only [if_neg hk] at h
      simp only [bget?, if_neg hk]
      exact ih (by cases hidx : bIdxOf? rest w <;> simp [hidx] at h ⊢)

theorem bIdxOf?_some_bget? {kvs : List (Int × SlotA)} {w : Int} {j : Nat}
    (h : bIdxOf? kvs w = some j) :
    ∃ s : SlotA, bget? kvs w = some s ∧ kvs[j]? = some (w, s) := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
    obtain ⟨k, s⟩ := kv
    simp only [bIdxOf?] at h
    by_cases hk : k = w
    · simp only [if_pos hk] at h
      cases h
      exact ⟨s, by simp [bget?, hk], by simp [hk]⟩
    · simp only [if_neg hk] at h
      cases hidx : bIdxOf? rest w with
      | none => simp [hidx] at h
      | some j' =>
        simp only [hidx, Option.map_some] at h
        cases h
        obtain ⟨s', hs1, hs2⟩ := ih hidx
        exact ⟨s', by simp [bget?, hk, hs1],
          by simpa [List.getElem?_cons_succ] using hs2⟩

theorem toEntriesB_getElem? (kvs : List (Int × SlotA)) (j : Nat)
    {w : Int} {s : SlotA} (h : kvs[j]? = some (w, s)) :
    (toEntriesB kvs)[j]? = some (.int w .uint64, slotV s) := by
  simp [toEntriesB, List.getElem?_map, h]

/-- **The byIndex comma-ok lookup** over the slot encoding: the value
is the first-match slot (the slot ZERO on a miss — Go's zero-value
comma-ok), the flag is the scan's success. Types premise feeds the
miss arm's `defaultValue` at the defined slot type. -/
theorem applyRhsOp_mapLookup_toEntriesB {σ : ExecState} {a : Addr}
    {kvs : List (Int × SlotA)} {w : Nat}
    (htypes : σ.types = twinTypes)
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntriesB kvs)⟩)
    (hw : w < 2 ^ 64) :
    applyRhsOp σ (.mapLookup (.int .uint64) (.defined ⟨"main.slot"⟩))
        [.map ⟨some (.base a)⟩, .int (w : Int) .uint64]
      = .ok [slotV ((bget? kvs (w : Int)).getD zeroSlot),
        .bool (bIdxOf? kvs (w : Int)).isSome] := by
  simp only [applyRhsOp, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int (w : Int) .uint64)
      = .ok (.int (w : Int) .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, GoLean.SliceMem.unorm_nat_of_lt hw]]
  simp only [mapLookupValue, mapEntries, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_toEntriesB]
  cases hidx : bIdxOf? kvs (w : Int) with
  | none =>
    rw [bIdxOf?_none_bget? hidx]
    simp [defaultValue_slot htypes, slotV, zeroSlot]
  | some j =>
    obtain ⟨s, hs1, hs2⟩ := bIdxOf?_some_bget? hidx
    rw [hs1]
    simp [toEntriesB_getElem? kvs j hs2]

/-- **The byIndex first-insert** (`t.byIndex[idx] = slot{…}`, taken
only on a scan miss — the only assignment the checker performs):
`mapAssignValue` appends. The slot value re-normalizes at the DEFINED
type (the table-footprint step, `normalize_slotFs`). -/
theorem mapAssignValue_toEntriesB_insert {σ : ExecState} {a : Addr}
    {kvs : List (Int × SlotA)} {w : Nat} {s : SlotA}
    (htypes : σ.types = twinTypes)
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntriesB kvs)⟩)
    (hmiss : bIdxOf? kvs (w : Int) = none)
    (hw : w < 2 ^ 64) (ht : s.1 < 2 ^ 64) (hn : s.2.2 < 2 ^ 64) :
    mapAssignValue σ (.int .uint64) (.defined ⟨"main.slot"⟩)
        (.map ⟨some (.base a)⟩) (.int (w : Int) .uint64) (slotV s)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (toEntriesB (kvs ++ [((w : Int), s)]))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int (w : Int) .uint64)
      = .ok (.int (w : Int) .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, GoLean.SliceMem.unorm_nat_of_lt hw]]
  rw [show normalizeValueForTy σ (.defined ⟨"main.slot"⟩) (slotV s)
      = .ok (slotV s) from
    normalize_slotFs htypes (by omega) (by omega) (by omega)
      (by omega)]
  simp only [mapEntries, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_toEntriesB, hmiss]
  show storeLoc σ (.base a)
    (.mapData ((toEntriesB kvs).push (.int (w : Int) .uint64, slotV s)))
      = _
  rw [show (toEntriesB kvs).push (.int (w : Int) .uint64, slotV s)
      = toEntriesB (kvs ++ [((w : Int), s)]) from by
    apply Array.toList_inj.mp
    simp [toEntriesB]]
  simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
    pure, Except.pure]

end GoLean.RaftSeam.SpanS23
