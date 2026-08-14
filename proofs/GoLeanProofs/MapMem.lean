import GoLean.GoCore.MachineSound

/-!
# Map-in-memory vocabulary + the executable map-op facts
(Gallery Campaign G0 item 3b, 2026-08-15 — the MapMem promotion)

The `map[uint64]uint64` analogue of `SliceMem`: the §10a
map-in-memory vocabulary (`mapCells`/`mapVal`), the abstract
association-list model (`idxOf?`/`cnt`/`setk` with `toEntries`, the
machine encoding), and the executable map-operation facts — what
`applyStrictOp`/`mapAssignValue`/`mapRangeSnapshotEntries` compute on
this fragment, conditioned on the lookup/normal-form hypotheses.

Promoted VERBATIM from `Examples/WordCount/Pure.lean` (where the
family was recorded as a "SliceMem promotion candidate" at birth,
scale-out slice 2026-08-13) under the §12 active-abstraction loop in
its campaign form: the landed consumer is WordCount (retrofitted in
this commit — the example-local copies are DELETED, the P6 rule);
the chartered consumers are the G1 candidates histogram and
fibonacci-memo, whose map phases state exactly these facts.

Everything speaks the private counts encoding `List (Int × Nat)` —
keys with `Nat` values (the machine stores values as wrapped uint64
`Int`s; `toEntries` is the encoding). WordCount's PURE counting layer
(`bump`/`countsList`/the max fold) is NOT here: it is wordcount's
spec vocabulary, not map machinery.

## PUBLIC API — the sealed interface (the W6 convention, as in
`SliceMem`)

**What consumers may depend on** (and nothing else):

* statement-adjacent vocabulary: `mapCells`, `mapVal`;
* the abstract model: `idxOf?`, `cnt`, `setk`, `toEntries`, and the
  model lemmas `idxOf?_none_cnt`, `idxOf?_none_setk`,
  `idxOf?_some_snd`, `idxOf?_some_setk`;
* the executable op facts, each conditioned on exactly its
  lookup/normal-form hypotheses: `applyStrictOp_mapGet` (read, with
  Go's zero-value-on-absent), `mapAssignValue_toEntries` (write,
  update-or-append = `setk`), `snapshot_toEntries` (the `mapRangeK`
  snapshot), `mapEntryIndex?_toEntries` (the key scan), and the
  scan engine `scan_generic`;
* the `toEntries` bridges: `toEntries_getElem?`, `toEntries_size`,
  `toEntries_eraseIdx`, `map_eraseIdx`.

**Internal** (`private` — spelling may change without notice):
`valueEq_u64`, `toEntries_setk`, `snapshot_norm`.

**The API discipline** (as `SliceMem`'s, verbatim in substance):
everything here is UNTRUSTED METHOD except the vocabulary defs, and
even those enter a headline only under the §11 statement closure
rules — a kit lemma NAME never appears in a headline statement (form
note §12b). Additions follow the §12 loop (≥2 consumers retrofitted
in the lifting commit, measured deltas). Lean's `private` hides names
without sealing definitional transparency; the seal is name-level +
this contract, and the statement layer has its own gate.
-/

namespace GoLean.MapMem

open GoLean GoLean.GoCore GoLean.GoCore.Machine

-- The unusedSimpArgs linter false-flags `letFun` (mapEntryIndex?) and
-- `valueAsMap` (snapshot) — removing either breaks the proof (verified
-- 2026-08-15); same suppression the example modules carry.
set_option linter.unusedSimpArgs false

/-! ## The §10a map-in-memory vocabulary -/

/-- The heap representation of a `map[uint64]uint64` holding the
association list `kvs` (insertion order = list order): one data cell at
`base`. The handle the program carries is `mapVal base`. -/
def mapCells (kvs : List (Int × Int)) (base : Nat) : Heap :=
  [(.base ⟨base⟩,
    ⟨none, .mapData ⟨kvs.map (fun kv => (.int kv.1 .uint64, .int kv.2 .uint64))⟩⟩)]

def mapVal (base : Nat) : GoValue := .map ⟨some (.base ⟨base⟩)⟩

/-! ## The abstract association-list model -/

/-- First index of key `w` (the machine's `mapEntryIndex?` order). -/
def idxOf? : List (Int × Nat) → Int → Option Nat
  | [], _ => none
  | (k, _) :: rest, w => if k = w then some 0 else (idxOf? rest w).map (· + 1)

/-- Assoc lookup at the FIRST occurrence, `0` when absent — exactly a
Go map read's zero-value semantics on this fragment. -/
def cnt : List (Int × Nat) → Int → Nat
  | [], _ => 0
  | (k, c) :: rest, w => if k = w then c else cnt rest w

/-- Update the first occurrence of `w`, or append — exactly
`mapAssignValue`'s update-or-insert on the entry list. -/
def setk : List (Int × Nat) → Int → Nat → List (Int × Nat)
  | [], w, v => [(w, v)]
  | (k, c) :: rest, w, v =>
      if k = w then (k, v) :: rest else (k, c) :: setk rest w v

/-- The machine encoding of a counts list: insertion-ordered
`mapData` entries of wrapped uint64 pairs. -/
def toEntries (kvs : List (Int × Nat)) : Array (GoValue × GoValue) :=
  ⟨kvs.map (fun kv => (.int kv.1 .uint64, .int (kv.2 : Int) .uint64))⟩

/-- The §10a vocabulary coheres with the counts encoding. -/
example (kvs : List (Int × Nat)) (base : Nat) :
    mapCells (kvs.map (fun p => (p.1, (p.2 : Int)))) base
      = [(.base ⟨base⟩, ⟨none, .mapData (toEntries kvs)⟩)] := by
  simp [mapCells, toEntries, List.map_map, Function.comp]

private theorem valueEq_u64 (σ : ExecState) (l r : Int) :
    valueEq σ (.int .uint64) (.int l .uint64) (.int r .uint64)
      = .ok (l == r) := by
  simp [valueEq, valueEqFuel, typeResolutionFuel]

/-- The key-scan loop of `mapEntryIndex?` over an abstract body `f`
(pinned only by its action on wrapped-integer entry pairs — the
abstraction is what lets `rw` unify it with the do-elaborated lambda),
generalized over the starting counter. -/
theorem scan_generic {w : Int}
    (f : GoValue × GoValue → MProd (Option (Option Nat)) Nat →
      Except GoError (ForInStep (MProd (Option (Option Nat)) Nat)))
    (hf : ∀ (k : Int) (v : GoValue) (r : MProd (Option (Option Nat)) Nat),
      f (.int k .uint64, v) r
        = .ok (if k = w then .done ⟨some (some r.snd), r.snd⟩
               else .yield ⟨none, r.snd + 1⟩)) :
    ∀ (kvs : List (Int × Nat)) (i : Nat),
    (forIn (m := Except GoError) (toEntries kvs)
      (⟨none, i⟩ : MProd (Option (Option Nat)) Nat) f)
      = pure (match idxOf? kvs w with
        | some j => ⟨some (some (j + i)), j + i⟩
        | none => ⟨none, i + kvs.length⟩) := by
  intro kvs
  induction kvs with
  | nil => intro i; simp [toEntries, idxOf?]
  | cons kv rest ih =>
      intro i
      obtain ⟨k, c⟩ := kv
      simp only [toEntries, List.map_cons, ← Array.forIn_toList] at ih ⊢
      rw [List.forIn_cons, hf]
      by_cases hk : k = w
      · simp [hk, idxOf?, Bind.bind, Except.bind]
      · simp only [if_neg hk, idxOf?, Bind.bind, Except.bind]
        rw [ih (i + 1)]
        cases hidx : idxOf? rest w with
        | none =>
            simp only [Option.map_none, List.length_cons]
            rw [show i + 1 + rest.length = i + (rest.length + 1) from by omega]
        | some j =>
            simp only [Option.map_some]
            rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The machine's key scan over an abstract `uint64 → uint64`
association list is the list-model first-index scan. -/
theorem mapEntryIndex?_toEntries (σ : ExecState)
    (kvs : List (Int × Nat)) (w : Int) (b : Bool) :
    mapEntryIndex? σ (.int .uint64) (toEntries kvs) (.int w .uint64) b
      = .ok (idxOf? kvs w) := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.int w .uint64) b (!(toEntries kvs).isEmpty)
      = .ok () from by simp [checkKeyHashable, valueHashability]]
  simp only [letFun]
  rw [scan_generic (w := w) _ ?hf kvs 0]
  case hf =>
    intro k v r
    simp only [valueEq_u64, Bind.bind, Except.bind]
    by_cases hk : k = w
    · simp [hk]
    · have hkb : (k == w) = false := by simpa using hk
      simp [hkb, hk]
  cases h : idxOf? kvs w <;> simp [Bind.bind, Except.bind, pure, Except.pure]

/-! ### The model lemmas: `idxOf?` against `cnt` and `setk` -/

theorem idxOf?_none_cnt {kvs : List (Int × Nat)} {w : Int}
    (h : idxOf? kvs w = none) : cnt kvs w = 0 := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [cnt, if_neg hk]
        exact ih (by cases hidx : idxOf? rest w <;> simp [hidx] at h ⊢)

theorem idxOf?_none_setk {kvs : List (Int × Nat)} {w : Int}
    (h : idxOf? kvs w = none) (v : Nat) : kvs ++ [(w, v)] = setk kvs w v := by
  induction kvs with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp [hk] at h
      · simp only [if_neg hk] at h
        simp only [List.cons_append, setk, if_neg hk]
        exact congrArg _
          (ih (by cases hidx : idxOf? rest w <;> simp [hidx] at h ⊢))

theorem idxOf?_some_snd {kvs : List (Int × Nat)} {w : Int} {j : Nat}
    (h : idxOf? kvs w = some j) :
    kvs[j]? = some (w, cnt kvs w) := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [cnt, hk]
      · simp only [if_neg hk] at h
        cases hidx : idxOf? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.getElem?_cons_succ, cnt, if_neg hk]
            exact ih hidx

theorem idxOf?_some_setk {kvs : List (Int × Nat)} {w : Int} {j : Nat}
    (h : idxOf? kvs w = some j) (v : Nat) :
    kvs.set j (w, v) = setk kvs w v := by
  induction kvs generalizing j with
  | nil => cases h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [idxOf?] at h
      by_cases hk : k = w
      · simp only [if_pos hk] at h
        cases h
        simp [setk, hk, List.set]
      · simp only [if_neg hk] at h
        cases hidx : idxOf? rest w with
        | none => simp [hidx] at h
        | some j' =>
            simp only [hidx, Option.map_some] at h
            cases h
            simp only [List.set, setk, if_neg hk]
            exact congrArg _ (ih hidx)

/-! ### The `toEntries` bridges -/

theorem toEntries_getElem? (kvs : List (Int × Nat)) (j : Nat)
    {p : Int × Nat} (h : kvs[j]? = some p) :
    (toEntries kvs)[j]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) := by
  simp [toEntries, List.getElem?_map, h]

theorem toEntries_size (kvs : List (Int × Nat)) :
    (toEntries kvs).size = kvs.length := by
  simp [toEntries]

theorem map_eraseIdx {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a rest ih =>
      intro i
      cases i with
      | zero => simp [List.eraseIdx]
      | succ n => simp [List.eraseIdx, ih n]

theorem toEntries_eraseIdx (kvs : List (Int × Nat)) (i : Nat)
    (h : i < (toEntries kvs).size) :
    (toEntries kvs).eraseIdx i h = toEntries (kvs.eraseIdx i) := by
  apply Array.toList_inj.mp
  simp [toEntries, map_eraseIdx]

/-! ## The executable map-op facts -/

/-- **The map-elem read** (`counts[w]`, expression position): a present
key answers its count, an absent key the ZERO VALUE — which is exactly
how `counts[w]++` starts a fresh key at 1. -/
theorem applyStrictOp_mapGet {σ : ExecState} {a : Addr}
    {kvs : List (Int × Nat)} {w : Int} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntries kvs)⟩)
    (hw : IntKind.normalize .uint64 w = w) :
    applyStrictOp σ (.mapGet (.int .uint64) (.int .uint64))
      [.map ⟨some (.base a)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64, σ) := by
  simp only [applyStrictOp, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int w .uint64)
      = .ok (.int w .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hw]]
  simp only [loadLoc, hlook, pure, Except.pure]
  rw [mapEntryIndex?_toEntries]
  cases hidx : idxOf? kvs w with
  | none =>
      rw [idxOf?_none_cnt hidx]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]
  | some j =>
      have hj := idxOf?_some_snd hidx
      simp [toEntries_getElem? kvs j hj]

private theorem toEntries_setk {kvs : List (Int × Nat)} {w : Int} {v : Nat} :
    (match idxOf? kvs w with
      | some i =>
          (toEntries kvs).set! i (.int w .uint64, .int (v : Int) .uint64)
      | none => (toEntries kvs).push (.int w .uint64, .int (v : Int) .uint64))
      = toEntries (setk kvs w v) := by
  cases hidx : idxOf? kvs w with
  | none =>
      show (toEntries kvs).push _ = _
      apply Array.toList_inj.mp
      simp [toEntries, ← idxOf?_none_setk hidx v]
  | some j =>
      show (toEntries kvs).set! j _ = _
      apply Array.toList_inj.mp
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
        toEntries, ← idxOf?_some_setk hidx v, List.map_set]

/-- **The map-elem write** (`counts[w] = v`): `mapAssignValue`'s
update-or-append on the abstract association list is `setk`. -/
theorem mapAssignValue_toEntries {σ : ExecState} {a : Addr}
    {kvs : List (Int × Nat)} {w : Int} {v : Nat}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntries kvs)⟩)
    (hw : IntKind.normalize .uint64 w = w)
    (hv : IntKind.normalize .uint64 (v : Int) = (v : Int)) :
    mapAssignValue σ (.int .uint64) (.int .uint64)
      (.map ⟨some (.base a)⟩) (.int w .uint64) (.int (v : Int) .uint64)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (toEntries (setk kvs w v))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ (.int .uint64) (.int w .uint64)
      = .ok (.int w .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hw]]
  rw [show normalizeValueForTy σ (.int .uint64) (.int (v : Int) .uint64)
      = .ok (.int (v : Int) .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
      hv]]
  simp only [mapEntries, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndex?_toEntries]
  cases hidx : idxOf? kvs w with
  | some j =>
      show storeLoc σ (.base a)
        (.mapData ((toEntries kvs).set! j
          (.int w .uint64, .int (v : Int) .uint64))) = _
      rw [show (toEntries kvs).set! j
          ((.int w .uint64 : GoValue), (.int (v : Int) .uint64 : GoValue))
          = toEntries (setk kvs w v) from by
        have h := toEntries_setk (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
        pure, Except.pure]
  | none =>
      show storeLoc σ (.base a)
        (.mapData ((toEntries kvs).push
          (.int w .uint64, .int (v : Int) .uint64))) = _
      rw [show (toEntries kvs).push
          ((.int w .uint64 : GoValue), (.int (v : Int) .uint64 : GoValue))
          = toEntries (setk kvs w v) from by
        have h := toEntries_setk (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind, Except.bind,
        pure, Except.pure]

private theorem snapshot_norm (types : TypeEnv) :
    ∀ kvs : List (Int × Nat),
    (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) →
    snapshotEntriesSelfNormalizedList types (.int .uint64) (.int .uint64)
      (kvs.map (fun kv =>
        ((.int kv.1 .uint64 : GoValue), (.int (kv.2 : Int) .uint64 : GoValue))))
      = true := by
  intro kvs
  induction kvs with
  | nil => intro _; rfl
  | cons p rest ih =>
      intro hkv
      have hp := hkv p (by simp)
      have hrest := ih (fun q hq => hkv q (by simp [hq]))
      simp only [List.map_cons, snapshotEntriesSelfNormalizedList]
      rw [hrest]
      simp [isNormalForTy, isNormalForTyFuel, typeResolutionFuel, hp.1, hp.2]

/-- **The range snapshot** (`mapRangeK`): reads the data cell and
validates every entry self-normalized — on the in-range fragment, the
identity. -/
theorem snapshot_toEntries {σ : ExecState} {a : Addr}
    {kvs : List (Int × Nat)} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntries kvs)⟩)
    (hkv : ∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    mapRangeSnapshotEntries σ (.int .uint64) (.int .uint64)
      (.map ⟨some (.base a)⟩)
      = .ok (toEntries kvs) := by
  have hnorm := snapshot_norm σ.types kvs hkv
  simp only [mapRangeSnapshotEntries, mapRangeEntries, valueAsMap, Bind.bind,
    Except.bind, pure, Except.pure, loadLoc, hlook,
    snapshotEntriesSelfNormalized]
  rw [show (toEntries kvs).toList
      = kvs.map (fun kv =>
        ((.int kv.1 .uint64 : GoValue), (.int (kv.2 : Int) .uint64 : GoValue)))
      from rfl, hnorm]
  simp

end GoLean.MapMem
