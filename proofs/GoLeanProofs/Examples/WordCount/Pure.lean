import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps

/-!
# WordCount — Pure

Per-phase shard of `GoLeanProofs.Examples.WordCount` (examples phase-2
slice 0, lever 2, 2026-08-14). Every statement and proof here is
BYTE-IDENTICAL to the pre-split module; only file placement changed, so
Lake's module-level caching can see the phases separately. The
user-facing headline theorems live in the thin root module
`GoLeanProofs.Examples.WordCount`; the module docstring there records
the example's design.
-/

namespace GoLean.Examples.WordCount

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The specification layer (order-independent, per §10b) -/

/-- Occurrences of `v` in `ws`. -/
def multiplicity (v : Int) (ws : List Int) : Nat :=
  (ws.filter (· = v)).length

/-- The largest multiplicity any value attains in `ws` (`0` for `[]`) —
a commutative-idempotent max-fold, so it is invariant under iteration
order: the shape the ∀-choices quantifier forces (§10b). -/
def maxMultiplicity (ws : List Int) : Nat :=
  ws.foldl (fun acc v => max acc (multiplicity v ws)) 0

/-! ## The §10a map-in-memory vocabulary

Shipped verbatim from the design note as the shared-vocabulary
candidate (report: SliceMem promotion). The headline itself never
mentions the map — it is program-internal — so `mapCells`/`mapVal` are
consumed here only through the private `Int × Nat` counts encoding
(`toEntries` below; the bridge lemma ties them). -/

/-- The heap representation of a `map[uint64]uint64` holding the
association list `kvs` (insertion order = list order): one data cell at
`base`. The handle the program carries is `mapVal base`. -/
def mapCells (kvs : List (Int × Int)) (base : Nat) : Heap :=
  [(.base ⟨base⟩,
    ⟨none, .mapData ⟨kvs.map (fun kv => (.int kv.1 .uint64, .int kv.2 .uint64))⟩⟩)]

def mapVal (base : Nat) : GoValue := .map ⟨some (.base ⟨base⟩)⟩

/-! ## The program-side statement vocabulary -/

/-- The subject's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def maxCountFunc : Func :=
  { id := { key := "maxCount" },
    args := #[{ id := "words", typ := .slice (.int .uint64) }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization
              { id := "$c0", typ := .map (.int .uint64) (.int .uint64) },
            .makeMap (.var "$c0") (.int .uint64) (.int .uint64) none],
        .seqn
          #[.initialization
              { id := "counts", typ := .map (.int .uint64) (.int .uint64) },
            .assign (.var "counts") (.var "$c0")],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 0 .int)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true)
                  (.block
                    #[]
                    #[.ifThenElse (.var "$forFirst")
                        (.assign (.var "$forFirst") (.boolLit false))
                        (.assign (.var "i")
                          (.add (.var "i") (.intLit 1 .int))),
                      .seqn #[],
                      .ifThenElse
                        (.lessCmp (.var "i")
                          (.length (.var "words")
                            (some (.slice (.int .uint64)))))
                        (.seqn #[])
                        .breakStmt,
                      .block
                        #[]
                        #[.seqn
                            #[.initialization
                                { id := "$c1",
                                  typ := .map (.int .uint64) (.int .uint64) },
                              .assign (.var "$c1") (.var "counts")],
                          .seqn
                            #[.initialization
                                { id := "$c2", typ := .int .uint64 },
                              .assign (.var "$c2")
                                (.indexGet (.var "words") (.var "i"))],
                          .mapAssign (.var "$c1") (.var "$c2")
                            (.add
                              (.mapGet (.var "$c1") (.var "$c2")
                                (.int .uint64) (.int .uint64))
                              (.intLit 1 .uint64))
                            (.int .uint64) (.int .uint64)]])]],
        .seqn
          #[.initialization { id := "best", typ := .int .uint64 },
            .assign (.var "best") (.intLit 0 .uint64)],
        .mapRange none (some "c") (.var "counts") (.int .uint64) (.int .uint64)
          (.block
            #[]
            #[.ifThenElse (.greaterCmp (.var "c") (.var "best"))
                (.block
                  #[]
                  #[.seqn #[.assign (.var "best") (.var "c")]])
                (.seqn #[])]),
        .seqn
          #[.assign (.var "$res0") (.var "best"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
example : findFunctionIn? wordCountLowered.funcs ⟨"maxCount"⟩
    = some maxCountFunc := rfl

/-- The harness cell the differential runner also reads. -/
def wcEnv : LocalEnv := [[("$callres", Loc.base ⟨0⟩)]]

/-- The zeroed uint64 result cell at address `0`. -/
def wcResCell : Heap := [(.base ⟨0⟩, ⟨some (.int .uint64), .int 0 .uint64⟩)]

/-- The driver: `$callres = maxCount(words)` — the words slice enters
as a slice expression over the backing array at `base` (the §9a
memory-input convention). -/
def wcCall (ws : List Int) (base : Nat) : Stmt :=
  .call #[.var "$callres"] ⟨"maxCount"⟩
    #[.slice (.locLit (.base ⟨base⟩)) (.intLit 0 .int)
        (.intLit ws.length .int) none]

/-- The framed seed: result cell, the input's backing cell at `base`,
an arbitrary frame `fr`, allocator at `na`. The canonical placement is
`wcSeed ws 1 [] 2` — TIGHT (dom = {0, 1}, na₀ = 2), as the frame
theorem's seed discharge requires. -/
def wcSeed (ws : List Int) (base : Nat) (fr : Heap) (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := wcResCell ++ sliceCells ws base ++ fr, nextAddr := na }

/-! ## The private counts encoding and the machine map facts

The reasoning layer speaks `List (Int × Nat)` — keys with their `Nat`
counts (the machine stores counts as wrapped uint64 `Int`s; `toEntries`
is the encoding). These executable facts on the `map[uint64]uint64`
fragment are the `storeTarget_slice_u64` analogs — SliceMem promotion
candidates (recorded in the slice report; kept private here). -/

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

/-- The §10a vocabulary coheres with the private encoding. -/
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
private theorem scan_generic {w : Int}
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
private theorem mapEntryIndex?_toEntries (σ : ExecState)
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

private theorem idxOf?_none_cnt {kvs : List (Int × Nat)} {w : Int}
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

private theorem idxOf?_none_setk {kvs : List (Int × Nat)} {w : Int}
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

private theorem idxOf?_some_snd {kvs : List (Int × Nat)} {w : Int} {j : Nat}
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

private theorem idxOf?_some_setk {kvs : List (Int × Nat)} {w : Int} {j : Nat}
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

theorem toEntries_getElem? (kvs : List (Int × Nat)) (j : Nat)
    {p : Int × Nat} (h : kvs[j]? = some p) :
    (toEntries kvs)[j]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) := by
  simp [toEntries, List.getElem?_map, h]

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
  simp [toEntries, Array.toList_eraseIdx, map_eraseIdx]

/-! ## The heap-append kit (symbolic-address algebra, §10c)

The in-loop cells live at length-dependent addresses past the nine
concrete front cells, so their reads/writes are discharged by this
small append algebra instead of definitional reduction. -/

/-! ## The pure counts layer: `bump`, `countsList`, and the max fold -/

/-- One word lands in the counts list: increment the first occurrence
of the key, or append `(v, 1)` — first-occurrence insertion order,
matching the machine's `mapAssign`. -/
def bump : List (Int × Nat) → Int → List (Int × Nat)
  | [], v => [(v, 1)]
  | (k, c) :: rest, v =>
      if k = v then (k, c + 1) :: rest else (k, c) :: bump rest v

/-- The counts list after processing `ws`, in first-occurrence
insertion order — the abstract content of the map data cell. -/
def countsList (ws : List Int) : List (Int × Nat) :=
  ws.foldl bump []

/-- What the machine's write computes is `bump`: the value written is
`counts[w] + 1` at the first occurrence (or `0 + 1` fresh). -/
theorem setk_cnt_succ :
    ∀ (kvs : List (Int × Nat)) (w : Int),
    setk kvs w (cnt kvs w + 1) = bump kvs w := by
  intro kvs
  induction kvs with
  | nil => intro w; rfl
  | cons kv rest ih =>
      intro w
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp [setk, cnt, bump, hk]
      · simp [setk, cnt, bump, hk, ih w]

theorem countsList_append_word (p : List Int) (w : Int) :
    countsList (p ++ [w]) = bump (countsList p) w := by
  simp [countsList, List.foldl_append]

private theorem multiplicity_nil (v : Int) : multiplicity v [] = 0 := rfl

private theorem multiplicity_cons (v w : Int) (ws : List Int) :
    multiplicity v (w :: ws)
      = (if w = v then 1 else 0) + multiplicity v ws := by
  simp only [multiplicity, List.filter_cons]
  by_cases h : w = v
  · simp [h, Nat.add_comm]
  · simp [h]

/-- `cnt` after a `bump`. -/
private theorem cnt_bump (kvs : List (Int × Nat)) (w x : Int) :
    cnt (bump kvs w) x
      = if x = w then cnt kvs w + 1 else cnt kvs x := by
  induction kvs with
  | nil =>
      by_cases hx : x = w
      · simp [bump, cnt, hx]
      · simp [bump, cnt, hx, Ne.symm hx]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · subst hk
        by_cases hx : x = k
        · simp [bump, cnt, hx]
        · simp [bump, cnt, Ne.symm hx, hx]
      · by_cases hxk : k = x
        · subst hxk
          simp [bump, cnt, hk]
        · simp [bump, cnt, hk, hxk, ih]

/-- **The counts-list invariant**: after processing `ws`, `cnt` at any
key is its multiplicity (0 included on both sides for absent keys). -/
private theorem cnt_countsList (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (x : Int),
    cnt (List.foldl bump kvs ws) x = cnt kvs x + multiplicity x ws := by
  induction ws with
  | nil => intro kvs x; simp [multiplicity_nil]
  | cons w rest ih =>
      intro kvs x
      simp only [List.foldl_cons, ih, cnt_bump, multiplicity_cons]
      by_cases hx : x = w
      · subst hx
        have h1 : (if x = x then cnt kvs x + 1 else cnt kvs x)
            = cnt kvs x + 1 := if_pos rfl
        have h2 : (if x = x then 1 else 0) = 1 := if_pos rfl
        omega
      · have h1 : (if x = w then cnt kvs w + 1 else cnt kvs x)
            = cnt kvs x := if_neg hx
        have h2 : (if w = x then 1 else 0) = 0 := if_neg (Ne.symm hx)
        omega

theorem cnt_countsList' (ws : List Int) (x : Int) :
    cnt (countsList ws) x = multiplicity x ws := by
  simpa [countsList, cnt] using cnt_countsList ws [] x

/-- Every entry of a `bump`-fold has its key in the processed words (or
in the seed). -/
private theorem mem_bump {kvs : List (Int × Nat)} {w : Int}
    {p : Int × Nat} (h : p ∈ bump kvs w) :
    p.1 = w ∨ p ∈ kvs := by
  induction kvs with
  | nil =>
      simp only [bump, List.mem_singleton] at h
      exact .inl (by rw [h])
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = w
      · simp only [bump, if_pos hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inl (by rw [h1]; exact hk)
        · exact .inr (List.mem_cons.mpr (.inr h1))
      · simp only [bump, if_neg hk] at h
        rcases List.mem_cons.mp h with h1 | h1
        · exact .inr (List.mem_cons.mpr (.inl h1))
        · rcases ih h1 with h2 | h2
          · exact .inl h2
          · exact .inr (List.mem_cons.mpr (.inr h2))

theorem countsList_key_mem (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (p : Int × Nat),
    p ∈ List.foldl bump kvs ws → p.1 ∈ ws ∨ p ∈ kvs := by
  induction ws with
  | nil => intro kvs p h; exact .inr h
  | cons w rest ih =>
      intro kvs p h
      simp only [List.foldl_cons] at h
      rcases ih (bump kvs w) p h with h | h
      · exact .inl (by simp [h])
      · rcases mem_bump h with h | h
        · exact .inl (by simp [h])
        · exact .inr h

/-- Distinct keys (`Nodup` on the key column) — `bump` preserves it. -/
private theorem nodup_keys_bump {kvs : List (Int × Nat)} {w : Int}
    (h : (kvs.map Prod.fst).Nodup) :
    ((bump kvs w).map Prod.fst).Nodup := by
  induction kvs with
  | nil => simp [bump]
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at h
      by_cases hk : k = w
      · simpa [bump, hk, List.nodup_cons] using h
      · simp only [bump, if_neg hk, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih h.2⟩
        intro hc
        rcases List.mem_map.mp hc with ⟨p, hp, hpk⟩
        rcases mem_bump hp with h1 | h1
        · exact hk (hpk ▸ h1)
        · exact h.1 (List.mem_map.mpr ⟨p, h1, hpk⟩)

private theorem nodup_keys_countsList (ws : List Int) :
    ∀ kvs : List (Int × Nat), (kvs.map Prod.fst).Nodup →
    ((List.foldl bump kvs ws).map Prod.fst).Nodup := by
  induction ws with
  | nil => intro kvs h; exact h
  | cons w rest ih =>
      intro kvs h
      exact ih (bump kvs w) (nodup_keys_bump h)

/-- With distinct keys, membership pins the count: `(k, c) ∈ kvs →
cnt kvs k = c`. -/
private theorem cnt_of_mem_nodup :
    ∀ {kvs : List (Int × Nat)} {k : Int} {c : Nat},
    (kvs.map Prod.fst).Nodup → (k, c) ∈ kvs → cnt kvs k = c := by
  intro kvs
  induction kvs with
  | nil => intro k c _ h; cases h
  | cons kv rest ih =>
      intro k c hnd h
      obtain ⟨k', c'⟩ := kv
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with h | h
      · injection h with h1 h2
        subst h1; subst h2
        simp [cnt]
      · have hk : k' ≠ k := by
          intro hc
          subst hc
          exact hnd.1 (List.mem_map.mpr ⟨(k', c), h, rfl⟩)
        simp only [cnt, if_neg hk]
        exact ih hnd.2 h

/-- Positive `cnt` means the key is present. -/
private theorem cnt_pos_mem {kvs : List (Int × Nat)} {x : Int}
    (h : 0 < cnt kvs x) : (x, cnt kvs x) ∈ kvs := by
  induction kvs with
  | nil => simp [cnt] at h
  | cons kv rest ih =>
      obtain ⟨k, c⟩ := kv
      by_cases hk : k = x
      · subst hk
        simp only [cnt, if_pos rfl] at h ⊢
        exact List.mem_cons.mpr (.inl rfl)
      · simp only [cnt, if_neg hk] at h ⊢
        exact List.mem_cons.mpr (.inr (ih h))

/-! ### The max fold -/

/-- Max over a `Nat` list (base 0) — the value-column aggregate. -/
def maxOf (l : List Nat) : Nat := l.foldr max 0

theorem maxOf_nil : maxOf [] = 0 := rfl

private theorem maxOf_cons (a : Nat) (l : List Nat) :
    maxOf (a :: l) = max a (maxOf l) := rfl

private theorem mem_le_maxOf {l : List Nat} {c : Nat} (h : c ∈ l) :
    c ≤ maxOf l := by
  induction l with
  | nil => cases h
  | cons a rest ih =>
      rcases List.mem_cons.mp h with h | h
      · rw [maxOf_cons, h]
        exact Nat.le_max_left _ _
      · simp only [maxOf_cons]
        exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem maxOf_le {l : List Nat} {B : Nat} (h : ∀ c ∈ l, c ≤ B) :
    maxOf l ≤ B := by
  induction l with
  | nil => simp [maxOf_nil]
  | cons a rest ih =>
      simp only [maxOf_cons, Nat.max_le]
      exact ⟨h a (by simp), ih (fun c hc => h c (by simp [hc]))⟩

/-- **The pick-and-erase law** (§10b): removing the picked entry and
maxing it back in recovers the whole fold — the per-iteration invariant
step, invariant under EVERY pick. -/
theorem maxOf_eraseIdx :
    ∀ (l : List Nat) (i : Nat), i < l.length →
    max l[i]! (maxOf (l.eraseIdx i)) = maxOf l := by
  intro l
  induction l with
  | nil => intro i h; cases h
  | cons a rest ih =>
      intro i hi
      cases i with
      | zero =>
          show max (a :: rest)[0]! (maxOf rest) = maxOf (a :: rest)
          rw [show (a :: rest)[0]! = a from by simp, maxOf_cons]
      | succ n =>
          have hn : n < rest.length := by simpa using hi
          simp only [List.eraseIdx_cons_succ, maxOf_cons]
          rw [show (a :: rest)[n + 1]! = rest[n]! from by
            simp [List.getElem!_cons_succ]]
          rw [← ih n hn]
          omega

/-! ### The spec bridge: `maxOf` of the counts equals
`maxMultiplicity` -/

private theorem foldl_max_le {f : Int → Nat} {B : Nat} :
    ∀ (l : List Int) (a : Nat), a ≤ B → (∀ v ∈ l, f v ≤ B) →
    l.foldl (fun acc v => max acc (f v)) a ≤ B := by
  intro l
  induction l with
  | nil => intro a ha _; simpa using ha
  | cons v rest ih =>
      intro a ha h
      simp only [List.foldl_cons]
      exact ih _ (Nat.max_le.mpr ⟨ha, h v (by simp)⟩)
        (fun x hx => h x (by simp [hx]))

private theorem foldl_max_ge_init {f : Int → Nat} :
    ∀ (l : List Int) (a : Nat),
    a ≤ l.foldl (fun acc v => max acc (f v)) a := by
  intro l
  induction l with
  | nil => intro a; exact Nat.le_refl a
  | cons w rest ih =>
      intro a
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem le_foldl_max {f : Int → Nat} :
    ∀ (l : List Int) (a : Nat) {v : Int}, v ∈ l →
    f v ≤ l.foldl (fun acc v => max acc (f v)) a := by
  intro l
  induction l with
  | nil => intro a v h; cases h
  | cons w rest ih =>
      intro a v h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with h | h
      · subst h
        exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge_init rest _)
      · exact ih _ h

theorem mult_le_maxMult {ws : List Int} {v : Int} (h : v ∈ ws) :
    multiplicity v ws ≤ maxMultiplicity ws :=
  le_foldl_max (f := fun v => multiplicity v ws) ws 0 h

theorem maxMult_le {ws : List Int} {B : Nat}
    (h : ∀ v ∈ ws, multiplicity v ws ≤ B) : maxMultiplicity ws ≤ B :=
  foldl_max_le (f := fun v => multiplicity v ws) ws 0 (Nat.zero_le _) h

private theorem mem_mult_pos {ws : List Int} {v : Int} (h : v ∈ ws) :
    0 < multiplicity v ws := by
  induction ws with
  | nil => cases h
  | cons w rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [multiplicity_cons]
        have h1 : (if v = v then 1 else 0) = 1 := if_pos rfl
        omega
      · rw [multiplicity_cons]
        have := ih h
        omega

/-- **The spec bridge**: the max over the counts-list value column IS
`maxMultiplicity`. -/
theorem maxOf_countsList (ws : List Int) :
    maxOf ((countsList ws).map Prod.snd) = maxMultiplicity ws := by
  have hnd : ((countsList ws).map Prod.fst).Nodup :=
    nodup_keys_countsList ws [] (by simp)
  apply Nat.le_antisymm
  · -- every count is some key's multiplicity, ≤ the max
    apply maxOf_le
    intro c hc
    rcases List.mem_map.mp hc with ⟨⟨k, c'⟩, hp, hsnd⟩
    have hkey : k ∈ ws := by
      rcases countsList_key_mem ws [] (k, c') hp with h | h
      · exact h
      · cases h
    have hcnt : cnt (countsList ws) k = c' := cnt_of_mem_nodup hnd hp
    have : c' = multiplicity k ws := by
      rw [← hcnt, cnt_countsList' ws k]
    subst hsnd
    show c' ≤ maxMultiplicity ws
    rw [this]
    exact mult_le_maxMult hkey
  · -- the max multiplicity is attained by some entry's count
    apply maxMult_le
    intro v hv
    have hpos : 0 < multiplicity v ws := mem_mult_pos hv
    have hcnt : cnt (countsList ws) v = multiplicity v ws :=
      cnt_countsList' ws v
    have hmem : (v, cnt (countsList ws) v) ∈ countsList ws :=
      cnt_pos_mem (by omega)
    have : cnt (countsList ws) v
        ∈ (countsList ws).map Prod.snd :=
      List.mem_map.mpr ⟨(v, cnt (countsList ws) v), hmem, rfl⟩
    rw [← hcnt]
    exact mem_le_maxOf this

/-- Value bound: counts never exceed the word count. -/
theorem countsList_val_le (ws : List Int) {p : Int × Nat}
    (hp : p ∈ countsList ws) : p.2 ≤ ws.length := by
  obtain ⟨k, c⟩ := p
  have hnd := nodup_keys_countsList ws [] (by simp)
  have hcnt : cnt (countsList ws) k = c := cnt_of_mem_nodup hnd hp
  have := cnt_countsList' ws k
  rw [hcnt] at this
  simp only [multiplicity] at this
  have hle : (ws.filter (· = k)).length ≤ ws.length :=
    List.length_filter_le _ _
  omega


end GoLean.Examples.WordCount
