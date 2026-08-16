import GoLeanProofs.Examples.WordFreq.Scan3
import GoLeanProofs.MapMem
import GoLeanProofs.MapLoops

/-!
# WordFreq — Count (part 1: the string-key map facts)

The `map[string]uint64` executable facts, derived locally at
`GoValue.string` keys following `GoLeanProofs/MapMem.lean`'s recipes
(GoString equality = byte equality), then the count-phase machine
segments.

-- GAP-WITNESS: key-generic MapMem (string keys; promotion
-- candidate) — every theorem in the `MapMemW` section below is
-- `GoLeanProofs.MapMem`'s uint64-key fact re-derived at
-- `(.string, .int .uint64)` key/value types over the Pure layer's
-- `idxOfW?`/`cntW`/`setkW` model. 2nd key type at the machine level;
-- the abstract model already has 2 consumers (see Pure.lean's
-- markers).
-/

namespace GoLean.Examples.WordFreq

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-! ## The string-key map encoding and executable facts (MapMemW) -/

/-- The machine encoding of a string-keyed counts list:
insertion-ordered `mapData` entries of `(string, wrapped uint64)`
pairs. -/
def toEntriesW (kvs : List (List UInt8 × Nat)) : Array (GoValue × GoValue) :=
  ⟨kvs.map (fun kv => (.string (gs kv.1), .int (kv.2 : Int) .uint64))⟩

/-- `GoString` equality is byte-list equality (the derived `BEq` chain
bottoms out in the lawful `List UInt8` instance). -/
theorem gs_beq_eq_decide (a b : List UInt8) :
    (gs a == gs b) = decide (a = b) := by
  show (⟨a⟩ == (⟨b⟩ : Array UInt8)) = decide (a = b)
  by_cases h : a = b
  · subst h; simp
  · have h2 : (⟨a⟩ : Array UInt8) ≠ ⟨b⟩ := fun hc => h (by cases hc; rfl)
    simp [h, h2]

/-- The machine's `==` at `.string` on wrapped byte lists. -/
theorem valueEq_str (σ : ExecState) (l r : List UInt8) :
    valueEq σ .string (.string (gs l)) (.string (gs r))
      = .ok (decide (l = r)) := by
  simp only [valueEq, valueEqFuel, typeResolutionFuel]
  rw [gs_beq_eq_decide]
  rfl

/-- The key-scan loop of `mapEntryIndex?` over an abstract body `f`
(MapMem's `scan_generic`, string keys). -/
theorem scan_genericW {w : List UInt8}
    (f : GoValue × GoValue → MProd (Option (Option Nat)) Nat →
      Except GoError (ForInStep (MProd (Option (Option Nat)) Nat)))
    (hf : ∀ (k : List UInt8) (v : GoValue)
      (r : MProd (Option (Option Nat)) Nat),
      f (.string (gs k), v) r
        = .ok (if k = w then .done ⟨some (some r.snd), r.snd⟩
               else .yield ⟨none, r.snd + 1⟩)) :
    ∀ (kvs : List (List UInt8 × Nat)) (i : Nat),
    (forIn (m := Except GoError) (toEntriesW kvs)
      (⟨none, i⟩ : MProd (Option (Option Nat)) Nat) f)
      = pure (match idxOfW? kvs w with
        | some j => ⟨some (some (j + i)), j + i⟩
        | none => ⟨none, i + kvs.length⟩) := by
  intro kvs
  induction kvs with
  | nil => intro i; simp [toEntriesW, idxOfW?]
  | cons kv rest ih =>
      intro i
      obtain ⟨k, c⟩ := kv
      simp only [toEntriesW, List.map_cons, ← Array.forIn_toList] at ih ⊢
      rw [List.forIn_cons, hf]
      by_cases hk : k = w
      · simp [hk, idxOfW?, Bind.bind, Except.bind]
      · simp only [if_neg hk, idxOfW?, Bind.bind, Except.bind]
        rw [ih (i + 1)]
        cases hidx : idxOfW? rest w with
        | none =>
            simp only [Option.map_none, List.length_cons]
            rw [show i + 1 + rest.length = i + (rest.length + 1) from by
              omega]
        | some j =>
            simp only [Option.map_some]
            rw [show j + 1 + i = j + (i + 1) from by omega]

/-- The machine's key scan over a `string → uint64` association list is
the list-model first-index scan. -/
theorem mapEntryIndexW?_toEntriesW (σ : ExecState)
    (kvs : List (List UInt8 × Nat)) (w : List UInt8) (b : Bool) :
    mapEntryIndex? σ .string (toEntriesW kvs) (.string (gs w)) b
      = .ok (idxOfW? kvs w) := by
  unfold mapEntryIndex?
  rw [show checkKeyHashable σ (.string (gs w)) b
        (!(toEntriesW kvs).isEmpty)
      = .ok () from by simp [checkKeyHashable, valueHashability]]
  simp only [letFun]
  rw [scan_genericW (w := w) _ ?hf kvs 0]
  case hf =>
    intro k v r
    simp only [valueEq_str, Bind.bind, Except.bind]
    by_cases hk : k = w
    · simp [hk]
    · simp [hk]
  cases h : idxOfW? kvs w <;>
    simp [Bind.bind, Except.bind, pure, Except.pure]

/-- **The map-elem read** (`counts[w]`, expression position, STRING
key): a present key answers its count, an absent key the ZERO VALUE. -/
theorem applyStrictOp_mapGetW {σ : ExecState} {a : Addr}
    {kvs : List (List UInt8 × Nat)} {w : List UInt8} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntriesW kvs)⟩) :
    applyStrictOp σ (.mapGet .string tU64)
      [.map ⟨some (.base a)⟩, .string (gs w)]
      = .ok (.int (cntW kvs w : Int) .uint64, σ) := by
  simp only [applyStrictOp, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ .string (.string (gs w))
      = .ok (.string (gs w)) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel]]
  simp only [loadLoc, hlook, pure, Except.pure]
  rw [mapEntryIndexW?_toEntriesW]
  cases hidx : idxOfW? kvs w with
  | none =>
      rw [idxOfW?_none_cnt hidx]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]
  | some j =>
      have hj := idxOfW?_some_snd hidx
      have : (toEntriesW kvs)[j]?
          = some (.string (gs w), .int (cntW kvs w : Int) .uint64) := by
        simp [toEntriesW, List.getElem?_map, hj]
      simp [this]

private theorem toEntriesW_setk {kvs : List (List UInt8 × Nat)}
    {w : List UInt8} {v : Nat} :
    (match idxOfW? kvs w with
      | some i =>
          (toEntriesW kvs).set! i
            (.string (gs w), .int (v : Int) .uint64)
      | none =>
          (toEntriesW kvs).push (.string (gs w), .int (v : Int) .uint64))
      = toEntriesW (setkW kvs w v) := by
  cases hidx : idxOfW? kvs w with
  | none =>
      show (toEntriesW kvs).push _ = _
      apply Array.toList_inj.mp
      simp [toEntriesW, ← idxOfW?_none_setk hidx v]
  | some j =>
      show (toEntriesW kvs).set! j _ = _
      apply Array.toList_inj.mp
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
        toEntriesW, ← idxOfW?_some_setk hidx v, List.map_set]

/-- **The map-elem write** (`counts[w] = v`, STRING key):
`mapAssignValue`'s update-or-append on the abstract association list is
`setkW`. -/
theorem mapAssignValue_toEntriesW {σ : ExecState} {a : Addr}
    {kvs : List (List UInt8 × Nat)} {w : List UInt8} {v : Nat}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨none, .mapData (toEntriesW kvs)⟩)
    (hv : IntKind.normalize .uint64 (v : Int) = (v : Int)) :
    mapAssignValue σ .string tU64
      (.map ⟨some (.base a)⟩) (.string (gs w)) (.int (v : Int) .uint64)
      = .ok { σ with heap := (Heap.set σ.heap (.base a)
          ⟨none, .mapData (toEntriesW (setkW kvs w v))⟩) } := by
  simp only [mapAssignValue, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure]
  rw [show normalizeValueForTy σ .string (.string (gs w))
      = .ok (.string (gs w)) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel]]
  rw [show normalizeValueForTy σ tU64 (.int (v : Int) .uint64)
      = .ok (.int (v : Int) .uint64) from by
    simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, hv]]
  simp only [mapEntries, valueAsMap, Bind.bind, Except.bind, pure,
    Except.pure, loadLoc, hlook]
  rw [mapEntryIndexW?_toEntriesW]
  cases hidx : idxOfW? kvs w with
  | some j =>
      show storeLoc σ (.base a)
        (.mapData ((toEntriesW kvs).set! j
          (.string (gs w), .int (v : Int) .uint64))) = _
      rw [show (toEntriesW kvs).set! j
          ((.string (gs w) : GoValue), (.int (v : Int) .uint64 : GoValue))
          = toEntriesW (setkW kvs w v) from by
        have h := toEntriesW_setk (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind,
        Except.bind, pure, Except.pure]
  | none =>
      show storeLoc σ (.base a)
        (.mapData ((toEntriesW kvs).push
          (.string (gs w), .int (v : Int) .uint64))) = _
      rw [show (toEntriesW kvs).push
          ((.string (gs w) : GoValue), (.int (v : Int) .uint64 : GoValue))
          = toEntriesW (setkW kvs w v) from by
        have h := toEntriesW_setk (kvs := kvs) (w := w) (v := v)
        rw [hidx] at h
        exact h]
      simp only [storeLoc, hlook, coerceStoredValue, Bind.bind,
        Except.bind, pure, Except.pure]

private theorem snapshot_normW (types : TypeEnv) :
    ∀ kvs : List (List UInt8 × Nat),
    (∀ p ∈ kvs, IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) →
    snapshotEntriesSelfNormalizedList types .string tU64
      (kvs.map (fun kv =>
        ((.string (gs kv.1) : GoValue),
          (.int (kv.2 : Int) .uint64 : GoValue))))
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
      simp [isNormalForTy, isNormalForTyFuel, typeResolutionFuel, hp]

/-- **The range snapshot** (`mapRangeK`, string keys): reads the data
cell and validates every entry self-normalized — on this fragment, the
identity (string keys are always self-normalized). -/
theorem snapshot_toEntriesW {σ : ExecState} {a : Addr}
    {kvs : List (List UInt8 × Nat)} {dty : Option Ty}
    (hlook : Heap.lookup σ.heap (.base a)
      = some ⟨dty, .mapData (toEntriesW kvs)⟩)
    (hkv : ∀ p ∈ kvs,
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    mapRangeSnapshotEntries σ .string tU64 (.map ⟨some (.base a)⟩)
      = .ok (toEntriesW kvs) := by
  have hnorm := snapshot_normW σ.types kvs hkv
  simp only [mapRangeSnapshotEntries, mapRangeEntries, valueAsMap,
    Bind.bind, Except.bind, pure, Except.pure, loadLoc, hlook,
    snapshotEntriesSelfNormalized]
  rw [show (toEntriesW kvs).toList
      = kvs.map (fun kv =>
        ((.string (gs kv.1) : GoValue),
          (.int (kv.2 : Int) .uint64 : GoValue)))
      from rfl, hnorm]
  simp

/-- The `toEntriesW` size bridge. -/
theorem toEntriesW_size (kvs : List (List UInt8 × Nat)) :
    (toEntriesW kvs).size = kvs.length := by
  simp [toEntriesW]

/-- The `toEntriesW` element bridge. -/
theorem toEntriesW_getElem? (kvs : List (List UInt8 × Nat)) (j : Nat)
    {p : List UInt8 × Nat} (h : kvs[j]? = some p) :
    (toEntriesW kvs)[j]?
      = some (.string (gs p.1), .int (p.2 : Int) .uint64) := by
  simp [toEntriesW, List.getElem?_map, h]

/-- The `toEntriesW` erase bridge. -/
theorem toEntriesW_eraseIdx (kvs : List (List UInt8 × Nat)) (i : Nat)
    (h : i < (toEntriesW kvs).size) :
    (toEntriesW kvs).eraseIdx i h = toEntriesW (kvs.eraseIdx i) := by
  apply Array.toList_inj.mp
  simp [toEntriesW, map_eraseIdx]

/-- **The choice-pick step at a VALUE-ONLY binder, string keys**
(`for _, c := range counts`): at a nonempty snapshot ONE choice is
consumed, the picked entry's VALUE cell is freshly allocated at the
current `nextAddr`, the picked entry is erased. -/
theorem stepFn_pickW_value {σ : ExecState}
    {rem : List (List UInt8 × Nat)} {idx : Nat} {ch ch' : Choices}
    {v : String} {body : Stmt} {env : LocalEnv} {k : Cont}
    {p : List UInt8 × Nat}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length)
    (hp : rem[idx]? = some p)
    (hv : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    stepFn σ
      (.next (.mapIterK none (some v) .string tU64 body
        (toEntriesW rem) env k)) ch
      = .ok (.exec body (env.pushScope.declare v (.base ⟨σ.nextAddr⟩))
          (.mapIterK none (some v) .string tU64 body
            (toEntriesW (rem.eraseIdx idx)) env k),
        { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some tU64, .int (p.2 : Int) .uint64⟩,
            nextAddr := σ.nextAddr + 1 },
        ch') := by
  have hne : (toEntriesW rem).isEmpty = false := by
    cases rem with
    | nil => cases hidx
    | cons q rest => rfl
  have hsz : (toEntriesW rem).size = rem.length := toEntriesW_size rem
  have hget : (toEntriesW rem)[idx]?
      = some (.string (gs p.1), .int (p.2 : Int) .uint64) :=
    toEntriesW_getElem? rem idx hp
  have hidx' : idx < (toEntriesW rem).size := by rw [hsz]; exact hidx
  have hbind : bindIterVars env.pushScope σ none (some v) .string tU64
      (.string (gs p.1)) (.int (p.2 : Int) .uint64)
      = .ok (env.pushScope.declare v (.base ⟨σ.nextAddr⟩),
          { σ with
              heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
                ⟨some tU64, .int (p.2 : Int) .uint64⟩,
              nextAddr := σ.nextAddr + 1 }) := by
    simp only [bindIterVars, Bind.bind, Except.bind, pure, Except.pure]
    rw [show normalizeValueForTy σ tU64 (.int (p.2 : Int) .uint64)
        = .ok (.int (p.2 : Int) .uint64) from by
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, hv]]
    simp only [Bind.bind, Except.bind, pure, Except.pure,
      ExecState.alloc, ExecState.freshLoc]
  simp only [stepFn, hne, Bool.false_eq_true, if_false]
  split
  · rename_i hnone
    rw [hsz, hconsume] at hnone
    simp only at hnone
    rw [hget] at hnone
    cases hnone
  · rename_i key value hsome
    rw [hsz, hconsume] at hsome
    simp only at hsome
    rw [hget] at hsome
    injection hsome with h1
    injection h1 with hk hv2
    subst hk
    subst hv2
    simp only [Bind.bind, Except.bind, hbind, pure, Except.pure, hsz,
      hconsume, toEntriesW_eraseIdx rem idx hidx']

/-- **The choice-pick loop, string keys** — `MapLoops.
mapPickLoop_generic` re-derived one key type over (the induction never
inspects the entries, only their count). -/
theorem mapPickLoopW {δ : Type}
    (T : δ → ExecState) (cfg : List (List UInt8 × Nat) → Config)
    (exitCfg : Config) (P : δ → List (List UInt8 × Nat) → Prop)
    (c e : Nat)
    (hIter : ∀ (d : δ) (rem : List (List UInt8 × Nat)) (idx : Nat)
      (p : List UInt8 × Nat) (ch ch₂ : Choices),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p → P d rem →
      ∃ (k : Nat) (d' : δ), k ≤ c ∧ P d' (rem.eraseIdx idx) ∧
        stepFnIter k (T d) (cfg rem) ch
          = .ok (cfg (rem.eraseIdx idx), T d', ch₂))
    (hExit : ∀ (d : δ) (ch : Choices), P d [] →
      stepFnIter e (T d) (cfg []) ch = .ok (exitCfg, T d, ch)) :
    ∀ (m : Nat) (rem : List (List UInt8 × Nat)), rem.length = m →
    ∀ (d : δ) (ch : Choices), P d rem →
    ∃ (k : Nat) (d' : δ) (ch' : Choices),
      k ≤ c * m + e ∧ P d' [] ∧
      stepFnIter k (T d) (cfg rem) ch = .ok (exitCfg, T d', ch') := by
  intro m
  induction m with
  | zero =>
      intro rem hm d ch hP
      have hnil : rem = [] := List.eq_nil_of_length_eq_zero hm
      subst hnil
      exact ⟨e, d, ch, by omega, hP, hExit d ch hP⟩
  | succ m ih =>
      intro rem hm d ch hP
      rcases hcons : Choices.consume ch rem.length with ⟨idx, ch₂⟩
      have hidx : idx < rem.length := by
        have := GoLean.MapLoops.consume_lt ch
          (show 0 < rem.length by omega)
        rw [hcons] at this
        exact this
      obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
        ⟨_, List.getElem?_eq_getElem hidx⟩
      obtain ⟨k₁, d₁, hk₁, hP₁, hrun₁⟩ :=
        hIter d rem idx p ch ch₂ hcons hidx hp hP
      obtain ⟨k₂, d₂, ch', hk₂, hP₂, hrun₂⟩ :=
        ih (rem.eraseIdx idx)
          (by rw [GoLean.MapLoops.eraseIdx_length_of_lt hidx]; omega)
          d₁ ch₂ hP₁
      refine ⟨k₁ + k₂, d₂, ch', ?_, hP₂, stepFnIter_chain hrun₁ hrun₂⟩
      have hms : c * (m + 1) = c * m + c := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

/-! ## The count-phase vocabulary

Addresses (probe `w4cfg-*.txt`, `(n, seed, qsel) = (2, 1, 0)`, seam
`na = 54`; everything below is relative to the SEAM base `a`):
`a = $c0` (map handle), `a+1` = the map DATA cell, `a+2 = counts`,
`a+3 = i`, `a+4 = $forFirst`; each counting iteration then allocates
`$c1`/`$c2` at the running allocator. -/

/-- The `map[string]uint64` handle cell over data address `bm`. -/
abbrev mhW (bm : Nat) : HeapCell := ⟨some tMapSU, .map ⟨some (.base ⟨bm⟩)⟩⟩
/-- The map DATA cell holding the encoded counts `kvs` (untyped, as
`makeMap` allocates it). -/
abbrev mdW (kvs : List (List UInt8 × Nat)) : HeapCell :=
  ⟨none, .mapData (toEntriesW kvs)⟩
/-- A `map[string]uint64` variable's default cell. -/
abbrev nilMapW : HeapCell := ⟨some tMapSU, .map ⟨none⟩⟩

/-- s2: `counts := $c0`. -/
abbrev wfS2 : Stmt :=
  .seqn #[.initialization { id := "counts", typ := tMapSU },
          .assign (.var "counts") (.var "$c0")]
/-- s3: the counting loop's block. -/
abbrev wfS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tInt },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) wordFreqFunc.wfWhileBody]]
/-- s4: `best := 0`. -/
abbrev wfBestSeqn : Stmt :=
  .seqn #[.initialization { id := "best", typ := tU64 },
          .assign (.var "best") (.intLit 0 .uint64)]
/-- s5: the `for _, c := range counts` statement. -/
abbrev wfRangeStmt : Stmt :=
  .mapRange none (some "c") (.var "counts") tStr tU64
    wordFreqFunc.wfRangeBody
/-- s6: the subject's result stores and return. -/
abbrev wfResSeqn : Stmt :=
  .seqn #[.assign (.var "$res0")
            (.mapGet (.var "counts") (.var "query") tStr tU64),
          .assign (.var "$res1") (.var "best"), .returnStmt]

/-! ### Environments (the count phase's scopes over `wfFrameScope`) -/

/-- After the `$c0` declaration. -/
def cEnvP0 (a : Nat) : LocalEnv :=
  [[("$c0", .base ⟨a⟩), ("words", .base ⟨21⟩)], wfFrameScope]
/-- The subject-level scope once `counts` is declared. -/
def cScopeC (a : Nat) : Scope :=
  [("counts", .base ⟨a + 2⟩), ("$c0", .base ⟨a⟩), ("words", .base ⟨21⟩)]
def cEnvC (a : Nat) : LocalEnv := [cScopeC a, wfFrameScope]
def cEnvI (a : Nat) : LocalEnv := [("i", .base ⟨a + 3⟩)] :: cEnvC a
def cEnvF (a : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨a + 4⟩)] :: cEnvI a
/-- The loop-body block's pushed scope. -/
def cEnvD (a : Nat) : LocalEnv := [] :: cEnvF a
/-- The count-body block's pushed scope. -/
def cEnvB (a : Nat) : LocalEnv := [] :: cEnvD a
/-- `$c1` declared at the iteration base. -/
def cEnvU1 (a na₀ : Nat) : LocalEnv := [("$c1", .base ⟨na₀⟩)] :: cEnvD a
/-- `$c2` declared over it. -/
def cEnvU (a na₀ : Nat) : LocalEnv :=
  [("$c2", .base ⟨na₀ + 1⟩), ("$c1", .base ⟨na₀⟩)] :: cEnvD a

/-! ### Continuations and the loop-head configuration -/

/-- The subject tail after the counting block (`best`, the range, the
result stores) — the count phase's exit seam. -/
def cKC (a : Nat) : Cont :=
  .seq [wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a) wfFrameK
/-- The i-block's residual. -/
def cKI (a : Nat) : Cont := .seq [] (cEnvI a) (cKC a)
/-- The ff-block's residual. -/
def cKF (a : Nat) : Cont := .seq [] (cEnvF a) (cKI a)
/-- The counting loop's HEAD configuration. -/
def cHeadCfg (a : Nat) : Config :=
  .exec (.while (.boolLit true) wordFreqFunc.wfWhileBody) (cEnvF a)
    (cKF a)
/-- The loop continuation. -/
def cLoopK (a : Nat) : Cont :=
  .loop (.boolLit true) wordFreqFunc.wfWhileBody (cEnvF a) (cKF a)
/-- The body sequence holding the counting block. -/
def cKBody (a : Nat) : Cont :=
  .seq [wordFreqFunc.wfCountBody] (cEnvD a) (cLoopK a)
/-- The exit test's delivery continuation. -/
def cCmpK (a : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (cEnvD a) (cKBody a)
/-- The count-body's governing sequence residual. -/
def cKD (a : Nat) : Cont := .seq [] (cEnvD a) (cLoopK a)

/-! ### The count-phase state family (footprint style)

`a` is the seam base; the five prologue cells sit between the scan
debris `D` and the iteration debris `tail`. -/

/-- The count-phase heap front: the 31 concrete cells, the scan debris
`D`, then the five prologue cells at `a … a+4`. -/
abbrev cnFront (nv sv qv bnv bsv : Int) (l q : List UInt8) (biv : Int)
    (b k cap : Nat) (iv0 sv2 : Int) (D : Heap) (a : Nat)
    (kvs : List (List UInt8 × Nat)) (civ : Int) (ff : Bool) : Heap :=
  wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D
    ++ [(.base ⟨a⟩, mhW (a + 1)), (.base ⟨a + 1⟩, mdW kvs),
        (.base ⟨a + 2⟩, mhW (a + 1)), (.base ⟨a + 3⟩, sint civ),
        (.base ⟨a + 4⟩, sbool ff)]

/-- The count-phase state. -/
abbrev cnSt (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (D : Heap) (a : Nat)
    (kvs : List (List UInt8 × Nat)) (civ : Int) (ff : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  wSt σ (cnFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ ff
    ++ tail) na

/-! ### Heap facts at the count front -/

/-- No front address reaches 31. -/
theorem lookup_wHeapCount_none (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b k cap : Nat) (iv sv2 : Int)
    {x : Nat} (hx : 31 ≤ x) :
    Heap.lookup (wHeapCount nv sv qv bnv bsv l q biv b k cap iv sv2)
      (.base ⟨x⟩) = none := by
  simp only [wHeapCount, wHeapWF, wHeapCall,
    List.append_assoc, List.cons_append, List.nil_append, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    base_beq_false (by omega : (9 : Nat) ≠ x),
    base_beq_false (by omega : (10 : Nat) ≠ x),
    base_beq_false (by omega : (11 : Nat) ≠ x),
    base_beq_false (by omega : (12 : Nat) ≠ x),
    base_beq_false (by omega : (13 : Nat) ≠ x),
    base_beq_false (by omega : (14 : Nat) ≠ x),
    base_beq_false (by omega : (15 : Nat) ≠ x),
    base_beq_false (by omega : (16 : Nat) ≠ x),
    base_beq_false (by omega : (17 : Nat) ≠ x),
    base_beq_false (by omega : (18 : Nat) ≠ x),
    base_beq_false (by omega : (19 : Nat) ≠ x),
    base_beq_false (by omega : (20 : Nat) ≠ x),
    base_beq_false (by omega : (21 : Nat) ≠ x),
    base_beq_false (by omega : (22 : Nat) ≠ x),
    base_beq_false (by omega : (23 : Nat) ≠ x),
    base_beq_false (by omega : (24 : Nat) ≠ x),
    base_beq_false (by omega : (25 : Nat) ≠ x),
    base_beq_false (by omega : (26 : Nat) ≠ x),
    base_beq_false (by omega : (27 : Nat) ≠ x),
    base_beq_false (by omega : (28 : Nat) ≠ x),
    base_beq_false (by omega : (29 : Nat) ≠ x),
    base_beq_false (by omega : (30 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- Lookup within the five-cell prologue suffix (position `j < 5`),
with an arbitrary further suffix `tail`. -/
theorem lookup_five {D : Heap} {a : Nat} (hD : DeadFrom D a)
    {c0 c1 c2 c3 c4 : HeapCell} {tail : Heap} {j : Nat} (hj : j < 5) :
    Heap.lookup (D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1),
        (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3), (.base ⟨a + 4⟩, c4)]
        ++ tail)
      (.base ⟨a + j⟩)
      = some ([c0, c1, c2, c3, c4].getD j c0) := by
  rw [List.append_assoc,
    lookup_append_right (hD (a + j) (by omega))]
  rcases j with _ | _ | _ | _ | _ | j
  · simp [Heap.lookup]
  all_goals first
  | omega
  | (simp [Heap.lookup, List.cons_append,
      base_beq_false (by omega : a ≠ a + 1),
      base_beq_false (by omega : a ≠ a + 2),
      base_beq_false (by omega : a ≠ a + 3),
      base_beq_false (by omega : a ≠ a + 4),
      base_beq_false (by omega : a + 1 ≠ a + 2),
      base_beq_false (by omega : a + 1 ≠ a + 3),
      base_beq_false (by omega : a + 1 ≠ a + 4),
      base_beq_false (by omega : a + 2 ≠ a + 3),
      base_beq_false (by omega : a + 2 ≠ a + 4),
      base_beq_false (by omega : a + 3 ≠ a + 4)])
  | omega

/-- Set within the five-cell prologue suffix at position 1 (the map
DATA cell), with an arbitrary further suffix. -/
theorem set_five1 {D : Heap} {a : Nat} (hD : DeadFrom D a)
    {c0 c1 c1' c2 c3 c4 : HeapCell} {tail : Heap} :
    Heap.set (D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1),
        (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3), (.base ⟨a + 4⟩, c4)]
        ++ tail)
      (.base ⟨a + 1⟩) c1'
      = D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1'),
          (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3), (.base ⟨a + 4⟩, c4)]
        ++ tail := by
  rw [List.append_assoc, set_append_right (hD (a + 1) (by omega)),
    List.append_assoc]
  congr 1
  simp [Heap.set, List.cons_append,
    base_beq_false (by omega : a ≠ a + 1)]

/-- Set within the five-cell prologue suffix at position 3 (the `i`
cell), with an arbitrary further suffix. -/
theorem set_five3 {D : Heap} {a : Nat} (hD : DeadFrom D a)
    {c0 c1 c2 c3 c3' c4 : HeapCell} {tail : Heap} :
    Heap.set (D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1),
        (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3), (.base ⟨a + 4⟩, c4)]
        ++ tail)
      (.base ⟨a + 3⟩) c3'
      = D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1),
          (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3'), (.base ⟨a + 4⟩, c4)]
        ++ tail := by
  rw [List.append_assoc, set_append_right (hD (a + 3) (by omega)),
    List.append_assoc]
  congr 1
  simp [Heap.set, List.cons_append,
    base_beq_false (by omega : a ≠ a + 3),
    base_beq_false (by omega : a + 1 ≠ a + 3),
    base_beq_false (by omega : a + 2 ≠ a + 3)]

/-- Set within the five-cell prologue suffix at position 4 (the
`$forFirst` cell), with an arbitrary further suffix. -/
theorem set_five4 {D : Heap} {a : Nat} (hD : DeadFrom D a)
    {c0 c1 c2 c3 c4 c4' : HeapCell} {tail : Heap} :
    Heap.set (D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1),
        (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3), (.base ⟨a + 4⟩, c4)]
        ++ tail)
      (.base ⟨a + 4⟩) c4'
      = D ++ [(.base ⟨a⟩, c0), (.base ⟨a + 1⟩, c1),
          (.base ⟨a + 2⟩, c2), (.base ⟨a + 3⟩, c3), (.base ⟨a + 4⟩, c4')]
        ++ tail := by
  rw [List.append_assoc, set_append_right (hD (a + 4) (by omega)),
    List.append_assoc]
  congr 1
  simp [Heap.set, List.cons_append,
    base_beq_false (by omega : a ≠ a + 4),
    base_beq_false (by omega : a + 1 ≠ a + 4),
    base_beq_false (by omega : a + 2 ≠ a + 4),
    base_beq_false (by omega : a + 3 ≠ a + 4)]

/-- No count-front address reaches `a + 5` (the loop's freshness
seed). -/
theorem lookup_cnFront_none (nv sv qv bnv bsv : Int) (l q : List UInt8)
    (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) {D : Heap} {a : Nat}
    (kvs : List (List UInt8 × Nat)) (civ : Int) (ff : Bool)
    (ha : 31 ≤ a) (hD : DeadFrom D a) {x : Nat} (hx : a + 5 ≤ x) :
    Heap.lookup
        (cnFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ ff)
      (.base ⟨x⟩) = none := by
  unfold cnFront
  rw [List.append_assoc,
    lookup_append_right
      (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
        (by omega)),
    lookup_append_right (hD x (by omega)),
    lookup_cons_ne (base_beq_false (by omega : a ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : a + 2 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : a + 3 ≠ x)),
    lookup_cons_ne (base_beq_false (by omega : a + 4 ≠ x))]
  rfl

/-! ### Defaults and the words-backing read -/

theorem defaultValue_tMapSU (σ : ExecState) :
    defaultValue σ tMapSU = .ok (.map ⟨none⟩) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

theorem defaultValue_tStr (σ : ExecState) :
    defaultValue σ tStr = .ok (.string GoString.empty) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

theorem normalize_mapHandle (σ : ExecState) (v : MapValue) :
    normalizeValueForTy σ tMapSU (.map v) = .ok (.map v) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]

theorem normalize_str (σ : ExecState) (s : GoString) :
    normalizeValueForTy σ tStr (.string s) = .ok (.string s) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]

/-- The `[]string` backing's element at an in-range index. -/
theorem strArr_getElem? (fs : List (List UInt8)) (cap i : Nat)
    (hi : i < fs.length) :
    ((fs.map (fun f => GoValue.string (gs f)))
        ++ List.replicate (cap - fs.length)
          (GoValue.string GoString.empty))[i]?
      = some (.string (gs (fs.getD i []))) := by
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `words[i]` at the count state: the backing at `b` (inside the scan
debris) answers word `i`. -/
theorem cn_words_read (σ : ExecState) (nv sv qv bnv bsv : Int)
    (l q : List UInt8) (biv : Int) (b cap : Nat)
    (fs : List (List UInt8)) (iv0 sv2 : Int) (D : Heap) (a : Nat)
    (kvs : List (List UInt8 × Nat)) (civ : Int) (ff : Bool)
    (tail : Heap) (na : Nat) (i : Nat) {ik : IntKind}
    (hb31 : 31 ≤ b)
    (hDb : Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
    (hcap : fs.length ≤ cap) (hi : i < fs.length) :
    applyStrictOp
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
          civ ff tail na)
        .indexGet
        [slsVal b 0 fs.length cap, .int (i : Nat) ik]
      = .ok (.string (gs (fs.getD i [])),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
            civ ff tail na) := by
  have hlook : Heap.lookup
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ ff tail na).heap
      (.base ⟨b⟩) = some (strArrCell fs cap) := by
    show Heap.lookup
      (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ ff ++ tail) (.base ⟨b⟩) = _
    unfold cnFront
    rw [List.append_assoc, List.append_assoc,
      lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b fs.length cap
          iv0 sv2 hb31),
      lookup_append_left hDb]
  exact applyStrictOp_indexGet_slice (dty := some (.array cap tStr))
    (off := 0) (len := fs.length) (cap := cap) (ik := ik) hlook hcap hi
    (by
      show ((fs.map (fun f => GoValue.string (gs f)))
        ++ List.replicate (cap - fs.length)
          (GoValue.string GoString.empty)).toArray[0 + i]? = _
      rw [Nat.zero_add, List.getElem?_toArray]
      exact strArr_getElem? fs cap i hi)

/-- `make(map[string]uint64)` at a freshly-declared nil-map target: the
empty data cell at the allocator, the handle stored over the target. -/
theorem applyStmtOp_makeMapW {σ : ExecState} {t : Nat} {ch : Choices}
    (hlook : Heap.lookup σ.heap (.base ⟨t⟩) = some nilMapW)
    (ht : t ≠ σ.nextAddr) :
    applyStmtOp σ ch (.makeMap false) 1 [.addr (.base ⟨t⟩)]
      = .ok ({ σ with
          heap := Heap.set
            (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨none, .mapData #[]⟩)
            (.base ⟨t⟩) (mhW σ.nextAddr),
          nextAddr := σ.nextAddr + 1 }, ch) := by
  have hlook2 : Heap.lookup
      (Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨none, .mapData #[]⟩)
      (.base ⟨t⟩) = some nilMapW := by
    rw [Machine.Heap.lookup_set_ne
      (by simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]; omega
        : (Loc.base ⟨σ.nextAddr⟩ : Loc) ≠ .base ⟨t⟩)]
    exact hlook
  simp only [applyStmtOp, applyStmtOpCore, Bind.bind, Except.bind, pure,
    Except.pure, ExecState.alloc, ExecState.freshLoc, valueAsLoc]
  simp only [storeLoc, hlook2, Bind.bind, Except.bind, pure, Except.pure]
  rw [show normalizeValueForTy
      { σ with
        heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
          (⟨none, .mapData #[]⟩ : HeapCell),
        nextAddr := σ.nextAddr + 1 } tMapSU
      (.map { base := some (.base ⟨σ.nextAddr⟩) })
      = .ok (.map { base := some (.base ⟨σ.nextAddr⟩) }) from
    normalize_mapHandle _ _]

/-- `IntKind.normalize` fixed points used by the prologue. -/
theorem normalize_int0 (σ : ExecState) :
    normalizeValueForTy σ tInt (.int 0 .int) = .ok (.int 0 .int) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]
  rfl

theorem defaultValue_tInt (σ : ExecState) :
    defaultValue σ tInt = .ok (.int 0 .int) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

theorem defaultValue_bool (σ : ExecState) :
    defaultValue σ .bool = .ok (.bool false) := by
  simp [defaultValue, defaultValueFuel, typeResolutionFuel]

/-! ## The count prologue (seam → loop head), 51 steps in three
composites -/

section Prologue

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (D : Heap) (a : Nat)
  (ch : Choices)

/-- The assignment `counts = $c0` (statement form). -/
abbrev wfAsgnCounts : Stmt := .assign (.var "counts") (.var "$c0")
/-- The makeMap statement. -/
abbrev wfMkMap : Stmt := .makeMap (.var "$c0") tStr tU64 none
/-- `i := 0` (statement form). -/
abbrev wfAsgnI0 : Stmt := .assign (.var "i") (.intLit 0 .int)
/-- The inner ff/while block. -/
abbrev wfBlockFF : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) wordFreqFunc.wfWhileBody]

/-- Prologue composite 1 (13 steps): seam → `$c0` allocated, the map
made, `counts` declared. -/
theorem cn_pro1 (ha : 31 ≤ a) (hD : DeadFrom D a) :
    stepFnIter 13
      (wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        a)
      (.exec (.seqn #[]) wfEnvW wfAfterShim) ch
      = .ok (.next (.seq [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt,
              wfResSeqn] (cEnvC a) wfFrameK),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
              ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, nilMapW)]) (a + 3), ch) := by
  have hWD : ∀ x : Nat, a ≤ x →
      Heap.lookup
        (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        (.base ⟨x⟩) = none := by
    intro x hx
    rw [lookup_append_right
      (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
        (by omega))]
    exact hD x hx
  -- L1 (4 steps, rfl): seam → the `$c0` initialization
  have h1 : stepFnIter 4
      (wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        a)
      (.exec (.seqn #[]) wfEnvW wfAfterShim) ch
      = .ok (.exec (.initialization { id := "$c0", typ := tMapSU })
            wfEnvW
            (.seq [wfMkMap, wfS2, wfS3, wfBestSeqn, wfRangeStmt,
              wfResSeqn] wfEnvW wfFrameK),
          wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D) a, ch) := by
    with_unfolding_all rfl
  -- L2 (1 step): `$c0` allocated at `a`
  have h2 : stepFnIter 1
      (wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        a)
      (.exec (.initialization { id := "$c0", typ := tMapSU }) wfEnvW
        (.seq [wfMkMap, wfS2, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
          wfEnvW wfFrameK)) ch
      = .ok (.next (.seq [wfMkMap, wfS2, wfS3, wfBestSeqn, wfRangeStmt,
              wfResSeqn] (cEnvP0 a) wfFrameK),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
              ++ D) ++ [(.base ⟨a⟩, nilMapW)]) (a + 1), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D) a)
      (p := { id := "$c0", typ := tMapSU })
      (rest := [wfMkMap, wfS2, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn])
      (env := wfEnvW) (k := wfFrameK) (ch := ch)
      (v := .map ⟨none⟩) (defaultValue_tMapSU _)
    rw [show Heap.set
        (wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
          ++ D) a).heap (.base ⟨a⟩) ⟨some tMapSU, .map ⟨none⟩⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, nilMapW)] from
      set_fresh (hWD a (Nat.le_refl a))] at h
    exact h
  -- L3 (3 steps, rfl): pop, exec makeMap, target ref delivered
  have h3 : stepFnIter 3
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, nilMapW)]) (a + 1))
      (.next (.seq [wfMkMap, wfS2, wfS3, wfBestSeqn, wfRangeStmt,
        wfResSeqn] (cEnvP0 a) wfFrameK)) ch
      = .ok (.retV (.addr (.base ⟨a⟩))
            (.stmtOpK (.makeMap false) 1 [] [] (cEnvP0 a)
              (.seq [wfS2, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
                (cEnvP0 a) wfFrameK)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D) ++ [(.base ⟨a⟩, nilMapW)]) (a + 1), ch) := by
    with_unfolding_all rfl
  -- L4 (1 step): the makeMap apply
  have h4 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, nilMapW)]) (a + 1))
      (.retV (.addr (.base ⟨a⟩))
        (.stmtOpK (.makeMap false) 1 [] [] (cEnvP0 a)
          (.seq [wfS2, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
            (cEnvP0 a) wfFrameK))) ch
      = .ok (.next (.seq [wfS2, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
            (cEnvP0 a) wfFrameK),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
              ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2), ch) := by
    refine stepFnIter_one (stepFn_stmtOp_apply ?_)
    have h := applyStmtOp_makeMapW
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D) ++ [(.base ⟨a⟩, nilMapW)]) (a + 1))
      (t := a) (ch := ch)
      (by
        show Heap.lookup
          ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
            ++ [(.base ⟨a⟩, nilMapW)]) (.base ⟨a⟩) = some nilMapW
        rw [lookup_append_right (hWD a (Nat.le_refl a))]
        exact lookup_singleton_self)
      (by show a ≠ a + 1; omega)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, nilMapW)]) (.base ⟨a + 1⟩)
        ⟨none, .mapData #[]⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, nilMapW),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)] from by
      rw [set_fresh (by
        rw [lookup_append_right (hWD (a + 1) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 1))]
        rfl)]
      simp [List.append_assoc]] at h
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, nilMapW),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (.base ⟨a⟩)
        (mhW (a + 1))
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)] from by
      rw [set_append_right (hWD a (Nat.le_refl a))]
      simp [Heap.set]] at h
    exact h
  -- L5 (3 steps, rfl): pop `wfS2`, splice, pop the `counts` init
  have h5 : stepFnIter 3
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2))
      (.next (.seq [wfS2, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
        (cEnvP0 a) wfFrameK)) ch
      = .ok (.exec (.initialization { id := "counts", typ := tMapSU })
            (cEnvP0 a)
            (.seq [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
              (cEnvP0 a) wfFrameK),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2), ch) := by
    have ha1 := stepFnIter_one (stepFn_seq_pop
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2))
      (t := wfS2)
      (rest := [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn])
      (env := cEnvP0 a) (k := wfFrameK) (ch := ch))
    have ha2 := stepFnIter_one (stepFn_seqn_splice
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2))
      (ss := #[.initialization { id := "counts", typ := tMapSU },
        wfAsgnCounts])
      (env := cEnvP0 a)
      (rest := [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn])
      (k := wfFrameK) (ch := ch))
    have ha3 := stepFnIter_one (stepFn_seq_pop
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2))
      (t := .initialization { id := "counts", typ := tMapSU })
      (rest := [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn])
      (env := cEnvP0 a) (k := wfFrameK) (ch := ch))
    exact stepFnIter_chain (stepFnIter_chain ha1 ha2) ha3
  -- L6 (1 step): `counts` allocated at `a + 2`
  have h6 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2))
      (.exec (.initialization { id := "counts", typ := tMapSU })
        (cEnvP0 a)
        (.seq [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]
          (cEnvP0 a) wfFrameK)) ch
      = .ok (.next (.seq [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt,
              wfResSeqn] (cEnvC a) wfFrameK),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
              ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, nilMapW)]) (a + 3), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (a + 2))
      (p := { id := "counts", typ := tMapSU })
      (rest := [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn])
      (env := cEnvP0 a) (k := wfFrameK) (ch := ch)
      (v := .map ⟨none⟩) (defaultValue_tMapSU _)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩)]) (.base ⟨a + 2⟩)
        ⟨some tMapSU, .map ⟨none⟩⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, nilMapW)] from by
      rw [set_fresh (by
        rw [lookup_append_right (hWD (a + 2) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 2)),
          lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ a + 2))]
        rfl)]
      simp [List.append_assoc]] at h
    exact h
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6

/-- Bool values normalize to themselves. -/
theorem normalize_bool (σ : ExecState) (v : Bool) :
    normalizeValueForTy σ .bool (.bool v) = .ok (.bool v) := by
  simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel]

/-- Prologue composite 2 (22 steps): `counts = $c0`, the loop block
entered, `i` allocated and zeroed. -/
theorem cn_pro2 (ha : 31 ≤ a) (hD : DeadFrom D a) :
    stepFnIter 22
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (a + 3))
      (.next (.seq [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt,
        wfResSeqn] (cEnvC a) wfFrameK)) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvI a)
            (.seq [wfBlockFF] (cEnvI a) (cKC a))),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
              ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0)]) (a + 4), ch) := by
  have hWD : ∀ x : Nat, a ≤ x →
      Heap.lookup
        (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        (.base ⟨x⟩) = none := by
    intro x hx
    rw [lookup_append_right
      (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
        (by omega))]
    exact hD x hx
  -- p7 (4 steps, rfl): pop the assignment, target banked, `$c0` read
  -- point
  have h1 : stepFnIter 4
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (a + 3))
      (.next (.seq [wfAsgnCounts, wfS3, wfBestSeqn, wfRangeStmt,
        wfResSeqn] (cEnvC a) wfFrameK)) ch
      = .ok (.evalE (.var "$c0") (cEnvC a)
            (.rhsK .vals [.chain (.addr (.base ⟨a + 2⟩)) [] []] [] []
              (.seqn #[]) (cEnvC a)
              (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
                wfFrameK)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, nilMapW)]) (a + 3), ch) := by
    with_unfolding_all rfl
  -- p8 (1 step): the `$c0` read
  have h2 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (a + 3))
      (.evalE (.var "$c0") (cEnvC a)
        (.rhsK .vals [.chain (.addr (.base ⟨a + 2⟩)) [] []] [] []
          (.seqn #[]) (cEnvC a)
          (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
            wfFrameK))) ch
      = .ok (.retV (.map ⟨some (.base ⟨a + 1⟩)⟩)
            (.rhsK .vals [.chain (.addr (.base ⟨a + 2⟩)) [] []] [] []
              (.seqn #[]) (cEnvC a)
              (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
                wfFrameK)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, nilMapW)]) (a + 3), ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a⟩) (c := mhW (a + 1))
      rfl ?_)
    show Heap.lookup
      ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (.base ⟨a⟩) = some (mhW (a + 1))
    rw [lookup_append_right (hWD a (Nat.le_refl a))]
    simp [Heap.lookup]
  -- p9 (1 step, rfl): the value banks at the store queue
  have h3 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (a + 3))
      (.retV (.map ⟨some (.base ⟨a + 1⟩)⟩)
        (.rhsK .vals [.chain (.addr (.base ⟨a + 2⟩)) [] []] [] []
          (.seqn #[]) (cEnvC a)
          (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
            wfFrameK))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 2⟩)) [] []]
            [.map ⟨some (.base ⟨a + 1⟩)⟩] (.seqn #[]) (cEnvC a)
            (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
              wfFrameK)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, nilMapW)]) (a + 3), ch) := by
    with_unfolding_all rfl
  -- p10 (1 step): the `counts` store
  have h4 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (a + 3))
      (.next (.storeK [.chain (.addr (.base ⟨a + 2⟩)) [] []]
        [.map ⟨some (.base ⟨a + 1⟩)⟩] (.seqn #[]) (cEnvC a)
        (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
          wfFrameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvC a)
            (.seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
              wfFrameK)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, nilMapW)]) (a + 3))
      (a := ⟨a + 2⟩) (ty := tMapSU) (old := .map ⟨none⟩)
      (v := .map ⟨some (.base ⟨a + 1⟩)⟩)
      (v' := .map ⟨some (.base ⟨a + 1⟩)⟩)
      (by
        show Heap.lookup
          ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, nilMapW)]) (.base ⟨a + 2⟩)
          = some ⟨some tMapSU, .map ⟨none⟩⟩
        rw [lookup_append_right (hWD (a + 2) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 2)),
          lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ a + 2))]
        exact lookup_singleton_self)
      (normalize_mapHandle _ _)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, nilMapW)]) (.base ⟨a + 2⟩)
        ⟨some tMapSU, .map ⟨some (.base ⟨a + 1⟩)⟩⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1))] from by
      rw [set_append_right (hWD (a + 2) (by omega))]
      simp [Heap.set, base_beq_false (by omega : a ≠ a + 2),
        base_beq_false (by omega : a + 1 ≠ a + 2)]] at h
    exact h
  -- p11 (7 steps): drain, the counting block entered, the `i` decl
  have h5a := stepFnIter_one (stepFn_storeK_nil
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
    (body := .seqn #[]) (env := cEnvC a)
    (k := .seq [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn] (cEnvC a)
      wfFrameK) (ch := ch))
  have h5b := stepFnIter_one (stepFn_seqn_splice
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
    (ss := #[]) (env := cEnvC a)
    (rest := [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn])
    (k := wfFrameK) (ch := ch))
  have h5c : stepFnIter 3
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [wfS3, wfBestSeqn, wfRangeStmt, wfResSeqn]) (cEnvC a)
        wfFrameK)) ch
      = .ok (.exec (.seqn #[.initialization { id := "i", typ := tInt },
              wfAsgnI0]) ([] :: cEnvC a)
            (.seq [wfBlockFF] ([] :: cEnvC a) (cKC a)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3), ch) := by
    with_unfolding_all rfl
  have h5d := stepFnIter_one (stepFn_seqn_splice
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
    (ss := #[.initialization { id := "i", typ := tInt }, wfAsgnI0])
    (env := [] :: cEnvC a) (rest := [wfBlockFF]) (k := cKC a) (ch := ch))
  have h5e := stepFnIter_one (stepFn_seq_pop
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
    (t := .initialization { id := "i", typ := tInt })
    (rest := [wfAsgnI0, wfBlockFF]) (env := [] :: cEnvC a) (k := cKC a)
    (ch := ch))
  -- p12 (1 step): `i` allocated at `a + 3`
  have h6 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
      (.exec (.initialization { id := "i", typ := tInt })
        ([] :: cEnvC a)
        (.seq [wfAsgnI0, wfBlockFF] ([] :: cEnvC a) (cKC a))) ch
      = .ok (.next (.seq [wfAsgnI0, wfBlockFF] (cEnvI a) (cKC a)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0)]) (a + 4), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1))]) (a + 3))
      (p := { id := "i", typ := tInt })
      (rest := [wfAsgnI0, wfBlockFF]) (env := [] :: cEnvC a)
      (k := cKC a) (ch := ch) (v := .int 0 .int) (defaultValue_tInt _)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1))]) (.base ⟨a + 3⟩)
        ⟨some tInt, .int 0 .int⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0)] from by
      rw [set_fresh (by
        rw [lookup_append_right (hWD (a + 3) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 3)),
          lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ a + 3)),
          lookup_cons_ne (base_beq_false (by omega : a + 2 ≠ a + 3))]
        rfl)]
      simp [List.append_assoc]] at h
    exact h
  -- p13 (6 steps, rfl): `i = 0` up to the banked store
  have h7 : stepFnIter 6
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (.next (.seq [wfAsgnI0, wfBlockFF] (cEnvI a) (cKC a))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 3⟩)) [] []]
            [.int 0 .int] (.seqn #[]) (cEnvI a)
            (.seq [wfBlockFF] (cEnvI a) (cKC a))),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0)]) (a + 4), ch) := by
    with_unfolding_all rfl
  -- p14 (1 step): the `i = 0` store
  have h8 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (.next (.storeK [.chain (.addr (.base ⟨a + 3⟩)) [] []]
        [.int 0 .int] (.seqn #[]) (cEnvI a)
        (.seq [wfBlockFF] (cEnvI a) (cKC a)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvI a)
            (.seq [wfBlockFF] (cEnvI a) (cKC a))),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0)]) (a + 4), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (a := ⟨a + 3⟩) (ty := tInt) (old := .int 0 .int)
      (v := .int 0 .int) (v' := .int 0 .int)
      (by
        show Heap.lookup
          ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0)]) (.base ⟨a + 3⟩)
          = some ⟨some tInt, .int 0 .int⟩
        rw [lookup_append_right (hWD (a + 3) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 3)),
          lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ a + 3)),
          lookup_cons_ne (base_beq_false (by omega : a + 2 ≠ a + 3))]
        exact lookup_singleton_self)
      (normalize_int0 _)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0)]) (.base ⟨a + 3⟩)
        ⟨some tInt, .int 0 .int⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0)] from by
      rw [set_append_right (hWD (a + 3) (by omega))]
      simp [Heap.set, base_beq_false (by omega : a ≠ a + 3),
        base_beq_false (by omega : a + 1 ≠ a + 3),
        base_beq_false (by omega : a + 2 ≠ a + 3)]] at h
    exact h
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5a) h5b)
          h5c) h5d) h5e) h6) h7) h8

/-- Prologue composite 3 (16 steps): the ff/while block entered,
`$forFirst` allocated and set, the loop HEAD reached — the machine
parks at `cHeadCfg` over the count state at the EMPTY counts map. -/
theorem cn_pro3 (ha : 31 ≤ a) (hD : DeadFrom D a) :
    stepFnIter 16
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (.next (.storeK [] [] (.seqn #[]) (cEnvI a)
        (.seq [wfBlockFF] (cEnvI a) (cKC a)))) ch
      = .ok (cHeadCfg a,
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a [] 0 true
            [] (a + 5), ch) := by
  have hWD : ∀ x : Nat, a ≤ x →
      Heap.lookup
        (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        (.base ⟨x⟩) = none := by
    intro x hx
    rw [lookup_append_right
      (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
        (by omega))]
    exact hD x hx
  -- p15 (5 steps): drain, splice, the ff/while block entered, the
  -- `$forFirst` decl reached
  have h1a := stepFnIter_one (stepFn_storeK_nil
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1)),
          (.base ⟨a + 3⟩, sint 0)]) (a + 4))
    (body := .seqn #[]) (env := cEnvI a)
    (k := .seq [wfBlockFF] (cEnvI a) (cKC a)) (ch := ch))
  have h1b := stepFnIter_one (stepFn_seqn_splice
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1)),
          (.base ⟨a + 3⟩, sint 0)]) (a + 4))
    (ss := #[]) (env := cEnvI a) (rest := [wfBlockFF]) (k := cKC a)
    (ch := ch))
  have h1c : stepFnIter 3
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (.next (.seq ((#[] : Array Stmt).toList ++ [wfBlockFF]) (cEnvI a)
        (cKC a))) ch
      = .ok (.exec (.initialization { id := "$forFirst", typ := .bool })
            ([] :: cEnvI a)
            (.seq [.assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) wordFreqFunc.wfWhileBody]
              ([] :: cEnvI a) (cKI a)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0)]) (a + 4), ch) := by
    with_unfolding_all rfl
  -- p16 (1 step): `$forFirst` allocated at `a + 4`
  have h2 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (.exec (.initialization { id := "$forFirst", typ := .bool })
        ([] :: cEnvI a)
        (.seq [.assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) wordFreqFunc.wfWhileBody]
          ([] :: cEnvI a) (cKI a))) ch
      = .ok (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) wordFreqFunc.wfWhileBody]
              (cEnvF a) (cKI a)),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0),
                (.base ⟨a + 4⟩, sbool false)]) (a + 5), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0)]) (a + 4))
      (p := { id := "$forFirst", typ := .bool })
      (rest := [.assign (.var "$forFirst") (.boolLit true),
        .while (.boolLit true) wordFreqFunc.wfWhileBody])
      (env := [] :: cEnvI a) (k := cKI a) (ch := ch)
      (v := .bool false) (defaultValue_bool _)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0)]) (.base ⟨a + 4⟩)
        ⟨some .bool, .bool false⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0),
              (.base ⟨a + 4⟩, sbool false)] from by
      rw [set_fresh (by
        rw [lookup_append_right (hWD (a + 4) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 4)),
          lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ a + 4)),
          lookup_cons_ne (base_beq_false (by omega : a + 2 ≠ a + 4)),
          lookup_cons_ne (base_beq_false (by omega : a + 3 ≠ a + 4))]
        rfl)]
      simp [List.append_assoc]] at h
    exact h
  -- p17 (6 steps, rfl): `$forFirst = true` to the banked store
  have h3 : stepFnIter 6
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0),
            (.base ⟨a + 4⟩, sbool false)]) (a + 5))
      (.next (.seq [.assign (.var "$forFirst") (.boolLit true),
        .while (.boolLit true) wordFreqFunc.wfWhileBody]
        (cEnvF a) (cKI a))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 4⟩)) [] []]
            [.bool true] (.seqn #[]) (cEnvF a)
            (.seq [.while (.boolLit true) wordFreqFunc.wfWhileBody]
              (cEnvF a) (cKI a))),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0),
                (.base ⟨a + 4⟩, sbool false)]) (a + 5), ch) := by
    with_unfolding_all rfl
  -- p18 (1 step): the `$forFirst = true` store
  have h4 : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0),
            (.base ⟨a + 4⟩, sbool false)]) (a + 5))
      (.next (.storeK [.chain (.addr (.base ⟨a + 4⟩)) [] []]
        [.bool true] (.seqn #[]) (cEnvF a)
        (.seq [.while (.boolLit true) wordFreqFunc.wfWhileBody]
          (cEnvF a) (cKI a)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvF a)
            (.seq [.while (.boolLit true) wordFreqFunc.wfWhileBody]
              (cEnvF a) (cKI a))),
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0),
                (.base ⟨a + 4⟩, sbool true)]) (a + 5), ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
        ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0),
            (.base ⟨a + 4⟩, sbool false)]) (a + 5))
      (a := ⟨a + 4⟩) (ty := .bool) (old := .bool false)
      (v := .bool true) (v' := .bool true)
      (by
        show Heap.lookup
          ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0),
                (.base ⟨a + 4⟩, sbool false)]) (.base ⟨a + 4⟩)
          = some ⟨some .bool, .bool false⟩
        rw [lookup_append_right (hWD (a + 4) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : a ≠ a + 4)),
          lookup_cons_ne (base_beq_false (by omega : a + 1 ≠ a + 4)),
          lookup_cons_ne (base_beq_false (by omega : a + 2 ≠ a + 4)),
          lookup_cons_ne (base_beq_false (by omega : a + 3 ≠ a + 4))]
        exact lookup_singleton_self)
      (normalize_bool _ _)
    rw [show Heap.set
        ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0),
              (.base ⟨a + 4⟩, sbool false)]) (.base ⟨a + 4⟩)
        ⟨some .bool, .bool true⟩
        = (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
          ++ [(.base ⟨a⟩, mhW (a + 1)),
              (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
              (.base ⟨a + 2⟩, mhW (a + 1)),
              (.base ⟨a + 3⟩, sint 0),
              (.base ⟨a + 4⟩, sbool true)] from by
      rw [set_append_right (hWD (a + 4) (by omega))]
      simp [Heap.set, base_beq_false (by omega : a ≠ a + 4),
        base_beq_false (by omega : a + 1 ≠ a + 4),
        base_beq_false (by omega : a + 2 ≠ a + 4),
        base_beq_false (by omega : a + 3 ≠ a + 4)]] at h
    exact h
  -- p19 (3 steps): drain, splice, the while popped — the loop head
  have h5a := stepFnIter_one (stepFn_storeK_nil
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1)),
          (.base ⟨a + 3⟩, sint 0),
          (.base ⟨a + 4⟩, sbool true)]) (a + 5))
    (body := .seqn #[]) (env := cEnvF a)
    (k := .seq [.while (.boolLit true) wordFreqFunc.wfWhileBody]
      (cEnvF a) (cKI a)) (ch := ch))
  have h5b := stepFnIter_one (stepFn_seqn_splice
    (σ := wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
      ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
          (.base ⟨a + 2⟩, mhW (a + 1)),
          (.base ⟨a + 3⟩, sint 0),
          (.base ⟨a + 4⟩, sbool true)]) (a + 5))
    (ss := #[]) (env := cEnvF a)
    (rest := [.while (.boolLit true) wordFreqFunc.wfWhileBody])
    (k := cKI a) (ch := ch))
  have h5c : stepFnIter 1
      (wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        ++ [(.base ⟨a⟩, mhW (a + 1)),
            (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
            (.base ⟨a + 2⟩, mhW (a + 1)),
            (.base ⟨a + 3⟩, sint 0),
            (.base ⟨a + 4⟩, sbool true)]) (a + 5))
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [.while (.boolLit true) wordFreqFunc.wfWhileBody]) (cEnvF a)
        (cKI a))) ch
      = .ok (cHeadCfg a,
          wSt σ ((wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2
            ++ D)
            ++ [(.base ⟨a⟩, mhW (a + 1)),
                (.base ⟨a + 1⟩, ⟨none, .mapData #[]⟩),
                (.base ⟨a + 2⟩, mhW (a + 1)),
                (.base ⟨a + 3⟩, sint 0),
                (.base ⟨a + 4⟩, sbool true)]) (a + 5), ch) := by
    with_unfolding_all rfl
  have hchain := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain h1a h1b) h1c) h2) h3) h4) h5a)
      (stepFnIter_chain h5b h5c)
  rw [show (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
      ++ [(.base ⟨a⟩, mhW (a + 1)),
          (.base ⟨a + 1⟩, (⟨none, .mapData #[]⟩ : HeapCell)),
          (.base ⟨a + 2⟩, mhW (a + 1)),
          (.base ⟨a + 3⟩, sint 0),
          (.base ⟨a + 4⟩, sbool true)]
      = cnFront nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a [] 0 true
        ++ ([] : Heap) from by
    rw [List.append_nil]
    rfl] at hchain
  exact hchain

/-- **The count prologue** (51 steps): from the shim-return seam to the
counting loop's head, the counts map made EMPTY, `i = 0`,
`$forFirst = true`. -/
theorem cn_prologue (ha : 31 ≤ a) (hD : DeadFrom D a) :
    stepFnIter 51
      (wSt σ (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D)
        a)
      (.exec (.seqn #[]) wfEnvW wfAfterShim) ch
      = .ok (cHeadCfg a,
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a [] 0 true
            [] (a + 5), ch) :=
  stepFnIter_chain (stepFnIter_chain
    (cn_pro1 σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a ch ha hD)
    (cn_pro2 σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a ch ha hD))
    (cn_pro3 σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a ch ha hD)

end Prologue

/-! ## The loop dispatch (head → exit-test delivery) -/

/-- `$forFirst = false` (the first-pass arm's store). -/
abbrev wfAsgnFFf : Stmt := .assign (.var "$forFirst") (.boolLit false)
/-- `i = i + 1` (the back-edge arm). -/
abbrev wfAsgnIinc : Stmt :=
  .assign (.var "i") (.add (.var "i") (.intLit 1 .int))
/-- The exit test. -/
abbrev wfIfTest : Stmt :=
  .ifThenElse (.lessCmp (.var "i") (.length (.var "words") (some tSlS)))
    (.seqn #[]) .breakStmt
/-- The dispatch's residual sequence. -/
def cKRest (a : Nat) : Cont :=
  .seq [.seqn #[], wfIfTest, wordFreqFunc.wfCountBody] (cEnvD a)
    (cLoopK a)

section Dispatch

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b k cap : Nat) (iv0 sv2 : Int) (D : Heap) (a : Nat)
  (kvs : List (List UInt8 × Nat)) (tail : Heap) (na : Nat)
  (ch : Choices)

/-- **The FIRST dispatch** (27 steps): head at `$forFirst = true` —
the flag drops, `i` unchanged, the exit test delivers. -/
theorem cn_disp_first (civ : Int) (ha : 31 ≤ a) (hD : DeadFrom D a)
    (hkcap : k ≤ cap) :
    stepFnIter 27
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ true
        tail na)
      (cHeadCfg a) ch
      = .ok (.retV (.bool (decide (civ < (k : Int)))) (cCmpK a),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D) a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
          (by omega))]
      exact hD x hx
  -- fd1 (6 steps, rfl): head → the `$forFirst` read
  have h1 : stepFnIter 6
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ true
        tail na)
      (cHeadCfg a) ch
      = .ok (.evalE (.var "$forFirst") (cEnvD a)
            (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            true tail na, ch) := by
    with_unfolding_all rfl
  -- fd2 (1 step): the `$forFirst` read (true)
  have h2 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ true
        tail na)
      (.evalE (.var "$forFirst") (cEnvD a)
        (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a))) ch
      = .ok (.retV (.bool true)
            (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            true tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 4⟩) (c := sbool true)
      rfl ?_)
    exact lookup_five hWD' (by omega : (4 : Nat) < 5)
  -- fd3 (6 steps, rfl): the flag-drop store banked
  have h3 : stepFnIter 6
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ true
        tail na)
      (.retV (.bool true)
        (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 4⟩)) [] []]
            [.bool false] (.seqn #[]) (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            true tail na, ch) := by
    with_unfolding_all rfl
  -- fd4 (1 step): the store
  have h4 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ true
        tail na)
      (.next (.storeK [.chain (.addr (.base ⟨a + 4⟩)) [] []]
        [.bool false] (.seqn #[]) (cEnvD a) (cKRest a))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        true tail na)
      (a := ⟨a + 4⟩) (ty := .bool) (old := .bool true)
      (v := .bool false) (v' := .bool false)
      (lookup_five hWD' (by omega : (4 : Nat) < 5))
      (normalize_bool _ _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
          true tail na).heap
        (.base ⟨a + 4⟩) ⟨some .bool, .bool false⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na).heap from set_five4 hWD'] at h
    exact h
  -- fd5 (7 steps): drain, splices, the test's `i` read point
  have h5a := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
      false tail na)
    (ss := #[]) (env := cEnvD a)
    (rest := [.seqn #[], wfIfTest, wordFreqFunc.wfCountBody])
    (k := cLoopK a) (ch := ch))
  have h5b : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ false
        tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [.seqn #[], wfIfTest, wordFreqFunc.wfCountBody]) (cEnvD a)
        (cLoopK a))) ch
      = .ok (.exec (.seqn #[]) (cEnvD a)
            (.seq [wfIfTest, wordFreqFunc.wfCountBody] (cEnvD a)
              (cLoopK a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
    with_unfolding_all rfl
  have h5c := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
      false tail na)
    (ss := #[]) (env := cEnvD a)
    (rest := [wfIfTest, wordFreqFunc.wfCountBody]) (k := cLoopK a)
    (ch := ch))
  have h5d : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ false
        tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [wfIfTest, wordFreqFunc.wfCountBody]) (cEnvD a) (cLoopK a)))
      ch
      = .ok (.evalE (.var "i") (cEnvD a)
            (.strictK .lessCmp []
              [.length (.var "words") (some tSlS)] (cEnvD a) (cCmpK a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
    with_unfolding_all rfl
  -- the storeK drain that precedes fd5's first splice
  have h5pre : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ false
        tail na)
      (.next (.storeK [] [] (.seqn #[]) (cEnvD a) (cKRest a))) ch
      = .ok (.exec (.seqn #[]) (cEnvD a) (cKRest a),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
    with_unfolding_all rfl
  -- fd6 (1 step): the `i` read
  have h6 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ false
        tail na)
      (.evalE (.var "i") (cEnvD a)
        (.strictK .lessCmp [] [.length (.var "words") (some tSlS)]
          (cEnvD a) (cCmpK a))) ch
      = .ok (.retV (.int civ .int)
            (.strictK .lessCmp [] [.length (.var "words") (some tSlS)]
              (cEnvD a) (cCmpK a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 3⟩) (c := sint civ)
      rfl ?_)
    exact lookup_five hWD' (by omega : (3 : Nat) < 5)
  -- fd7 (3 steps, rfl): to the `words` handle delivery
  have h7 : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ false
        tail na)
      (.retV (.int civ .int)
        (.strictK .lessCmp [] [.length (.var "words") (some tSlS)]
          (cEnvD a) (cCmpK a))) ch
      = .ok (.retV (slsVal b 0 k cap)
            (.strictK (.lengthOf (some tSlS)) [] [] (cEnvD a)
              (.strictK .lessCmp [.int civ .int] [] (cEnvD a)
                (cCmpK a))),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
            false tail na, ch) := by
    with_unfolding_all rfl
  -- fd8 (1 step): the `len` apply
  have h8 := stepFnIter_one (stepFn_strict_apply (done := [])
    (env := cEnvD a)
    (k := .strictK .lessCmp [.int civ .int] [] (cEnvD a) (cCmpK a))
    (ch := ch)
    (applyStrictOp_len_slice
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na)
      (b := .base ⟨b⟩) (off := 0) (len := k) (cap := cap)
      (elem := tStr) hkcap))
  -- fd9 (1 step): the comparison apply
  have h9 := stepFnIter_one (stepFn_strict_apply
    (done := [.int civ .int]) (env := cEnvD a) (k := cCmpK a) (ch := ch)
    (applyStrictOp_lessCmp_int
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs civ
        false tail na)
      (a := civ) (b := ((k : Nat) : Int)) (k := .int) (k' := .int)))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5pre) h5a)
          h5b) h5c) h5d) h6) h7)
    (stepFnIter_chain h8 h9)

/-- **The back-edge dispatch** (31 steps): head at
`$forFirst = false`, position `i` — `i` steps to `i + 1`, the exit
test delivers. -/
theorem cn_disp (i : Nat) (ha : 31 ≤ a) (hD : DeadFrom D a)
    (hkcap : k ≤ cap) (hi63 : i + 1 < 2 ^ 63) :
    stepFnIter 31
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (cHeadCfg a) ch
      = .ok (.retV (.bool (decide (((i + 1 : Nat) : Int) < (k : Int))))
            (cCmpK a),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b k cap iv0 sv2 ++ D) a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b k cap iv0 sv2
          (by omega))]
      exact hD x hx
  -- a1 (6 steps, rfl): head → the `$forFirst` read
  have h1 : stepFnIter 6
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (cHeadCfg a) ch
      = .ok (.evalE (.var "$forFirst") (cEnvD a)
            (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  -- a2 (1 step): the `$forFirst` read (false)
  have h2 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (.evalE (.var "$forFirst") (cEnvD a)
        (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a))) ch
      = .ok (.retV (.bool false)
            (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i : Nat) : Int) false tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 4⟩) (c := sbool false)
      rfl ?_)
    exact lookup_five hWD' (by omega : (4 : Nat) < 5)
  -- a3 (5 steps, rfl): else arm → the `i` read of `i + 1`
  have h3 : stepFnIter 5
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (.retV (.bool false)
        (.ifK wfAsgnFFf wfAsgnIinc (cEnvD a) (cKRest a))) ch
      = .ok (.evalE (.var "i") (cEnvD a)
            (.strictK .add [] [.intLit 1 .int] (cEnvD a)
              (.rhsK .vals [.chain (.addr (.base ⟨a + 3⟩)) [] []] [] []
                (.seqn #[]) (cEnvD a) (cKRest a))),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  -- a4 (1 step): the `i` read
  have h4 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (.evalE (.var "i") (cEnvD a)
        (.strictK .add [] [.intLit 1 .int] (cEnvD a)
          (.rhsK .vals [.chain (.addr (.base ⟨a + 3⟩)) [] []] [] []
            (.seqn #[]) (cEnvD a) (cKRest a)))) ch
      = .ok (.retV (.int ((i : Nat) : Int) .int)
            (.strictK .add [] [.intLit 1 .int] (cEnvD a)
              (.rhsK .vals [.chain (.addr (.base ⟨a + 3⟩)) [] []] [] []
                (.seqn #[]) (cEnvD a) (cKRest a))),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i : Nat) : Int) false tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 3⟩)
      (c := sint ((i : Nat) : Int)) rfl ?_)
    exact lookup_five hWD' (by omega : (3 : Nat) < 5)
  -- a5 (4 steps, rfl): the add and the banked store
  have h5 : stepFnIter 4
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (.retV (.int ((i : Nat) : Int) .int)
        (.strictK .add [] [.intLit 1 .int] (cEnvD a)
          (.rhsK .vals [.chain (.addr (.base ⟨a + 3⟩)) [] []] [] []
            (.seqn #[]) (cEnvD a) (cKRest a)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨a + 3⟩)) [] []]
            [.int (IntKind.normalize .int (((i : Nat) : Int) + 1)) .int]
            (.seqn #[]) (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    inorm_nat_of_lt hi63] at h5
  -- a6 (1 step): the `i` store
  have h6 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (.next (.storeK [.chain (.addr (.base ⟨a + 3⟩)) [] []]
        [.int ((i + 1 : Nat) : Int) .int]
        (.seqn #[]) (cEnvD a) (cKRest a))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvD a) (cKRest a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (a := ⟨a + 3⟩) (ty := tInt) (old := .int ((i : Nat) : Int) .int)
      (v := .int ((i + 1 : Nat) : Int) .int)
      (v' := .int ((i + 1 : Nat) : Int) .int)
      (lookup_five hWD' (by omega : (3 : Nat) < 5))
      (by
        simp only [normalizeValueForTy, normalizeValueForTyFuel,
          typeResolutionFuel]
        rw [inorm_nat_of_lt hi63]
        rfl)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
          ((i : Nat) : Int) false tail na).heap
        (.base ⟨a + 3⟩) ⟨some tInt, .int ((i + 1 : Nat) : Int) .int⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na).heap from
      set_five3 hWD'] at h
    exact h
  -- a7…a11: the shared test suffix
  have h5pre : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (.next (.storeK [] [] (.seqn #[]) (cEnvD a) (cKRest a))) ch
      = .ok (.exec (.seqn #[]) (cEnvD a) (cKRest a),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  have h5a := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
      ((i + 1 : Nat) : Int) false tail na)
    (ss := #[]) (env := cEnvD a)
    (rest := [.seqn #[], wfIfTest, wordFreqFunc.wfCountBody])
    (k := cLoopK a) (ch := ch))
  have h5b : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [.seqn #[], wfIfTest, wordFreqFunc.wfCountBody]) (cEnvD a)
        (cLoopK a))) ch
      = .ok (.exec (.seqn #[]) (cEnvD a)
            (.seq [wfIfTest, wordFreqFunc.wfCountBody] (cEnvD a)
              (cLoopK a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  have h5c := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
      ((i + 1 : Nat) : Int) false tail na)
    (ss := #[]) (env := cEnvD a)
    (rest := [wfIfTest, wordFreqFunc.wfCountBody]) (k := cLoopK a)
    (ch := ch))
  have h5d : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [wfIfTest, wordFreqFunc.wfCountBody]) (cEnvD a) (cLoopK a)))
      ch
      = .ok (.evalE (.var "i") (cEnvD a)
            (.strictK .lessCmp []
              [.length (.var "words") (some tSlS)] (cEnvD a) (cCmpK a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  have h7 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (.evalE (.var "i") (cEnvD a)
        (.strictK .lessCmp [] [.length (.var "words") (some tSlS)]
          (cEnvD a) (cCmpK a))) ch
      = .ok (.retV (.int ((i + 1 : Nat) : Int) .int)
            (.strictK .lessCmp [] [.length (.var "words") (some tSlS)]
              (cEnvD a) (cCmpK a)),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 3⟩)
      (c := sint ((i + 1 : Nat) : Int)) rfl ?_)
    exact lookup_five hWD' (by omega : (3 : Nat) < 5)
  have h8 : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (.retV (.int ((i + 1 : Nat) : Int) .int)
        (.strictK .lessCmp [] [.length (.var "words") (some tSlS)]
          (cEnvD a) (cCmpK a))) ch
      = .ok (.retV (slsVal b 0 k cap)
            (.strictK (.lengthOf (some tSlS)) [] [] (cEnvD a)
              (.strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] []
                (cEnvD a) (cCmpK a))),
          cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
            ((i + 1 : Nat) : Int) false tail na, ch) := by
    with_unfolding_all rfl
  have h9 := stepFnIter_one (stepFn_strict_apply (done := [])
    (env := cEnvD a)
    (k := .strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] []
      (cEnvD a) (cCmpK a))
    (ch := ch)
    (applyStrictOp_len_slice
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (b := .base ⟨b⟩) (off := 0) (len := k) (cap := cap)
      (elem := tStr) hkcap))
  have h10 := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i + 1 : Nat) : Int) .int]) (env := cEnvD a)
    (k := cCmpK a) (ch := ch)
    (applyStrictOp_lessCmp_int
      (σ := cnSt σ nv sv qv bnv bsv l q biv b k cap iv0 sv2 D a kvs
        ((i + 1 : Nat) : Int) false tail na)
      (a := ((i + 1 : Nat) : Int)) (b := ((k : Nat) : Int)) (k := .int)
      (k' := .int)))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain h1 h2) h3) h4) h5) h6) h5pre) h5a) h5b)
            h5c) h5d) h7) h8)
    (stepFnIter_chain h9 h10)

end Dispatch

/-! ## One counting iteration (53 steps in four composites) -/

/-- `$c1 = counts`. -/
abbrev wfAsgnC1 : Stmt := .assign (.var "$c1") (.var "counts")
/-- The `$c1` declaration + read. -/
abbrev wfSeqnC1 : Stmt :=
  .seqn #[.initialization { id := "$c1", typ := tMapSU }, wfAsgnC1]
/-- `$c2 = words[i]`. -/
abbrev wfAsgnC2 : Stmt :=
  .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))
/-- The `$c2` declaration + read, as the frontend splices it. -/
abbrev wfSeqnC2 : Stmt :=
  .seqn #[.initialization { id := "$c2", typ := tStr }, wfAsgnC2]
/-- The `mapAssign` spine of `counts[$c2]++`. -/
abbrev wfMapAsgnStmt : Stmt :=
  .mapAssign (.var "$c1") (.var "$c2")
    (.add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
      (.intLit 1 .uint64))
    tStr tU64

section CountIter

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (iv0 sv2 : Int)
  (D : Heap) (a : Nat) (kvs : List (List UInt8 × Nat)) (tail : Heap)
  (na : Nat) (ch : Choices)

/-- Iteration composite 1 (20 steps): test true → `$c1` allocated and
holding the map handle, the `$c2` declaration reached. -/
theorem cn_iter1 (civ : Int) (ha : 31 ≤ a) (hD : DeadFrom D a)
    (htail : DeadFrom tail na) (hna : a + 5 ≤ na) :
    stepFnIter 20
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false tail na)
      (.retV (.bool true) (cCmpK a)) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tStr })
            (cEnvU1 a na)
            (.seq [wfAsgnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))])
            (na + 1), ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 ++ D)
      a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b fs.length cap
          iv0 sv2 (by omega))]
      exact hD x hx
  have hfront : ∀ (kvs' : List (List UInt8 × Nat)) (civ' : Int)
      (ff : Bool) (x : Nat), na ≤ x →
      Heap.lookup
        (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
          kvs' civ' ff) (.base ⟨x⟩) = none :=
    fun kvs' civ' ff x hx =>
      lookup_cnFront_none nv sv qv bnv bsv l q biv b fs.length cap iv0
        sv2 kvs' civ' ff ha hD (by omega)
  -- h1: ifK true → the body's empty seqn
  have h1 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false tail na)
      (.retV (.bool true) (cCmpK a)) ch
      = .ok (.exec (.seqn #[]) (cEnvD a) (cKBody a),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false tail na)
    (ss := #[]) (env := cEnvD a)
    (rest := [wordFreqFunc.wfCountBody]) (k := cLoopK a) (ch := ch))
  have h3 : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false tail na)
      (.next (.seq ((#[] : Array Stmt).toList
        ++ [wordFreqFunc.wfCountBody]) (cEnvD a) (cLoopK a))) ch
      = .ok (.exec wfSeqnC1 (cEnvB a)
            (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvB a) (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false tail na, ch) := by
    with_unfolding_all rfl
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false tail na)
    (ss := #[.initialization { id := "$c1", typ := tMapSU }, wfAsgnC1])
    (env := cEnvB a) (rest := [wfSeqnC2, wfMapAsgnStmt]) (k := cKD a)
    (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false tail na)
    (t := .initialization { id := "$c1", typ := tMapSU })
    (rest := [wfAsgnC1, wfSeqnC2, wfMapAsgnStmt]) (env := cEnvB a)
    (k := cKD a) (ch := ch))
  -- h6: `$c1` allocated at `na`
  have h6 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false tail na)
      (.exec (.initialization { id := "$c1", typ := tMapSU }) (cEnvB a)
        (.seq [wfAsgnC1, wfSeqnC2, wfMapAsgnStmt] (cEnvB a) (cKD a)))
      ch
      = .ok (.next (.seq [wfAsgnC1, wfSeqnC2, wfMapAsgnStmt]
            (cEnvU1 a na) (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1),
          ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
        kvs civ false tail na)
      (p := { id := "$c1", typ := tMapSU })
      (rest := [wfAsgnC1, wfSeqnC2, wfMapAsgnStmt]) (env := cEnvB a)
      (k := cKD a) (ch := ch) (v := .map ⟨none⟩) (defaultValue_tMapSU _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
          civ false tail na).heap (.base ⟨na⟩)
        ⟨some tMapSU, .map ⟨none⟩⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1)).heap
        from by
      show Heap.set (_ ++ tail) _ _ = _ ++ (tail ++ _)
      rw [set_fresh (by
        rw [lookup_append_right (hfront kvs civ false na (Nat.le_refl _))]
        exact htail na (Nat.le_refl _))]
      simp [List.append_assoc]] at h
    exact h
  -- h7 (4 steps, rfl): `$c1 = counts` to the `counts` read point
  have h7 : stepFnIter 4
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1))
      (.next (.seq [wfAsgnC1, wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na)
        (cKD a))) ch
      = .ok (.evalE (.var "counts") (cEnvU1 a na)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (cEnvU1 a na)
              (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1),
          ch) := by
    with_unfolding_all rfl
  -- h8: the `counts` read
  have h8 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1))
      (.evalE (.var "counts") (cEnvU1 a na)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (cEnvU1 a na)
          (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a)))) ch
      = .ok (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
            (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
              (.seqn #[]) (cEnvU1 a na)
              (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1),
          ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 2⟩)
      (c := mhW (a + 1)) rfl ?_)
    exact lookup_five hWD' (by omega : (2 : Nat) < 5)
  -- h9 (1 step, rfl): banks at the store queue
  have h9 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1))
      (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
        (.rhsK .vals [.chain (.addr (.base ⟨na⟩)) [] []] [] []
          (.seqn #[]) (cEnvU1 a na)
          (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
            [.map ⟨some (Loc.base ⟨a + 1⟩)⟩] (.seqn #[]) (cEnvU1 a na)
            (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1),
          ch) := by
    with_unfolding_all rfl
  -- h10: the `$c1` store
  have h10 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1))
      (.next (.storeK [.chain (.addr (.base ⟨na⟩)) [] []]
        [.map ⟨some (Loc.base ⟨a + 1⟩)⟩] (.seqn #[]) (cEnvU1 a na)
        (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvU1 a na)
            (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1),
          ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
        kvs civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1))
      (a := ⟨na⟩) (ty := tMapSU) (old := .map ⟨none⟩)
      (v := .map ⟨some (Loc.base ⟨a + 1⟩)⟩)
      (v' := .map ⟨some (Loc.base ⟨a + 1⟩)⟩)
      (by
        show Heap.lookup (_ ++ (tail ++ [(Loc.base ⟨na⟩, nilMapW)]))
          (.base ⟨na⟩) = some ⟨some tMapSU, .map ⟨none⟩⟩
        rw [lookup_append_right (hfront kvs civ false na (Nat.le_refl _)),
          lookup_append_right (htail na (Nat.le_refl _))]
        exact lookup_singleton_self)
      (normalize_mapHandle _ _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
          civ false (tail ++ [(Loc.base ⟨na⟩, nilMapW)]) (na + 1)).heap
        (.base ⟨na⟩) ⟨some tMapSU, .map ⟨some (Loc.base ⟨a + 1⟩)⟩⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))])
            (na + 1)).heap from by
      show Heap.set (_ ++ (tail ++ [(Loc.base ⟨na⟩, nilMapW)])) _ _ = _
      rw [set_append_right (hfront kvs civ false na (Nat.le_refl _)),
        set_append_right (htail na (Nat.le_refl _)),
        set_singleton_self]] at h
    exact h
  -- h11…h15: drain to the `$c2` declaration
  have h11 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1))
      (.next (.storeK [] [] (.seqn #[]) (cEnvU1 a na)
        (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a)))) ch
      = .ok (.exec (.seqn #[]) (cEnvU1 a na)
            (.seq [wfSeqnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1),
          ch) := by
    with_unfolding_all rfl
  have h12 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1))
    (ss := #[]) (env := cEnvU1 a na)
    (rest := [wfSeqnC2, wfMapAsgnStmt]) (k := cKD a) (ch := ch))
  have h13 := stepFnIter_one (stepFn_seq_pop
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1))
    (t := wfSeqnC2) (rest := [wfMapAsgnStmt]) (env := cEnvU1 a na)
    (k := cKD a) (ch := ch))
  have h14 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1))
    (ss := #[.initialization { id := "$c2", typ := tStr }, wfAsgnC2])
    (env := cEnvU1 a na) (rest := [wfMapAsgnStmt]) (k := cKD a)
    (ch := ch))
  have h15 := stepFnIter_one (stepFn_seq_pop
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs civ false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1))
    (t := .initialization { id := "$c2", typ := tStr })
    (rest := [wfAsgnC2, wfMapAsgnStmt]) (env := cEnvU1 a na)
    (k := cKD a) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
      (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
        (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
          (stepFnIter_chain h1 h2) h3) h4) h5) h6) h7) h8) h9) h10)
            h11) h12) h13)
    (stepFnIter_chain h14 h15)

/-- Iteration composite 2 (12 steps): the `$c2` declaration through the
`words[i]` read and store — the word lands in `$c2`. -/
theorem cn_iter2 (i : Nat) (ha : 31 ≤ a) (hD : DeadFrom D a)
    (htail : DeadFrom tail na) (hna : a + 5 ≤ na)
    (hb31 : 31 ≤ b)
    (hDb : Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
    (hcap : fs.length ≤ cap) (hi : i < fs.length) :
    stepFnIter 12
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))])
        (na + 1))
      (.exec (.initialization { id := "$c2", typ := tStr })
        (cEnvU1 a na)
        (.seq [wfAsgnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvU a na)
            (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs (fs.getD i [])))]) (na + 2),
          ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 ++ D)
      a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b fs.length cap
          iv0 sv2 (by omega))]
      exact hD x hx
  have hfront : ∀ (kvs' : List (List UInt8 × Nat)) (civ' : Int)
      (ff : Bool) (x : Nat), na ≤ x →
      Heap.lookup
        (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
          kvs' civ' ff) (.base ⟨x⟩) = none :=
    fun kvs' civ' ff x hx =>
      lookup_cnFront_none nv sv qv bnv bsv l q biv b fs.length cap iv0
        sv2 kvs' civ' ff ha hD (by omega)
  -- h1: `$c2` allocated at `na + 1`
  have h1 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))])
        (na + 1))
      (.exec (.initialization { id := "$c2", typ := tStr })
        (cEnvU1 a na)
        (.seq [wfAsgnC2, wfMapAsgnStmt] (cEnvU1 a na) (cKD a))) ch
      = .ok (.next (.seq [wfAsgnC2, wfMapAsgnStmt] (cEnvU a na)
            (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2), ch) := by
    refine stepFnIter_one ?_
    have h := stepFn_init_seq
      (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
        kvs ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1))
      (p := { id := "$c2", typ := tStr })
      (rest := [wfAsgnC2, wfMapAsgnStmt]) (env := cEnvU1 a na)
      (k := cKD a) (ch := ch) (v := .string GoString.empty)
      (defaultValue_tStr _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
          ((i : Nat) : Int) false
          (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))]) (na + 1)).heap
        (.base ⟨na + 1⟩) ⟨some tStr, .string GoString.empty⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2)).heap
        from by
      show Heap.set (_ ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1))])) _ _ = _
      rw [set_fresh (by
        rw [lookup_append_right
          (hfront kvs ((i : Nat) : Int) false (na + 1) (by omega)),
          lookup_append_right (htail (na + 1) (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
        rfl)]
      simp [List.append_assoc]] at h
    exact h
  -- h2 (7 steps, rfl): `$c2 = words[i]` to the `i` read point
  have h2 : stepFnIter 7
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2))
      (.next (.seq [wfAsgnC2, wfMapAsgnStmt] (cEnvU a na) (cKD a))) ch
      = .ok (.evalE (.var "i") (cEnvU a na)
            (.strictK .indexGet [slsVal b 0 fs.length cap] []
              (cEnvU a na)
              (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
                (.seqn #[]) (cEnvU a na)
                (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2), ch) := by
    with_unfolding_all rfl
  -- h3: the `i` read
  have h3 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2))
      (.evalE (.var "i") (cEnvU a na)
        (.strictK .indexGet [slsVal b 0 fs.length cap] [] (cEnvU a na)
          (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
            (.seqn #[]) (cEnvU a na)
            (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a))))) ch
      = .ok (.retV (.int ((i : Nat) : Int) .int)
            (.strictK .indexGet [slsVal b 0 fs.length cap] []
              (cEnvU a na)
              (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
                (.seqn #[]) (cEnvU a na)
                (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2), ch) := by
    refine stepFnIter_one (stepFn_var (a := ⟨a + 3⟩)
      (c := sint ((i : Nat) : Int)) rfl ?_)
    exact lookup_five hWD' (by omega : (3 : Nat) < 5)
  -- h4: the `words[i]` read
  have h4 := stepFnIter_one (stepFn_strict_apply
    (done := [slsVal b 0 fs.length cap]) (env := cEnvU a na)
    (k := .rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
      (.seqn #[]) (cEnvU a na)
      (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))
    (ch := ch)
    (cn_words_read σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a kvs
      ((i : Nat) : Int) false
      (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2) i
      (ik := .int) hb31 hDb hcap hi))
  -- h5 (1 step, rfl): banks at the store queue
  have h5 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2))
      (.retV (.string (gs (fs.getD i [])))
        (.rhsK .vals [.chain (.addr (.base ⟨na + 1⟩)) [] []] [] []
          (.seqn #[]) (cEnvU a na)
          (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na + 1⟩)) [] []]
            [.string (gs (fs.getD i []))] (.seqn #[]) (cEnvU a na)
            (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2), ch) := by
    with_unfolding_all rfl
  -- h6: the `$c2` store
  have h6 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2))
      (.next (.storeK [.chain (.addr (.base ⟨na + 1⟩)) [] []]
        [.string (gs (fs.getD i []))] (.seqn #[]) (cEnvU a na)
        (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (cEnvU a na)
            (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs (fs.getD i [])))]) (na + 2),
          ch) := by
    refine stepFnIter_one (stepFn_store_step (rs := []) (vs := []) ?_)
    have h := storeTarget_addr
      (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
        kvs ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2))
      (a := ⟨na + 1⟩) (ty := tStr) (old := .string GoString.empty)
      (v := .string (gs (fs.getD i [])))
      (v' := .string (gs (fs.getD i [])))
      (by
        show Heap.lookup
          (_ ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
            (Loc.base ⟨na + 1⟩, sstr GoString.empty)]))
          (.base ⟨na + 1⟩) = some ⟨some tStr, .string GoString.empty⟩
        rw [lookup_append_right
          (hfront kvs ((i : Nat) : Int) false (na + 1) (by omega))]
        exact lookup_c2of2 htail)
      (normalize_str _ _)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
          ((i : Nat) : Int) false
          (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
            (Loc.base ⟨na + 1⟩, sstr GoString.empty)]) (na + 2)).heap
        (.base ⟨na + 1⟩) ⟨some tStr, .string (gs (fs.getD i []))⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs (fs.getD i [])))])
            (na + 2)).heap from by
      show Heap.set (_ ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr GoString.empty)])) _ _ = _
      rw [set_append_right
        (hfront kvs ((i : Nat) : Int) false (na + 1) (by omega)),
        set_c2of2 htail]] at h
    exact h
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain h1 h2) h3) h4) h5) h6

/-- Iteration composite 3 (10 steps): the `mapAssign` spine to the
`mapGet` argument read point. -/
theorem cn_iter3 (i : Nat) (w : List UInt8) (ha : 31 ≤ a)
    (hD : DeadFrom D a) (htail : DeadFrom tail na) (hna : a + 5 ≤ na) :
    stepFnIter 10
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.next (.storeK [] [] (.seqn #[]) (cEnvU a na)
        (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))) ch
      = .ok (.evalE (.var "$c1") (cEnvU a na)
            (.strictK (.mapGet tStr tU64) [] [.var "$c2"] (cEnvU a na)
              (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
                (.stmtOpK (.mapAssign tStr tU64) 0
                  [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
                  (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 ++ D)
      a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b fs.length cap
          iv0 sv2 (by omega))]
      exact hD x hx
  have hfront : ∀ (kvs' : List (List UInt8 × Nat)) (civ' : Int)
      (ff : Bool) (x : Nat), na ≤ x →
      Heap.lookup
        (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
          kvs' civ' ff) (.base ⟨x⟩) = none :=
    fun kvs' civ' ff x hx =>
      lookup_cnFront_none nv sv qv bnv bsv l q biv b fs.length cap iv0
        sv2 kvs' civ' ff ha hD (by omega)
  have h1 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.next (.storeK [] [] (.seqn #[]) (cEnvU a na)
        (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)))) ch
      = .ok (.exec (.seqn #[]) (cEnvU a na)
            (.seq [wfMapAsgnStmt] (cEnvU a na) (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs ((i : Nat) : Int) false
      (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
    (ss := #[]) (env := cEnvU a na) (rest := [wfMapAsgnStmt])
    (k := cKD a) (ch := ch))
  have h3 : stepFnIter 2
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.next (.seq ((#[] : Array Stmt).toList ++ [wfMapAsgnStmt])
        (cEnvU a na) (cKD a))) ch
      = .ok (.evalE (.var "$c1") (cEnvU a na)
            (.stmtOpK (.mapAssign tStr tU64) 0 []
              [.var "$c2",
               .add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
                 (.intLit 1 .uint64)]
              (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  -- the `$c1` read
  have hlk1 : Heap.lookup
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap
      (.base ⟨na⟩) = some (mhW (a + 1)) := by
    show Heap.lookup
      (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))])) (.base ⟨na⟩) = _
    rw [lookup_append_right
      (hfront kvs ((i : Nat) : Int) false na (Nat.le_refl _))]
    exact lookup_c1of2 htail
  have hlk2 : Heap.lookup
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap
      (.base ⟨na + 1⟩) = some (sstr (gs w)) := by
    show Heap.lookup
      (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))])) (.base ⟨na + 1⟩) = _
    rw [lookup_append_right
      (hfront kvs ((i : Nat) : Int) false (na + 1) (by omega))]
    exact lookup_c2of2 htail
  have h4 := stepFnIter_one (stepFn_var
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs ((i : Nat) : Int) false
      (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
    (x := "$c1") (env := cEnvU a na) (a := ⟨na⟩)
    (k := .stmtOpK (.mapAssign tStr tU64) 0 []
      [.var "$c2",
       .add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
         (.intLit 1 .uint64)]
      (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))
    (ch := ch) rfl hlk1)
  have h5 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
        (.stmtOpK (.mapAssign tStr tU64) 0 []
          [.var "$c2",
           .add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
             (.intLit 1 .uint64)]
          (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))) ch
      = .ok (.evalE (.var "$c2") (cEnvU a na)
            (.stmtOpK (.mapAssign tStr tU64) 0
              [.map ⟨some (Loc.base ⟨a + 1⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
                (.intLit 1 .uint64)]
              (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  have h6 := stepFnIter_one (stepFn_var
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs ((i : Nat) : Int) false
      (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
    (x := "$c2") (env := cEnvU a na) (a := ⟨na + 1⟩)
    (k := .stmtOpK (.mapAssign tStr tU64) 0
      [.map ⟨some (Loc.base ⟨a + 1⟩)⟩]
      [.add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
        (.intLit 1 .uint64)]
      (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))
    (ch := ch) rfl hlk2)
  have h7 : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.retV (.string (gs w))
        (.stmtOpK (.mapAssign tStr tU64) 0
          [.map ⟨some (Loc.base ⟨a + 1⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tStr tU64)
            (.intLit 1 .uint64)]
          (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))) ch
      = .ok (.evalE (.var "$c1") (cEnvU a na)
            (.strictK (.mapGet tStr tU64) [] [.var "$c2"] (cEnvU a na)
              (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
                (.stmtOpK (.mapAssign tStr tU64) 0
                  [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
                  (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3)
      h4) h5) h6) h7

/-- Iteration composite 4 (11 steps): the `mapGet`, the increment, the
map WRITE, back to the loop head — the counts fold advances one word. -/
theorem cn_iter4 (i : Nat) (w : List UInt8) (ha : 31 ≤ a)
    (hD : DeadFrom D a) (htail : DeadFrom tail na) (hna : a + 5 ≤ na)
    (hcnt64 : cntW kvs w + 1 < 2 ^ 64) :
    stepFnIter 11
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.evalE (.var "$c1") (cEnvU a na)
        (.strictK (.mapGet tStr tU64) [] [.var "$c2"] (cEnvU a na)
          (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
            (.stmtOpK (.mapAssign tStr tU64) 0
              [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
              (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))))) ch
      = .ok (cHeadCfg a,
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            (setkW kvs w (cntW kvs w + 1)) ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
  have hWD' : DeadFrom
      (wHeapCount nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 ++ D)
      a :=
    fun x hx => by
      rw [lookup_append_right
        (lookup_wHeapCount_none nv sv qv bnv bsv l q biv b fs.length cap
          iv0 sv2 (by omega))]
      exact hD x hx
  have hfront : ∀ (kvs' : List (List UInt8 × Nat)) (civ' : Int)
      (ff : Bool) (x : Nat), na ≤ x →
      Heap.lookup
        (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
          kvs' civ' ff) (.base ⟨x⟩) = none :=
    fun kvs' civ' ff x hx =>
      lookup_cnFront_none nv sv qv bnv bsv l q biv b fs.length cap iv0
        sv2 kvs' civ' ff ha hD (by omega)
  have hlk1 : Heap.lookup
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap
      (.base ⟨na⟩) = some (mhW (a + 1)) := by
    show Heap.lookup
      (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))])) (.base ⟨na⟩) = _
    rw [lookup_append_right
      (hfront kvs ((i : Nat) : Int) false na (Nat.le_refl _))]
    exact lookup_c1of2 htail
  have hlk2 : Heap.lookup
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap
      (.base ⟨na + 1⟩) = some (sstr (gs w)) := by
    show Heap.lookup
      (cnFront nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        ++ (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))])) (.base ⟨na + 1⟩) = _
    rw [lookup_append_right
      (hfront kvs ((i : Nat) : Int) false (na + 1) (by omega))]
    exact lookup_c2of2 htail
  have h1 := stepFnIter_one (stepFn_var
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs ((i : Nat) : Int) false
      (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
    (x := "$c1") (env := cEnvU a na) (a := ⟨na⟩)
    (k := .strictK (.mapGet tStr tU64) [] [.var "$c2"] (cEnvU a na)
      (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
        (.stmtOpK (.mapAssign tStr tU64) 0
          [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
          (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))))
    (ch := ch) rfl hlk1)
  have h2 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.retV (.map ⟨some (Loc.base ⟨a + 1⟩)⟩)
        (.strictK (.mapGet tStr tU64) [] [.var "$c2"] (cEnvU a na)
          (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
            (.stmtOpK (.mapAssign tStr tU64) 0
              [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
              (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))))) ch
      = .ok (.evalE (.var "$c2") (cEnvU a na)
            (.strictK (.mapGet tStr tU64) [.map ⟨some (Loc.base ⟨a + 1⟩)⟩]
              [] (cEnvU a na)
              (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
                (.stmtOpK (.mapAssign tStr tU64) 0
                  [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
                  (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  have h3 := stepFnIter_one (stepFn_var
    (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
      kvs ((i : Nat) : Int) false
      (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
        (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
    (x := "$c2") (env := cEnvU a na) (a := ⟨na + 1⟩)
    (k := .strictK (.mapGet tStr tU64) [.map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
      (cEnvU a na)
      (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
        (.stmtOpK (.mapAssign tStr tU64) 0
          [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
          (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))))
    (ch := ch) rfl hlk2)
  -- the mapGet apply
  have hlkD : Heap.lookup
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap
      (.base ⟨a + 1⟩) = some ⟨none, .mapData (toEntriesW kvs)⟩ :=
    lookup_five hWD' (by omega : (1 : Nat) < 5)
  have h4 := stepFnIter_one (stepFn_strict_apply
    (done := [.map ⟨some (Loc.base ⟨a + 1⟩)⟩]) (env := cEnvU a na)
    (k := .strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
      (.stmtOpK (.mapAssign tStr tU64) 0
        [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
        (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))))
    (ch := ch)
    (applyStrictOp_mapGetW (a := ⟨a + 1⟩) (kvs := kvs) (w := w)
      (dty := none) hlkD))
  -- the increment
  have h5 : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.retV (.int (cntW kvs w : Int) .uint64)
        (.strictK .add [] [.intLit 1 .uint64] (cEnvU a na)
          (.stmtOpK (.mapAssign tStr tU64) 0
            [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
            (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))))) ch
      = .ok (.retV
            (.int (IntKind.normalize .uint64 ((cntW kvs w : Int) + 1))
              .uint64)
            (.stmtOpK (.mapAssign tStr tU64) 0
              [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
              (cEnvU a na) (.seq [] (cEnvU a na) (cKD a))),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  rw [show ((cntW kvs w : Nat) : Int) + 1
      = ((cntW kvs w + 1 : Nat) : Int) from by omega,
    unorm_nat_of_lt hcnt64] at h5
  -- the map WRITE
  have h6 : stepFnIter 1
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.retV (.int ((cntW kvs w + 1 : Nat) : Int) .uint64)
        (.stmtOpK (.mapAssign tStr tU64) 0
          [.string (gs w), .map ⟨some (Loc.base ⟨a + 1⟩)⟩] []
          (cEnvU a na) (.seq [] (cEnvU a na) (cKD a)))) ch
      = .ok (.next (.seq [] (cEnvU a na) (cKD a)),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            (setkW kvs w (cntW kvs w + 1)) ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    refine stepFnIter_one (stepFn_mapAssign_apply ?_)
    have h := mapAssignValue_toEntriesW
      (σ := cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
        kvs ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (a := ⟨a + 1⟩) (kvs := kvs) (w := w) (v := cntW kvs w + 1)
      (lookup_five hWD' (by omega : (1 : Nat) < 5))
      (unorm_nat_of_lt hcnt64)
    rw [show Heap.set
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
          ((i : Nat) : Int) false
          (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
            (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap
        (.base ⟨a + 1⟩)
        ⟨none, .mapData (toEntriesW (setkW kvs w (cntW kvs w + 1)))⟩
        = (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            (setkW kvs w (cntW kvs w + 1)) ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2)).heap from
      set_five1 hWD'] at h
    exact h
  -- back to the head
  have h7 : stepFnIter 3
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
        (setkW kvs w (cntW kvs w + 1)) ((i : Nat) : Int) false
        (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
          (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2))
      (.next (.seq [] (cEnvU a na) (cKD a))) ch
      = .ok (cHeadCfg a,
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            (setkW kvs w (cntW kvs w + 1)) ((i : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs w))]) (na + 2), ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain h1 h2) h3)
      h4) h5) h6) h7

/-- **One counting iteration** (84 steps): exit-test true at word `i`
→ `counts[words[i]]++` → the next exit-test delivery at `i + 1`. -/
theorem cn_iter (i : Nat) (ha : 31 ≤ a) (hD : DeadFrom D a)
    (htail : DeadFrom tail na) (hna : a + 5 ≤ na) (hb31 : 31 ≤ b)
    (hDb : Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
    (hcap : fs.length ≤ cap) (hi : i < fs.length)
    (hi63 : i + 1 < 2 ^ 63)
    (hcnt64 : cntW kvs (fs.getD i []) + 1 < 2 ^ 64) :
    stepFnIter 84
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        ((i : Nat) : Int) false tail na)
      (.retV (.bool true) (cCmpK a)) ch
      = .ok (.retV (.bool (decide (((i + 1 : Nat) : Int)
              < (fs.length : Int)))) (cCmpK a),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            (bumpW kvs (fs.getD i [])) ((i + 1 : Nat) : Int) false
            (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
              (Loc.base ⟨na + 1⟩, sstr (gs (fs.getD i [])))]) (na + 2),
          ch) := by
  have h1 := cn_iter1 σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a
    kvs tail na ch ((i : Nat) : Int) ha hD htail hna
  have h2 := cn_iter2 σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a
    kvs tail na ch i ha hD htail hna hb31 hDb hcap hi
  have h3 := cn_iter3 σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a
    kvs tail na ch i (fs.getD i []) ha hD htail hna
  have h4 := cn_iter4 σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a
    kvs tail na ch i (fs.getD i []) ha hD htail hna hcnt64
  have hdisp := cn_disp σ nv sv qv bnv bsv l q biv b fs.length cap iv0
    sv2 D a (setkW kvs (fs.getD i []) (cntW kvs (fs.getD i []) + 1))
    (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
      (Loc.base ⟨na + 1⟩, sstr (gs (fs.getD i [])))]) (na + 2) ch i ha hD
    hcap hi63
  have hchain := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) hdisp
  rw [setkW_cnt_succ] at hchain
  exact hchain

end CountIter

/-! ## The counting loop, its exit, and the assembled count phase -/

section CountLoop

variable (σ : ExecState) (nv sv qv bnv bsv : Int) (l q : List UInt8)
  (biv : Int) (b cap : Nat) (fs : List (List UInt8)) (iv0 sv2 : Int)
  (D : Heap) (a : Nat)

/-- **The counting loop** (exactly `84·(|fs| − i)` steps): from the
exit-test delivery at word `i` over the fold-so-far, every remaining
word lands in the counts map; ends at the test's `false` delivery over
the full fold. -/
theorem cn_loop (ha : 31 ≤ a) (hD : DeadFrom D a)
    (hbOr : (31 ≤ b
        ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
      ∨ (b = 25 ∧ cap = 0 ∧ fs = []))
    (hcap : fs.length ≤ cap) (hlen : fs.length < 2 ^ 60) :
    ∀ m i : Nat, m = fs.length - i → i ≤ fs.length →
    ∀ (tail : Heap) (na : Nat) (ch : Choices),
    DeadFrom tail na → a + 5 ≤ na →
    ∃ (tail' : Heap) (na' : Nat),
      DeadFrom tail' na' ∧ na ≤ na' ∧
      stepFnIter (84 * m)
        (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
          (countsFoldW (fs.take i)) ((i : Nat) : Int) false tail na)
        (.retV (.bool (decide (((i : Nat) : Int) < (fs.length : Int))))
          (cCmpK a)) ch
        = .ok (.retV (.bool false) (cCmpK a),
            cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
              (countsFoldW fs) ((fs.length : Nat) : Int) false tail'
              na', ch) := by
  intro m
  induction m with
  | zero =>
      intro i hm hi tail na ch htail hna
      have hieq : i = fs.length := by omega
      subst hieq
      rw [show (decide (((fs.length : Nat) : Int) < (fs.length : Int)))
          = false from decide_eq_false (by omega), List.take_length]
      exact ⟨tail, na, htail, Nat.le_refl _, rfl⟩
  | succ m ih =>
      intro i hm hi tail na ch htail hna
      have hilt : i < fs.length := by omega
      have hbd : 31 ≤ b
          ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap) := by
        rcases hbOr with h | ⟨-, -, hfs⟩
        · exact h
        · subst hfs
          simp at hilt
      obtain ⟨hb31, hDb⟩ := hbd
      rw [show (decide (((i : Nat) : Int) < (fs.length : Int))) = true
        from decide_eq_true (by exact_mod_cast hilt)]
      have hcnt64 : cntW (countsFoldW (fs.take i)) (fs.getD i []) + 1
          < 2 ^ 64 := by
        have := cntW_take_le (ws := fs) (i := i) (fs.getD i [])
        omega
      have hIt := cn_iter σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D
        a (countsFoldW (fs.take i)) tail na ch i ha hD htail hna hb31
        hDb hcap hilt (by omega) hcnt64
      rw [show bumpW (countsFoldW (fs.take i)) (fs.getD i [])
          = countsFoldW (fs.take (i + 1)) from by
        rw [← countsFoldW_append, ← take_succ_getD hilt]] at hIt
      obtain ⟨tail', na', htail', hle', hrun⟩ :=
        ih (i + 1) (by omega) (by omega)
          (tail ++ [(Loc.base ⟨na⟩, mhW (a + 1)),
            (Loc.base ⟨na + 1⟩, sstr (gs (fs.getD i [])))]) (na + 2) ch
          (DeadFrom.push2 htail) (by omega)
      refine ⟨tail', na', htail', by omega, ?_⟩
      have hchain := stepFnIter_chain hIt hrun
      rw [show 84 + 84 * m = 84 * (m + 1) from by omega] at hchain
      exact hchain

/-- **The count exit** (7 steps): the test's `false` delivery breaks
out of the loop and pops to the `best := 0` statement — the range
phase's entry seam. -/
theorem cn_exit (kvs : List (List UInt8 × Nat)) (civ : Int)
    (tail : Heap) (na : Nat) (ch : Choices) :
    stepFnIter 7
      (cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a kvs
        civ false tail na)
      (.retV (.bool false) (cCmpK a)) ch
      = .ok (.exec wfBestSeqn (cEnvC a)
            (.seq [wfRangeStmt, wfResSeqn] (cEnvC a) wfFrameK),
          cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
            kvs civ false tail na, ch) := by
  with_unfolding_all rfl

/-- **The count phase, assembled** (`84·n + 85` steps): from the
shim-return seam, the counts map is BUILT — `countsFoldW fs` — and the
machine parks at the `best := 0` seam. -/
theorem cn_phase (ha : 31 ≤ a) (hD : DeadFrom D a)
    (hbOr : (31 ≤ b
        ∧ Heap.lookup D (.base ⟨b⟩) = some (strArrCell fs cap))
      ∨ (b = 25 ∧ cap = 0 ∧ fs = []))
    (hcap : fs.length ≤ cap) (hlen : fs.length < 2 ^ 60)
    (ch : Choices) :
    ∃ (tail' : Heap) (na' : Nat),
      DeadFrom tail' na' ∧ a + 5 ≤ na' ∧
      stepFnIter (84 * fs.length + 85)
        (wSt σ (wHeapCount nv sv qv bnv bsv l q biv b fs.length cap iv0
          sv2 ++ D) a)
        (.exec (.seqn #[]) wfEnvW wfAfterShim) ch
        = .ok (.exec wfBestSeqn (cEnvC a)
              (.seq [wfRangeStmt, wfResSeqn] (cEnvC a) wfFrameK),
            cnSt σ nv sv qv bnv bsv l q biv b fs.length cap iv0 sv2 D a
              (countsFoldW fs) ((fs.length : Nat) : Int) false tail'
              na', ch) := by
  have hpro := cn_prologue σ nv sv qv bnv bsv l q biv b fs.length cap
    iv0 sv2 D a ch ha hD
  have hdisp := cn_disp_first σ nv sv qv bnv bsv l q biv b fs.length
    cap iv0 sv2 D a [] [] (a + 5) ch 0 ha hD hcap
  obtain ⟨tail', na', htail', hle', hloop⟩ :=
    cn_loop σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a ha hD hbOr
      hcap hlen (fs.length - 0) 0 rfl (by omega) [] (a + 5) ch
      (fun x _ => rfl) (Nat.le_refl _)
  have hexit := cn_exit σ nv sv qv bnv bsv l q biv b cap fs iv0 sv2 D a
    (countsFoldW fs) ((fs.length : Nat) : Int) tail' na' ch
  rw [show countsFoldW (fs.take 0) = [] from rfl] at hloop
  rw [show ((0 : Nat) : Int) = (0 : Int) from rfl] at hloop
  have hchain := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    hpro hdisp) hloop) hexit
  rw [show 51 + 27 + 84 * (fs.length - 0) + 7
      = 84 * fs.length + 85 from by omega] at hchain
  exact ⟨tail', na', htail', by omega, hchain⟩

end CountLoop

end GoLean.Examples.WordFreq
