import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId

/-!
# Verified example: word count over a Go map (verified-examples slice 2c,
2026-08-13)

The map scale-out example over the settled memory-quantified form
(design note `docs/2026-08-12_example-spec-form.md` §10): the Go program
is the canonical corpus source
`Corpus/coverage/exec/examples/wordcount/main.go` (6/6 differentially
green against `go run`); `wordCountLowered` is its pinned frontend
lowering (`scripts/check-golden`, both links). The subject `maxCount`
builds `counts : map[uint64]uint64` from a `[]uint64` and takes the max
count with `for _, c := range counts`.

**Statement form of record (harness ruling 2026-08-13, form note §11)**:
user-facing headlines are three-phase Go HARNESSES stated over
`runFunctionWithContextM` — termination + returned values only, no
Lean-side heap vocabulary. What THIS module ships against that form:

* `maxCount_total_canonical` — the SUPPORTING inner-run theorem
  (fallback rung 2): for EVERY uint64 word list, the `maxCount` run at
  the canonical placement completes past the explicit fuel bound
  `132 + 108·len`, at EVERY nondeterminism-choice stream, with exactly
  `maxMultiplicity ws` delivered and the input backing untouched. All
  the semantic content (the ∀-choices range induction included) lives
  here; it is ∀-ws (STRONGER than any scalar-parameterized harness
  family).
* `wordcount_empty_ok` — the harness FORM, witnessed end to end at the
  pinned `maxCountEmpty` harness (the zero-parameter instance).
* NAMED DEBT (§10d clause, now pointing at the harness form): the
  `(n, seed)`-parameterized `wordcount_ok` over `wordcount_harness` —
  its remaining cost is purely the MACHINE-LAYER RE-INSTANTIATION of
  this module's address-concrete configuration tower at the harness
  placement (see the slice report's gap G1); the two loop inductions
  and every executable fact are placement-generic already.

**The teaching point (§10b): the ∀-choices quantifier does REAL work
here.** `for … range m` consumes one `Choices` pick per iteration
(`stepFn`'s `mapIterK` arm), so the headline quantifies over every
ITERATION ORDER of the map — the claim holds at all of them, which is
exactly why the specification function `maxMultiplicity` must be an
order-independent fold (max is commutative-idempotent). A spec that
named "the first key with maximal count" would be unprovable — different
orders yield different firsts — and that unprovability is the envelope
working, not failing. The proof's range half is the §10b choice-pick
induction: destructure `Choices.consume` (its `% bound` contract gives
`idx < size`), erase the picked index, re-establish the max-fold
invariant.

**The §10c obstruction, realized**: `bindIterVars` allocates a fresh
value cell per range iteration, so in-loop addresses are symbolic in
the iteration count and `with_unfolding_all rfl` segments cannot carry
the range body — its heap-touching steps are HAND-GLUED conditioned
steps (`stepFn` unfoldings + `Heap.lookup`/`storeLoc` facts at symbolic
addresses, closed by `beq`-disequality simp, not `rfl`). RECORDED
DEVIATION from the §10 plan (a finding, per the slice instructions):
the plan expected phase C (the counting loop) to be address-concrete
with `nextAddr` first moving at the range loop; in fact the frontend
lowers `counts[words[i]]++` through per-iteration temporaries `$c1`/
`$c2` whose `initialization` ALLOCATES two fresh cells per counting
iteration, so phase C is in the symbolic-address regime too and is
glued the same way. (Probe: `xs = [7,3,7]` runs 432 steps, `nextAddr`
2 → 18 — 7 entry cells, 2 per counting iteration, 1 per range
iteration.) The `best` cell is likewise at the length-dependent address
`9 + 2·len`, not a concrete one.

Scope honesty (the charter's two-questions separation): usability
evidence only — never machine-hardening evidence.
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
private def idxOf? : List (Int × Nat) → Int → Option Nat
  | [], _ => none
  | (k, _) :: rest, w => if k = w then some 0 else (idxOf? rest w).map (· + 1)

/-- Assoc lookup at the FIRST occurrence, `0` when absent — exactly a
Go map read's zero-value semantics on this fragment. -/
private def cnt : List (Int × Nat) → Int → Nat
  | [], _ => 0
  | (k, c) :: rest, w => if k = w then c else cnt rest w

/-- Update the first occurrence of `w`, or append — exactly
`mapAssignValue`'s update-or-insert on the entry list. -/
private def setk : List (Int × Nat) → Int → Nat → List (Int × Nat)
  | [], w, v => [(w, v)]
  | (k, c) :: rest, w, v =>
      if k = w then (k, v) :: rest else (k, c) :: setk rest w v

/-- The machine encoding of a counts list: insertion-ordered
`mapData` entries of wrapped uint64 pairs. -/
private def toEntries (kvs : List (Int × Nat)) : Array (GoValue × GoValue) :=
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

private theorem toEntries_getElem? (kvs : List (Int × Nat)) (j : Nat)
    {p : Int × Nat} (h : kvs[j]? = some p) :
    (toEntries kvs)[j]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) := by
  simp [toEntries, List.getElem?_map, h]

/-- **The map-elem read** (`counts[w]`, expression position): a present
key answers its count, an absent key the ZERO VALUE — which is exactly
how `counts[w]++` starts a fresh key at 1. -/
private theorem applyStrictOp_mapGet {σ : ExecState} {a : Addr}
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
private theorem mapAssignValue_toEntries {σ : ExecState} {a : Addr}
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
private theorem snapshot_toEntries {σ : ExecState} {a : Addr}
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

private theorem toEntries_size (kvs : List (Int × Nat)) :
    (toEntries kvs).size = kvs.length := by
  simp [toEntries]

private theorem map_eraseIdx {α β : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat), (l.map f).eraseIdx i = (l.eraseIdx i).map f := by
  intro l
  induction l with
  | nil => intro i; simp
  | cons a rest ih =>
      intro i
      cases i with
      | zero => simp [List.eraseIdx]
      | succ n => simp [List.eraseIdx, ih n]

private theorem toEntries_eraseIdx (kvs : List (Int × Nat)) (i : Nat)
    (h : i < (toEntries kvs).size) :
    (toEntries kvs).eraseIdx i h = toEntries (kvs.eraseIdx i) := by
  apply Array.toList_inj.mp
  simp [toEntries, Array.toList_eraseIdx, map_eraseIdx]

/-! ## The heap-append kit (symbolic-address algebra, §10c)

The in-loop cells live at length-dependent addresses past the nine
concrete front cells, so their reads/writes are discharged by this
small append algebra instead of definitional reduction. -/

private theorem lookup_append_left {h₁ h₂ : Heap} {l : Loc} {c : HeapCell}
    (h : Heap.lookup h₁ l = some c) :
    Heap.lookup (h₁ ++ h₂) l = some c := by
  induction h₁ with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup, List.cons_append] at h ⊢
      cases hb : (k == l) with
      | true => simpa [hb] using h
      | false =>
          rw [hb] at h
          simpa [hb] using ih h

private theorem lookup_append_right {h₁ h₂ : Heap} {l : Loc}
    (h : Heap.lookup h₁ l = none) :
    Heap.lookup (h₁ ++ h₂) l = Heap.lookup h₂ l := by
  induction h₁ with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup, List.cons_append] at h ⊢
      cases hb : (k == l) with
      | true => simp [hb] at h
      | false =>
          rw [hb] at h
          simpa [hb] using ih h

private theorem set_append_right {h₁ h₂ : Heap} {l : Loc} {c : HeapCell}
    (h : Heap.lookup h₁ l = none) :
    Heap.set (h₁ ++ h₂) l c = h₁ ++ Heap.set h₂ l c := by
  induction h₁ with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup] at h
      cases hb : (k == l) with
      | true => simp [hb] at h
      | false =>
          rw [hb] at h
          simp only [List.cons_append, Heap.set, hb, Bool.false_eq_true,
            if_false]
          exact congrArg _ (ih h)

private theorem set_fresh {h : Heap} {l : Loc} {c : HeapCell}
    (hmiss : Heap.lookup h l = none) :
    Heap.set h l c = h ++ [(l, c)] := by
  induction h with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup] at hmiss
      cases hb : (k == l) with
      | true => simp [hb] at hmiss
      | false =>
          rw [hb] at hmiss
          simp only [Heap.set, hb, Bool.false_eq_true, if_false,
            List.cons_append]
          exact congrArg _ (ih hmiss)

private theorem base_beq_false {a b : Nat} (h : a ≠ b) :
    ((Loc.base ⟨a⟩ : Loc) == Loc.base ⟨b⟩) = false :=
  beq_false_of_ne (by simp [h])

private theorem lookup_cons_ne {k : Loc} {c : HeapCell} {h : Heap} {l : Loc}
    (hne : (k == l) = false) :
    Heap.lookup ((k, c) :: h) l = Heap.lookup h l := by
  simp [Heap.lookup, hne]

private theorem set_cons_ne {k : Loc} {c₀ : HeapCell} {h : Heap} {l : Loc}
    {c : HeapCell} (hne : (k == l) = false) :
    Heap.set ((k, c₀) :: h) l c = (k, c₀) :: Heap.set h l c := by
  simp [Heap.set, hne]

/-! ## The pure counts layer: `bump`, `countsList`, and the max fold -/

/-- One word lands in the counts list: increment the first occurrence
of the key, or append `(v, 1)` — first-occurrence insertion order,
matching the machine's `mapAssign`. -/
private def bump : List (Int × Nat) → Int → List (Int × Nat)
  | [], v => [(v, 1)]
  | (k, c) :: rest, v =>
      if k = v then (k, c + 1) :: rest else (k, c) :: bump rest v

/-- The counts list after processing `ws`, in first-occurrence
insertion order — the abstract content of the map data cell. -/
private def countsList (ws : List Int) : List (Int × Nat) :=
  ws.foldl bump []

/-- What the machine's write computes is `bump`: the value written is
`counts[w] + 1` at the first occurrence (or `0 + 1` fresh). -/
private theorem setk_cnt_succ :
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

private theorem countsList_append_word (p : List Int) (w : Int) :
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

private theorem cnt_countsList' (ws : List Int) (x : Int) :
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

private theorem countsList_key_mem (ws : List Int) :
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
private def maxOf (l : List Nat) : Nat := l.foldr max 0

private theorem maxOf_nil : maxOf [] = 0 := rfl

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
private theorem maxOf_eraseIdx :
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

private theorem mult_le_maxMult {ws : List Int} {v : Int} (h : v ∈ ws) :
    multiplicity v ws ≤ maxMultiplicity ws :=
  le_foldl_max (f := fun v => multiplicity v ws) ws 0 h

private theorem maxMult_le {ws : List Int} {B : Nat}
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
private theorem maxOf_countsList (ws : List Int) :
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
private theorem countsList_val_le (ws : List Int) {p : Int × Nat}
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

/-! ## Machine-layer configurations

Transcribed from the machine (probe-verified against a concrete run;
every raw segment below re-checks the transcription by `rfl`). Address
layout at the canonical placement (`base = 1`, `na = 2`): 0 =
`$callres`, 1 = the words backing array, 2 = the parameter `words`
(the handle), 3 = `$res0`, 4 = `$c0`, 5 = the map DATA cell, 6 =
`counts`, 7 = `i`, 8 = `$forFirst` — then the SYMBOLIC region: two
fresh `$c1`/`$c2` cells per counting iteration (9 + 2k), `best` at
`9 + 2·len`, one fresh `c` value cell per range iteration. -/

private abbrev tU64 : Ty := .int .uint64
private abbrev tMap : Ty := .map tU64 tU64

private abbrev wcCountBody : Stmt :=
  .block
    #[]
    #[.seqn
        #[.initialization { id := "$c1", typ := tMap },
          .assign (.var "$c1") (.var "counts")],
      .seqn
        #[.initialization { id := "$c2", typ := tU64 },
          .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))],
      .mapAssign (.var "$c1") (.var "$c2")
        (.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
          (.intLit 1 .uint64))
        tU64 tU64]

private abbrev wcWhileBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i")
          (.length (.var "words") (some (.slice tU64))))
        (.seqn #[])
        .breakStmt,
      wcCountBody]

private abbrev wcRangeBody : Stmt :=
  .block
    #[]
    #[.ifThenElse (.greaterCmp (.var "c") (.var "best"))
        (.block
          #[]
          #[.seqn #[.assign (.var "best") (.var "c")]])
        (.seqn #[])]

private abbrev wcMapRangeStmt : Stmt :=
  .mapRange none (some "c") (.var "counts") tU64 tU64 wcRangeBody

private abbrev bestSeqn : Stmt :=
  .seqn
    #[.initialization { id := "best", typ := tU64 },
      .assign (.var "best") (.intLit 0 .uint64)]

private abbrev retSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "best"), .returnStmt]

private abbrev asgnC1 : Stmt := .assign (.var "$c1") (.var "counts")
private abbrev seqnC2 : Stmt :=
  .seqn
    #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))]
private abbrev mapAsgnStmt : Stmt :=
  .mapAssign (.var "$c1") (.var "$c2")
    (.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64))
    tU64 tU64

/-! ### Environments and continuations -/

private def sc0 : Scope := [("$res0", .base ⟨3⟩), ("words", .base ⟨2⟩)]
private def sc1 : Scope := [("counts", .base ⟨6⟩), ("$c0", .base ⟨4⟩)]
private def envR0 : LocalEnv := [sc1, sc0]
private def envB : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)], sc1, sc0]
private def envB1 : LocalEnv := [[("i", .base ⟨7⟩)], sc1, sc0]
private def env2 : LocalEnv := [] :: envB
private def env3 : LocalEnv := [] :: env2
private def u1Env (na : Nat) : LocalEnv := [("$c1", .base ⟨na⟩)] :: env2
private def uEnv (na : Nat) : LocalEnv :=
  [("$c2", .base ⟨na + 1⟩), ("$c1", .base ⟨na⟩)] :: env2

private def frameK : Cont :=
  .frame [(.chain [], [.ref "$callres"])] [[("$callres", .base ⟨0⟩)]]
    [.base ⟨3⟩] [] .stop false
private def tailB : Cont :=
  .seq [] envB (.seq [] envB1
    (.seq [bestSeqn, wcMapRangeStmt, retSeqn] envR0 frameK))
/-- The counting-loop head configuration. -/
private def headC : Config :=
  .exec (.while (.boolLit true) wcWhileBody) envB tailB
private def loopKC : Cont := .loop (.boolLit true) wcWhileBody envB tailB
private def bodyTail : Cont := .seq [wcCountBody] env2 loopKC
/-- The exit test's delivery continuation (segment split point). -/
private def cmpContC : Cont := .ifK (.seqn #[]) .breakStmt env2 bodyTail
/-- The `len(words)` apply point inside the exit test. -/
private def lenK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] env2
    (.strictK .lessCmp [.int iv .int] [] env2 cmpContC)
private def postBodyK : Cont := .seq [] env2 loopKC

/-! ### Heap cells and the phase-C state family -/

private abbrev u64cell (v : Int) : HeapCell :=
  ⟨some tU64, .int v .uint64⟩
private abbrev intcell (v : Int) : HeapCell :=
  ⟨some (.int .int), .int v .int⟩
private abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
private abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
private abbrev handleCell (n : Nat) : HeapCell :=
  ⟨some (.slice tU64), .slice ⟨some (.base ⟨1⟩), 0, n, n⟩⟩
private abbrev sliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨1⟩), 0, n, n⟩
private abbrev mhCell : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨5⟩)⟩⟩
private abbrev mdCell (kvs : List (Int × Nat)) : HeapCell :=
  ⟨none, .mapData (toEntries kvs)⟩

/-- The nine concrete front cells during the counting loop. -/
private def frontC (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell 0), (.base ⟨1⟩, arrCell L ws),
   (.base ⟨2⟩, handleCell L), (.base ⟨3⟩, u64cell 0),
   (.base ⟨4⟩, mhCell), (.base ⟨5⟩, mdCell kvs),
   (.base ⟨6⟩, mhCell), (.base ⟨7⟩, intcell iv), (.base ⟨8⟩, bcell ff)]

/-- The phase-C state: concrete front + the symbolic dead-cell tail. -/
private def σC (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (iv : Int) (ff : Bool) (dead : Heap) (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontC L ws kvs iv ff ++ dead, nextAddr := na }

/-! ### Generic single-step glue -/

private theorem stepFnIter_one {σ : ExecState} {c : Config} {ch : Choices}
    {r : Config × ExecState × Choices}
    (h : stepFn σ c ch = .ok r) : stepFnIter 1 σ c ch = .ok r := by
  obtain ⟨c', σ', ch'⟩ := r
  simp [stepFnIter, h, Bind.bind, Except.bind]

/-- The strict-apply machine step, conditioned on the op fact. -/
private theorem stepFn_strict_apply {σ σ' : ExecState} {op : StrictOp}
    {done : List GoValue} {v out : GoValue} {env : LocalEnv} {k : Cont}
    {ch : Choices}
    (h : applyStrictOp σ op (v :: done).reverse = .ok (out, σ')) :
    stepFn σ (.retV v (.strictK op done [] env k)) ch
      = .ok (.retV out k, σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- The phase-2 store machine step, conditioned on the store fact. -/
private theorem stepFn_store_step {σ σ' : ExecState} {r : TargetRef}
    {val : GoValue} {rs : List TargetRef} {vs : List GoValue} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : storeTarget σ r val = .ok σ') :
    stepFn σ (.next (.storeK (r :: rs) (val :: vs) body env k)) ch
      = .ok (.next (.storeK rs vs body env k), σ', ch) := by
  simp only [stepFn]
  rw [h]
  rfl

/-- A plain-variable store target is a `storeLoc` at its cell. -/
private theorem storeTarget_addr {σ : ExecState} {a : Addr} {ty : Ty}
    {old v v' : GoValue}
    (hlook : Heap.lookup σ.heap (.base a) = some ⟨some ty, old⟩)
    (hnorm : normalizeValueForTy σ ty v = .ok v') :
    storeTarget σ (.chain (.addr (.base a)) [] []) v
      = .ok { σ with heap := Heap.set σ.heap (.base a) ⟨some ty, v'⟩ } := by
  simp only [storeTarget, resolveChain, valueAsLoc, Bind.bind, Except.bind,
    pure, Except.pure, storeLoc, hlook, hnorm]

/-- The variable-read step at a symbolic heap address, conditioned on
the env binding and the cell lookup. -/
private theorem stepFn_var {σ : ExecState} {x : String} {env : LocalEnv}
    {a : Addr} {k : Cont} {ch : Choices} {c : HeapCell}
    (henv : LocalEnv.lookup env x = some (.base a))
    (hlook : Heap.lookup σ.heap (.base a) = some c) :
    stepFn σ (.evalE (.var x) env k) ch = .ok (.retV c.value k, σ, ch) := by
  simp only [stepFn, henv, loadLoc, hlook, Bind.bind, Except.bind, pure,
    Except.pure]

/-- The `initialization` step under its governing sequence: allocate the
zero value at the CURRENT `nextAddr` (symbolic in-loop), declare. -/
private theorem stepFn_init_seq {σ : ExecState} {p : Param}
    {rest : List Stmt} {env : LocalEnv} {k : Cont} {ch : Choices}
    {v : GoValue}
    (hdef : defaultValue σ p.typ = .ok v) :
    stepFn σ (.exec (.initialization p) env (.seq rest env k)) ch
      = .ok (.next (.seq rest (env.declare p.id (.base ⟨σ.nextAddr⟩)) k),
          { σ with heap := (Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some p.typ, v⟩), nextAddr := σ.nextAddr + 1 }, ch) := by
  simp only [stepFn]
  rw [if_pos trivial]
  simp only [hdef, Bind.bind, Except.bind, pure, Except.pure,
    ExecState.alloc, ExecState.freshLoc]

/-- The `mapAssign` wide-op apply step, conditioned on the
`mapAssignValue` fact. -/
private theorem stepFn_mapAssign_apply {σ σ' : ExecState}
    {b kv vv : GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : mapAssignValue σ tU64 tU64 b kv vv = .ok σ') :
    stepFn σ (.retV vv (.stmtOpK (.mapAssign tU64 tU64) 0 [kv, b] [] env k))
      ch
      = .ok (.next k, σ', ch) := by
  simp only [stepFn, applyStmtOp, applyStmtOpCore, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, h, Bind.bind,
    Except.bind, pure, Except.pure]

/-- The `mapRangeK` snapshot step, conditioned on the snapshot fact. -/
private theorem stepFn_snapshot {σ : ExecState} {v : GoValue}
    {entries : Array (GoValue × GoValue)} {body : Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices}
    (h : mapRangeSnapshotEntries σ tU64 tU64 v = .ok entries) :
    stepFn σ (.retV v (.mapRangeK none (some "c") tU64 tU64 body env k)) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 body entries env k),
          σ, ch) := by
  simp only [stepFn, h, Bind.bind, Except.bind, pure, Except.pure]

/-- **The choice-pick step** (§10b): at a nonempty snapshot, ONE choice
is consumed (`idx < size` from `Choices.consume`'s `% bound` contract),
the picked entry's VALUE cell is freshly allocated at the current
`nextAddr`, and the entry is erased. -/
private theorem stepFn_pick {σ : ExecState} {rem : List (Int × Nat)}
    {idx : Nat} {ch ch' : Choices} {body : Stmt} {env : LocalEnv} {k : Cont}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length)
    {p : Int × Nat} (hp : rem[idx]? = some p)
    (hv : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int)) :
    stepFn σ
      (.next (.mapIterK none (some "c") tU64 tU64 body (toEntries rem) env k))
      ch
      = .ok (.exec body (env.pushScope.declare "c" (.base ⟨σ.nextAddr⟩))
          (.mapIterK none (some "c") tU64 tU64 body
            (toEntries (rem.eraseIdx idx)) env k),
        { σ with
            heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩)
              ⟨some tU64, .int (p.2 : Int) .uint64⟩,
            nextAddr := σ.nextAddr + 1 },
        ch') := by
  have hne : (toEntries rem).isEmpty = false := by
    cases rem with
    | nil => cases hidx
    | cons q rest => rfl
  have hsz : (toEntries rem).size = rem.length := toEntries_size rem
  have hget : (toEntries rem)[idx]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) :=
    toEntries_getElem? rem idx hp
  have hidx' : idx < (toEntries rem).size := by rw [hsz]; exact hidx
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
    simp only [bindIterVars, Bind.bind, Except.bind, pure, Except.pure]
    rw [show normalizeValueForTy σ tU64 (.int (p.2 : Int) .uint64)
        = .ok (.int (p.2 : Int) .uint64) from by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        hv]]
    simp only [Bind.bind, Except.bind, pure, Except.pure, ExecState.alloc,
      ExecState.freshLoc, hsz, hconsume, toEntries_eraseIdx rem idx hidx']

/-! ## Entry and dispatch segments (`with_unfolding_all rfl` where every
step is address-concrete; conditioned glue at the data-dependent
points) -/

private def callK : Cont :=
  .callArgsK ⟨"maxCount"⟩ [(.chain [], [.ref "$callres"])] [] [] wcEnv .stop

/-- Entry A: driver start → the slice-expression apply point. 7 steps. -/
private theorem wc_entryA_raw (ws : List Int) (ch : Choices) :
    stepFnIter 7 (wcSeed ws 1 [] 2) (.exec (wcCall ws 1) wcEnv .stop) ch
      = .ok (.retV (.int (IntKind.normalize .int (ws.length : Int)) .int)
            (.strictK (.sliceExpr false) [.int 0 .int, .addr (.base ⟨1⟩)] []
              wcEnv callK),
          wcSeed ws 1 [] 2, ch) := by
  with_unfolding_all rfl

/-- Entry B: frame entry, `$c0`/`makeMap`/`counts`/`i`/`$forFirst`
setup → the counting-loop head at `nextAddr = 9`. 52 steps. -/
private theorem wc_entryB_raw (ws : List Int) (ch : Choices) :
    stepFnIter 52 (wcSeed ws 1 [] 2) (.retV (sliceH ws.length) callK) ch
      = .ok (headC, σC ws.length ws [] 0 true [] 9, ch) := by
  with_unfolding_all rfl

/-- First-pass dispatch: head with the flag up → the `len(words)` apply
point (the flag comes down; counters untouched). 25 steps. -/
private theorem wc_segA0_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 25 (σC L ws kvs iv true dead na) headC ch
      = .ok (.retV (sliceH L) (lenK iv), σC L ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → `i++`, then the
`len(words)` apply point. 29 steps. -/
private theorem wc_segA1_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 29 (σC L ws kvs iv false dead na) headC ch
      = .ok (.retV (sliceH L)
            (lenK (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σC L ws kvs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false dead na, ch) := by
  with_unfolding_all rfl

/-- The `<` apply after the length delivery: one step, the comparison
riding symbolically. -/
private theorem wc_cmp_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv jv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false dead na)
      (.retV (.int (L : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] env2 cmpContC)) ch
      = .ok (.retV (.bool (decide (jv < (L : Int)))) cmpContC,
          σC L ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-! ## The counting-iteration segments (§10c glue: the per-iteration
`$c1`/`$c2` cells live at the SYMBOLIC addresses `na`, `na + 1`) -/

private theorem lookup_frontC_none (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) {x : Nat} (hx : 9 ≤ x) :
    Heap.lookup (frontC L ws kvs iv ff) (.base ⟨x⟩) = none := by
  simp only [frontC, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

private theorem set_singleton_self {l : Loc} {c₀ c : HeapCell} :
    Heap.set [(l, c₀)] l c = [(l, c)] := by
  simp [Heap.set]

/-- Element read of the wrapped-uint64 backing array. -/
private theorem getElem?_mapU (l : List Int) (k : Nat) (hk : k < l.length) :
    (⟨l.map (fun v => .int v .uint64)⟩ : Array GoValue)[k]?
      = some (.int (l.getD k 0) .uint64) := by
  simp [List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk]

private def stK0 (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnv na) (.seq [] (uEnv na) postBodyK)
private def stK2 (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨5⟩)⟩] []
    (uEnv na) (.seq [] (uEnv na) postBodyK)
private def addK (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnv na) (stK2 na w)
private def mapGetK (na : Nat) (w : Int) : Cont :=
  .strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨5⟩)⟩] [] (uEnv na)
    (addK na w)

/-- C1: exit test true → the `$c1` initialization. 7 steps. -/
private theorem wc_segC1_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 7 (σC L ws kvs iv false tail na) (.retV (.bool true) cmpContC)
      ch
      = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3 postBodyK),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C2: `$c1` declared → its store point (`$c1 := counts` delivered). 6
steps. -/
private theorem wc_segC2_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σC L ws kvs iv false tail na)
      (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨5⟩)⟩] (.seqn #[]) (u1Env na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- The `.seqn`-splice step under a symbolic-address environment (the
`seqCont` env comparison does not kernel-reduce there — glue). -/
private theorem stepFn_seqn {σ : ExecState} {ss : Array Stmt}
    {env : LocalEnv} {rest : List Stmt} {k : Cont} {ch : Choices} :
    stepFn σ (.exec (.seqn ss) env (.seq rest env k)) ch
      = .ok (.next (.seq (ss.toList ++ rest) env k), σ, ch) := by
  simp only [stepFn, seqCont]
  rw [if_pos trivial]
  rfl

/-- One `.seq`-pop step (statement dispatch; no env comparison). -/
private theorem stepFn_seq_pop {σ : ExecState} {t : Stmt}
    {rest : List Stmt} {env : LocalEnv} {k : Cont} {ch : Choices} :
    stepFn σ (.next (.seq (t :: rest) env k)) ch
      = .ok (.exec t env (.seq rest env k), σ, ch) := rfl

/-- The empty-store drain step. -/
private theorem stepFn_storeK_nil {σ : ExecState} {body : Stmt}
    {env : LocalEnv} {k : Cont} {ch : Choices} :
    stepFn σ (.next (.storeK [] [] body env k)) ch
      = .ok (.exec body env k, σ, ch) := rfl

/-- C3 (composed from glue: two `.seqn` splices under the symbolic env):
`$c1` stored → the `$c2` initialization. 5 steps. -/
private theorem wc_segC3_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (u1Env na₀)
        (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK))) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tU64 }) (u1Env na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1Env na₀) postBodyK),
          σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := u1Env na₀)
    (k := .seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := u1Env na₀)
    (rest := [seqnC2, mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σC L ws kvs iv false tail na) (t := seqnC2)
    (rest := [mapAsgnStmt]) (env := u1Env na₀) (k := postBodyK) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn
    (σ := σC L ws kvs iv false tail na)
    (ss := #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))])
    (env := u1Env na₀) (rest := [mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σC L ws kvs iv false tail na)
    (t := .initialization { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1Env na₀) (k := postBodyK) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- C4: `$c2` declared → the `words[i]` read point. 8 steps. -/
private theorem wc_segC4_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 8 (σC L ws kvs iv false tail na)
      (.next (.seq [.assign (.var "$c2")
          (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
        (uEnv na₀) postBodyK)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [sliceH L] [] (uEnv na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                (.seqn #[]) (uEnv na₀)
                (.seq [mapAsgnStmt] (uEnv na₀) postBodyK))),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C5: element delivered → its store point. 1 step. -/
private theorem wc_segC5_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV w
        (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
          (.seqn #[]) (uEnv na₀) (.seq [mapAsgnStmt] (uEnv na₀) postBodyK)))
      ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
            (.seqn #[]) (uEnv na₀)
            (.seq [mapAsgnStmt] (uEnv na₀) postBodyK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C6 (composed): `$c2` stored → the `mapAssign` operand walk's first
`$c1` read. 4 steps. -/
private theorem wc_segC6_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (uEnv na₀)
        (.seq [mapAsgnStmt] (uEnv na₀) postBodyK))) ch
      = .ok (.evalE (.var "$c1") (uEnv na₀) (stK0 na₀),
          σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := uEnv na₀) (k := .seq [mapAsgnStmt] (uEnv na₀) postBodyK)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := uEnv na₀)
    (rest := [mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h3 : stepFnIter 2 (σC L ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [mapAsgnStmt]) (uEnv na₀)
        postBodyK)) ch
      = .ok (.evalE (.var "$c1") (uEnv na₀) (stK0 na₀),
          σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- C7: map handle delivered → the `$c2` operand read. 1 step. -/
private theorem wc_segC7_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨5⟩)⟩) (stK0 na₀)) ch
      = .ok (.evalE (.var "$c2") (uEnv na₀)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨5⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnv na₀) (.seq [] (uEnv na₀) postBodyK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C8: key delivered → the `mapGet`'s `$c1` read. 3 steps. -/
private theorem wc_segC8_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.retV (.int w .uint64)
        (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨5⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
            (.intLit 1 .uint64)]
          (uEnv na₀) (.seq [] (uEnv na₀) postBodyK))) ch
      = .ok (.evalE (.var "$c1") (uEnv na₀)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnv na₀)
              (addK na₀ w)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C9: `mapGet`'s handle delivered → its `$c2` read. 1 step. -/
private theorem wc_segC9_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨5⟩)⟩)
        (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnv na₀)
          (addK na₀ w))) ch
      = .ok (.evalE (.var "$c2") (uEnv na₀) (mapGetK na₀ w),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C10: the count delivered → the `+ 1` runs → the `mapAssign` apply
point. 3 steps. -/
private theorem wc_segC10_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w cv : Int) (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.retV (.int cv .uint64) (addK na₀ w)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
            (stK2 na₀ w),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C11: `mapAssign` applied → back to the loop head. 3 steps. -/
private theorem wc_segC11_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.next (.seq [] (uEnv na₀) postBodyK)) ch
      = .ok (headC, σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-! ## The composed counting iteration -/

private theorem take_succ_getD {ws : List Int} {i : Nat}
    (hi : i < ws.length) :
    ws.take (i + 1) = ws.take i ++ [ws.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem cnt_take_le {ws : List Int} {i : Nat} (w : Int) :
    cnt (countsList (ws.take i)) w ≤ i := by
  rw [cnt_countsList']
  simp only [multiplicity]
  have h1 : ((ws.take i).filter (· = w)).length ≤ (ws.take i).length :=
    List.length_filter_le _ _
  have h2 : (ws.take i).length ≤ i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  omega

private theorem getD_mem {xs : List Int} {k : Nat} (hk : k < xs.length) :
    xs.getD k 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact List.getElem_mem hk

private theorem lookup_singleton_self {l : Loc} {c : HeapCell} :
    Heap.lookup [(l, c)] l = some c := by
  simp [Heap.lookup]

/-- **One counting iteration** (exit test true at word `i`): the map
data cell advances from the counts of `ws.take i` to those of
`ws.take (i+1)`; two fresh dead cells land at `na`, `na + 1`. 53
steps. -/
private theorem wc_count_iter (ws : List Int) (i : Nat) (dead : Heap)
    (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 9 ≤ na)
    (hdead : ∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) :
    stepFnIter 53
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false dead na)
      (.retV (.bool true) cmpContC) ch
      = .ok (headC,
          σC ws.length ws (countsList (ws.take (i + 1))) (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCell),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hwmem : (ws.getD i 0) ∈ ws := getD_mem hi
  have hwr := hws (ws.getD i 0) hwmem
  have hwnorm : IntKind.normalize .uint64 (ws.getD i 0) = (ws.getD i 0) :=
    unorm_of_range hwr.1 hwr.2
  have hcnt_le : cnt (countsList (ws.take i)) (ws.getD i 0) ≤ i := cnt_take_le (ws.getD i 0)
  -- the σ₀ fresh-address fact
  have hσ0miss : Heap.lookup (frontC ws.length ws (countsList (ws.take i)) (i : Int) false ++ dead)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int) false hna)]
    exact hdead na (Nat.le_refl na)
  -- C1
  have hC1 := wc_segC1_raw ws.length ws (countsList (ws.take i)) (i : Int) dead na ch
  -- init $c1
  have hInit1 := stepFn_init_seq
    (σ := σC ws.length ws (countsList (ws.take i)) (i : Int) false dead na)
    (p := { id := "$c1", typ := tMap })
    (rest := [asgnC1, seqnC2, mapAsgnStmt]) (env := env3) (k := postBodyK)
    (ch := ch)
    (v := .map ⟨none⟩)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws (countsList (ws.take i)) (i : Int) false dead na).nextAddr = na from rfl,
    show (σC ws.length ws (countsList (ws.take i)) (i : Int) false dead na).heap
      = frontC ws.length ws (countsList (ws.take i)) (i : Int) false ++ dead from rfl,
    set_fresh hσ0miss, List.append_assoc] at hInit1
  have h1 := stepFnIter_chain hC1 (stepFnIter_one hInit1)
  -- C2 at tail₁ = dead ++ [(na, nil-map)]
  have hC2 := wc_segC2_raw ws.length ws (countsList (ws.take i)) (i : Int)
    (dead ++ [(.base ⟨na⟩, ⟨some tMap, .map ⟨none⟩⟩)]) na (na + 1) ch
  have h2 := stepFnIter_chain h1 hC2
  -- store $c1 := counts
  have htail1na : Heap.lookup
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ [(.base ⟨na⟩, ⟨some tMap, .map ⟨none⟩⟩)]) (na + 1)).heap
      (.base ⟨na⟩) = some ⟨some tMap, .map ⟨none⟩⟩ := by
    show Heap.lookup
      (frontC ws.length ws (countsList (ws.take i)) (i : Int) false
        ++ (dead ++ [(.base ⟨na⟩, ⟨some tMap, .map ⟨none⟩⟩)]))
      (.base ⟨na⟩) = some ⟨some tMap, .map ⟨none⟩⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int) false hna),
      lookup_append_right (hdead na (Nat.le_refl na))]
    exact lookup_singleton_self
  have hst1 := storeTarget_addr
    (σ := σC ws.length ws (countsList (ws.take i)) (i : Int) false
      (dead ++ [(.base ⟨na⟩, ⟨some tMap, .map ⟨none⟩⟩)]) (na + 1))
    (a := ⟨na⟩) (v := .map ⟨some (.base ⟨5⟩)⟩)
    (v' := .map ⟨some (.base ⟨5⟩)⟩) htail1na
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel])
  rw [show (σC ws.length ws (countsList (ws.take i)) (i : Int) false
      (dead ++ [(.base ⟨na⟩, ⟨some tMap, .map ⟨none⟩⟩)]) (na + 1)).heap
      = frontC ws.length ws (countsList (ws.take i)) (i : Int) false
        ++ (dead ++ [(.base ⟨na⟩, ⟨some tMap, .map ⟨none⟩⟩)]) from rfl,
    set_append_right (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int) false hna),
    set_append_right (hdead na (Nat.le_refl na)),
    set_singleton_self] at hst1
  have h3 := stepFnIter_chain h2 (stepFnIter_one (stepFn_store_step hst1))
  -- C3 at tail₂ = dead ++ [(na, map handle)]
  have hC3 := wc_segC3_raw ws.length ws (countsList (ws.take i)) (i : Int)
    (dead ++ [(.base ⟨na⟩, mhCell)]) na (na + 1) ch
  have h4 := stepFnIter_chain h3 hC3
  -- init $c2
  have hσ1miss : Heap.lookup
      (frontC ws.length ws (countsList (ws.take i)) (i : Int) false ++ (dead ++ [(.base ⟨na⟩, mhCell)]))
      (.base ⟨na + 1⟩) = none := by
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int) false (by omega)),
      lookup_append_right (hdead (na + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    rfl
  have hInit2 := stepFn_init_seq
    (σ := σC ws.length ws (countsList (ws.take i)) (i : Int) false (dead ++ [(.base ⟨na⟩, mhCell)])
      (na + 1))
    (p := { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1Env na) (k := postBodyK) (ch := ch)
    (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws (countsList (ws.take i)) (i : Int) false (dead ++ [(.base ⟨na⟩, mhCell)])
        (na + 1)).nextAddr = na + 1 from rfl,
    show (σC ws.length ws (countsList (ws.take i)) (i : Int) false (dead ++ [(.base ⟨na⟩, mhCell)])
        (na + 1)).heap
      = frontC ws.length ws (countsList (ws.take i)) (i : Int) false ++ (dead ++ [(.base ⟨na⟩, mhCell)])
      from rfl,
    set_fresh hσ1miss, List.append_assoc, List.append_assoc] at hInit2
  have h5 := stepFnIter_chain h4 (stepFnIter_one hInit2)
  -- C4 at tail₃ = dead ++ ([(na, mh)] ++ [(na+1, zero)])
  have hC4 := wc_segC4_raw ws.length ws (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
    na (na + 2) ch
  have h6 := stepFnIter_chain h5 hC4
  -- the words[i] read
  have hread : applyStrictOp
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
        (na + 2))
      .indexGet [sliceH ws.length, .int (i : Nat) .int]
      = .ok (.int (ws.getD i 0) .uint64, σC ws.length ws (countsList (ws.take i)) (i : Int) false
          (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
          (na + 2)) := by
    have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
        = some (.int (ws.getD i 0) .uint64) := by
      rw [Nat.zero_add, getElem?_mapU ws i hi]
    exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
      (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) rfl (Nat.le_refl ws.length) hi
      hget
  have h7 := stepFnIter_chain h6
    (stepFnIter_one (stepFn_strict_apply (done := [sliceH ws.length]) hread))
  -- C5
  have hC5 := wc_segC5_raw ws.length ws (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
    na (na + 2) (.int (ws.getD i 0) .uint64) ch
  have h8 := stepFnIter_chain h7 hC5
  -- store $c2 := (ws.getD i 0)
  have htail3na1 : Heap.lookup
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
        (na + 2)).heap
      (.base ⟨na + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws (countsList (ws.take i)) (i : Int) false
        ++ (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)])))
      (.base ⟨na + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int) false (by omega)),
      lookup_append_right (hdead (na + 1) (by omega)),
      List.singleton_append,
      lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
    exact lookup_singleton_self
  have hst2 := storeTarget_addr
    (σ := σC ws.length ws (countsList (ws.take i)) (i : Int) false
      (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
      (na + 2))
    (a := ⟨na + 1⟩) (v := .int (ws.getD i 0) .uint64)
    (v' := .int (ws.getD i 0) .uint64) htail3na1
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hwnorm]
      rfl)
  rw [show (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
        (na + 2)).heap
      = frontC ws.length ws (countsList (ws.take i)) (i : Int) false
        ++ (dead ++ ([(.base ⟨na⟩, mhCell)] ++ [(.base ⟨na + 1⟩, u64cell 0)]))
      from rfl,
    set_append_right
      (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int) false (by omega)),
    set_append_right (hdead (na + 1) (by omega)),
    set_append_right (show Heap.lookup [(.base ⟨na⟩, mhCell)]
        (.base ⟨na + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
      rfl),
    set_singleton_self] at hst2
  have h9 := stepFnIter_chain h8 (stepFnIter_one (stepFn_store_step hst2))
  -- tail from here on: T = dead ++ ([(na, map handle)] ++ [(na+1, w)])
  have hlkc1 : Heap.lookup
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) (na + 2)).heap
      (.base ⟨na⟩) = some mhCell := by
    show Heap.lookup
      (frontC ws.length ws (countsList (ws.take i)) (i : Int) false
        ++ (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])))
      (.base ⟨na⟩) = some mhCell
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int)
          false hna),
      lookup_append_right (hdead na (Nat.le_refl na))]
    exact lookup_append_left lookup_singleton_self
  have hlkc2 : Heap.lookup
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) (na + 2)).heap
      (.base ⟨na + 1⟩) = some (u64cell (ws.getD i 0)) := by
    show Heap.lookup
      (frontC ws.length ws (countsList (ws.take i)) (i : Int) false
        ++ (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])))
      (.base ⟨na + 1⟩) = some (u64cell (ws.getD i 0))
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws (countsList (ws.take i)) (i : Int)
          false (by omega)),
      lookup_append_right (hdead (na + 1) (by omega)),
      lookup_append_right (show Heap.lookup [(.base ⟨na⟩, mhCell)]
          (.base ⟨na + 1⟩) = none from by
        rw [lookup_cons_ne (base_beq_false (by omega : na ≠ na + 1))]
        rfl)]
    exact lookup_singleton_self
  have hlk5 : Heap.lookup
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) (na + 2)).heap
      (.base ⟨5⟩)
      = some ⟨none, .mapData (toEntries (countsList (ws.take i)))⟩ := rfl
  -- C6 + the four operand reads + mapGet
  have h10 := stepFnIter_chain h9 (wc_segC6_raw ws.length ws
    (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)]
      ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) na (na + 2) ch)
  have h11 := stepFnIter_chain h10 (stepFnIter_one
    (stepFn_var (x := "$c1") (env := uEnv na) (a := ⟨na⟩)
      (k := stK0 na) (ch := ch) rfl hlkc1))
  have h12 := stepFnIter_chain h11 (wc_segC7_raw ws.length ws
    (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)]
      ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) na (na + 2) ch)
  have h13 := stepFnIter_chain h12 (stepFnIter_one
    (stepFn_var (x := "$c2") (env := uEnv na) (a := ⟨na + 1⟩)
      (ch := ch) rfl hlkc2))
  have h14 := stepFnIter_chain h13 (wc_segC8_raw ws.length ws
    (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)]
      ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) na (na + 2)
    (ws.getD i 0) ch)
  have h15 := stepFnIter_chain h14 (stepFnIter_one
    (stepFn_var (x := "$c1") (env := uEnv na) (a := ⟨na⟩)
      (ch := ch) rfl hlkc1))
  have h16 := stepFnIter_chain h15 (wc_segC9_raw ws.length ws
    (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)]
      ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) na (na + 2)
    (ws.getD i 0) ch)
  have h17 := stepFnIter_chain h16 (stepFnIter_one
    (stepFn_var (x := "$c2") (env := uEnv na) (a := ⟨na + 1⟩)
      (ch := ch) rfl hlkc2))
  have h18 := stepFnIter_chain h17 (stepFnIter_one
    (stepFn_strict_apply (done := [.map ⟨some (.base ⟨5⟩)⟩])
      (applyStrictOp_mapGet (a := ⟨5⟩) (dty := none) hlk5 hwnorm)))
  have h19 := stepFnIter_chain h18 (wc_segC10_raw ws.length ws
    (countsList (ws.take i)) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)]
      ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) na (na + 2)
    (ws.getD i 0) (cnt (countsList (ws.take i)) (ws.getD i 0) : Int) ch)
  -- clean the wrapped `count + 1`
  have hcast : (cnt (countsList (ws.take i)) (ws.getD i 0) : Int) + 1
      = ((cnt (countsList (ws.take i)) (ws.getD i 0) + 1 : Nat) : Int) := by
    omega
  have hnorm1 : IntKind.normalize .uint64
      ((cnt (countsList (ws.take i)) (ws.getD i 0) + 1 : Nat) : Int)
      = ((cnt (countsList (ws.take i)) (ws.getD i 0) + 1 : Nat) : Int) := by
    refine unorm_of_range (by omega) ?_
    have : cnt (countsList (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
      omega
    exact_mod_cast this
  rw [hcast, hnorm1] at h19
  -- the mapAssign apply
  have hMA := mapAssignValue_toEntries (a := ⟨5⟩)
    (σ := σC ws.length ws (countsList (ws.take i)) (i : Int) false
      (dead ++ ([(.base ⟨na⟩, mhCell)]
        ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) (na + 2))
    (v := cnt (countsList (ws.take i)) (ws.getD i 0) + 1)
    hlk5 hwnorm hnorm1
  have hbump : setk (countsList (ws.take i)) (ws.getD i 0)
      (cnt (countsList (ws.take i)) (ws.getD i 0) + 1)
      = countsList (ws.take (i + 1)) := by
    rw [setk_cnt_succ, ← countsList_append_word, ← take_succ_getD hi]
  rw [hbump] at hMA
  rw [show Heap.set
      (σC ws.length ws (countsList (ws.take i)) (i : Int) false
        (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) (na + 2)).heap
      (.base ⟨5⟩)
      ⟨none, .mapData (toEntries (countsList (ws.take (i + 1))))⟩
      = frontC ws.length ws (countsList (ws.take (i + 1))) (i : Int) false
        ++ (dead ++ ([(.base ⟨na⟩, mhCell)]
          ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) from rfl] at hMA
  have h20 := stepFnIter_chain h19 (stepFnIter_one
    (stepFn_mapAssign_apply hMA))
  have h21 := stepFnIter_chain h20 (wc_segC11_raw ws.length ws
    (countsList (ws.take (i + 1))) (i : Int)
    (dead ++ ([(.base ⟨na⟩, mhCell)]
      ++ [(.base ⟨na + 1⟩, u64cell (ws.getD i 0))])) na (na + 2) ch)
  exact h21

/-! ## Exit of the counting loop → the range head -/

private def envRB (B : Nat) : LocalEnv := (("best", .base ⟨B⟩) :: sc1) :: [sc0]
private def kR (B : Nat) : Cont := .seq [retSeqn] (envRB B) frameK
/-- The range-loop head: the `mapIterK` pick point at snapshot `rem`. -/
private def rangeHead (B : Nat) (rem : List (Int × Nat)) : Config :=
  .next (.mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRB B) (kR B))

/-- X0: exit test false → break unwinding → the `best` initialization.
9 steps. -/
private theorem wc_segX0_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 9 (σC L ws kvs iv false tail na)
      (.retV (.bool false) cmpContC) ch
      = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0 frameK),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0b: `best` declared → its zeroing store point. 6 steps. -/
private theorem wc_segX0b_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σC L ws kvs iv false tail na)
      (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
        wcMapRangeStmt, retSeqn] (envRB B) frameK)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRB B)
            (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0c: `best` stored → the ranged map handle delivered at the
snapshot point. 5 steps (one `.seqn` splice glued). -/
private theorem wc_segX0c_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRB B)
        (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK))) ch
      = .ok (.retV (.map ⟨some (.base ⟨5⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
              (kR B)),
          σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := envRB B) (k := .seq [wcMapRangeStmt, retSeqn] (envRB B) frameK)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := envRB B)
    (rest := [wcMapRangeStmt, retSeqn]) (k := frameK) (ch := ch))
  have h3 : stepFnIter 3 (σC L ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [wcMapRangeStmt, retSeqn])
        (envRB B) frameK)) ch
      = .ok (.retV (.map ⟨some (.base ⟨5⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
              (kR B)),
          σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The counts-list range facts (keys are words; values are counts). -/
private theorem countsList_norm (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ p ∈ countsList ws, IntKind.normalize .uint64 p.1 = p.1
      ∧ IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) := by
  intro p hp
  have hkey : p.1 ∈ ws := by
    rcases countsList_key_mem ws [] p hp with h | h
    · exact h
    · cases h
  have hkr := hws p.1 hkey
  have hvle : p.2 ≤ ws.length := countsList_val_le ws hp
  refine ⟨unorm_of_range hkr.1 hkr.2, unorm_of_range (by omega) ?_⟩
  have : p.2 < 2 ^ 64 := by omega
  exact_mod_cast this

/-- **The counting loop**, by strong induction on the remaining word
count: from the exit-test delivery at word `i`, the run reaches the
RANGE HEAD over the snapshot of the full counts, with `best` zeroed at
address `na + 2·(L - i)`, within `84·(L-i) + 23` steps. -/
private theorem wc_count_loop (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), 9 ≤ na →
    (∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ (∀ x : Nat, na + 2 * n + 1 ≤ x →
          Heap.lookup tail (.base ⟨x⟩) = none)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (σC ws.length ws (countsList (ws.take i)) (i : Int) false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContC)
          ch
        = .ok (rangeHead (na + 2 * n) (countsList ws),
            σC ws.length ws (countsList ws) (ws.length : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi dead na hna hdead ch
    rcases Nat.lt_or_ge i ws.length with hlt | hge
    · -- iterate
      have hn1 : n = (n - 1) + 1 := by omega
      rw [show (decide ((i : Int) < (ws.length : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hIter := wc_count_iter ws i dead na ch hws hlen hlt hna hdead
      -- dispatch at i+1
      have hdead₂ : ∀ x : Nat, na + 2 ≤ x →
          Heap.lookup (dead ++ [(.base ⟨na⟩, mhCell),
            (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (.base ⟨x⟩)
          = none := by
        intro x hx
        rw [lookup_append_right (hdead x (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ x)),
          lookup_cons_ne (base_beq_false (by omega : na + 1 ≠ x))]
        rfl
      have hA1 := wc_segA1_raw ws.length ws (countsList (ws.take (i + 1)))
        (i : Int)
        (dead ++ [(.base ⟨na⟩, mhCell),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) ch
      rw [show (i : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63),
        inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63)] at hA1
      have hlen_apply : applyStrictOp
          (σC ws.length ws (countsList (ws.take (i + 1)))
            ((i + 1 : Nat) : Int) false
            (dead ++ [(.base ⟨na⟩, mhCell),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
          (.lengthOf (some (.slice tU64))) [sliceH ws.length]
          = .ok (.int (ws.length : Nat) .int,
              σC ws.length ws (countsList (ws.take (i + 1)))
                ((i + 1 : Nat) : Int) false
                (dead ++ [(.base ⟨na⟩, mhCell),
                  (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2)) :=
        applyStrictOp_len_slice (Nat.le_refl _)
      have hCmp := wc_cmp_raw ws.length ws (countsList (ws.take (i + 1)))
        ((i + 1 : Nat) : Int) ((i + 1 : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhCell),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) ch
      -- recurse
      obtain ⟨k, tail, hk, htail, hbest, hrun⟩ := ih (n - 1) (by omega)
        (i + 1) (by omega) (by omega)
        (dead ++ [(.base ⟨na⟩, mhCell),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2)
        (by omega) hdead₂ ch
      refine ⟨53 + 29 + 1 + 1 + k, tail, by omega, ?_, ?_, ?_⟩
      · intro x hx
        exact htail x (by omega)
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact hbest
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact stepFnIter_chain
          (stepFnIter_chain
            (stepFnIter_chain (stepFnIter_chain hIter hA1)
              (stepFnIter_one (stepFn_strict_apply (done := []) hlen_apply)))
            hCmp)
          hrun
    · -- exit: i = L
      have hiL : i = ws.length := by omega
      rw [hiL]
      rw [show (decide ((ws.length : Int) < (ws.length : Int))) = false from
        decide_eq_false (by omega)]
      -- X0
      have hX0 := wc_segX0_raw ws.length ws (countsList (ws.take ws.length))
        (ws.length : Int) dead na ch
      -- init best
      have hσmiss : Heap.lookup
          (frontC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            ++ dead) (.base ⟨na⟩) = none := by
        rw [lookup_append_right
          (lookup_frontC_none ws.length ws (countsList (ws.take ws.length))
            (ws.length : Int) false hna)]
        exact hdead na (Nat.le_refl na)
      have hInitB := stepFn_init_seq
        (σ := σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false dead
          na)
        (p := { id := "best", typ := tU64 })
        (rest := [.assign (.var "best") (.intLit 0 .uint64),
          wcMapRangeStmt, retSeqn])
        (env := envR0) (k := frameK) (ch := ch) (v := .int 0 .uint64)
        (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
      rw [show (σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            dead na).nextAddr = na from rfl,
        show (σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false dead
            na).heap
          = frontC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            ++ dead from rfl,
        set_fresh hσmiss, List.append_assoc] at hInitB
      have h1 := stepFnIter_chain hX0 (stepFnIter_one hInitB)
      -- X0b
      have hX0b := wc_segX0b_raw ws.length ws (countsList (ws.take ws.length))
        (ws.length : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na (na + 1) ch
      have h2 := stepFnIter_chain h1 hX0b
      -- store best := 0
      have hlkB : Heap.lookup
          (σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1)).heap
          (.base ⟨na⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
        show Heap.lookup
          (frontC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            ++ (dead ++ [(.base ⟨na⟩, u64cell 0)]))
          (.base ⟨na⟩) = some ⟨some tU64, .int 0 .uint64⟩
        rw [lookup_append_right
            (lookup_frontC_none ws.length ws (countsList (ws.take ws.length))
              (ws.length : Int) false hna),
          lookup_append_right (hdead na (Nat.le_refl na))]
        exact lookup_singleton_self
      have hstB := storeTarget_addr
        (σ := σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
          (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
        (a := ⟨na⟩) (v := .int 0 .uint64) (v' := .int 0 .uint64) hlkB
        (by simp [normalizeValueForTy, normalizeValueForTyFuel,
          typeResolutionFuel, IntKind.normalize, IntKind.bits?,
          IntKind.signed])
      rw [show (σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1)).heap
          = frontC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
            ++ (dead ++ [(.base ⟨na⟩, u64cell 0)]) from rfl,
        set_append_right
          (lookup_frontC_none ws.length ws (countsList (ws.take ws.length))
            (ws.length : Int) false hna),
        set_append_right (hdead na (Nat.le_refl na)),
        set_singleton_self] at hstB
      have h3 := stepFnIter_chain h2
        (stepFnIter_one (stepFn_store_step hstB))
      -- X0c
      have hX0c := wc_segX0c_raw ws.length ws (countsList (ws.take ws.length))
        (ws.length : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na (na + 1) ch
      have h4 := stepFnIter_chain h3 hX0c
      -- the snapshot
      have hsnap := snapshot_toEntries (a := ⟨5⟩) (dty := none)
        (σ := σC ws.length ws (countsList (ws.take ws.length)) (ws.length : Int) false
          (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1))
        (kvs := countsList ws)
        (by rw [List.take_of_length_le (Nat.le_refl ws.length)]; rfl)
        (countsList_norm ws hws hlen)
      have h5 := stepFnIter_chain h4 (stepFnIter_one (stepFn_snapshot
        (body := wcRangeBody) (env := envRB na) (k := kR na) hsnap))
      refine ⟨9 + 1 + 6 + 1 + 5 + 1, dead ++ [(.base ⟨na⟩, u64cell 0)],
        by omega, ?_, ?_, ?_⟩
      · intro x hx
        rw [lookup_append_right (hdead x (by omega)),
          lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
        rfl
      · rw [show na + 2 * n = na from by omega,
          lookup_append_right (hdead na (Nat.le_refl na))]
        exact lookup_singleton_self
      · rw [show na + 2 * n = na from by omega,
          show ws.take ws.length = ws from
            List.take_of_length_le (Nat.le_refl ws.length)]
        rw [show ws.take ws.length = ws from
          List.take_of_length_le (Nat.le_refl ws.length)] at h5
        exact h5

/-! ## The range loop (§10b): segments and the choice-pick induction -/

private theorem set_append_left {h₁ h₂ : Heap} {l : Loc} {c₀ c : HeapCell}
    (h : Heap.lookup h₁ l = some c₀) :
    Heap.set (h₁ ++ h₂) l c = Heap.set h₁ l c ++ h₂ := by
  induction h₁ with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨k, c'⟩ := p
      simp only [Heap.lookup] at h
      cases hb : (k == l) with
      | true => simp [Heap.set, hb]
      | false =>
          rw [hb] at h
          simp only [List.cons_append, Heap.set, hb, Bool.false_eq_true,
            if_false]
          exact congrArg _ (ih h)

/-- `Choices.consume`'s `% bound` contract: the pick is in range. -/
private theorem consume_lt (ch : Choices) {n : Nat} (hn : 0 < n) :
    (Choices.consume ch n).1 < n := by
  cases ch with
  | nil => simpa [Choices.consume] using hn
  | cons c rest =>
      simp only [Choices.consume]
      have : max 1 n = n := by omega
      rw [this]
      exact Nat.mod_lt _ hn

private theorem mem_of_mem_eraseIdx {α : Type} :
    ∀ {l : List α} {i : Nat} {a : α}, a ∈ l.eraseIdx i → a ∈ l := by
  intro l
  induction l with
  | nil => intro i a h; cases h
  | cons x rest ih =>
      intro i a h
      cases i with
      | zero =>
          rw [List.eraseIdx_cons_zero] at h
          exact List.mem_cons.mpr (.inr h)
      | succ n =>
          rw [List.eraseIdx_cons_succ] at h
          rcases List.mem_cons.mp h with h | h
          · exact List.mem_cons.mpr (.inl h)
          · exact List.mem_cons.mpr (.inr (ih h))

/-! ### Range-body configurations -/

private def envIter (B na : Nat) : LocalEnv :=
  [("c", .base ⟨na⟩)] :: envRB B
private def envIf (B na : Nat) : LocalEnv := [] :: envIter B na
private def thenBlk : Stmt :=
  .block #[] #[.seqn #[.assign (.var "best") (.var "c")]]
private def iterK (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRB B) (kR B)
private def ifKR (B na : Nat) (rem : List (Int × Nat)) : Cont :=
  .ifK thenBlk (.seqn #[]) (envIf B na)
    (.seq [] (envIf B na) (iterK B rem))
private def env4 (B na : Nat) : LocalEnv := [] :: envIf B na
private def storeBestK (B na : Nat) (rem : List (Int × Nat)) : Cont :=
  .seq [] (env4 B na) (.seq [] (envIf B na) (iterK B rem))

/-- R1: body entry → the `c` read of the comparison. 4 steps. -/
private theorem wc_segR1_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σC L ws kvs iv false tail na)
      (.exec wcRangeBody (envIter B na₀) (iterK B rem)) ch
      = .ok (.evalE (.var "c") (envIf B na₀)
            (.strictK .greaterCmp [] [.var "best"] (envIf B na₀)
              (ifKR B na₀ rem)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- R2: `c` delivered → the `best` read. 1 step. -/
private theorem wc_segR2_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (cv : GoValue) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV cv
        (.strictK .greaterCmp [] [.var "best"] (envIf B na₀)
          (ifKR B na₀ rem))) ch
      = .ok (.evalE (.var "best") (envIf B na₀)
            (.strictK .greaterCmp [cv] [] (envIf B na₀) (ifKR B na₀ rem)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- R3: `best` delivered → the `>` apply, riding symbolically. 1
step. -/
private theorem wc_segR3_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (cv bv : Int) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV (.int bv .uint64)
        (.strictK .greaterCmp [.int cv .uint64] [] (envIf B na₀)
          (ifKR B na₀ rem))) ch
      = .ok (.retV (.bool (decide (bv < cv))) (ifKR B na₀ rem),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- R4 (then branch, part a): the comparison true → the inner `.seqn`
splice point. 3 steps. -/
private theorem wc_segR4a_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.retV (.bool true) (ifKR B na₀ rem)) ch
      = .ok (.exec (.seqn #[.assign (.var "best") (.var "c")]) (env4 B na₀)
            (.seq [] (env4 B na₀) (.seq [] (envIf B na₀) (iterK B rem))),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- R4 (then branch, part b): assign dispatch → the `c` read of the
store. 4 steps. -/
private theorem wc_segR4b_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σC L ws kvs iv false tail na)
      (.next (.seq [.assign (.var "best") (.var "c")] (env4 B na₀)
        (.seq [] (envIf B na₀) (iterK B rem)))) ch
      = .ok (.evalE (.var "c") (env4 B na₀)
            (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
              (.seqn #[]) (env4 B na₀) (storeBestK B na₀ rem)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- R4 (then branch, part c): the store value delivered → the store
point. 1 step. -/
private theorem wc_segR4c_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (cv : GoValue) (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV cv
        (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
          (.seqn #[]) (env4 B na₀) (storeBestK B na₀ rem))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []] [cv]
            (.seqn #[]) (env4 B na₀) (storeBestK B na₀ rem)),
          σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- R5: `best` stored → the next pick point. 4 steps (one `.seqn`
splice glued). -/
private theorem wc_segR5_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σC L ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (env4 B na₀)
        (storeBestK B na₀ rem))) ch
      = .ok (rangeHead B rem, σC L ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σC L ws kvs iv false tail na) (body := .seqn #[])
    (env := env4 B na₀) (k := storeBestK B na₀ rem) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := env4 B na₀)
    (rest := []) (k := .seq [] (envIf B na₀) (iterK B rem)) (ch := ch))
  have h3 : stepFnIter 2 (σC L ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (env4 B na₀)
        (.seq [] (envIf B na₀) (iterK B rem)))) ch
      = .ok (rangeHead B rem, σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- R4' (else branch): the comparison false → the next pick point. 3
steps (one `.seqn` splice glued). -/
private theorem wc_segR4e_raw (L : Nat) (ws : List Int)
    (kvs rem : List (Int × Nat)) (iv : Int) (tail : Heap) (B na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 3 (σC L ws kvs iv false tail na)
      (.retV (.bool false) (ifKR B na₀ rem)) ch
      = .ok (rangeHead B rem, σC L ws kvs iv false tail na, ch) := by
  have h1 : stepFnIter 1 (σC L ws kvs iv false tail na)
      (.retV (.bool false) (ifKR B na₀ rem)) ch
      = .ok (.exec (.seqn #[]) (envIf B na₀)
            (.seq [] (envIf B na₀) (iterK B rem)),
          σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := envIf B na₀)
    (rest := []) (k := iterK B rem) (ch := ch))
  have h3 : stepFnIter 1 (σC L ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (envIf B na₀)
        (iterK B rem))) ch
      = .ok (rangeHead B rem, σC L ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The empty-snapshot drain: no choice consumed, the loop exits. 1
step. -/
private theorem wc_segRexit_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σC L ws kvs iv false tail na) (rangeHead B []) ch
      = .ok (.next (kR B), σC L ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-! ### The §10b choice-pick induction -/

/-- **The range loop, at every choice stream** — induction on the
snapshot size, ∀ remaining sub-list, ∀ accumulator `bv` with the
max-fold invariant, ∀ choices: the pick is destructured through
`Choices.consume` (`idx < size` from its `% bound` contract), the body
re-establishes the invariant at `remaining.eraseIdx idx` (the
pick-and-erase law `maxOf_eraseIdx`), and the loop exits with `best`
holding `max bv (maxOf remaining)` — an ORDER-INDEPENDENT value, which
is the §10b teaching point. -/
private theorem wc_range_loop (ws : List Int) (kvs : List (Int × Nat)) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ ws.length) → ws.length < 2 ^ 63 → bv ≤ ws.length →
    9 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    (∀ x : Nat, na ≤ x → Heap.lookup tail (.base ⟨x⟩) = none) →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ (∀ x : Nat, na' ≤ x → Heap.lookup tail' (.base ⟨x⟩) = none)
      ∧ stepFnIter k (σC ws.length ws kvs (ws.length : Int) false tail na)
          (rangeHead B rem) ch
        = .ok (.next (kR B),
            σC ws.length ws kvs (ws.length : Int) false tail' na', ch') := by
  intro m
  induction m with
  | zero =>
      intro rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
      have hnil : rem = [] := List.eq_nil_of_length_eq_zero hm
      subst hnil
      refine ⟨1, ch, tail, na, by omega, Nat.le_refl na, ?_, htail, ?_⟩
      · simpa [maxOf_nil] using hbest
      · exact wc_segRexit_raw ws.length ws kvs (ws.length : Int) tail B na ch
  | succ m ih =>
      intro rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
      -- destructure the pick
      rcases hcons : Choices.consume ch rem.length with ⟨idx, ch₂⟩
      have hidx : idx < rem.length := by
        have := consume_lt ch (show 0 < rem.length by omega)
        rw [hcons] at this
        exact this
      obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
        ⟨_, List.getElem?_eq_getElem hidx⟩
      have hpmem : p ∈ rem := by
        obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.mp hp
        exact h2 ▸ List.getElem_mem h1
      have hpc : p.2 ≤ ws.length := hrem p hpmem
      have hvnorm : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) := by
        refine unorm_of_range (by omega) ?_
        have : p.2 < 2 ^ 64 := by omega
        exact_mod_cast this
      -- the pick step
      have hmiss : Heap.lookup
          (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
          (.base ⟨na⟩) = none := by
        rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
          (ws.length : Int) false (by omega))]
        exact htail na (Nat.le_refl na)
      have hPick := stepFn_pick
        (σ := σC ws.length ws kvs (ws.length : Int) false tail na)
        (body := wcRangeBody) (env := envRB B) (k := kR B)
        hcons hidx hp hvnorm
      rw [show (σC ws.length ws kvs (ws.length : Int) false tail
            na).nextAddr = na from rfl,
        show (σC ws.length ws kvs (ws.length : Int) false tail na).heap
          = frontC ws.length ws kvs (ws.length : Int) false ++ tail
          from rfl,
        set_fresh hmiss, List.append_assoc] at hPick
      have h1 := stepFnIter_one hPick
      -- the body prefix to the comparison delivery
      have hR1 := wc_segR1_raw ws.length ws kvs (rem.eraseIdx idx)
        (ws.length : Int)
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        B na (na + 1) ch₂
      have h2 := stepFnIter_chain h1 hR1
      have hlkc : Heap.lookup
          (σC ws.length ws kvs (ws.length : Int) false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1)).heap
          (.base ⟨na⟩) = some ⟨some tU64, .int (p.2 : Int) .uint64⟩ := by
        show Heap.lookup
          (frontC ws.length ws kvs (ws.length : Int) false
            ++ (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)]))
          (.base ⟨na⟩) = some ⟨some tU64, .int (p.2 : Int) .uint64⟩
        rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
            (ws.length : Int) false (by omega)),
          lookup_append_right (htail na (Nat.le_refl na))]
        exact lookup_singleton_self
      have hlkb : Heap.lookup
          (σC ws.length ws kvs (ws.length : Int) false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1)).heap
          (.base ⟨B⟩) = some (u64cell (bv : Int)) := by
        show Heap.lookup
          (frontC ws.length ws kvs (ws.length : Int) false
            ++ (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)]))
          (.base ⟨B⟩) = some (u64cell (bv : Int))
        rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
            (ws.length : Int) false hB)]
        exact lookup_append_left hbest
      have h3 := stepFnIter_chain h2 (stepFnIter_one
        (stepFn_var (x := "c") (env := envIf B na) (a := ⟨na⟩)
          (ch := ch₂) rfl hlkc))
      have hR2 := wc_segR2_raw ws.length ws kvs (rem.eraseIdx idx)
        (ws.length : Int)
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        B na (na + 1) (.int (p.2 : Int) .uint64) ch₂
      have h4 := stepFnIter_chain h3 hR2
      have h5 := stepFnIter_chain h4 (stepFnIter_one
        (stepFn_var (x := "best") (env := envIf B na) (a := ⟨B⟩)
          (ch := ch₂) rfl hlkb))
      have hR3 := wc_segR3_raw ws.length ws kvs (rem.eraseIdx idx)
        (ws.length : Int)
        (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
        B na (na + 1) (p.2 : Int) (bv : Int) ch₂
      have h6 := stepFnIter_chain h5 hR3
      -- the pick-and-erase law instances
      have hgetbang : (rem.map Prod.snd)[idx]! = p.2 := by
        have hmap : (rem.map Prod.snd)[idx]? = some p.2 := by
          simp [List.getElem?_map, hp]
        simp [List.getElem!_eq_getElem?_getD, hmap]
      have hmaxsplit : maxOf (rem.map Prod.snd)
          = max p.2 (maxOf ((rem.eraseIdx idx).map Prod.snd)) := by
        rw [← maxOf_eraseIdx (rem.map Prod.snd) idx
            (by simpa using hidx), hgetbang, map_eraseIdx]
      have hlenerase : (rem.eraseIdx idx).length = m := by
        rw [List.length_eraseIdx_of_lt hidx]
        omega
      have hremerase : ∀ q ∈ rem.eraseIdx idx, q.2 ≤ ws.length :=
        fun q hq => hrem q (mem_of_mem_eraseIdx hq)
      by_cases hcmp : bv < p.2
      · -- the branch that improves `best`
        rw [show (decide ((bv : Int) < (p.2 : Int))) = true from
          decide_eq_true (by exact_mod_cast hcmp)] at h6
        have hR4a := wc_segR4a_raw ws.length ws kvs (rem.eraseIdx idx)
          (ws.length : Int)
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) ch₂
        have h7 := stepFnIter_chain h6 hR4a
        have h8 := stepFnIter_chain h7 (stepFnIter_one (stepFn_seqn
          (σ := σC ws.length ws kvs (ws.length : Int) false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (ss := #[.assign (.var "best") (.var "c")]) (env := env4 B na)
          (rest := []) (k := .seq [] (envIf B na)
            (iterK B (rem.eraseIdx idx))) (ch := ch₂)))
        have hR4b := wc_segR4b_raw ws.length ws kvs (rem.eraseIdx idx)
          (ws.length : Int)
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) ch₂
        have h9 := stepFnIter_chain h8 hR4b
        have h10 := stepFnIter_chain h9 (stepFnIter_one
          (stepFn_var (x := "c") (env := env4 B na) (a := ⟨na⟩)
            (ch := ch₂) rfl hlkc))
        have hR4c := wc_segR4c_raw ws.length ws kvs (rem.eraseIdx idx)
          (ws.length : Int)
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) (.int (p.2 : Int) .uint64) ch₂
        have h11 := stepFnIter_chain h10 hR4c
        -- the store to `best`
        have hstB := storeTarget_addr
          (σ := σC ws.length ws kvs (ws.length : Int) false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (a := ⟨B⟩) (v := .int (p.2 : Int) .uint64)
          (v' := .int (p.2 : Int) .uint64) hlkb
          (by
            simp only [normalizeValueForTy, normalizeValueForTyFuel,
              typeResolutionFuel]
            rw [hvnorm]
            rfl)
        rw [show (σC ws.length ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1)).heap
            = frontC ws.length ws kvs (ws.length : Int) false
              ++ (tail
                ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            from rfl,
          set_append_right (lookup_frontC_none ws.length ws kvs
            (ws.length : Int) false hB),
          set_append_left hbest] at hstB
        have h12 := stepFnIter_chain h11
          (stepFnIter_one (stepFn_store_step hstB))
        have hR5 := wc_segR5_raw ws.length ws kvs (rem.eraseIdx idx)
          (ws.length : Int)
          (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
            ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) ch₂
        have h13 := stepFnIter_chain h12 hR5
        -- recurse
        have hbest' : Heap.lookup
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (.base ⟨B⟩) = some (u64cell (p.2 : Int)) :=
          lookup_append_left Frame.Heap.lookup_set_self
        have htail' : ∀ x : Nat, na + 1 ≤ x →
            Heap.lookup
              (Heap.set tail (.base ⟨B⟩)
                  ⟨some tU64, .int (p.2 : Int) .uint64⟩
                ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (.base ⟨x⟩) = none := by
          intro x hx
          rw [lookup_append_right (by
            rw [Machine.Heap.lookup_set_ne
              (show (.base ⟨B⟩ : Loc) ≠ .base ⟨x⟩ from by
                simp only [ne_eq, Loc.base.injEq, Addr.mk.injEq]
                omega)]
            exact htail x (by omega)),
            lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
          rfl
        obtain ⟨k', ch', tail₃, na₃, hk', hna₃, hbest₃, htail₃, hrun⟩ :=
          ih (rem.eraseIdx idx) hlenerase p.2 B (na + 1)
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            ch₂ hremerase hlen hpc hB (by omega) hbest' htail'
        refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + 1 + 4 + 1 + 1 + 1 + 4 + k',
          ch', tail₃, na₃, by omega, by omega, ?_, htail₃, ?_⟩
        · rw [show max bv (maxOf (rem.map Prod.snd))
              = max p.2 (maxOf ((rem.eraseIdx idx).map Prod.snd)) from by
            rw [hmaxsplit]
            omega]
          exact hbest₃
        · exact stepFnIter_chain h13 hrun
      · -- the branch that keeps `best`
        rw [show (decide ((bv : Int) < (p.2 : Int))) = false from
          decide_eq_false (by
            intro hc
            exact hcmp (by exact_mod_cast hc))] at h6
        have hR4e := wc_segR4e_raw ws.length ws kvs (rem.eraseIdx idx)
          (ws.length : Int)
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) ch₂
        have h7 := stepFnIter_chain h6 hR4e
        have hbest' : Heap.lookup
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (.base ⟨B⟩) = some (u64cell (bv : Int)) :=
          lookup_append_left hbest
        have htail' : ∀ x : Nat, na + 1 ≤ x →
            Heap.lookup
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (.base ⟨x⟩) = none := by
          intro x hx
          rw [lookup_append_right (htail x (by omega)),
            lookup_cons_ne (base_beq_false (by omega : na ≠ x))]
          rfl
        obtain ⟨k', ch', tail₃, na₃, hk', hna₃, hbest₃, htail₃, hrun⟩ :=
          ih (rem.eraseIdx idx) hlenerase bv B (na + 1)
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            ch₂ hremerase hlen hbv hB (by omega) hbest' htail'
        refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + k', ch', tail₃, na₃, by omega,
          by omega, ?_, htail₃, ?_⟩
        · rw [show max bv (maxOf (rem.map Prod.snd))
              = max bv (maxOf ((rem.eraseIdx idx).map Prod.snd)) from by
            rw [hmaxsplit]
            omega]
          exact hbest₃
        · exact stepFnIter_chain h7 hrun

/-! ## The return path (range exit → the driver terminal) -/

/-- The exit-phase front: result cells written (`$callres` at 0, `$res0`
at 3), counters at their final values. -/
private def frontX (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (r0 r3 : Int) : Heap :=
  [(.base ⟨0⟩, u64cell r0), (.base ⟨1⟩, arrCell L ws),
   (.base ⟨2⟩, handleCell L), (.base ⟨3⟩, u64cell r3),
   (.base ⟨4⟩, mhCell), (.base ⟨5⟩, mdCell kvs),
   (.base ⟨6⟩, mhCell), (.base ⟨7⟩, intcell (L : Int)),
   (.base ⟨8⟩, bcell false)]

private def σX (L : Nat) (ws : List Int) (kvs : List (Int × Nat))
    (r0 r3 : Int) (tail : Heap) (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontX L ws kvs r0 r3 ++ tail, nextAddr := na }

private theorem lookup_frontX_none (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) {x : Nat} (hx : 9 ≤ x) :
    Heap.lookup (frontX L ws kvs r0 r3) (.base ⟨x⟩) = none := by
  simp only [frontX, Heap.lookup,
    base_beq_false (by omega : (0 : Nat) ≠ x),
    base_beq_false (by omega : (1 : Nat) ≠ x),
    base_beq_false (by omega : (2 : Nat) ≠ x),
    base_beq_false (by omega : (3 : Nat) ≠ x),
    base_beq_false (by omega : (4 : Nat) ≠ x),
    base_beq_false (by omega : (5 : Nat) ≠ x),
    base_beq_false (by omega : (6 : Nat) ≠ x),
    base_beq_false (by omega : (7 : Nat) ≠ x),
    base_beq_false (by omega : (8 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- X1: loop exit → the `best` read of `$res0 := best`. 6 steps (one
`.seqn` splice glued). -/
private theorem wc_segX1_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σX L ws kvs r0 r3 tail na) (.next (kR B)) ch
      = .ok (.evalE (.var "best") (envRB B)
            (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
              (.seqn #[]) (envRB B)
              (.seq [.returnStmt] (envRB B) frameK)),
          σX L ws kvs r0 r3 tail na, ch) := by
  have h1 : stepFnIter 1 (σX L ws kvs r0 r3 tail na) (.next (kR B)) ch
      = .ok (.exec retSeqn (envRB B) (.seq [] (envRB B) frameK),
          σX L ws kvs r0 r3 tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σX L ws kvs r0 r3 tail na)
    (ss := #[.assign (.var "$res0") (.var "best"), .returnStmt])
    (env := envRB B) (rest := []) (k := frameK) (ch := ch))
  have h3 : stepFnIter 4 (σX L ws kvs r0 r3 tail na)
      (.next (.seq
        ((#[.assign (.var "$res0") (.var "best"),
          .returnStmt] : Array Stmt).toList ++ [])
        (envRB B) frameK)) ch
      = .ok (.evalE (.var "best") (envRB B)
            (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] []
              (.seqn #[]) (envRB B)
              (.seq [.returnStmt] (envRB B) frameK)),
          σX L ws kvs r0 r3 tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X2a: the `best` value delivered → stored into `$res0` (concrete
cell 3; the wrap rides). 2 steps. -/
private theorem wc_segX2a_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 bvv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σX L ws kvs r0 r3 tail na)
      (.retV (.int bvv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨3⟩)) [] []] [] [] (.seqn #[])
          (envRB B) (.seq [.returnStmt] (envRB B) frameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRB B)
            (.seq [.returnStmt] (envRB B) frameK)),
          σX L ws kvs r0 (IntKind.normalize .uint64 bvv) tail na, ch) := by
  with_unfolding_all rfl

/-- X2b + the splice: → the `returnStmt` dispatch point. 2 steps. -/
private theorem wc_segX2b_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σX L ws kvs r0 r3 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRB B)
        (.seq [.returnStmt] (envRB B) frameK))) ch
      = .ok (.next (.seq
            (((#[] : Array Stmt).toList) ++ [.returnStmt]) (envRB B) frameK),
          σX L ws kvs r0 r3 tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σX L ws kvs r0 r3 tail na) (body := .seqn #[]) (env := envRB B)
    (k := .seq [.returnStmt] (envRB B) frameK) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn
    (σ := σX L ws kvs r0 r3 tail na) (ss := #[]) (env := envRB B)
    (rest := [.returnStmt]) (k := frameK) (ch := ch))
  exact stepFnIter_chain h1 h2

/-- X2c: `return`, the frame exit's result read, the `$callres`
write-back, the driver terminal. 10 steps. -/
private theorem wc_segX2c_raw (L : Nat) (ws : List Int)
    (kvs : List (Int × Nat)) (r0 r3 : Int) (tail : Heap) (na : Nat)
    (B : Nat) (ch : Choices) :
    stepFnIter 10 (σX L ws kvs r0 r3 tail na)
      (.next (.seq (((#[] : Array Stmt).toList) ++ [.returnStmt])
        (envRB B) frameK)) ch
      = .ok (.next .stop,
          σX L ws kvs (IntKind.normalize .uint64 r3) r3 tail na, ch) := by
  with_unfolding_all rfl

/-! ## The canonical run, end to end -/

private theorem countsList_length_le (ws : List Int) :
    (countsList ws).length ≤ ws.length := by
  have hbump : ∀ (kvs : List (Int × Nat)) (w : Int),
      (bump kvs w).length ≤ kvs.length + 1 := by
    intro kvs w
    induction kvs with
    | nil => simp [bump]
    | cons kv rest ih =>
        obtain ⟨k, c⟩ := kv
        by_cases hk : k = w
        · simp [bump, hk]
        · simp only [bump, if_neg hk, List.length_cons]
          omega
  have hfold : ∀ (l : List Int) (kvs : List (Int × Nat)),
      (List.foldl bump kvs l).length ≤ kvs.length + l.length := by
    intro l
    induction l with
    | nil => intro kvs; simp
    | cons w rest ih =>
        intro kvs
        simp only [List.foldl_cons, List.length_cons]
        have h1 := ih (bump kvs w)
        have h2 := hbump kvs w
        omega
  simpa [countsList] using hfold ws []

private theorem maxMult_le_len (ws : List Int) :
    maxMultiplicity ws ≤ ws.length := by
  refine maxMult_le (fun v _ => ?_)
  simp only [multiplicity]
  exact List.length_filter_le _ _

/-- **The canonical run, end to end**: from the canonical seed the
driver completes at the `.normal` terminal within `132 + 108·len`
steps, at EVERY choice stream, with `maxMultiplicity ws` in the
result cell and the input backing untouched. -/
private theorem wc_runs (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices) (tail : Heap) (na : Nat),
      k ≤ 132 + 108 * ws.length ∧
      stepFnIter k (wcSeed ws 1 [] 2) (.exec (wcCall ws 1) wcEnv .stop) ch
        = .ok (.next .stop,
            σX ws.length ws (countsList ws)
              ((maxMultiplicity ws : Nat) : Int)
              ((maxMultiplicity ws : Nat) : Int) tail na, ch') := by
  have hM : maxMultiplicity ws ≤ ws.length := maxMult_le_len ws
  have hMnorm : IntKind.normalize .uint64 ((maxMultiplicity ws : Nat) : Int)
      = ((maxMultiplicity ws : Nat) : Int) := by
    refine unorm_of_range (by omega) ?_
    have : maxMultiplicity ws < 2 ^ 64 := by omega
    exact_mod_cast this
  -- entry
  have hE1 := wc_entryA_raw ws ch
  rw [inorm_nat_of_lt hlen] at hE1
  have happ : applyStrictOp (wcSeed ws 1 [] 2) (.sliceExpr false)
      [.addr (.base ⟨1⟩), .int 0 .int, .int ((ws.length : Nat) : Int) .int]
      = .ok (sliceH ws.length, wcSeed ws 1 [] 2) :=
    applyStrictOp_sliceExpr_array
      (show Heap.lookup (wcSeed ws 1 [] 2).heap (.base ⟨1⟩)
          = some ⟨some (.array ws.length tU64),
              .array ⟨ws.map (fun v => .int v .uint64)⟩⟩ from rfl)
      (by simp)
  have hE := stepFnIter_chain
    (stepFnIter_chain hE1
      (stepFnIter_one (stepFn_strict_apply
        (done := [.int 0 .int, .addr (.base ⟨1⟩)]) happ)))
    (wc_entryB_raw ws ch)
  -- first dispatch
  have hA0 := wc_segA0_raw ws.length ws [] 0 [] 9 ch
  have hlen_apply : applyStrictOp (σC ws.length ws [] 0 false [] 9)
      (.lengthOf (some (.slice tU64))) [sliceH ws.length]
      = .ok (.int (ws.length : Nat) .int, σC ws.length ws [] 0 false [] 9) :=
    applyStrictOp_len_slice (Nat.le_refl _)
  have hCmp := wc_cmp_raw ws.length ws [] 0 0 [] 9 ch
  have hD := stepFnIter_chain
    (stepFnIter_chain (stepFnIter_chain hE hA0)
      (stepFnIter_one (stepFn_strict_apply (done := []) hlen_apply)))
    hCmp
  -- the counting loop to the range head
  obtain ⟨k₁, tail₁, hk₁, htail₁, hbest₁, hrun₁⟩ :=
    wc_count_loop ws hws hlen (ws.length - 0) 0 rfl (by omega) [] 9
      (by omega) (fun _ _ => rfl) ch
  have hC := stepFnIter_chain hD hrun₁
  -- the range loop
  obtain ⟨k₂, ch₂, tail₂, na₂, hk₂, hna₂, hbest₂, htail₂, hrun₂⟩ :=
    wc_range_loop ws (countsList ws) (countsList ws).length (countsList ws)
      rfl 0 (9 + 2 * (ws.length - 0)) (9 + 2 * (ws.length - 0) + 1) tail₁
      ch (fun p hp => countsList_val_le ws hp) hlen (by omega) (by omega)
      (by omega) hbest₁ htail₁
  have hR := stepFnIter_chain hC hrun₂
  rw [show max 0 (maxOf ((countsList ws).map Prod.snd))
      = maxMultiplicity ws from by
    rw [Nat.zero_max]
    exact maxOf_countsList ws] at hbest₂
  -- the return path
  have hX1 := wc_segX1_raw ws.length ws (countsList ws) 0 0 tail₂
    (9 + 2 * (ws.length - 0)) na₂ ch₂
  have hX := stepFnIter_chain hR hX1
  have hlkB : Heap.lookup
      (σX ws.length ws (countsList ws) 0 0 tail₂ na₂).heap
      (.base ⟨9 + 2 * (ws.length - 0)⟩)
      = some (u64cell ((maxMultiplicity ws : Nat) : Int)) := by
    show Heap.lookup (frontX ws.length ws (countsList ws) 0 0 ++ tail₂)
      (.base ⟨9 + 2 * (ws.length - 0)⟩)
      = some (u64cell ((maxMultiplicity ws : Nat) : Int))
    rw [lookup_append_right
      (lookup_frontX_none ws.length ws (countsList ws) 0 0 (by omega))]
    exact hbest₂
  have hX2 := stepFnIter_chain hX (stepFnIter_one
    (stepFn_var (x := "best") (env := envRB (9 + 2 * (ws.length - 0)))
      (a := ⟨9 + 2 * (ws.length - 0)⟩) (ch := ch₂) rfl hlkB))
  have hX2a := wc_segX2a_raw ws.length ws (countsList ws) 0 0
    ((maxMultiplicity ws : Nat) : Int) tail₂
    (9 + 2 * (ws.length - 0)) na₂ ch₂
  rw [hMnorm] at hX2a
  have hX3 := stepFnIter_chain hX2 hX2a
  have hX4 := stepFnIter_chain hX3
    (wc_segX2b_raw ws.length ws (countsList ws) 0
      ((maxMultiplicity ws : Nat) : Int) tail₂
      (9 + 2 * (ws.length - 0)) na₂ ch₂)
  have hX2c := wc_segX2c_raw ws.length ws (countsList ws) 0
    ((maxMultiplicity ws : Nat) : Int) tail₂ na₂
    (9 + 2 * (ws.length - 0)) ch₂
  rw [hMnorm] at hX2c
  have hX5 := stepFnIter_chain hX4 hX2c
  refine ⟨_, ch₂, tail₂, na₂, ?_, hX5⟩
  have hm := countsList_length_le ws
  omega

/-- **Total correctness of the `maxCount` run at the canonical
placement** — the SUPPORTING inner-run theorem beneath the harness-form
headline (statement-form ruling 2026-08-13: user-facing headlines
quantify over `GoValue` arguments at the `runFunctionWithContextM`
boundary; this canonical-driver form carries the semantic content — the
∀-choices total run with the order-independent readout — and is what
the shared harness entry-glue consumes). Past fuel `132 + 108·len`,
at EVERY choice stream (every map-iteration order), execution completes
normally with EXACTLY `maxMultiplicity ws` in the result cell and the
input backing untouched. -/
theorem maxCount_total_canonical (ws : List Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ fuel : Nat, 132 + 108 * ws.length ≤ fuel → ∀ ch : Choices,
      ∃ (σf : ExecState) (ch' : Choices),
        execStmt fuel wcEnv (wcSeed ws 1 [] 2) ch (wcCall ws 1)
          = .ok (.normal σf, ch')
        ∧ loadLoc σf (.base ⟨0⟩)
            = .ok (.int ((maxMultiplicity ws : Nat) : Int) .uint64)
        ∧ Heap.lookup σf.heap (.base ⟨1⟩)
            = some ⟨some (.array ws.length tU64),
                .array ⟨ws.map (fun v => .int v .uint64)⟩⟩ := by
  intro fuel hfuel ch
  obtain ⟨k, ch', tail, na, hk, hrun⟩ := wc_runs ws hws hlen ch
  refine ⟨σX ws.length ws (countsList ws)
    ((maxMultiplicity ws : Nat) : Int) ((maxMultiplicity ws : Nat) : Int)
    tail na, ch', ?_, rfl, rfl⟩
  show execStmtLoop fuel (wcSeed ws 1 [] 2)
    (.exec (wcCall ws 1) wcEnv .stop) ch = _
  have hfold := execStmtLoop_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  rw [hfold, execStmtLoop_next_stop]

/-! ## The harness form (statement-form ruling 2026-08-13)

The user-facing statement shape: a fixed Go HARNESS function — setup
phase builds the memory from scalar parameters, the call under test,
test phase folds the verdict into return values — observed ONLY through
`runFunctionWithContextM` termination + return values, quantified over
the `GoValue` arguments. The pinned lowering carries three such
harnesses (`maxCountEmpty`/`maxCountOne`/`maxCountFour`). This module
ships the form at `maxCountEmpty` (the zero-parameter instance — the
run is address-concrete throughout, so no shared entry-glue is needed);
the parameterized instances consume the shared harness entry-glue layer
plus this module's placement-generic inductions (`wc_range_loop` is
already placement-generic in `B`/`na`/`tail`; the address-CONCRETE defs
`frontC`/`envB`/`frameK` are the re-parameterization point — see the
slice report). -/

/-- The `maxCountEmpty` harness's `Func` record, verbatim from the
pinned lowering (the `example` pin ties it by `rfl`): setup builds an
empty `[]uint64`, the call under test runs `maxCount`, the result
returns. -/
def maxCountEmptyFunc : Func :=
  { id := { key := "maxCountEmpty" },
    args := #[],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "$c7", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c7") (.int .uint64) (.intLit 0 .int)
              (some (.intLit 0 .int))],
        .seqn
          #[.initialization { id := "$c8", typ := .int .uint64 },
            .call #[.var "$c8"] { key := "maxCount" } #[.var "$c7"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c8"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

example : findFunctionIn? wordCountLowered.funcs ⟨"maxCountEmpty"⟩
    = some maxCountEmptyFunc := rfl

/-- The harness run's terminal state (probe-pinned; re-checked by the
`rfl` below). -/
private def σEmptyFin : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [
      (.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩),
      (.base ⟨1⟩, ⟨some (.slice tU64), .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩⟩),
      (.base ⟨2⟩, ⟨some (.array 0 tU64), .array #[]⟩),
      (.base ⟨3⟩, ⟨some tU64, .int 0 .uint64⟩),
      (.base ⟨4⟩, ⟨some (.slice tU64), .slice ⟨some (.base ⟨2⟩), 0, 0, 0⟩⟩),
      (.base ⟨5⟩, ⟨some tU64, .int 0 .uint64⟩),
      (.base ⟨6⟩, ⟨some tMap, .map ⟨some (.base ⟨7⟩)⟩⟩),
      (.base ⟨7⟩, ⟨none, .mapData #[]⟩),
      (.base ⟨8⟩, ⟨some tMap, .map ⟨some (.base ⟨7⟩)⟩⟩),
      (.base ⟨9⟩, ⟨some (.int .int), .int 0 .int⟩),
      (.base ⟨10⟩, ⟨some .bool, .bool false⟩),
      (.base ⟨11⟩, ⟨some tU64, .int 0 .uint64⟩)],
    nextAddr := 12 }

set_option maxHeartbeats 12000000 in
/-- The whole harness run at the empty-map instance: 158 steps, every
address concrete, NO choice consumed (an empty snapshot picks
nothing) — the stream rides through untouched. -/
private theorem wc_empty_run (ch : Choices) :
    stepFnIter 158
      { types := wordCountLowered.typeDefs.toList,
        functions := wordCountLowered.funcs,
        methods := wordCountLowered.methods,
        heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop))
      ch
      = .ok (.next .stop, σEmptyFin, ch) := by
  with_unfolding_all rfl

/-- **The harness-form statement at the empty instance** (ruling
2026-08-13): the fixed harness `maxCountEmpty` — observed only through
the native entry `runFunctionWithContextM`, termination + return
value — returns exactly `maxMultiplicity []` past one fuel bound, at
EVERY choice stream. The zero-parameter degenerate of the form: the
∀-args quantifier is empty and the empty map consumes no pick; the
parameterized instances (`maxCountOne`/`maxCountFour`) are the shared
entry-glue layer's consumers (slice report, gap G1). -/
theorem wordcount_empty_ok :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
        wordCountLowered.funcs maxCountEmptyFunc #[]
        wordCountLowered.methods ch
        = .ok ⟨#[.int ((maxMultiplicity [] : Nat) : Int) .uint64]⟩ := by
  refine ⟨158, fun fuel hfuel ch => ?_⟩
  have hrun := wc_empty_run ch
  have hfold := runConfig_of_stepFnIter hrun (fuel - 158)
  rw [show 158 + (fuel - 158) = fuel from by omega] at hfold
  have hfull : runConfig fuel
      { types := wordCountLowered.typeDefs.toList,
        functions := wordCountLowered.funcs,
        methods := wordCountLowered.methods,
        heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)], nextAddr := 1 }
      (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
        (.frame [] [] [] [] .stop))
      ch = .ok (σEmptyFin, ch) := by
    rw [hfold, runConfig_next_stop]
  have hshape : runFunctionWithContextM fuel
      wordCountLowered.typeDefs.toList wordCountLowered.funcs
      maxCountEmptyFunc #[] wordCountLowered.methods ch
      = (do
          let r ← runConfig fuel
            { types := wordCountLowered.typeDefs.toList,
              functions := wordCountLowered.funcs,
              methods := wordCountLowered.methods,
              heap := [(.base ⟨0⟩, ⟨some tU64, .int 0 .uint64⟩)],
              nextAddr := 1 }
            (.exec maxCountEmptyFunc.body [[("$res0", .base ⟨0⟩)]]
              (.frame [] [] [] [] .stop))
            ch
          return { values := (← loadMany r.1 [.base ⟨0⟩]).toArray }) := by
    with_unfolding_all rfl
  rw [hshape, hfull]
  with_unfolding_all rfl

end GoLean.Examples.WordCount
