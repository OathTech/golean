import GoLeanProofs.Examples.WordCountProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps

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
* `wordcount_ok` — **gap G1 CLOSED (consolidation slice,
  2026-08-14)**: the `(n, seed)`-parameterized §11 harness headline
  over `wordcount_harness`, hypotheses just `n < 2^63` and
  `seed < 2^64` (the seed-wrap caveat stays refuted), returned value
  EXACTLY `(n+2)/3` via `wcFamily_maxMult`; `wordcount_readout` is the
  derived D1 twin. Closed as the FIRST CONSUMER of the
  placement-generic composition layer (`wcIter_generic`/
  `wcLoop_generic`/`wcRange_generic` below): the compositions are
  stated once over an abstract state family and instantiated at both
  the canonical and harness placements — the 2026-08-13 elaborator
  storm (diagnosed as exponential delta-fallback unification over
  concrete fronts, `docs/2026-08-13_consolidation-slice.md` §1) is
  structurally impossible in this form.

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

/-! ## The placement-generic counting-loop composition (consolidation
slice 2026-08-13, worklist item 1)

The counting loop's COMPOSITION layer, stated ONCE over an abstract
state family `S`, abstract placement environments/continuations, and
the per-segment transition facts as hypotheses. Design informed by the
storm diagnosis (`docs/2026-08-13_consolidation-slice.md` §1): in this
layer the unifier only ever matches the VARIABLE `S`, and every
instantiation site discharges a hypothesis whose type pins all
intermediate states/configurations (variant E's fix made structural) —
the storm class cannot ignite here. The two consumers are the
canonical placement (`wc_count_iter`/`wc_count_loop` below, retrofitted
to instantiations) and the harness placement (`wcH_count_iter`/
`wcH_count_loop`, the former gap-G1 blocker). Full segment
α-abstraction was considered and REJECTED (recorded): per-placement
`rfl` segments are cheap and were never the storm's site; the
composition + the conditioned state-massage discharges were. -/

/-- Freshness of a heap tail from an address up. -/
def DeadFrom (dead : Heap) (na : Nat) : Prop :=
  ∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none

theorem DeadFrom.mono {dead : Heap} {na na' : Nat} (h : DeadFrom dead na)
    (hle : na ≤ na') : DeadFrom dead na' :=
  fun x hx => h x (by omega)

theorem DeadFrom.push {dead : Heap} {na : Nat} {c : HeapCell}
    (h : DeadFrom dead na) :
    DeadFrom (dead ++ [(.base ⟨na⟩, c)]) (na + 1) := by
  intro x hx
  rw [GoLean.Surface.lookup_append_right (h x (by omega)),
    GoLean.Surface.lookup_cons_ne
      (GoLean.Surface.base_beq_false (by omega : na ≠ x))]
  rfl

theorem DeadFrom.push2 {dead : Heap} {na : Nat} {c c' : HeapCell}
    (h : DeadFrom dead na) :
    DeadFrom (dead ++ [(.base ⟨na⟩, c), (.base ⟨na + 1⟩, c')]) (na + 2) := by
  intro x hx
  rw [GoLean.Surface.lookup_append_right (h x (by omega)),
    GoLean.Surface.lookup_cons_ne
      (GoLean.Surface.base_beq_false (by omega : na ≠ x)),
    GoLean.Surface.lookup_cons_ne
      (GoLean.Surface.base_beq_false (by omega : na + 1 ≠ x))]
  rfl

section CountGeneric

open GoLean.Surface GoLean.SliceMem

/-- The map-handle heap cell at data address `bMap`. -/
abbrev mhG (bMap : Nat) : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨bMap⟩)⟩⟩
/-- The nil-map cell (`$c1`'s default). -/
abbrev nilMapCell : HeapCell := ⟨some tMap, .map ⟨none⟩⟩
/-- The input-slice handle over backing address `bArr`. -/
abbrev wsHG (bArr L : Nat) : GoValue :=
  .slice ⟨some (.base ⟨bArr⟩), 0, L, L⟩

/-- **The placement-generic counting ITERATION** (53 steps): stated over
an abstract state family `S`, abstract placement environments/
continuations, and the per-segment transition FACTS as hypotheses —
each hypothesis type pins every intermediate state and configuration,
so no instantiation can send the unifier into the concrete front (the
storm-class fix, session note §1 fix 2). -/
theorem wcIter_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp postK : Cont)
    (env3g : LocalEnv) (u1Envg uEnvg : Nat → LocalEnv)
    -- the segment facts
    (hC1 : ∀ kvs iv dead na ch,
      stepFnIter 7 (S kvs iv false dead na) (.retV (.bool true) cmp) ch
        = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3g
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3g postK),
          S kvs iv false dead na, ch))
    (hInit1 : ∀ kvs iv dead na ch, base0 ≤ na → DeadFrom dead na →
      stepFn (S kvs iv false dead na)
          (.exec (.initialization { id := "$c1", typ := tMap }) env3g
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3g postK)) ch
        = .ok (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Envg na) postK),
          S kvs iv false (dead ++ [(.base ⟨na⟩, nilMapCell)]) (na + 1), ch))
    (hC2 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 6 (S kvs iv false dead na)
          (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Envg na₀) postK)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
              [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK)),
          S kvs iv false dead na, ch))
    (hSt1 : ∀ kvs iv dead na₀ na ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨bMap⟩)⟩] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
              (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK)),
          S kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG bMap)]) na, ch))
    (hC3 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 5 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (u1Envg na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Envg na₀) postK))) ch
        = .ok (.exec (.initialization { id := "$c2", typ := tU64 })
              (u1Envg na₀)
              (.seq [.assign (.var "$c2")
                  (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
                (u1Envg na₀) postK),
          S kvs iv false dead na, ch))
    (hInit2 : ∀ kvs iv dead na₀ ch, base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG bMap)]) (na₀ + 1))
          (.exec (.initialization { id := "$c2", typ := tU64 }) (u1Envg na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1Envg na₀) postK)) ch
        = .ok (.next (.seq [.assign (.var "$c2")
              (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (uEnvg na₀) postK),
          S kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch))
    (hC4 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 8 (S kvs iv false dead na)
          (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (uEnvg na₀) postK)) ch
        = .ok (.retV (.int iv .int)
              (.strictK .indexGet [wsHG bArr ws.length] [] (uEnvg na₀)
                (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                  (.seqn #[]) (uEnvg na₀)
                  (.seq [mapAsgnStmt] (uEnvg na₀) postK))),
          S kvs iv false dead na, ch))
    (hRead : ∀ kvs (i : Nat) dead na, i < ws.length →
      applyStrictOp (S kvs ((i : Nat) : Int) false dead na) .indexGet
          [wsHG bArr ws.length, .int ((i : Nat) : Int) .int]
        = .ok (.int (ws.getD i 0) .uint64,
            S kvs ((i : Nat) : Int) false dead na))
    (hC5 : ∀ kvs iv dead na₀ na (w : GoValue) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV w (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
            (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnStmt] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
              (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnStmt] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hSt2 : ∀ kvs iv dead na₀ na (w : Int) ch, 0 ≤ w → w < 2 ^ 64 →
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell 0)])
          na)
          (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
            [.int w .uint64] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnStmt] (uEnvg na₀) postK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
              (.seq [mapAsgnStmt] (uEnvg na₀) postK)),
          S kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch))
    (hC6 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 4 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (uEnvg na₀)
            (.seq [mapAsgnStmt] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var "$c1") (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 []
                [.var "$c2",
                 .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                   (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hVar1 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var "$c1") (uEnvg na₀) k) ch
        = .ok (.retV (.map ⟨some (.base ⟨bMap⟩)⟩) k,
            S kvs iv false
              (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
              na, ch))
    (hVar2 : ∀ kvs iv (w : Int) dead na₀ na (k : Cont) ch,
      base0 ≤ na₀ → DeadFrom dead na₀ →
      stepFn (S kvs iv false
          (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
          na)
          (.evalE (.var "$c2") (uEnvg na₀) k) ch
        = .ok (.retV (.int w .uint64) k,
            S kvs iv false
              (dead ++ [(.base ⟨na₀⟩, mhG bMap), (.base ⟨na₀ + 1⟩, u64cell w)])
              na, ch))
    (hC7 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.stmtOpK (.mapAssign tU64 tU64) 0 []
              [.var "$c2",
               .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                 (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var "$c2") (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
                [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                  (.intLit 1 .uint64)]
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hC8 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int w .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨bMap⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.evalE (.var "$c1") (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hC9 : ∀ kvs iv dead na₀ na (w : Int) ch,
      stepFnIter 1 (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvg na₀)
              (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                (.stmtOpK (.mapAssign tU64 tU64) 0
                  [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                  (uEnvg na₀) (.seq [] (uEnvg na₀) postK))))) ch
        = .ok (.evalE (.var "$c2") (uEnvg na₀)
              (.strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀)
                (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
                  (.stmtOpK (.mapAssign tU64 tU64) 0
                    [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                    (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))),
          S kvs iv false dead na, ch))
    (hMapGet : ∀ kvs iv dead na (w : Int), 0 ≤ w → w < 2 ^ 64 →
      applyStrictOp (S kvs iv false dead na) (.mapGet tU64 tU64)
          [.map ⟨some (.base ⟨bMap⟩)⟩, .int w .uint64]
        = .ok (.int (cnt kvs w : Int) .uint64, S kvs iv false dead na))
    (hC10 : ∀ kvs iv dead na₀ na (w cv : Int) ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.retV (.int cv .uint64)
            (.strictK .add [] [.intLit 1 .uint64] (uEnvg na₀)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)))) ch
        = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
              (.stmtOpK (.mapAssign tU64 tU64) 0
                [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
                (uEnvg na₀) (.seq [] (uEnvg na₀) postK)),
          S kvs iv false dead na, ch))
    (hMapAsgn : ∀ kvs iv dead na₀ na (w : Int) (v : Nat) ch,
      0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
      stepFn (S kvs iv false dead na)
          (.retV (.int ((v : Nat) : Int) .uint64)
            (.stmtOpK (.mapAssign tU64 tU64) 0
              [.int w .uint64, .map ⟨some (.base ⟨bMap⟩)⟩] []
              (uEnvg na₀) (.seq [] (uEnvg na₀) postK))) ch
        = .ok (.next (.seq [] (uEnvg na₀) postK),
            S (setk kvs w v) iv false dead na, ch))
    (hC11 : ∀ kvs iv dead na₀ na ch,
      stepFnIter 3 (S kvs iv false dead na)
          (.next (.seq [] (uEnvg na₀) postK)) ch
        = .ok (head, S kvs iv false dead na, ch))
    -- the iteration-level hypotheses
    (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat)
    (ch : Choices)
    (hi : i < ws.length)
    (hw0 : 0 ≤ ws.getD i 0) (hw64 : ws.getD i 0 < 2 ^ 64)
    (hcnt : cnt kvs (ws.getD i 0) + 1 < 2 ^ 64)
    (hna : base0 ≤ na) (hdead : DeadFrom dead na) :
    stepFnIter 53 (S kvs ((i : Nat) : Int) false dead na)
        (.retV (.bool true) cmp) ch
      = .ok (head,
          S (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1))
            ((i : Nat) : Int) false
            (dead ++ [(.base ⟨na⟩, mhG bMap),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have h1 := stepFnIter_chain (hC1 kvs ((i : Nat) : Int) dead na ch)
    (stepFnIter_one (hInit1 kvs ((i : Nat) : Int) dead na ch hna hdead))
  have h2 := stepFnIter_chain h1
    (hC2 kvs ((i : Nat) : Int) (dead ++ [(.base ⟨na⟩, nilMapCell)]) na
      (na + 1) ch)
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (hSt1 kvs ((i : Nat) : Int) dead na (na + 1) ch hna hdead))
  have h4 := stepFnIter_chain h3
    (hC3 kvs ((i : Nat) : Int) (dead ++ [(.base ⟨na⟩, mhG bMap)]) na (na + 1)
      ch)
  have h5 := stepFnIter_chain h4
    (stepFnIter_one (hInit2 kvs ((i : Nat) : Int) dead na ch hna hdead))
  have h6 := stepFnIter_chain h5
    (hC4 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) ch)
  have h7 := stepFnIter_chain h6
    (stepFnIter_one (stepFn_strict_apply (done := [wsHG bArr ws.length])
      (hRead kvs i
        (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell 0)])
        (na + 2) hi)))
  have h8 := stepFnIter_chain h7
    (hC5 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell 0)]) na
      (na + 2) (.int (ws.getD i 0) .uint64) ch)
  have h9 := stepFnIter_chain h8
    (stepFnIter_one (hSt2 kvs ((i : Nat) : Int) dead na (na + 2) (ws.getD i 0) ch hw0 hw64
      hna hdead))
  have h10 := stepFnIter_chain h9
    (hC6 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) ch)
  have h11 := stepFnIter_chain h10
    (stepFnIter_one (hVar1 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h12 := stepFnIter_chain h11
    (hC7 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) ch)
  have h13 := stepFnIter_chain h12
    (stepFnIter_one (hVar2 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h14 := stepFnIter_chain h13
    (hC8 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) (ws.getD i 0) ch)
  have h15 := stepFnIter_chain h14
    (stepFnIter_one (hVar1 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h16 := stepFnIter_chain h15
    (hC9 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) (ws.getD i 0) ch)
  have h17 := stepFnIter_chain h16
    (stepFnIter_one (hVar2 kvs ((i : Nat) : Int) (ws.getD i 0) dead na (na + 2) _ ch hna
      hdead))
  have h18 := stepFnIter_chain h17
    (stepFnIter_one (stepFn_strict_apply
      (done := [.map ⟨some (.base ⟨bMap⟩)⟩])
      (hMapGet kvs ((i : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
        (na + 2) (ws.getD i 0) hw0 hw64)))
  have h19 := stepFnIter_chain h18
    (hC10 kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) (ws.getD i 0) ((cnt kvs (ws.getD i 0) : Nat) : Int) ch)
  have hcast : ((cnt kvs (ws.getD i 0) : Nat) : Int) + 1
      = ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int) := by omega
  have hnorm1 : IntKind.normalize .uint64 ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int)
      = ((cnt kvs (ws.getD i 0) + 1 : Nat) : Int) := by
    refine GoLean.SliceMem.unorm_of_range (by omega) ?_
    exact_mod_cast hcnt
  rw [hcast, hnorm1] at h19
  have h20 := stepFnIter_chain h19
    (stepFnIter_one (hMapAsgn kvs ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))])
      na (na + 2) (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1) ch hw0 hw64 hcnt))
  have h21 := stepFnIter_chain h20
    (hC11 (setk kvs (ws.getD i 0) (cnt kvs (ws.getD i 0) + 1)) ((i : Nat) : Int)
      (dead ++ [(.base ⟨na⟩, mhG bMap), (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) na
      (na + 2) ch)
  exact h21


/-- **The placement-generic counting LOOP + exit** (strong induction on
the remaining word count): from the exit-test delivery at word `i`, the
run reaches the range head (`mapIterK`) over the snapshot of the full
counts, with `best` zeroed at `na + 2·(L−i)`, within `84·(L−i) + 23`
steps. -/
theorem wcLoop_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ws : List Int) (bArr bMap base0 : Nat)
    (head : Config) (cmp : Cont) (exitK : Cont)
    (env2g envR0g : LocalEnv) (envRBg : Nat → LocalEnv) (kRg : Nat → Cont)
    (hlen : ws.length < 2 ^ 63)
    (hIter : ∀ (i : Nat) (dead : Heap) (na : Nat) (ch : Choices),
      i < ws.length → base0 ≤ na → DeadFrom dead na →
      stepFnIter 53 (S (countsList (ws.take i)) ((i : Nat) : Int) false dead
          na) (.retV (.bool true) cmp) ch
        = .ok (head,
            S (countsList (ws.take (i + 1))) ((i : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch))
    (hA1 : ∀ kvs iv dead na ch,
      stepFnIter 29 (S kvs iv false dead na) head ch
        = .ok (.retV (wsHG bArr ws.length)
              (.strictK (.lengthOf (some (.slice tU64))) [] [] env2g
                (.strictK .lessCmp
                  [.int (IntKind.normalize .int
                    (IntKind.normalize .int (iv + 1))) .int]
                  [] env2g cmp)),
            S kvs (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
              false dead na, ch))
    (hX0 : ∀ kvs iv dead na ch,
      stepFnIter 9 (S kvs iv false dead na) (.retV (.bool false) cmp) ch
        = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0g
              (.seq [.assign (.var "best") (.intLit 0 .uint64),
                wcMapRangeStmt, retSeqn] envR0g exitK),
            S kvs iv false dead na, ch))
    (hInitBest : ∀ kvs iv dead na ch, base0 ≤ na → DeadFrom dead na →
      stepFn (S kvs iv false dead na)
          (.exec (.initialization { id := "best", typ := tU64 }) envR0g
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0g exitK)) ch
        = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] (envRBg na) exitK),
            S kvs iv false (dead ++ [(.base ⟨na⟩, u64cell 0)]) (na + 1), ch))
    (hX0b : ∀ kvs iv dead B na ch,
      stepFnIter 6 (S kvs iv false dead na)
          (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRBg B) exitK)) ch
        = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
              [.int 0 .uint64] (.seqn #[]) (envRBg B)
              (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK)),
            S kvs iv false dead na, ch))
    (hStBest : ∀ kvs iv dead B na ch, base0 ≤ B → DeadFrom dead B →
      stepFn (S kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRBg B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (envRBg B)
              (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK)),
            S kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na, ch))
    (hX0c : ∀ kvs iv dead B na ch,
      stepFnIter 5 (S kvs iv false dead na)
          (.next (.storeK [] [] (.seqn #[]) (envRBg B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBg B) exitK))) ch
        = .ok (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
              (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBg B)
                (kRg B)),
            S kvs iv false dead na, ch))
    (hSnap : ∀ kvs iv dead B na ch,
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int) = ((p.2 : Nat) : Int)) →
      stepFn (S kvs iv false dead na)
          (.retV (.map ⟨some (.base ⟨bMap⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBg B)
              (kRg B))) ch
        = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
              (toEntries kvs) (envRBg B) (kRg B)),
            S kvs iv false dead na, ch))
    (hNormKvs : ∀ p ∈ countsList ws,
      IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int) = ((p.2 : Nat) : Int)) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), base0 ≤ na → DeadFrom dead na →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ DeadFrom tail (na + 2 * n + 1)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (S (countsList (ws.take i)) ((i : Nat) : Int) false dead na)
          (.retV (.bool (decide (((i : Nat) : Int) < (ws.length : Int)))) cmp)
          ch
        = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
              (toEntries (countsList ws)) (envRBg (na + 2 * n))
              (kRg (na + 2 * n))),
            S (countsList ws) ((ws.length : Nat) : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi dead na hna hdead ch
    rcases Nat.lt_or_ge i ws.length with hlt | hge
    · -- iterate
      rw [show (decide (((i : Nat) : Int) < (ws.length : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hIt := hIter i dead na ch hlt hna hdead
      have hdead₂ : DeadFrom (dead ++ [(.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) :=
        DeadFrom.push2 hdead
      have hA1' := hA1 (countsList (ws.take (i + 1))) ((i : Nat) : Int)
        (dead ++ [(.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2) ch
      rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63),
        GoLean.SliceMem.inorm_nat_of_lt (by omega : i + 1 < 2 ^ 63)] at hA1'
      have hLen := GoLean.Surface.stepFnIter_one
        (GoLean.Surface.stepFn_strict_apply (done := []) (env := env2g)
          (k := .strictK .lessCmp [.int ((i + 1 : Nat) : Int) .int] [] env2g
            cmp)
          (ch := ch)
          (GoLean.SliceMem.applyStrictOp_len_slice
            (σ := S (countsList (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (b := .base ⟨bArr⟩) (off := 0) (len := ws.length)
            (cap := ws.length) (elem := tU64) (Nat.le_refl _)))
      have hCmp := GoLean.Surface.stepFnIter_one
        (GoLean.Surface.stepFn_strict_apply
          (done := [.int ((i + 1 : Nat) : Int) .int]) (env := env2g)
          (k := cmp) (ch := ch)
          (GoLean.SliceMem.applyStrictOp_lessCmp_int
            (σ := S (countsList (ws.take (i + 1))) ((i + 1 : Nat) : Int) false
              (dead ++ [(.base ⟨na⟩, mhG bMap),
                (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2))
            (a := ((i + 1 : Nat) : Int)) (b := ((ws.length : Nat) : Int))
            (k := .int) (k' := .int)))
      obtain ⟨k, tail, hk, htail, hbest, hrun⟩ := ih (n - 1) (by omega)
        (i + 1) (by omega) (by omega)
        (dead ++ [(.base ⟨na⟩, mhG bMap),
          (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2)
        (by omega) hdead₂ ch
      refine ⟨53 + 29 + 1 + 1 + k, tail, by omega, ?_, ?_, ?_⟩
      · intro x hx
        exact htail x (by omega)
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact hbest
      · rw [show na + 2 * n = na + 2 + 2 * (n - 1) from by omega]
        exact stepFnIter_chain
          (stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hIt hA1')
            hLen) hCmp) hrun
    · -- exit: i = ws.length
      have hiL : i = ws.length := by omega
      subst hiL
      have hn0 : n = 0 := by omega
      subst hn0
      rw [show (decide (((ws.length : Nat) : Int) < ((ws.length : Nat) : Int)))
          = false from decide_eq_false (by omega)]
      have hX := hX0 (countsList (ws.take ws.length)) ((ws.length : Nat) : Int)
        dead na ch
      have hIB := hInitBest (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) dead na ch hna hdead
      have h1 := stepFnIter_chain hX (stepFnIter_one hIB)
      have hXb := hX0b (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na
        (na + 1) ch
      have h2 := stepFnIter_chain h1 hXb
      have hSB := hStBest (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) dead na (na + 1) ch hna hdead
      have h3 := stepFnIter_chain h2 (stepFnIter_one hSB)
      have hXc := hX0c (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na
        (na + 1) ch
      have h4 := stepFnIter_chain h3 hXc
      have hSn := hSnap (countsList (ws.take ws.length))
        ((ws.length : Nat) : Int) (dead ++ [(.base ⟨na⟩, u64cell 0)]) na
        (na + 1) ch
        (by rw [List.take_length]; exact hNormKvs)
      have h5 := stepFnIter_chain h4 (stepFnIter_one hSn)
      rw [List.take_length] at h5
      refine ⟨23, dead ++ [(.base ⟨na⟩, u64cell 0)], by omega, ?_, ?_, ?_⟩
      · simpa using DeadFrom.push (c := u64cell 0) hdead
      · rw [Nat.mul_zero, Nat.add_zero,
          GoLean.Surface.lookup_append_right (hdead na (Nat.le_refl na))]
        exact GoLean.Surface.lookup_singleton_self
      · simpa using h5


end CountGeneric

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
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σC L ws kvs iv false tail na) (ss := #[]) (env := u1Env na₀)
    (rest := [seqnC2, mapAsgnStmt]) (k := postBodyK) (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σC L ws kvs iv false tail na) (t := seqnC2)
    (rest := [mapAsgnStmt]) (env := u1Env na₀) (k := postBodyK) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
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
  have h2 := stepFnIter_one (stepFn_seqn_splice
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

/-! ## The canonical placement's discharge lemmas (the generic layer's
hypotheses at `S := σC ws.length ws`; every statement pins the full
transition — the E-form made structural) -/

private theorem wcC_init1 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 9 ≤ na → DeadFrom dead na →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.exec (.initialization { id := "$c1", typ := tMap }) env3
          (.seq [asgnC1, seqnC2, mapAsgnStmt] env3 postBodyK)) ch
      = .ok (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1Env na) postBodyK),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨na⟩, nilMapCell)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σC ws.length ws kvs iv false dead na)
    (p := { id := "$c1", typ := tMap })
    (rest := [asgnC1, seqnC2, mapAsgnStmt]) (env := env3) (k := postBodyK)
    (ch := ch) (v := .map ⟨none⟩)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false dead na).nextAddr = na from rfl,
    show (σC ws.length ws kvs iv false dead na).heap
      = frontC ws.length ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcC_st1 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
          [.map ⟨some (.base ⟨5⟩)⟩] (.seqn #[]) (u1Env na₀)
          (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (u1Env na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1Env na₀) postBodyK)),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhCell)]) na,
          ch) := by
  intro kvs iv dead na₀ na ch hna hdead
  have hlook : Heap.lookup
      (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]))
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false
        hna),
      lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .map ⟨some (.base ⟨5⟩)⟩)
    (v' := .map ⟨some (.base ⟨5⟩)⟩) hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      = frontC ws.length ws kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs iv false hna),
    set_append_right (hdead na₀ (Nat.le_refl na₀)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcC_init2 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ : Nat)
      (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5)]) (na₀ + 1))
        (.exec (.initialization { id := "$c2", typ := tU64 }) (u1Env na₀)
          (.seq [.assign (.var "$c2")
              (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (u1Env na₀) postBodyK)) ch
      = .ok (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (uEnv na₀) postBodyK),
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch) := by
  intro kvs iv dead na₀ ch hna hdead
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨na₀⟩, mhG 5)]))
      (.base ⟨na₀ + 1⟩) = none := by
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
    rfl
  have h := stepFn_init_seq
    (σ := σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 5)])
      (na₀ + 1))
    (p := { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1Env na₀) (k := postBodyK) (ch := ch)
    (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 5)])
        (na₀ + 1)).nextAddr = na₀ + 1 from rfl,
    show (σC ws.length ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 5)])
        (na₀ + 1)).heap
      = frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨na₀⟩, mhG 5)])
      from rfl,
    set_fresh hmiss, List.append_assoc, List.append_assoc] at h
  exact h

private theorem wcC_st2 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (ch : Choices), 0 ≤ w → w < 2 ^ 64 →
      9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
          [.int w .uint64] (.seqn #[]) (uEnv na₀)
          (.seq [mapAsgnStmt] (uEnv na₀) postBodyK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (uEnv na₀)
            (.seq [mapAsgnStmt] (uEnv na₀) postBodyK)),
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv dead na₀ na w ch hw0 hw64 hna hdead
  have hwnorm : IntKind.normalize .uint64 w = w := unorm_of_range hw0 hw64
  have hlook : Heap.lookup
      (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 5)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])))
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontC_none ws.length ws kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 5)]
          (.base ⟨na₀ + 1⟩) = none from by
        rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
        rfl)]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int w .uint64) (v' := .int w .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hwnorm]
      rfl)
  rw [show (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      = frontC ws.length ws kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 5)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])) from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs iv false
      (by omega)),
    set_append_right (hdead (na₀ + 1) (by omega)),
    set_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 5)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcC_lk1 (ws : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 9 ≤ na₀) (hdead : DeadFrom dead na₀) :
    Heap.lookup (σC ws.length ws kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀⟩) = some mhCell := by
  show Heap.lookup
    (frontC ws.length ws kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCell)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀⟩) = some mhCell
  rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_append_left lookup_singleton_self

private theorem wcC_lk2 (ws : List Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 9 ≤ na₀) (hdead : DeadFrom dead na₀) :
    Heap.lookup (σC ws.length ws kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀ + 1⟩) = some (u64cell w) := by
  show Heap.lookup
    (frontC ws.length ws kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCell)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀ + 1⟩) = some (u64cell w)
  rw [lookup_append_right
      (lookup_frontC_none ws.length ws kvs iv false (by omega)),
    lookup_append_right (hdead (na₀ + 1) (by omega)),
    lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCell)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl)]
  exact lookup_singleton_self

private theorem wcC_var1 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c1") (uEnv na₀) k) ch
      = .ok (.retV (.map ⟨some (.base ⟨5⟩)⟩) k,
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcC_lk1 ws kvs iv w dead na₀ na hna hdead)

private theorem wcC_var2 (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 9 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c2") (uEnv na₀) k) ch
      = .ok (.retV (.int w .uint64) k,
          σC ws.length ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 5), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcC_lk2 ws kvs iv w dead na₀ na hna hdead)

private theorem wcC_read (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat),
      i < ws.length →
    applyStrictOp (σC ws.length ws kvs ((i : Nat) : Int) false dead na)
        .indexGet [wsHG 1 ws.length, .int ((i : Nat) : Int) .int]
      = .ok (.int (ws.getD i 0) .uint64,
          σC ws.length ws kvs ((i : Nat) : Int) false dead na) := by
  intro kvs i dead na hi
  have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
      = some (.int (ws.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU ws i hi]
  exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
    (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) rfl
    (Nat.le_refl ws.length) hi hget

private theorem wcC_mapGet (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (w : Int), 0 ≤ w → w < 2 ^ 64 →
    applyStrictOp (σC ws.length ws kvs iv false dead na) (.mapGet tU64 tU64)
        [.map ⟨some (.base ⟨5⟩)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64,
          σC ws.length ws kvs iv false dead na) := by
  intro kvs iv dead na w hw0 hw64
  exact applyStrictOp_mapGet (a := ⟨5⟩) (dty := none) rfl
    (unorm_of_range hw0 hw64)

private theorem wcC_mapAsgn (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (v : Nat) (ch : Choices), 0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.retV (.int ((v : Nat) : Int) .uint64)
          (.stmtOpK (.mapAssign tU64 tU64) 0
            [.int w .uint64, .map ⟨some (.base ⟨5⟩)⟩] []
            (uEnv na₀) (.seq [] (uEnv na₀) postBodyK))) ch
      = .ok (.next (.seq [] (uEnv na₀) postBodyK),
          σC ws.length ws (setk kvs w v) iv false dead na, ch) := by
  intro kvs iv dead na₀ na w v ch hw0 hw64 hv
  have hMA := mapAssignValue_toEntries (a := ⟨5⟩)
    (σ := σC ws.length ws kvs iv false dead na)
    (v := v) rfl (unorm_of_range hw0 hw64)
    (unorm_of_range (by omega) (by exact_mod_cast hv))
  rw [show Heap.set (σC ws.length ws kvs iv false dead na).heap (.base ⟨5⟩)
      ⟨none, .mapData (toEntries (setk kvs w v))⟩
      = frontC ws.length ws (setk kvs w v) iv false ++ dead from rfl] at hMA
  exact stepFn_mapAssign_apply hMA

/-- **One counting iteration** (exit test true at word `i`): the map
data cell advances from the counts of `ws.take i` to those of
`ws.take (i+1)`; two fresh dead cells land at `na`, `na + 1`. 53
steps — INSTANTIATED from the placement-generic `wcIter_generic`
(consolidation slice 2026-08-13). -/
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
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsList (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h := wcIter_generic (σC ws.length ws) ws 1 5 9 headC cmpContC
    postBodyK env3 u1Env uEnv
    (fun kvs iv dead na ch => wc_segC1_raw ws.length ws kvs iv dead na ch)
    (wcC_init1 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC2_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_st1 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC3_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_init2 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC4_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_read ws)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC5_raw ws.length ws kvs iv dead na₀ na w ch)
    (wcC_st2 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC6_raw ws.length ws kvs iv dead na₀ na ch)
    (wcC_var1 ws)
    (wcC_var2 ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC7_raw ws.length ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC8_raw ws.length ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      wc_segC9_raw ws.length ws kvs iv dead na₀ na w ch)
    (wcC_mapGet ws)
    (fun kvs iv dead na₀ na w cv ch =>
      wc_segC10_raw ws.length ws kvs iv dead na₀ na w cv ch)
    (wcC_mapAsgn ws)
    (fun kvs iv dead na₀ na ch =>
      wc_segC11_raw ws.length ws kvs iv dead na₀ na ch)
    (countsList (ws.take i)) i dead na ch hi hw.1 hw.2 hcnt hna hdead
  rw [show setk (countsList (ws.take i)) (ws.getD i 0)
      (cnt (countsList (ws.take i)) (ws.getD i 0) + 1)
      = countsList (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsList_append_word, ← take_succ_getD hi]] at h
  exact h

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
  have h2 := stepFnIter_one (stepFn_seqn_splice
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

private theorem wcC_initBest (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 9 ≤ na → DeadFrom dead na →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.exec (.initialization { id := "best", typ := tU64 }) envR0
          (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] envR0 frameK)) ch
      = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRB na) frameK),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨na⟩, u64cell 0)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σC ws.length ws kvs iv false dead na)
    (p := { id := "best", typ := tU64 })
    (rest := [.assign (.var "best") (.intLit 0 .uint64),
      wcMapRangeStmt, retSeqn])
    (env := envR0) (k := frameK) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σC ws.length ws kvs iv false dead na).nextAddr = na from rfl,
    show (σC ws.length ws kvs iv false dead na).heap
      = frontC ws.length ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcC_stBest (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), 9 ≤ B → DeadFrom dead B →
    stepFn (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
          [.int 0 .uint64] (.seqn #[]) (envRB B)
          (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRB B)
            (.seq [wcMapRangeStmt, retSeqn] (envRB B) frameK)),
          σC ws.length ws kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na,
          ch) := by
  intro kvs iv dead B na ch hB hdead
  have hlook : Heap.lookup
      (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)]))
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs iv false hB),
      lookup_append_right (hdead B (Nat.le_refl B))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int 0 .uint64) (v' := .int 0 .uint64)
    hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, IntKind.normalize, IntKind.bits?, IntKind.signed])
  rw [show (σC ws.length ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      = frontC ws.length ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)])
      from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs iv false hB),
    set_append_right (hdead B (Nat.le_refl B)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcC_snap (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int)) →
    stepFn (σC ws.length ws kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨5⟩)⟩)
          (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRB B)
            (kR B))) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
            (toEntries kvs) (envRB B) (kR B)),
          σC ws.length ws kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch hkv
  exact stepFn_snapshot (snapshot_toEntries (a := ⟨5⟩) (dty := none) rfl hkv)

/-- **The counting loop**, by strong induction on the remaining word
count: from the exit-test delivery at word `i`, the run reaches the
RANGE HEAD over the snapshot of the full counts, with `best` zeroed at
address `na + 2·(L - i)`, within `84·(L-i) + 23` steps — INSTANTIATED
from the placement-generic `wcLoop_generic` (consolidation slice
2026-08-13). -/
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
  intro n i hn hi dead na hna hdead ch
  obtain ⟨k, tail, hk, htail, hbest, hrun⟩ :=
    wcLoop_generic (σC ws.length ws) ws 1 5 9 headC cmpContC frameK
      env2 envR0 envRB kR hlen
      (fun i dead na ch hi hna hdead =>
        wc_count_iter ws i dead na ch hws hlen hi hna hdead)
      (fun kvs iv dead na ch =>
        wc_segA1_raw ws.length ws kvs iv dead na ch)
      (fun kvs iv dead na ch =>
        wc_segX0_raw ws.length ws kvs iv dead na ch)
      (wcC_initBest ws)
      (fun kvs iv dead B na ch =>
        wc_segX0b_raw ws.length ws kvs iv dead B na ch)
      (wcC_stBest ws)
      (fun kvs iv dead B na ch =>
        wc_segX0c_raw ws.length ws kvs iv dead B na ch)
      (wcC_snap ws)
      (countsList_norm ws hws hlen)
      n i hn hi dead na hna hdead ch
  exact ⟨k, tail, hk, htail, hbest, hrun⟩

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

/-! ### The placement-generic range loop (consolidation slice: the
§10b choice-pick induction stated once)

The range body's segments never touch the heap — they are proven ONCE
over a fully abstract `σ : ExecState` (the state rides through). The
per-placement content is exactly four transitions: the pick (allocates
the iteration's value cell), the two variable reads (`c`, `best`), and
the `best` store — hypotheses whose types pin every state (the E-form
made structural, as in the counting layer). -/

section RangeGeneric

variable (envRBg : Nat → LocalEnv) (kRg : Nat → Cont)

/-- The iteration env: `c` at the pick cell over the placement's
range env. -/
private def envIterR (B na : Nat) : LocalEnv :=
  [("c", .base ⟨na⟩)] :: envRBg B
private def envIfR (B na : Nat) : LocalEnv := [] :: envIterR envRBg B na
private def thenBlkR : Stmt :=
  .block #[] #[.seqn #[.assign (.var "best") (.var "c")]]
private def iterKR (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRBg B) (kRg B)
private def ifKRR (B na : Nat) (rem : List (Int × Nat)) : Cont :=
  .ifK thenBlkR (.seqn #[]) (envIfR envRBg B na)
    (.seq [] (envIfR envRBg B na) (iterKR envRBg kRg B rem))
private def env4R (B na : Nat) : LocalEnv := [] :: envIfR envRBg B na
private def storeBestKR (B na : Nat) (rem : List (Int × Nat)) : Cont :=
  .seq [] (env4R envRBg B na)
    (.seq [] (envIfR envRBg B na) (iterKR envRBg kRg B rem))
/-- The range head at the placement. -/
private def rangeHeadR (B : Nat) (rem : List (Int × Nat)) : Config :=
  .next (iterKR envRBg kRg B rem)

/-- R1: body entry → the `c` read of the comparison. 4 steps —
σ-abstract (no heap touch). -/
private theorem segR1_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.exec wcRangeBody (envIterR envRBg B na₀) (iterKR envRBg kRg B rem))
      ch
      = .ok (.evalE (.var "c") (envIfR envRBg B na₀)
            (.strictK .greaterCmp [] [.var "best"] (envIfR envRBg B na₀)
              (ifKRR envRBg kRg B na₀ rem)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R2: `c` delivered → the `best` read. 1 step. -/
private theorem segR2_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (cv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV cv
        (.strictK .greaterCmp [] [.var "best"] (envIfR envRBg B na₀)
          (ifKRR envRBg kRg B na₀ rem))) ch
      = .ok (.evalE (.var "best") (envIfR envRBg B na₀)
            (.strictK .greaterCmp [cv] [] (envIfR envRBg B na₀)
              (ifKRR envRBg kRg B na₀ rem)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R3: `best` delivered → the `>` apply, riding symbolically. 1
step. -/
private theorem segR3_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (cv bv : Int) (ch : Choices) :
    stepFnIter 1 σ
      (.retV (.int bv .uint64)
        (.strictK .greaterCmp [.int cv .uint64] [] (envIfR envRBg B na₀)
          (ifKRR envRBg kRg B na₀ rem))) ch
      = .ok (.retV (.bool (decide (bv < cv))) (ifKRR envRBg kRg B na₀ rem),
          σ, ch) := by
  with_unfolding_all rfl

/-- R4a (then): comparison true → the inner `.seqn` splice point. 3
steps. -/
private theorem segR4a_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool true) (ifKRR envRBg kRg B na₀ rem)) ch
      = .ok (.exec (.seqn #[.assign (.var "best") (.var "c")])
            (env4R envRBg B na₀)
            (.seq [] (env4R envRBg B na₀)
              (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem))),
          σ, ch) := by
  with_unfolding_all rfl

/-- R4c: the store value delivered → the store point. 1 step. -/
private theorem segR4c_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (cv : GoValue) (ch : Choices) :
    stepFnIter 1 σ
      (.retV cv
        (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
          (.seqn #[]) (env4R envRBg B na₀)
          (storeBestKR envRBg kRg B na₀ rem))) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []] [cv]
            (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg B na₀ rem)),
          σ, ch) := by
  with_unfolding_all rfl

/-- R5: `best` stored → the next pick point. 4 steps. -/
private theorem segR5_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 4 σ
      (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
        (storeBestKR envRBg kRg B na₀ rem))) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σ) (body := .seqn #[])
    (env := env4R envRBg B na₀) (k := storeBestKR envRBg kRg B na₀ rem)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σ) (ss := #[]) (env := env4R envRBg B na₀)
    (rest := []) (k := .seq [] (envIfR envRBg B na₀)
      (iterKR envRBg kRg B rem)) (ch := ch))
  have h3 : stepFnIter 2 σ
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (env4R envRBg B na₀)
        (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem)))) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- R4e (else): comparison false → the next pick point. 3 steps. -/
private theorem segR4e_g (σ : ExecState) (rem : List (Int × Nat))
    (B na₀ : Nat) (ch : Choices) :
    stepFnIter 3 σ (.retV (.bool false) (ifKRR envRBg kRg B na₀ rem)) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
  have h1 : stepFnIter 1 σ
      (.retV (.bool false) (ifKRR envRBg kRg B na₀ rem)) ch
      = .ok (.exec (.seqn #[]) (envIfR envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem)),
          σ, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σ) (ss := #[]) (env := envIfR envRBg B na₀)
    (rest := []) (k := iterKR envRBg kRg B rem) (ch := ch))
  have h3 : stepFnIter 1 σ
      (.next (.seq ((#[] : Array Stmt).toList ++ []) (envIfR envRBg B na₀)
        (iterKR envRBg kRg B rem))) ch
      = .ok (rangeHeadR envRBg kRg B rem, σ, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The empty-snapshot drain: no choice consumed, the loop exits. 1
step. -/
private theorem segRexit_g (σ : ExecState) (B : Nat) (ch : Choices) :
    stepFnIter 1 σ (rangeHeadR envRBg kRg B []) ch
      = .ok (.next (kRg B), σ, ch) := by
  with_unfolding_all rfl

/-- **The placement-generic range loop, at every choice stream** —
induction on the snapshot size, ∀ remaining sub-list, ∀ accumulator
`bv` with the max-fold invariant, ∀ choices (§10b). The placement
enters through four pinned transition hypotheses: the choice-pick
(allocating the iteration's value cell), the `c`/`best` reads, and the
`best` store. -/
private theorem wcRange_generic
    (S : List (Int × Nat) → Int → Bool → Heap → Nat → ExecState)
    (ivP : Int) (base0 bound : Nat)
    (hbound : bound < 2 ^ 63)
    (hEnvBest : ∀ B na₀ : Nat,
      LocalEnv.lookup (envIfR envRBg B na₀) "best" = some (.base ⟨B⟩))
    (hPick : ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      base0 ≤ na → DeadFrom tail na →
      stepFn (S kvs ivP false tail na) (rangeHeadR envRBg kRg B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRBg B na)
              (iterKR envRBg kRg B (rem.eraseIdx idx)),
            S kvs ivP false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂))
    (hR4b : ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (S kvs ivP false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBg B na₀)
            (.seq [] (envIfR envRBg B na₀) (iterKR envRBg kRg B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRBg B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBg B na₀)
                (storeBestKR envRBg kRg B na₀ rem)),
            S kvs ivP false tail na, ch))
    (hVarC : ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      base0 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (S kvs ivP false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            S kvs ivP false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na, ch))
    (hVarBest : ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → base0 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (S kvs ivP false tail na) (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k, S kvs ivP false tail na, ch))
    (hStB : ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      base0 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (S kvs ivP false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBg B na₀)
            (storeBestKR envRBg kRg B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBg B na₀)
              (storeBestKR envRBg kRg B na₀ rem)),
            S kvs ivP false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch)) :
    ∀ (m : Nat) (kvs rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ bound) → bv ≤ bound →
    base0 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    DeadFrom tail na →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ DeadFrom tail' na'
      ∧ stepFnIter k (S kvs ivP false tail na)
          (rangeHeadR envRBg kRg B rem) ch
        = .ok (.next (kRg B), S kvs ivP false tail' na', ch') := by
  intro m
  induction m with
  | zero =>
      intro kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
      have hnil : rem = [] := List.eq_nil_of_length_eq_zero hm
      subst hnil
      refine ⟨1, ch, tail, na, by omega, Nat.le_refl na, ?_, htail, ?_⟩
      · simpa [maxOf_nil] using hbest
      · exact segRexit_g envRBg kRg (S kvs ivP false tail na) B ch
  | succ m ih =>
      intro kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
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
      have hpc : p.2 ≤ bound := hrem p hpmem
      have hvnorm : IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) := by
        refine unorm_of_range (by omega) ?_
        have : p.2 < 2 ^ 64 := by omega
        exact_mod_cast this
      have h1 := stepFnIter_one
        (hPick kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm
          (by omega) htail)
      have hR1 := segR1_g envRBg kRg
        (S kvs ivP false
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (na + 1))
        (rem.eraseIdx idx) B na ch₂
      have h2 := stepFnIter_chain h1 hR1
      have hbest₁ : Heap.lookup
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (.base ⟨B⟩) = some (u64cell (bv : Int)) :=
        lookup_append_left hbest
      have h3 := stepFnIter_chain h2 (stepFnIter_one
        (hVarC kvs tail na (na + 1) (p.2 : Int)
          (envIfR envRBg B na) _ ch₂ rfl (by omega) htail))
      have hR2 := segR2_g envRBg kRg
        (S kvs ivP false
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (na + 1))
        (rem.eraseIdx idx) B na (.int (p.2 : Int) .uint64) ch₂
      have h4 := stepFnIter_chain h3 hR2
      have h5 := stepFnIter_chain h4 (stepFnIter_one
        (hVarBest kvs
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B (na + 1) (bv : Int) (envIfR envRBg B na) _ ch₂ (hEnvBest B na)
          hB hbest₁))
      have hR3 := segR3_g envRBg kRg
        (S kvs ivP false
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          (na + 1))
        (rem.eraseIdx idx) B na (p.2 : Int) (bv : Int) ch₂
      have h6 := stepFnIter_chain h5 hR3
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
      have hremerase : ∀ q ∈ rem.eraseIdx idx, q.2 ≤ bound :=
        fun q hq => hrem q (mem_of_mem_eraseIdx hq)
      by_cases hcmp : bv < p.2
      · rw [show (decide ((bv : Int) < (p.2 : Int))) = true from
          decide_eq_true (by exact_mod_cast hcmp)] at h6
        have hR4a := segR4a_g envRBg kRg
          (S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na ch₂
        have h7 := stepFnIter_chain h6 hR4a
        have h8 := stepFnIter_chain h7 (stepFnIter_one (stepFn_seqn_splice
          (σ := S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (ss := #[.assign (.var "best") (.var "c")])
          (env := env4R envRBg B na)
          (rest := []) (k := .seq [] (envIfR envRBg B na)
            (iterKR envRBg kRg B (rem.eraseIdx idx))) (ch := ch₂)))
        have hR4b := hR4b kvs (rem.eraseIdx idx)
          (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
          B na (na + 1) ch₂
        have h9 := stepFnIter_chain h8 hR4b
        have h10 := stepFnIter_chain h9 (stepFnIter_one
          (hVarC kvs tail na (na + 1) (p.2 : Int)
            (env4R envRBg B na) _ ch₂ rfl (by omega) htail))
        have hR4c := segR4c_g envRBg kRg
          (S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na (.int (p.2 : Int) .uint64) ch₂
        have h11 := stepFnIter_chain h10 hR4c
        have h12 := stepFnIter_chain h11 (stepFnIter_one
          (hStB kvs (rem.eraseIdx idx)
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            B na (na + 1) (bv : Int) (p.2 : Int) ch₂ hB hbest₁ hvnorm))
        rw [set_append_left hbest] at h12
        have hR5 := segR5_g envRBg kRg
          (S kvs ivP false
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na ch₂
        have h13 := stepFnIter_chain h12 hR5
        have hbest' : Heap.lookup
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (.base ⟨B⟩) = some (u64cell (p.2 : Int)) :=
          lookup_append_left Frame.Heap.lookup_set_self
        have htail' : DeadFrom
            (Heap.set tail (.base ⟨B⟩)
                ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1) := by
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
          ih kvs (rem.eraseIdx idx) hlenerase p.2 B (na + 1)
            (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int (p.2 : Int) .uint64⟩
              ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            ch₂ hremerase hpc hB (by omega) hbest' htail'
        refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + 1 + 4 + 1 + 1 + 1 + 4 + k',
          ch', tail₃, na₃, by omega, by omega, ?_, htail₃, ?_⟩
        · rw [show max bv (maxOf (rem.map Prod.snd))
              = max p.2 (maxOf ((rem.eraseIdx idx).map Prod.snd)) from by
            rw [hmaxsplit]
            omega]
          exact hbest₃
        · exact stepFnIter_chain h13 hrun
      · rw [show (decide ((bv : Int) < (p.2 : Int))) = false from
          decide_eq_false (by
            intro hc
            exact hcmp (by exact_mod_cast hc))] at h6
        have hR4e := segR4e_g envRBg kRg
          (S kvs ivP false
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1))
          (rem.eraseIdx idx) B na ch₂
        have h7 := stepFnIter_chain h6 hR4e
        have hbest' : Heap.lookup
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (.base ⟨B⟩) = some (u64cell (bv : Int)) :=
          lookup_append_left hbest
        have htail' : DeadFrom
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            (na + 1) := DeadFrom.push htail
        obtain ⟨k', ch', tail₃, na₃, hk', hna₃, hbest₃, htail₃, hrun⟩ :=
          ih kvs (rem.eraseIdx idx) hlenerase bv B (na + 1)
            (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
            ch₂ hremerase hbv hB (by omega) hbest' htail'
        refine ⟨1 + 4 + 1 + 1 + 1 + 1 + 3 + k', ch', tail₃, na₃, by omega,
          by omega, ?_, htail₃, ?_⟩
        · rw [show max bv (maxOf (rem.map Prod.snd))
              = max bv (maxOf ((rem.eraseIdx idx).map Prod.snd)) from by
            rw [hmaxsplit]
            omega]
          exact hbest₃
        · exact stepFnIter_chain h7 hrun

end RangeGeneric


/-! ### The canonical placement's range-loop discharges + wrapper -/

private theorem wcC_pick (ws : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      9 ≤ na → DeadFrom tail na →
      stepFn (σC ws.length ws kvs (ws.length : Int) false tail na)
          (rangeHeadR envRB kR B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRB B na)
              (iterKR envRB kR B (rem.eraseIdx idx)),
            σC ws.length ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂) := by
  intro kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm hna htail
  have hmiss : Heap.lookup
      (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hna)]
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
  exact hPick

private theorem wcC_R4b (ws : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (σC ws.length ws kvs (ws.length : Int) false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRB B na₀)
            (.seq [] (envIfR envRB B na₀) (iterKR envRB kR B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRB B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRB B na₀)
                (storeBestKR envRB kR B na₀ rem)),
            σC ws.length ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs rem tail B na₀ na ch
  with_unfolding_all rfl

private theorem wcC_varC (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      9 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (σC ws.length ws kvs (ws.length : Int) false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            σC ws.length ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na,
            ch) := by
  intro kvs tail na₀ na v env k ch henv hna hdead
  refine stepFn_var (c := ⟨some tU64, .int v .uint64⟩) henv ?_
  show Heap.lookup
    (frontC ws.length ws kvs (ws.length : Int) false
      ++ (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]))
    (.base ⟨na₀⟩) = some ⟨some tU64, .int v .uint64⟩
  rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_singleton_self

private theorem wcC_varBest (ws : List Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → 9 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (σC ws.length ws kvs (ws.length : Int) false tail na)
          (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k,
            σC ws.length ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs tail B na bv env k ch henv hB hlkB
  refine stepFn_var (c := u64cell bv) henv ?_
  show Heap.lookup
    (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
    (.base ⟨B⟩) = some (u64cell bv)
  rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hB)]
  exact hlkB

private theorem wcC_stB (ws : List Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      9 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (σC ws.length ws kvs (ws.length : Int) false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRB B na₀)
            (storeBestKR envRB kR B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRB B na₀)
              (storeBestKR envRB kR B na₀ rem)),
            σC ws.length ws kvs (ws.length : Int) false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch) := by
  intro kvs rem tail B na₀ na bv v ch hB hlkB hvn
  have hlook : Heap.lookup
      (σC ws.length ws kvs (ws.length : Int) false tail na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup
      (frontC ws.length ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right (lookup_frontC_none ws.length ws kvs
        (ws.length : Int) false hB)]
    exact hlkB
  have h := storeTarget_addr (v := .int v .uint64) (v' := .int v .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hvn]
      rfl)
  rw [show (σC ws.length ws kvs (ws.length : Int) false tail na).heap
      = frontC ws.length ws kvs (ws.length : Int) false ++ tail from rfl,
    set_append_right (lookup_frontC_none ws.length ws kvs
      (ws.length : Int) false hB)] at h
  exact stepFn_store_step h

/-- **The range loop, at every choice stream** — INSTANTIATED from the
placement-generic `wcRange_generic` (§10b; consolidation slice
2026-08-13). -/
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
  intro m rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
  obtain ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩ :=
    wcRange_generic envRB kR (σC ws.length ws) (ws.length : Int) 9
      ws.length hlen
      (fun B na₀ => rfl)
      (wcC_pick ws) (wcC_R4b ws) (wcC_varC ws) (wcC_varBest ws)
      (wcC_stB ws)
      m kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
  exact ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩


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
  have h2 := stepFnIter_one (stepFn_seqn_splice
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
  have h2 := stepFnIter_one (stepFn_seqn_splice
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

/-! ## The parameterized harness (gap G1 — CLOSED, consolidation
slice 2026-08-14)

The `(n, seed)`-parameterized §11 headline over `wordcount_harness`
(setup builds `w[i] = seed + i%3`, the call under test runs
`maxCount(w)`, the max count returns as data) is SHIPPED below as
`wordcount_ok` (+ the derived `wordcount_readout`), fuel bound
`229 + 165·n`, axioms the classical trio.

**HOW THE 2026-08-13 BLOCKER CLOSED (the record the old gap note owed
its successor).** The former storm — the harness composition proofs
(`wcH_count_iter`/`wcH_count_loop` as verbatim address-renames)
grinding the elaborator at 52 GB — was DIAGNOSED by bisection
(variants in `.tmp/prof-{A..E}.lean`; full record
`docs/2026-08-13_consolidation-slice.md` §1): postponed-elaboration
metavariables inside a big concrete-state argument defeat structural
unification, and isDefEq's delta fallback compares `Heap.lookup` over
the concrete front at a symbolic address — a stuck-`if` nest compared
without caching, ~2^N in the front length (2^9 canonical squeaked by;
2^16 harness stormed). The recorded "combination with the rw-surgered
hypothesis" theory was REFUTED (a context-minimal variant storms
identically); a full-type-ascribed application is INSTANT. Fix, made
structural: the counting AND range compositions are stated ONCE over
an abstract state family with every per-segment transition fact a
hypothesis whose type pins the intermediate states
(`wcIter_generic`/`wcLoop_generic`/`wcRange_generic`); the canonical
and harness placements consume them by instantiation, so no concrete
front ever reaches the unifier.

**THE SEED-WRAP CAVEAT, SETTLED (recorded finding, kept)**: the gap
record carried `hseed : seed + 2 < 2^64` on the theory that family
values collide near the wrap boundary and change `maxMultiplicity`.
That is WRONG: the family's values are `(seed + r) mod 2^64` for
`r ∈ {0,1,2}`, and two of those are equal iff `r ≡ r' (mod 2^64)` —
impossible for distinct `r, r' ≤ 2`. So no collision exists at ANY
seed, the wrap belongs in the family definition (`wcFamily`), the
shipped hypothesis is just the uint64 domain `hseed : seed < 2^64`
(consumed only by the entry equation's argument normalization), and
the returned value is `⌈n/3⌉ = (n+2)/3` unconditionally — proven as
`wcFamily_maxMult`, where the no-collision analysis is actually
consumed.

Address layout (probe-verified at `(n, seed) = (4, 7)`; every raw
segment below re-checks the transcription by `rfl`): 0 = `n`,
1 = `seed`, 2 = the harness `$res0`, 3 = `$c9` (the make temp),
4 = the `w` BACKING array, 5 = `w`, 6 = the setup counter (parked at
`n`), 7 = the setup flag, 8 = `$c10` (the call-result temp), 9 = the
subject's `words` parameter, 10 = the subject's `$res0`, 11 = `$c0`,
12 = the map DATA cell, 13 = `counts`, 14 = the subject's `i`,
15 = the subject's `$forFirst` — then the symbolic region from 16
(two dead cells per counting iteration, `best` at `16 + 2n`, one per
range iteration). Fuel bound: `229 + 165·n` (probe: the whole
`(4, 7)` run is 841 steps; the bound gives 889). -/

/-- **The input family**: the slice contents the setup phase builds from
`(n, seed)` — `w[i] = seed + i%3`, wrapped at `2^64` (Go's uint64
addition; the wrap is part of the family by design, so the family
covers wrap-boundary seeds). -/
def wcFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => (((seed + i % 3) % 2 ^ 64 : Nat) : Int))

private theorem wcFamily_length (n seed : Nat) :
    (wcFamily n seed).length = n := by
  simp [wcFamily]

private theorem wcFamily_range (n seed : Nat) :
    ∀ v ∈ wcFamily n seed, 0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  simp only [wcFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, -, rfl⟩ := hv
  have : (seed + i % 3) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  omega

private theorem wcFamilyZ_range {n seed i : Nat} :
    ∀ v ∈ wcFamily i seed ++ List.replicate (n - i) (0 : Int),
      0 ≤ v ∧ v < 2 ^ 64 := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact wcFamily_range i seed v hv
  · rcases List.mem_replicate.mp hv with ⟨-, rfl⟩
    omega

private theorem wcFamily_succ (i seed : Nat) :
    wcFamily (i + 1) seed
      = wcFamily i seed ++ [(((seed + i % 3) % 2 ^ 64 : Nat) : Int)] := by
  simp [wcFamily, List.range_succ]

/-- One setup store advances the family prefix. -/
private theorem wcFamily_set {n seed i : Nat} (hi : i < n) :
    (wcFamily i seed ++ List.replicate (n - i) 0).set i
        (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      = wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0 := by
  have hlen : (wcFamily i seed).length = i := wcFamily_length i seed
  have hnm : n - i = (n - (i + 1)) + 1 := by omega
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, hnm,
    List.replicate_succ, List.set_cons_zero, wcFamily_succ]
  simp

/-! ### The closed-form value: `maxMultiplicity (wcFamily n seed)
= ⌈n/3⌉`, at EVERY seed — the no-collision analysis, consumed -/

/-- The family's value at residue `r`. -/
private def wcVal (seed r : Nat) : Int := (((seed + r) % 2 ^ 64 : Nat) : Int)

/-- **No collision at any seed**: two residue values are equal only at
equal residues — `(seed + a) ≡ (seed + b) (mod 2^64)` forces `a = b`
for `a, b < 3 ≤ 2^64`. This refutes the recorded `seed + 2 < 2^64`
caveat. -/
private theorem wcVal_inj {seed a b : Nat} (ha : a < 3) (hb : b < 3)
    (h : wcVal seed a = wcVal seed b) : a = b := by
  have h' : (seed + a) % 2 ^ 64 = (seed + b) % 2 ^ 64 := by
    have h2 := h
    simp only [wcVal] at h2
    exact_mod_cast h2
  omega

private theorem multiplicity_append_one (v w : Int) (ws : List Int) :
    multiplicity v (ws ++ [w])
      = multiplicity v ws + (if w = v then 1 else 0) := by
  simp only [multiplicity, List.filter_append, List.length_append]
  by_cases h : w = v
  · simp [h]
  · simp [h]

/-- Residue `r`'s multiplicity in the family is the count of `i < n`
with `i % 3 = r`, in closed form. -/
private theorem multiplicity_wcVal (seed r : Nat) (hr : r < 3) :
    ∀ n : Nat, multiplicity (wcVal seed r) (wcFamily n seed)
      = (n + (2 - r)) / 3 := by
  intro n
  induction n with
  | zero =>
      have h0 : multiplicity (wcVal seed r) (wcFamily 0 seed) = 0 := rfl
      rw [h0]
      omega
  | succ m ih =>
      rw [wcFamily_succ, multiplicity_append_one, ih,
        show (((seed + m % 3) % 2 ^ 64 : Nat) : Int) = wcVal seed (m % 3)
          from rfl]
      by_cases h : m % 3 = r
      · rw [if_pos (show wcVal seed (m % 3) = wcVal seed r from by rw [h])]
        omega
      · rw [if_neg (fun hc =>
          h (wcVal_inj (Nat.mod_lt _ (by omega)) hr hc))]
        omega

private theorem mem_wcFamily_eq {n seed : Nat} {v : Int}
    (hv : v ∈ wcFamily n seed) : ∃ i, i < n ∧ v = wcVal seed (i % 3) := by
  simp only [wcFamily, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact ⟨i, hi, rfl⟩

private theorem wcVal_mem {n seed i : Nat} (hi : i < n) :
    wcVal seed (i % 3) ∈ wcFamily n seed := by
  simp only [wcFamily, List.mem_map, List.mem_range]
  exact ⟨i, hi, rfl⟩

/-- **The headline's returned value in closed arithmetic form**: the
max multiplicity of the setup family is `⌈n/3⌉ = (n+2)/3`, at EVERY
seed — residue 0 is always (weakly) most frequent, and no seed makes
two residue values collide (`wcVal_inj`). -/
theorem wcFamily_maxMult (n seed : Nat) :
    maxMultiplicity (wcFamily n seed) = (n + 2) / 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · apply Nat.le_antisymm
    · apply maxMult_le
      intro v hv
      obtain ⟨i, hi, rfl⟩ := mem_wcFamily_eq hv
      rw [multiplicity_wcVal seed (i % 3) (Nat.mod_lt _ (by omega)) n]
      omega
    · have h0 : multiplicity (wcVal seed 0) (wcFamily n seed)
          = (n + 2) / 3 := multiplicity_wcVal seed 0 (by omega) n
      rw [← h0]
      apply mult_le_maxMult
      have := wcVal_mem (seed := seed) (i := 0) hn
      simpa using this

/-! ### The harness `Func`, pinned -/

/-- The harness `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`): setup `w := make([]uint64, n)`
filled with `w[i] = seed + i%3`, the call under test `maxCount(w)`,
the max count returned as data. -/
def wordcountHarnessFunc : Func :=
  { id := { key := "wordcount_harness" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "$c9", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c9") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "w", typ := .slice (.int .uint64) },
            .assign (.var "w") (.var "$c9")],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) suBody]],
        .seqn
          #[.initialization { id := "$c10", typ := .int .uint64 },
            .call #[.var "$c10"] { key := "maxCount" } #[.var "w"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c10"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The setup loop's desugared body: the `$forFirst` dispatch, the
    exit test, the fill block `{ w[i] = seed + i%3 }`. -/
    suBody : Stmt :=
      .block
        #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i")
              (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n"))
            (.seqn #[])
            .breakStmt,
          .block
            #[]
            #[.seqn
                #[.assign (.addr (.indexAddr (.var "w") (.var "i")))
                    (.add (.var "seed")
                      (.mod (.var "i") (.intLit 3 .uint64)))]]]

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
example : findFunctionIn? wordCountLowered.funcs ⟨"wordcount_harness"⟩
    = some wordcountHarnessFunc := rfl

/-! ### The entry equation and the setup phase (harness addresses
0–8; every segment `with_unfolding_all rfl` except the conditioned
makeSlice / `%` / element-store steps) -/

private def hWScope0 : Scope :=
  [("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]

/-- The machine entry's post-prelude state: the three frame cells the
prelude allocates from the EMPTY heap (arguments normalized at their
declared uint64 — the normalize is applied at the ARGUMENT position so
the headline's hypotheses can collapse it). -/
private def σWH0 (nv sv : Int) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv),
             (.base ⟨2⟩, u64cell 0)],
    nextAddr := 3 }

private def hWFrame0 : Cont := .frame [] [] [] [] .stop

/-- **The entry equation** (§11 glue, wordcount instance): the machine
entry IS its post-prelude `runConfig` form — `with_unfolding_all rfl`
at fully symbolic arguments, fuel, and choices. -/
private theorem wcH_entry_eq (nv sv : Int) (fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
        wordCountLowered.funcs wordcountHarnessFunc
        #[.int nv .uint64, .int sv .uint64]
        wordCountLowered.methods ch
      = (do
          let r ← runConfig fuel
            (σWH0 (IntKind.normalize .uint64 nv)
              (IntKind.normalize .uint64 sv))
            (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
          return { values := (← loadMany r.1 [.base ⟨2⟩]).toArray }) := by
  with_unfolding_all rfl

/-- The harness slice handle: backing at its fixed address 4. -/
private abbrev wHandleCell (n : Nat) : HeapCell :=
  ⟨some (.slice tU64), .slice ⟨some (.base ⟨4⟩), 0, n, n⟩⟩
private abbrev wSliceH (n : Nat) : GoValue :=
  .slice ⟨some (.base ⟨4⟩), 0, n, n⟩

/-- The harness body's top statement list (projection of the pinned
record — reducible data, so the `rfl` segments see through it). -/
private def hWBodyList : List Stmt :=
  match wordcountHarnessFunc.body with
  | .block _ ss => ss.toList
  | _ => []

private def envWC9 : LocalEnv := [[("$c9", .base ⟨3⟩)], hWScope0]
private def hWAfterMsK : Cont := .seq (hWBodyList.drop 1) envWC9 hWFrame0
private def hWMsK : Cont :=
  .stmtOpK (.makeSlice tU64 false) 1 [.addr (.base ⟨3⟩)] [] envWC9
    hWAfterMsK

/-- `$c9` declared (default slice), the makeSlice length delivered. -/
private def σWStartC9 (nv sv : Int) : ExecState :=
  { σWH0 nv sv with
    heap := (σWH0 nv sv).heap
      ++ [(.base ⟨3⟩, ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩)],
    nextAddr := 4 }

/-- Entry A: harness body start → the makeSlice length delivery.
10 steps. -/
private theorem wcH_E1_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 10 (σWH0 ((n : Nat) : Int) ((seed : Nat) : Int))
      (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
      = .ok (.retV (.int ((n : Nat) : Int) .uint64) hWMsK,
          σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int), ch) := by
  with_unfolding_all rfl

/-- Post-makeSlice: the handle in `$c9`, the zeroed backing at 4. -/
private def σWMkS (n seed : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell (seed : Int)),
             (.base ⟨2⟩, u64cell 0),
             (.base ⟨3⟩, wHandleCell n),
             (.base ⟨4⟩, arrCell n (List.replicate n 0))],
    nextAddr := 5 }

/-- **The makeSlice apply at a SYMBOLIC length**: allocates the zeroed
backing at 4 and stores the handle in `$c9`
(`GoLean.Iris.buildDefaultArrayValue_int`, proof-side import). -/
private theorem wcH_makeSlice (n seed : Nat) (ch : Choices) :
    stepFn (σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int))
      (.retV (.int ((n : Nat) : Int) .uint64) hWMsK) ch
      = .ok (.next hWAfterMsK, σWMkS n seed, ch) := by
  have hb := GoLean.Iris.buildDefaultArrayValue_int
    (σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int)) .uint64 n
  have harr : (List.replicate n (GoValue.int 0 .uint64)).toArray
      = (⟨(List.replicate n (0 : Int)).map
          (fun v => GoValue.int v .uint64)⟩ : Array GoValue) := by
    simp [List.map_replicate]
  rw [harr] at hb
  have hnn1 := natFromNonneg_cast
    "runtime error: makeslice: len out of range" n
  have hnn2 := natFromNonneg_cast
    "runtime error: makeslice: cap out of range" n
  have happly : applyStmtOp (σWStartC9 ((n : Nat) : Int) ((seed : Nat) : Int))
      ch (.makeSlice tU64 false) 1
      [.addr (.base ⟨3⟩), .int ((n : Nat) : Int) .uint64]
      = .ok (σWMkS n seed, ch) := by
    simp only [applyStmtOp, applyStmtOpCore, valueAsInt, valueAsLoc,
      hnn1, hnn2, hb, Bind.bind, Except.bind, pure, Except.pure]
    rw [if_neg (Nat.lt_irrefl n)]
    with_unfolding_all rfl
  exact stepFn_stmtOp_apply
    (done := [.addr (.base ⟨3⟩)]) (v := .int ((n : Nat) : Int) .uint64)
    happly

/-! ### The setup loop (fixed cells 0–7; the loop never allocates) -/

private def wScopeH : Scope := [("w", .base ⟨5⟩), ("$c9", .base ⟨3⟩)]
private def suWEnv : LocalEnv :=
  [[("$forFirst", .base ⟨7⟩)], [("i", .base ⟨6⟩)], wScopeH, hWScope0]

/-- The setup-loop state family: backing list `l`, counter `iv`,
flag. -/
private def sWSU (n : Nat) (sv : Int) (l : List Int) (iv : Int)
    (ff : Bool) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell sv),
             (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, wHandleCell n),
             (.base ⟨4⟩, arrCell n l), (.base ⟨5⟩, wHandleCell n),
             (.base ⟨6⟩, u64cell iv), (.base ⟨7⟩, bcell ff)],
    nextAddr := 8 }

private def suWTail : Cont :=
  .seq [] suWEnv
    (.seq [] [[("i", .base ⟨6⟩)], wScopeH, hWScope0]
      (.seq (hWBodyList.drop 3) [wScopeH, hWScope0] hWFrame0))
private def suWHeadCfg : Config :=
  .exec (.while (.boolLit true) wordcountHarnessFunc.suBody) suWEnv suWTail
private def suWLoopK : Cont :=
  .loop (.boolLit true) wordcountHarnessFunc.suBody suWEnv suWTail
private def suWStoreBlk : Stmt :=
  .block #[]
    #[.seqn
        #[.assign (.addr (.indexAddr (.var "w") (.var "i")))
            (.add (.var "seed") (.mod (.var "i") (.intLit 3 .uint64)))]]
private def suWCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suWEnv)
    (.seq [suWStoreBlk] ([] :: suWEnv) suWLoopK)
private def envW6 : LocalEnv := [] :: [] :: suWEnv
private def suWRef (n : Nat) (iv : Int) : TargetRef :=
  .chain (wSliceH n) [.int iv .uint64] [.index]
private def suWStoreTail : Cont :=
  .seq [] envW6 (.seq [] ([] :: suWEnv) suWLoopK)
private def suWRhsK (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [suWRef n iv] [] [] (.seqn #[]) envW6 suWStoreTail
private def suWAddK (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] envW6 (suWRhsK n iv)
private def suWModK (n : Nat) (sv iv : Int) : Cont :=
  .strictK .mod [.int iv .uint64] [] envW6 (suWAddK n sv iv)

/-- Entry B: makeSlice done → `w := $c9`, `i := 0`, the flag block →
the setup loop head. 42 steps. -/
private theorem wcH_E2_raw (n seed : Nat) (ch : Choices) :
    stepFnIter 42 (σWMkS n seed) (.next hWAfterMsK) ch
      = .ok (suWHeadCfg,
          sWSU n (seed : Int) (List.replicate n 0) 0 true, ch) := by
  with_unfolding_all rfl

/-- Setup first-pass dispatch: the flag drops, the exit test `i < n`
delivers. 25 steps. -/
private theorem wcH_suA0_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 25 (sWSU n sv l iv true) suWHeadCfg ch
      = .ok (.retV (.bool (decide (iv < ((n : Nat) : Int)))) suWCmpK,
          sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase A: test true → the `%` apply point (the divisor
literal delivered; the one data-dependent arithmetic branch is the
divide-by-zero check, discharged by the conditioned step below).
19 steps. -/
private theorem wcH_suB1a_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 19 (sWSU n sv l iv false) (.retV (.bool true) suWCmpK) ch
      = .ok (.retV (.int 3 .uint64) (suWModK n sv iv),
          sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill phase B: the `%` result delivered → the add runs → the
element-store point (the wrapped `seed + i%3` riding). 2 steps. -/
private theorem wcH_suB1b_raw (n : Nat) (sv iv rv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 2 (sWSU n sv l iv false)
      (.retV (.int rv .uint64) (suWAddK n sv iv)) ch
      = .ok (.next (.storeK [suWRef n iv]
            [.int (IntKind.normalize .uint64 (sv + rv)) .uint64]
            (.seqn #[]) envW6 suWStoreTail),
          sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup fill tail: store done → back to the loop head. 5 steps. -/
private theorem wcH_suD_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 5 (sWSU n sv l iv false)
      (.next (.storeK [] [] (.seqn #[]) envW6 suWStoreTail)) ch
      = .ok (suWHeadCfg, sWSU n sv l iv false, ch) := by
  with_unfolding_all rfl

/-- Setup later-pass dispatch: `i++`, then the exit test. 29 steps. -/
private theorem wcH_suA1_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 29 (sWSU n sv l iv false) suWHeadCfg ch
      = .ok (.retV (.bool (decide
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1))
              < ((n : Nat) : Int)))) suWCmpK,
          sWSU n sv l
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 (iv + 1)))
            false, ch) := by
  with_unfolding_all rfl

/-- One setup iteration from the exit-test's true delivery at `i`:
`i % 3` (conditioned), the wrapped add, the element store, back to the
head, `i++`, the next test — the family prefix advanced. 57 steps. -/
private theorem wcH_su_iter (n seed i : Nat) (hn : n < 2 ^ 63)
    (hi : i < n) (ch : Choices) :
    stepFnIter 57
      (sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool true) suWCmpK) ch
      = .ok (.retV (.bool (decide
            (((i + 1 : Nat) : Int) < ((n : Nat) : Int)))) suWCmpK,
          sWSU n (seed : Int)
            (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0)
            ((i + 1 : Nat) : Int) false, ch) := by
  have hB1a := wcH_suB1a_raw n (seed : Int) ((i : Nat) : Int)
    (wcFamily i seed ++ List.replicate (n - i) 0) ch
  -- the % apply, conditioned
  have hmod := stepFnIter_one (stepFn_strict_apply
    (done := [.int ((i : Nat) : Int) .uint64])
    (env := envW6) (k := suWAddK n (seed : Int) ((i : Nat) : Int))
    (ch := ch)
    (applyStrictOp_mod_u64
      (σ := sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (a := i) (b := 3) (by omega) (by omega)))
  have h1 := stepFnIter_chain hB1a hmod
  -- the add + rhs collect
  have hB1b := wcH_suB1b_raw n (seed : Int) ((i : Nat) : Int)
    ((i % 3 : Nat) : Int) (wcFamily i seed ++ List.replicate (n - i) 0) ch
  rw [unorm_add_nat seed (i % 3)] at hB1b
  have h2 := stepFnIter_chain h1 hB1b
  -- the element store
  have hw : (0 : Int) ≤ (((seed + i % 3) % 2 ^ 64 : Nat) : Int)
      ∧ (((seed + i % 3) % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
    have := Nat.mod_lt (seed + i % 3) (y := 2 ^ 64) (by omega)
    omega
  have hst := storeTarget_slice_u64
    (σ := sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
      ((i : Nat) : Int) false)
    (a := ⟨4⟩) (off := 0) (len := n) (cap := n) (i := i) (n := n)
    (ik := .uint64) (l := wcFamily i seed ++ List.replicate (n - i) 0)
    (w := (((seed + i % 3) % 2 ^ 64 : Nat) : Int))
    rfl (Nat.le_refl n) hi
    (by rw [List.length_append, wcFamily_length, List.length_replicate]
        omega)
    (by rw [List.length_append, wcFamily_length, List.length_replicate]
        omega)
    wcFamilyZ_range hw
  rw [Nat.zero_add, wcFamily_set hi] at hst
  have h3 := stepFnIter_chain h2
    (stepFnIter_one (stepFn_store_step hst))
  -- store drain → head → i++ → the next test
  have hD := wcH_suD_raw n (seed : Int) ((i : Nat) : Int)
    (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
  have h4 := stepFnIter_chain h3 hD
  have hA1 := wcH_suA1_raw n (seed : Int) ((i : Nat) : Int)
    (wcFamily (i + 1) seed ++ List.replicate (n - (i + 1)) 0) ch
  rw [show ((i : Nat) : Int) + 1 = ((i + 1 : Nat) : Int) from by omega,
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega),
    unorm_of_range (v := ((i + 1 : Nat) : Int)) (by omega) (by omega)] at hA1
  exact stepFnIter_chain h4 hA1

/-- **The setup loop**, by strong induction on `n - i`: exactly
`57·(n-i)` steps materialize the wrapped `seed + i%3` family. No
seed hypothesis — the wrap is the family's own definition; only the
length domain `n < 2^63` is consumed, for the counter arithmetic. -/
private theorem wcH_setup_loop (n seed : Nat) (hn : n < 2 ^ 63) :
    ∀ μ i, μ = n - i → i ≤ n → ∀ ch : Choices,
    stepFnIter (57 * (n - i))
      (sWSU n (seed : Int) (wcFamily i seed ++ List.replicate (n - i) 0)
        ((i : Nat) : Int) false)
      (.retV (.bool (decide (((i : Nat) : Int) < ((n : Nat) : Int))))
        suWCmpK) ch
      = .ok (.retV (.bool (decide
            (((n : Nat) : Int) < ((n : Nat) : Int)))) suWCmpK,
          sWSU n (seed : Int) (wcFamily n seed) ((n : Nat) : Int) false,
          ch) := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
    intro i hμ hin ch
    rcases Nat.lt_or_ge i n with hlt | hge
    · rw [show (decide (((i : Nat) : Int) < ((n : Nat) : Int))) = true from
        decide_eq_true (by exact_mod_cast hlt)]
      have hiter := wcH_su_iter n seed i hn hlt ch
      have hrec := ih (n - (i + 1)) (by omega) (i + 1) rfl (by omega) ch
      have hc := stepFnIter_chain hiter hrec
      rw [show 57 + 57 * (n - (i + 1)) = 57 * (n - i) from by omega] at hc
      exact hc
    · have hEq : i = n := by omega
      subst hEq
      simp only [Nat.sub_self, Nat.mul_zero, List.replicate_zero,
        List.append_nil]
      rfl

/-! ### The subject phase at the harness placement (front cells 0–15,
symbolic region from 16) — the phase-C tower re-instantiated: same
statements, same step counts, new concrete addresses, and the subject
frame sitting on the harness's after-call continuation instead of the
driver's `frameK` -/

private def envWCall : LocalEnv :=
  [[("$c10", .base ⟨8⟩), ("w", .base ⟨5⟩), ("$c9", .base ⟨3⟩)], hWScope0]
private def afterCallKW : Cont := .seq (hWBodyList.drop 4) envWCall hWFrame0
private def callKW : Cont :=
  .callArgsK ⟨"maxCount"⟩ [(.chain [], [.ref "$c10"])] [] [] envWCall
    afterCallKW
/-- The subject's call frame: result loc 10, write-back target `$c10`,
returning into the harness's tail — the abstract-outer-continuation
point of the re-instantiation. -/
private def frameKH : Cont :=
  .frame [(.chain [], [.ref "$c10"])] envWCall [.base ⟨10⟩] [] afterCallKW

private def sc0H : Scope := [("$res0", .base ⟨10⟩), ("words", .base ⟨9⟩)]
private def sc1H : Scope := [("counts", .base ⟨13⟩), ("$c0", .base ⟨11⟩)]
private def envR0H : LocalEnv := [sc1H, sc0H]
private def envBH : LocalEnv :=
  [[("$forFirst", .base ⟨15⟩)], [("i", .base ⟨14⟩)], sc1H, sc0H]
private def envB1H : LocalEnv := [[("i", .base ⟨14⟩)], sc1H, sc0H]
private def env2H : LocalEnv := [] :: envBH
private def env3H : LocalEnv := [] :: env2H
private def u1EnvH (na : Nat) : LocalEnv := [("$c1", .base ⟨na⟩)] :: env2H
private def uEnvH (na : Nat) : LocalEnv :=
  [("$c2", .base ⟨na + 1⟩), ("$c1", .base ⟨na⟩)] :: env2H

private def tailBH : Cont :=
  .seq [] envBH (.seq [] envB1H
    (.seq [bestSeqn, wcMapRangeStmt, retSeqn] envR0H frameKH))
/-- The counting-loop head configuration (harness placement). -/
private def headCH : Config :=
  .exec (.while (.boolLit true) wcWhileBody) envBH tailBH
private def loopKCH : Cont := .loop (.boolLit true) wcWhileBody envBH tailBH
private def bodyTailH : Cont := .seq [wcCountBody] env2H loopKCH
private def cmpContCH : Cont := .ifK (.seqn #[]) .breakStmt env2H bodyTailH
private def lenKH (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] env2H
    (.strictK .lessCmp [.int iv .int] [] env2H cmpContCH)
private def postBodyKH : Cont := .seq [] env2H loopKCH

private abbrev mhCellW : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨12⟩)⟩⟩

/-- The sixteen concrete front cells during the harness counting loop
(`sv` = the parked `seed` cell, `siv` = the parked setup counter). -/
private def frontH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, wHandleCell L),
   (.base ⟨4⟩, arrCell L ws), (.base ⟨5⟩, wHandleCell L),
   (.base ⟨6⟩, u64cell siv), (.base ⟨7⟩, bcell false),
   (.base ⟨8⟩, u64cell 0), (.base ⟨9⟩, wHandleCell L),
   (.base ⟨10⟩, u64cell 0), (.base ⟨11⟩, mhCellW),
   (.base ⟨12⟩, mdCell kvs), (.base ⟨13⟩, mhCellW),
   (.base ⟨14⟩, intcell iv), (.base ⟨15⟩, bcell ff)]

/-- The harness phase-C state: concrete front + the symbolic dead-cell
tail. -/
private def σH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) (dead : Heap)
    (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontH L sv siv ws kvs iv ff ++ dead, nextAddr := na }

private theorem lookup_frontH_none (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) {x : Nat}
    (hx : 16 ≤ x) :
    Heap.lookup (frontH L sv siv ws kvs iv ff) (.base ⟨x⟩) = none := by
  simp only [frontH, Heap.lookup,
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
    Bool.false_eq_true, if_false]

/-- `$c10` declared: the setup-exit state at the call's argument
delivery (cells 0–8, allocator at 9). -/
private def σWCallg (n : Nat) (sv : Int) (l : List Int) (iv : Int) :
    ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := [(.base ⟨0⟩, u64cell (n : Int)), (.base ⟨1⟩, u64cell sv),
             (.base ⟨2⟩, u64cell 0), (.base ⟨3⟩, wHandleCell n),
             (.base ⟨4⟩, arrCell n l), (.base ⟨5⟩, wHandleCell n),
             (.base ⟨6⟩, u64cell iv), (.base ⟨7⟩, bcell false),
             (.base ⟨8⟩, u64cell 0)],
    nextAddr := 9 }

/-- Setup exit: test false → break unwinding → `$c10` declared → the
call's `w` argument delivered at the frame-entry point. 13 steps. -/
private theorem wcH_X_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 13 (sWSU n sv l iv false) (.retV (.bool false) suWCmpK) ch
      = .ok (.retV (wSliceH n) callKW, σWCallg n sv l iv, ch) := by
  with_unfolding_all rfl

/-- Subject entry: frame entered (`words` at 9, `$res0` at 10), the
subject prologue (`$c0`/makeMap/`counts`/`i`/`$forFirst`) → the
counting-loop head at `nextAddr = 16`. 52 steps — the harness twin of
the canonical `wc_entryB_raw`. -/
private theorem wcH_entryS_raw (n : Nat) (sv iv : Int) (l : List Int)
    (ch : Choices) :
    stepFnIter 52 (σWCallg n sv l iv) (.retV (wSliceH n) callKW) ch
      = .ok (headCH, σH n sv iv l [] 0 true [] 16, ch) := by
  with_unfolding_all rfl

/-! ### The counting-loop segments at the harness placement (step
counts identical to the canonical tower — the statements are the same;
only addresses and the outer continuation differ) -/

/-- First-pass dispatch: head with the flag up → the `len(words)`
apply point. 25 steps. -/
private theorem wcH_segA0_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 25 (σH L sv siv ws kvs iv true dead na) headCH ch
      = .ok (.retV (wSliceH L) (lenKH iv),
          σH L sv siv ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

/-- Later-pass dispatch: head with the flag down → `i++`, then the
`len(words)` apply point. 29 steps. -/
private theorem wcH_segA1_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 29 (σH L sv siv ws kvs iv false dead na) headCH ch
      = .ok (.retV (wSliceH L)
            (lenKH (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))),
          σH L sv siv ws kvs
            (IntKind.normalize .int (IntKind.normalize .int (iv + 1)))
            false dead na, ch) := by
  with_unfolding_all rfl

/-- The `<` apply after the length delivery: one step. -/
private theorem wcH_cmp_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv jv : Int) (dead : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false dead na)
      (.retV (.int (L : Int) .int)
        (.strictK .lessCmp [.int jv .int] [] env2H cmpContCH)) ch
      = .ok (.retV (.bool (decide (jv < (L : Int)))) cmpContCH,
          σH L sv siv ws kvs iv false dead na, ch) := by
  with_unfolding_all rfl

private def stK0H (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnvH na) (.seq [] (uEnvH na) postBodyKH)
private def stK2H (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨12⟩)⟩] []
    (uEnvH na) (.seq [] (uEnvH na) postBodyKH)
private def addKH (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnvH na) (stK2H na w)
private def mapGetKH (na : Nat) (w : Int) : Cont :=
  .strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨12⟩)⟩] [] (uEnvH na)
    (addKH na w)

/-- C1: exit test true → the `$c1` initialization. 7 steps. -/
private theorem wcH_segC1_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 7 (σH L sv siv ws kvs iv false tail na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (.exec (.initialization { id := "$c1", typ := tMap }) env3H
            (.seq [asgnC1, seqnC2, mapAsgnStmt] env3H postBodyKH),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C2: `$c1` declared → its store point. 6 steps. -/
private theorem wcH_segC2_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
            [.map ⟨some (.base ⟨12⟩)⟩] (.seqn #[]) (u1EnvH na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C3 (composed from the generic glue): `$c1` stored → the `$c2`
initialization. 5 steps. -/
private theorem wcH_segC3_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σH L sv siv ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (u1EnvH na₀)
        (.seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH))) ch
      = .ok (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvH na₀)
            (.seq [.assign (.var "$c2")
                (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
              (u1EnvH na₀) postBodyKH),
          σH L sv siv ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH L sv siv ws kvs iv false tail na) (body := .seqn #[])
    (env := u1EnvH na₀)
    (k := .seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na) (ss := #[]) (env := u1EnvH na₀)
    (rest := [seqnC2, mapAsgnStmt]) (k := postBodyKH) (ch := ch))
  have h3 := stepFnIter_one (stepFn_seq_pop
    (σ := σH L sv siv ws kvs iv false tail na) (t := seqnC2)
    (rest := [mapAsgnStmt]) (env := u1EnvH na₀) (k := postBodyKH) (ch := ch))
  have h4 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na)
    (ss := #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "words") (.var "i"))])
    (env := u1EnvH na₀) (rest := [mapAsgnStmt]) (k := postBodyKH) (ch := ch))
  have h5 := stepFnIter_one (stepFn_seq_pop
    (σ := σH L sv siv ws kvs iv false tail na)
    (t := .initialization { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1EnvH na₀) (k := postBodyKH) (ch := ch))
  exact stepFnIter_chain (stepFnIter_chain (stepFnIter_chain
    (stepFnIter_chain h1 h2) h3) h4) h5

/-- C4: `$c2` declared → the `words[i]` read point. 8 steps. -/
private theorem wcH_segC4_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 8 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [.assign (.var "$c2")
          (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
        (uEnvH na₀) postBodyKH)) ch
      = .ok (.retV (.int iv .int)
            (.strictK .indexGet [wSliceH L] [] (uEnvH na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
                (.seqn #[]) (uEnvH na₀)
                (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH))),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C5: element delivered → its store point. 1 step. -/
private theorem wcH_segC5_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : GoValue) (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false tail na)
      (.retV w
        (.rhsK .vals [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [] []
          (.seqn #[]) (uEnvH na₀) (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)))
      ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []] [w]
            (.seqn #[]) (uEnvH na₀)
            (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C6 (composed): `$c2` stored → the `mapAssign` operand walk's first
`$c1` read. 4 steps. -/
private theorem wcH_segC6_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 4 (σH L sv siv ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (uEnvH na₀)
        (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH))) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀) (stK0H na₀),
          σH L sv siv ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH L sv siv ws kvs iv false tail na) (body := .seqn #[])
    (env := uEnvH na₀) (k := .seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na) (ss := #[]) (env := uEnvH na₀)
    (rest := [mapAsgnStmt]) (k := postBodyKH) (ch := ch))
  have h3 : stepFnIter 2 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [mapAsgnStmt]) (uEnvH na₀)
        postBodyKH)) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀) (stK0H na₀),
          σH L sv siv ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- C7: map handle delivered → the `$c2` operand read. 1 step. -/
private theorem wcH_segC7_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨12⟩)⟩) (stK0H na₀)) ch
      = .ok (.evalE (.var "$c2") (uEnvH na₀)
            (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨12⟩)⟩]
              [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
                (.intLit 1 .uint64)]
              (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C8: key delivered → the `mapGet`'s `$c1` read. 3 steps. -/
private theorem wcH_segC8_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.retV (.int w .uint64)
        (.stmtOpK (.mapAssign tU64 tU64) 0 [.map ⟨some (.base ⟨12⟩)⟩]
          [.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64)
            (.intLit 1 .uint64)]
          (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH))) ch
      = .ok (.evalE (.var "$c1") (uEnvH na₀)
            (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvH na₀)
              (addKH na₀ w)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C9: `mapGet`'s handle delivered → its `$c2` read. 1 step. -/
private theorem wcH_segC9_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w : Int) (ch : Choices) :
    stepFnIter 1 (σH L sv siv ws kvs iv false tail na)
      (.retV (.map ⟨some (.base ⟨12⟩)⟩)
        (.strictK (.mapGet tU64 tU64) [] [.var "$c2"] (uEnvH na₀)
          (addKH na₀ w))) ch
      = .ok (.evalE (.var "$c2") (uEnvH na₀) (mapGetKH na₀ w),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C10: the count delivered → the `+ 1` runs → the `mapAssign` apply
point. 3 steps. -/
private theorem wcH_segC10_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (w cv : Int) (ch : Choices) :
    stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.retV (.int cv .uint64) (addKH na₀ w)) ch
      = .ok (.retV (.int (IntKind.normalize .uint64 (cv + 1)) .uint64)
            (stK2H na₀ w),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- C11: `mapAssign` applied → back to the loop head. 3 steps. -/
private theorem wcH_segC11_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na₀ na : Nat)
    (ch : Choices) :
    stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [] (uEnvH na₀) postBodyKH)) ch
      = .ok (headCH, σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- The `mapAssign` wide-op apply step at the harness data cell,
conditioned on the `mapAssignValue` fact. -/
private theorem stepFn_mapAssign_applyH {σ σ' : ExecState}
    {b kv vv : GoValue} {env : LocalEnv} {k : Cont} {ch : Choices}
    (h : mapAssignValue σ tU64 tU64 b kv vv = .ok σ') :
    stepFn σ (.retV vv (.stmtOpK (.mapAssign tU64 tU64) 0 [kv, b] [] env k))
      ch
      = .ok (.next k, σ', ch) :=
  stepFn_mapAssign_apply h


/-! ### Counting-loop exit → the range head (harness placement) -/

private def envRBH (B : Nat) : LocalEnv :=
  (("best", .base ⟨B⟩) :: sc1H) :: [sc0H]
private def kRH (B : Nat) : Cont := .seq [retSeqn] (envRBH B) frameKH
/-- The range-loop head: the `mapIterK` pick point at snapshot `rem`. -/
private def rangeHeadH (B : Nat) (rem : List (Int × Nat)) : Config :=
  .next (.mapIterK none (some "c") tU64 tU64 wcRangeBody (toEntries rem)
    (envRBH B) (kRH B))

/-- X0: exit test false → break unwinding → the `best` initialization.
9 steps. -/
private theorem wcH_segX0_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (na : Nat)
    (ch : Choices) :
    stepFnIter 9 (σH L sv siv ws kvs iv false tail na)
      (.retV (.bool false) cmpContCH) ch
      = .ok (.exec (.initialization { id := "best", typ := tU64 }) envR0H
            (.seq [.assign (.var "best") (.intLit 0 .uint64),
              wcMapRangeStmt, retSeqn] envR0H frameKH),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0b: `best` declared → its zeroing store point. 6 steps. -/
private theorem wcH_segX0b_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
        wcMapRangeStmt, retSeqn] (envRBH B) frameKH)) ch
      = .ok (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int 0 .uint64] (.seqn #[]) (envRBH B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  with_unfolding_all rfl

/-- X0c: `best` stored → the ranged map handle delivered at the
snapshot point. 5 steps (one `.seqn` splice glued). -/
private theorem wcH_segX0c_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 5 (σH L sv siv ws kvs iv false tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBH B)
        (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH))) ch
      = .ok (.retV (.map ⟨some (.base ⟨12⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBH B)
              (kRH B)),
          σH L sv siv ws kvs iv false tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σH L sv siv ws kvs iv false tail na) (body := .seqn #[])
    (env := envRBH B) (k := .seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH)
    (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σH L sv siv ws kvs iv false tail na) (ss := #[]) (env := envRBH B)
    (rest := [wcMapRangeStmt, retSeqn]) (k := frameKH) (ch := ch))
  have h3 : stepFnIter 3 (σH L sv siv ws kvs iv false tail na)
      (.next (.seq ((#[] : Array Stmt).toList ++ [wcMapRangeStmt, retSeqn])
        (envRBH B) frameKH)) ch
      = .ok (.retV (.map ⟨some (.base ⟨12⟩)⟩)
            (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBH B)
              (kRH B)),
          σH L sv siv ws kvs iv false tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- The `mapRangeK` snapshot step at the harness placement. -/
private theorem stepFn_snapshotH {σ : ExecState} {v : GoValue}
    {entries : Array (GoValue × GoValue)} {body : Stmt} {env : LocalEnv}
    {k : Cont} {ch : Choices}
    (h : mapRangeSnapshotEntries σ tU64 tU64 v = .ok entries) :
    stepFn σ (.retV v (.mapRangeK none (some "c") tU64 tU64 body env k)) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 body entries env k),
          σ, ch) :=
  stepFn_snapshot h


/-! ## The harness counting tower — the generic layer's SECOND consumer
(the former storm site closes by instantiation; consolidation slice
2026-08-13) -/

/-! ## The HARNESS placement's discharge lemmas (gap G1's former storm site) (the generic layer's
hypotheses at `S := σH ws.length sv siv ws`; every statement pins the full
transition — the E-form made structural) -/

private theorem wcH_init1 (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 16 ≤ na → DeadFrom dead na →
    stepFn (σH ws.length sv siv ws kvs iv false dead na)
        (.exec (.initialization { id := "$c1", typ := tMap }) env3H
          (.seq [asgnC1, seqnC2, mapAsgnStmt] env3H postBodyKH)) ch
      = .ok (.next (.seq [asgnC1, seqnC2, mapAsgnStmt] (u1EnvH na) postBodyKH),
          σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na⟩, nilMapCell)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontH ws.length sv siv ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σH ws.length sv siv ws kvs iv false dead na)
    (p := { id := "$c1", typ := tMap })
    (rest := [asgnC1, seqnC2, mapAsgnStmt]) (env := env3H) (k := postBodyKH)
    (ch := ch) (v := .map ⟨none⟩)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH ws.length sv siv ws kvs iv false dead na).nextAddr = na from rfl,
    show (σH ws.length sv siv ws kvs iv false dead na).heap
      = frontH ws.length sv siv ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcH_st1 (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (ch : Choices), 16 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀⟩)) [] []]
          [.map ⟨some (.base ⟨12⟩)⟩] (.seqn #[]) (u1EnvH na₀)
          (.seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (u1EnvH na₀)
            (.seq [seqnC2, mapAsgnStmt] (u1EnvH na₀) postBodyKH)),
          σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhCellW)]) na,
          ch) := by
  intro kvs iv dead na₀ na ch hna hdead
  have hlook : Heap.lookup
      (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩ := by
    show Heap.lookup
      (frontH ws.length sv siv ws kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]))
      (.base ⟨na₀⟩) = some ⟨some tMap, .map ⟨none⟩⟩
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false
        hna),
      lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .map ⟨some (.base ⟨12⟩)⟩)
    (v' := .map ⟨some (.base ⟨12⟩)⟩) hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel])
  rw [show (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) na).heap
      = frontH ws.length sv siv ws kvs iv false
        ++ (dead ++ [(.base ⟨na₀⟩, nilMapCell)]) from rfl,
    set_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false hna),
    set_append_right (hdead na₀ (Nat.le_refl na₀)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcH_init2 (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ : Nat)
      (ch : Choices), 16 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 12)]) (na₀ + 1))
        (.exec (.initialization { id := "$c2", typ := tU64 }) (u1EnvH na₀)
          (.seq [.assign (.var "$c2")
              (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (u1EnvH na₀) postBodyKH)) ch
      = .ok (.next (.seq [.assign (.var "$c2")
            (.indexGet (.var "words") (.var "i")), mapAsgnStmt]
            (uEnvH na₀) postBodyKH),
          σH ws.length sv siv ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell 0)])
            (na₀ + 2), ch) := by
  intro kvs iv dead na₀ ch hna hdead
  have hmiss : Heap.lookup
      (frontH ws.length sv siv ws kvs iv false ++ (dead ++ [(.base ⟨na₀⟩, mhG 12)]))
      (.base ⟨na₀ + 1⟩) = none := by
    rw [lookup_append_right
        (lookup_frontH_none ws.length sv siv ws kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
    rfl
  have h := stepFn_init_seq
    (σ := σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 12)])
      (na₀ + 1))
    (p := { id := "$c2", typ := tU64 })
    (rest := [.assign (.var "$c2")
      (.indexGet (.var "words") (.var "i")), mapAsgnStmt])
    (env := u1EnvH na₀) (k := postBodyKH) (ch := ch)
    (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 12)])
        (na₀ + 1)).nextAddr = na₀ + 1 from rfl,
    show (σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na₀⟩, mhG 12)])
        (na₀ + 1)).heap
      = frontH ws.length sv siv ws kvs iv false ++ (dead ++ [(.base ⟨na₀⟩, mhG 12)])
      from rfl,
    set_fresh hmiss, List.append_assoc, List.append_assoc] at h
  exact h

private theorem wcH_st2 (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (ch : Choices), 0 ≤ w → w < 2 ^ 64 →
      16 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨na₀ + 1⟩)) [] []]
          [.int w .uint64] (.seqn #[]) (uEnvH na₀)
          (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (uEnvH na₀)
            (.seq [mapAsgnStmt] (uEnvH na₀) postBodyKH)),
          σH ws.length sv siv ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv dead na₀ na w ch hw0 hw64 hna hdead
  have hwnorm : IntKind.normalize .uint64 w = w := unorm_of_range hw0 hw64
  have hlook : Heap.lookup
      (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontH ws.length sv siv ws kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 12)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])))
      (.base ⟨na₀ + 1⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right
        (lookup_frontH_none ws.length sv siv ws kvs iv false (by omega)),
      lookup_append_right (hdead (na₀ + 1) (by omega)),
      lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 12)]
          (.base ⟨na₀ + 1⟩) = none from by
        rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
        rfl)]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int w .uint64) (v' := .int w .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hwnorm]
      rfl)
  rw [show (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell 0)])
        na).heap
      = frontH ws.length sv siv ws kvs iv false
        ++ (dead ++ ([(.base ⟨na₀⟩, mhG 12)]
          ++ [(.base ⟨na₀ + 1⟩, u64cell 0)])) from rfl,
    set_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false
      (by omega)),
    set_append_right (hdead (na₀ + 1) (by omega)),
    set_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhG 12)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcH_lk1 (ws : List Int) (sv siv : Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 16 ≤ na₀) (hdead : DeadFrom dead na₀) :
    Heap.lookup (σH ws.length sv siv ws kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀⟩) = some mhCellW := by
  show Heap.lookup
    (frontH ws.length sv siv ws kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCellW)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀⟩) = some mhCellW
  rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_append_left lookup_singleton_self

private theorem wcH_lk2 (ws : List Int) (sv siv : Int) (kvs : List (Int × Nat)) (iv w : Int)
    (dead : Heap) (na₀ na : Nat) (hna : 16 ≤ na₀) (hdead : DeadFrom dead na₀) :
    Heap.lookup (σH ws.length sv siv ws kvs iv false
      (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)]) na).heap
      (.base ⟨na₀ + 1⟩) = some (u64cell w) := by
  show Heap.lookup
    (frontH ws.length sv siv ws kvs iv false
      ++ (dead ++ ([(.base ⟨na₀⟩, mhCellW)]
        ++ [(.base ⟨na₀ + 1⟩, u64cell w)])))
    (.base ⟨na₀ + 1⟩) = some (u64cell w)
  rw [lookup_append_right
      (lookup_frontH_none ws.length sv siv ws kvs iv false (by omega)),
    lookup_append_right (hdead (na₀ + 1) (by omega)),
    lookup_append_right (show Heap.lookup [(.base ⟨na₀⟩, mhCellW)]
        (.base ⟨na₀ + 1⟩) = none from by
      rw [lookup_cons_ne (base_beq_false (by omega : na₀ ≠ na₀ + 1))]
      rfl)]
  exact lookup_singleton_self

private theorem wcH_var1 (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 16 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c1") (uEnvH na₀) k) ch
      = .ok (.retV (.map ⟨some (.base ⟨12⟩)⟩) k,
          σH ws.length sv siv ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcH_lk1 ws sv siv kvs iv w dead na₀ na hna hdead)

private theorem wcH_var2 (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv w : Int) (dead : Heap) (na₀ na : Nat)
      (k : Cont) (ch : Choices), 16 ≤ na₀ → DeadFrom dead na₀ →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)]) na)
        (.evalE (.var "$c2") (uEnvH na₀) k) ch
      = .ok (.retV (.int w .uint64) k,
          σH ws.length sv siv ws kvs iv false
            (dead ++ [(.base ⟨na₀⟩, mhG 12), (.base ⟨na₀ + 1⟩, u64cell w)])
            na, ch) := by
  intro kvs iv w dead na₀ na k ch hna hdead
  exact stepFn_var rfl (wcH_lk2 ws sv siv kvs iv w dead na₀ na hna hdead)

private theorem wcH_read (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (i : Nat) (dead : Heap) (na : Nat),
      i < ws.length →
    applyStrictOp (σH ws.length sv siv ws kvs ((i : Nat) : Int) false dead na)
        .indexGet [wsHG 4 ws.length, .int ((i : Nat) : Int) .int]
      = .ok (.int (ws.getD i 0) .uint64,
          σH ws.length sv siv ws kvs ((i : Nat) : Int) false dead na) := by
  intro kvs i dead na hi
  have hget : (⟨ws.map (fun v => .int v .uint64)⟩ : Array GoValue)[0 + i]?
      = some (.int (ws.getD i 0) .uint64) := by
    rw [Nat.zero_add, getElem?_mapU ws i hi]
  exact applyStrictOp_indexGet_slice (dty := some (.array ws.length tU64))
    (off := 0) (len := ws.length) (cap := ws.length) (ik := .int) rfl
    (Nat.le_refl ws.length) hi hget

private theorem wcH_mapGet (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (w : Int), 0 ≤ w → w < 2 ^ 64 →
    applyStrictOp (σH ws.length sv siv ws kvs iv false dead na) (.mapGet tU64 tU64)
        [.map ⟨some (.base ⟨12⟩)⟩, .int w .uint64]
      = .ok (.int (cnt kvs w : Int) .uint64,
          σH ws.length sv siv ws kvs iv false dead na) := by
  intro kvs iv dead na w hw0 hw64
  exact applyStrictOp_mapGet (a := ⟨12⟩) (dty := none) rfl
    (unorm_of_range hw0 hw64)

private theorem wcH_mapAsgn (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na₀ na : Nat)
      (w : Int) (v : Nat) (ch : Choices), 0 ≤ w → w < 2 ^ 64 → v < 2 ^ 64 →
    stepFn (σH ws.length sv siv ws kvs iv false dead na)
        (.retV (.int ((v : Nat) : Int) .uint64)
          (.stmtOpK (.mapAssign tU64 tU64) 0
            [.int w .uint64, .map ⟨some (.base ⟨12⟩)⟩] []
            (uEnvH na₀) (.seq [] (uEnvH na₀) postBodyKH))) ch
      = .ok (.next (.seq [] (uEnvH na₀) postBodyKH),
          σH ws.length sv siv ws (setk kvs w v) iv false dead na, ch) := by
  intro kvs iv dead na₀ na w v ch hw0 hw64 hv
  have hMA := mapAssignValue_toEntries (a := ⟨12⟩)
    (σ := σH ws.length sv siv ws kvs iv false dead na)
    (v := v) rfl (unorm_of_range hw0 hw64)
    (unorm_of_range (by omega) (by exact_mod_cast hv))
  rw [show Heap.set (σH ws.length sv siv ws kvs iv false dead na).heap (.base ⟨12⟩)
      ⟨none, .mapData (toEntries (setk kvs w v))⟩
      = frontH ws.length sv siv ws (setk kvs w v) iv false ++ dead from rfl] at hMA
  exact stepFn_mapAssign_apply hMA

/-- **One counting iteration** (exit test true at word `i`): the map
data cell advances from the counts of `ws.take i` to those of
`ws.take (i+1)`; two fresh dead cells land at `na`, `na + 1`. 53
steps — INSTANTIATED from the placement-generic `wcIter_generic`
(consolidation slice 2026-08-13). -/
private theorem wcH_count_iter (ws : List Int) (sv siv : Int) (i : Nat)
    (dead : Heap)
    (na : Nat) (ch : Choices)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63)
    (hi : i < ws.length) (hna : 16 ≤ na)
    (hdead : ∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) :
    stepFnIter 53
      (σH ws.length sv siv ws (countsList (ws.take i)) (i : Int) false dead na)
      (.retV (.bool true) cmpContCH) ch
      = .ok (headCH,
          σH ws.length sv siv ws (countsList (ws.take (i + 1))) (i : Int) false
            (dead ++ [(.base ⟨na⟩, mhCellW),
              (.base ⟨na + 1⟩, u64cell (ws.getD i 0))]) (na + 2), ch) := by
  have hw := hws (ws.getD i 0) (getD_mem hi)
  have hcnt : cnt (countsList (ws.take i)) (ws.getD i 0) + 1 < 2 ^ 64 := by
    have := cnt_take_le (ws := ws) (i := i) (ws.getD i 0)
    omega
  have h := wcIter_generic (σH ws.length sv siv ws) ws 4 12 16 headCH cmpContCH
    postBodyKH env3H u1EnvH uEnvH
    (fun kvs iv dead na ch => wcH_segC1_raw ws.length sv siv ws kvs iv dead na ch)
    (wcH_init1 ws sv siv)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC2_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (wcH_st1 ws sv siv)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC3_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (wcH_init2 ws sv siv)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC4_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (wcH_read ws sv siv)
    (fun kvs iv dead na₀ na w ch =>
      wcH_segC5_raw ws.length sv siv ws kvs iv dead na₀ na w ch)
    (wcH_st2 ws sv siv)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC6_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (wcH_var1 ws sv siv)
    (wcH_var2 ws sv siv)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC7_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (fun kvs iv dead na₀ na w ch =>
      wcH_segC8_raw ws.length sv siv ws kvs iv dead na₀ na w ch)
    (fun kvs iv dead na₀ na w ch =>
      wcH_segC9_raw ws.length sv siv ws kvs iv dead na₀ na w ch)
    (wcH_mapGet ws sv siv)
    (fun kvs iv dead na₀ na w cv ch =>
      wcH_segC10_raw ws.length sv siv ws kvs iv dead na₀ na w cv ch)
    (wcH_mapAsgn ws sv siv)
    (fun kvs iv dead na₀ na ch =>
      wcH_segC11_raw ws.length sv siv ws kvs iv dead na₀ na ch)
    (countsList (ws.take i)) i dead na ch hi hw.1 hw.2 hcnt hna hdead
  rw [show setk (countsList (ws.take i)) (ws.getD i 0)
      (cnt (countsList (ws.take i)) (ws.getD i 0) + 1)
      = countsList (ws.take (i + 1)) from by
    rw [setk_cnt_succ, ← countsList_append_word, ← take_succ_getD hi]] at h
  exact h

private theorem wcH_initBest (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (na : Nat)
      (ch : Choices), 16 ≤ na → DeadFrom dead na →
    stepFn (σH ws.length sv siv ws kvs iv false dead na)
        (.exec (.initialization { id := "best", typ := tU64 }) envR0H
          (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] envR0H frameKH)) ch
      = .ok (.next (.seq [.assign (.var "best") (.intLit 0 .uint64),
            wcMapRangeStmt, retSeqn] (envRBH na) frameKH),
          σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨na⟩, u64cell 0)])
            (na + 1), ch) := by
  intro kvs iv dead na ch hna hdead
  have hmiss : Heap.lookup
      (frontH ws.length sv siv ws kvs iv false ++ dead) (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false
      hna)]
    exact hdead na (Nat.le_refl na)
  have h := stepFn_init_seq (σ := σH ws.length sv siv ws kvs iv false dead na)
    (p := { id := "best", typ := tU64 })
    (rest := [.assign (.var "best") (.intLit 0 .uint64),
      wcMapRangeStmt, retSeqn])
    (env := envR0H) (k := frameKH) (ch := ch) (v := .int 0 .uint64)
    (by simp [defaultValue, defaultValueFuel, typeResolutionFuel])
  rw [show (σH ws.length sv siv ws kvs iv false dead na).nextAddr = na from rfl,
    show (σH ws.length sv siv ws kvs iv false dead na).heap
      = frontH ws.length sv siv ws kvs iv false ++ dead from rfl,
    set_fresh hmiss, List.append_assoc] at h
  exact h

private theorem wcH_stBest (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices), 16 ≤ B → DeadFrom dead B →
    stepFn (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na)
        (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
          [.int 0 .uint64] (.seqn #[]) (envRBH B)
          (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBH B)
            (.seq [wcMapRangeStmt, retSeqn] (envRBH B) frameKH)),
          σH ws.length sv siv ws kvs iv false (dead ++ [(.base ⟨B⟩, u64cell 0)]) na,
          ch) := by
  intro kvs iv dead B na ch hB hdead
  have hlook : Heap.lookup
      (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩ := by
    show Heap.lookup
      (frontH ws.length sv siv ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)]))
      (.base ⟨B⟩) = some ⟨some tU64, .int 0 .uint64⟩
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false hB),
      lookup_append_right (hdead B (Nat.le_refl B))]
    exact lookup_singleton_self
  have h := storeTarget_addr (v := .int 0 .uint64) (v' := .int 0 .uint64)
    hlook
    (by simp [normalizeValueForTy, normalizeValueForTyFuel,
      typeResolutionFuel, IntKind.normalize, IntKind.bits?, IntKind.signed])
  rw [show (σH ws.length sv siv ws kvs iv false
        (dead ++ [(.base ⟨B⟩, u64cell 0)]) na).heap
      = frontH ws.length sv siv ws kvs iv false ++ (dead ++ [(.base ⟨B⟩, u64cell 0)])
      from rfl,
    set_append_right (lookup_frontH_none ws.length sv siv ws kvs iv false hB),
    set_append_right (hdead B (Nat.le_refl B)),
    set_singleton_self] at h
  exact stepFn_store_step h

private theorem wcH_snap (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (iv : Int) (dead : Heap) (B na : Nat)
      (ch : Choices),
      (∀ p ∈ kvs, IntKind.normalize .uint64 p.1 = p.1
        ∧ IntKind.normalize .uint64 ((p.2 : Nat) : Int)
            = ((p.2 : Nat) : Int)) →
    stepFn (σH ws.length sv siv ws kvs iv false dead na)
        (.retV (.map ⟨some (.base ⟨12⟩)⟩)
          (.mapRangeK none (some "c") tU64 tU64 wcRangeBody (envRBH B)
            (kRH B))) ch
      = .ok (.next (.mapIterK none (some "c") tU64 tU64 wcRangeBody
            (toEntries kvs) (envRBH B) (kRH B)),
          σH ws.length sv siv ws kvs iv false dead na, ch) := by
  intro kvs iv dead B na ch hkv
  exact stepFn_snapshot (snapshot_toEntries (a := ⟨12⟩) (dty := none) rfl hkv)

/-- **The counting loop**, by strong induction on the remaining word
count: from the exit-test delivery at word `i`, the run reaches the
RANGE HEAD over the snapshot of the full counts, with `best` zeroed at
address `na + 2·(L - i)`, within `84·(L-i) + 23` steps — INSTANTIATED
from the placement-generic `wcLoop_generic` (consolidation slice
2026-08-13). -/
private theorem wcH_count_loop (ws : List Int) (sv siv : Int)
    (hws : ∀ v ∈ ws, 0 ≤ v ∧ v < 2 ^ 64) (hlen : ws.length < 2 ^ 63) :
    ∀ (n i : Nat), n = ws.length - i → i ≤ ws.length →
    ∀ (dead : Heap) (na : Nat), 16 ≤ na →
    (∀ x : Nat, na ≤ x → Heap.lookup dead (.base ⟨x⟩) = none) →
    ∀ ch : Choices,
    ∃ (k : Nat) (tail : Heap),
      k ≤ 84 * n + 23
      ∧ (∀ x : Nat, na + 2 * n + 1 ≤ x →
          Heap.lookup tail (.base ⟨x⟩) = none)
      ∧ Heap.lookup tail (.base ⟨na + 2 * n⟩) = some (u64cell 0)
      ∧ stepFnIter k
          (σH ws.length sv siv ws (countsList (ws.take i)) (i : Int) false dead na)
          (.retV (.bool (decide ((i : Int) < (ws.length : Int)))) cmpContCH)
          ch
        = .ok (rangeHeadH (na + 2 * n) (countsList ws),
            σH ws.length sv siv ws (countsList ws) (ws.length : Int) false tail
              (na + 2 * n + 1), ch) := by
  intro n i hn hi dead na hna hdead ch
  obtain ⟨k, tail, hk, htail, hbest, hrun⟩ :=
    wcLoop_generic (σH ws.length sv siv ws) ws 4 12 16 headCH cmpContCH frameKH
      env2H envR0H envRBH kRH hlen
      (fun i dead na ch hi hna hdead =>
        wcH_count_iter ws sv siv i dead na ch hws hlen hi hna hdead)
      (fun kvs iv dead na ch =>
        wcH_segA1_raw ws.length sv siv ws kvs iv dead na ch)
      (fun kvs iv dead na ch =>
        wcH_segX0_raw ws.length sv siv ws kvs iv dead na ch)
      (wcH_initBest ws sv siv)
      (fun kvs iv dead B na ch =>
        wcH_segX0b_raw ws.length sv siv ws kvs iv dead B na ch)
      (wcH_stBest ws sv siv)
      (fun kvs iv dead B na ch =>
        wcH_segX0c_raw ws.length sv siv ws kvs iv dead B na ch)
      (wcH_snap ws sv siv)
      (countsList_norm ws hws hlen)
      n i hn hi dead na hna hdead ch
  exact ⟨k, tail, hk, htail, hbest, hrun⟩

/-! ### The HARNESS placement's range-loop discharges + wrapper -/

private theorem wcH_pick (ws : List Int) (sv siv : Int) :
    ∀ (kvs rem : List (Int × Nat)) (idx : Nat) (ch ch₂ : Choices)
      (p : Int × Nat) (tail : Heap) (B na : Nat),
      Choices.consume ch rem.length = (idx, ch₂) → idx < rem.length →
      rem[idx]? = some p →
      IntKind.normalize .uint64 (p.2 : Int) = (p.2 : Int) →
      16 ≤ na → DeadFrom tail na →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (rangeHeadR envRBH kRH B rem) ch
        = .ok (.exec wcRangeBody (envIterR envRBH B na)
              (iterKR envRBH kRH B (rem.eraseIdx idx)),
            σH ws.length sv siv ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na⟩, ⟨some tU64, .int (p.2 : Int) .uint64⟩)])
              (na + 1), ch₂) := by
  intro kvs rem idx ch ch₂ p tail B na hcons hidx hp hvnorm hna htail
  have hmiss : Heap.lookup
      (frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨na⟩) = none := by
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hna)]
    exact htail na (Nat.le_refl na)
  have hPick := stepFn_pick
    (σ := σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
    (body := wcRangeBody) (env := envRBH B) (k := kRH B)
    hcons hidx hp hvnorm
  rw [show (σH ws.length sv siv ws kvs (ws.length : Int) false tail
        na).nextAddr = na from rfl,
    show (σH ws.length sv siv ws kvs (ws.length : Int) false tail na).heap
      = frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail
      from rfl,
    set_fresh hmiss, List.append_assoc] at hPick
  exact hPick

private theorem wcH_R4b (ws : List Int) (sv siv : Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (ch : Choices),
      stepFnIter 4 (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (.next (.seq [.assign (.var "best") (.var "c")]
            (env4R envRBH B na₀)
            (.seq [] (envIfR envRBH B na₀) (iterKR envRBH kRH B rem)))) ch
        = .ok (.evalE (.var "c") (env4R envRBH B na₀)
              (.rhsK .vals [.chain (.addr (.base ⟨B⟩)) [] []] [] []
                (.seqn #[]) (env4R envRBH B na₀)
                (storeBestKR envRBH kRH B na₀ rem)),
            σH ws.length sv siv ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs rem tail B na₀ na ch
  with_unfolding_all rfl

private theorem wcH_varC (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (na₀ na : Nat)
      (v : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "c" = some (.base ⟨na₀⟩) →
      16 ≤ na₀ → DeadFrom tail na₀ →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false
          (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na)
          (.evalE (.var "c") env k) ch
        = .ok (.retV (.int v .uint64) k,
            σH ws.length sv siv ws kvs (ws.length : Int) false
              (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]) na,
            ch) := by
  intro kvs tail na₀ na v env k ch henv hna hdead
  refine stepFn_var (c := ⟨some tU64, .int v .uint64⟩) henv ?_
  show Heap.lookup
    (frontH ws.length sv siv ws kvs (ws.length : Int) false
      ++ (tail ++ [(.base ⟨na₀⟩, ⟨some tU64, .int v .uint64⟩)]))
    (.base ⟨na₀⟩) = some ⟨some tU64, .int v .uint64⟩
  rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hna),
    lookup_append_right (hdead na₀ (Nat.le_refl na₀))]
  exact lookup_singleton_self

private theorem wcH_varBest (ws : List Int) (sv siv : Int) :
    ∀ (kvs : List (Int × Nat)) (tail : Heap) (B na : Nat)
      (bv : Int) (env : LocalEnv) (k : Cont) (ch : Choices),
      LocalEnv.lookup env "best" = some (.base ⟨B⟩) → 16 ≤ B →
      Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (.evalE (.var "best") env k) ch
        = .ok (.retV (.int bv .uint64) k,
            σH ws.length sv siv ws kvs (ws.length : Int) false tail na, ch) := by
  intro kvs tail B na bv env k ch henv hB hlkB
  refine stepFn_var (c := u64cell bv) henv ?_
  show Heap.lookup
    (frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail)
    (.base ⟨B⟩) = some (u64cell bv)
  rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hB)]
  exact hlkB

private theorem wcH_stB (ws : List Int) (sv siv : Int) :
    ∀ (kvs rem : List (Int × Nat)) (tail : Heap) (B na₀ na : Nat)
      (bv v : Int) (ch : Choices),
      16 ≤ B → Heap.lookup tail (.base ⟨B⟩) = some (u64cell bv) →
      IntKind.normalize .uint64 v = v →
      stepFn (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (.next (.storeK [.chain (.addr (.base ⟨B⟩)) [] []]
            [.int v .uint64] (.seqn #[]) (env4R envRBH B na₀)
            (storeBestKR envRBH kRH B na₀ rem))) ch
        = .ok (.next (.storeK [] [] (.seqn #[]) (env4R envRBH B na₀)
              (storeBestKR envRBH kRH B na₀ rem)),
            σH ws.length sv siv ws kvs (ws.length : Int) false
              (Heap.set tail (.base ⟨B⟩) ⟨some tU64, .int v .uint64⟩) na,
            ch) := by
  intro kvs rem tail B na₀ na bv v ch hB hlkB hvn
  have hlook : Heap.lookup
      (σH ws.length sv siv ws kvs (ws.length : Int) false tail na).heap
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩ := by
    show Heap.lookup
      (frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail)
      (.base ⟨B⟩) = some ⟨some tU64, .int bv .uint64⟩
    rw [lookup_append_right (lookup_frontH_none ws.length sv siv ws kvs
        (ws.length : Int) false hB)]
    exact hlkB
  have h := storeTarget_addr (v := .int v .uint64) (v' := .int v .uint64)
    hlook
    (by
      simp only [normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel]
      rw [hvn]
      rfl)
  rw [show (σH ws.length sv siv ws kvs (ws.length : Int) false tail na).heap
      = frontH ws.length sv siv ws kvs (ws.length : Int) false ++ tail from rfl,
    set_append_right (lookup_frontH_none ws.length sv siv ws kvs
      (ws.length : Int) false hB)] at h
  exact stepFn_store_step h

/-- **The range loop, at every choice stream** — INSTANTIATED from the
placement-generic `wcRange_generic` (§10b; consolidation slice
2026-08-13). -/
private theorem wcH_range_loop (ws : List Int) (sv siv : Int)
    (kvs : List (Int × Nat)) :
    ∀ (m : Nat) (rem : List (Int × Nat)), rem.length = m →
    ∀ (bv : Nat) (B na : Nat) (tail : Heap) (ch : Choices),
    (∀ p ∈ rem, p.2 ≤ ws.length) → ws.length < 2 ^ 63 → bv ≤ ws.length →
    16 ≤ B → B < na →
    Heap.lookup tail (.base ⟨B⟩) = some (u64cell (bv : Int)) →
    (∀ x : Nat, na ≤ x → Heap.lookup tail (.base ⟨x⟩) = none) →
    ∃ (k : Nat) (ch' : Choices) (tail' : Heap) (na' : Nat),
      k ≤ 24 * m + 1 ∧ na ≤ na'
      ∧ Heap.lookup tail' (.base ⟨B⟩)
          = some (u64cell ((max bv (maxOf (rem.map Prod.snd)) : Nat) : Int))
      ∧ (∀ x : Nat, na' ≤ x → Heap.lookup tail' (.base ⟨x⟩) = none)
      ∧ stepFnIter k (σH ws.length sv siv ws kvs (ws.length : Int) false tail na)
          (rangeHeadH B rem) ch
        = .ok (.next (kRH B),
            σH ws.length sv siv ws kvs (ws.length : Int) false tail' na', ch') := by
  intro m rem hm bv B na tail ch hrem hlen hbv hB hBna hbest htail
  obtain ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩ :=
    wcRange_generic envRBH kRH (σH ws.length sv siv ws) (ws.length : Int)
      16 ws.length hlen
      (fun B na₀ => rfl)
      (wcH_pick ws sv siv) (wcH_R4b ws sv siv) (wcH_varC ws sv siv) (wcH_varBest ws sv siv)
      (wcH_stB ws sv siv)
      m kvs rem hm bv B na tail ch hrem hbv hB hBna hbest htail
  exact ⟨k, ch', tail', na', hk, hna', hbest', htail', hrun⟩



/-- The harness exit-phase front: harness `$res0` (2), `$c10` (8), the
subject's `$res0` (10) generalized. -/
private def frontXH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, u64cell r2), (.base ⟨3⟩, wHandleCell L),
   (.base ⟨4⟩, arrCell L ws), (.base ⟨5⟩, wHandleCell L),
   (.base ⟨6⟩, u64cell siv), (.base ⟨7⟩, bcell false),
   (.base ⟨8⟩, u64cell r8), (.base ⟨9⟩, wHandleCell L),
   (.base ⟨10⟩, u64cell r10), (.base ⟨11⟩, mhCellW),
   (.base ⟨12⟩, mdCell kvs), (.base ⟨13⟩, mhCellW),
   (.base ⟨14⟩, intcell ((L : Nat) : Int)), (.base ⟨15⟩, bcell false)]

private def σXH (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap)
    (na : Nat) : ExecState :=
  { types := wordCountLowered.typeDefs.toList,
    functions := wordCountLowered.funcs,
    methods := wordCountLowered.methods,
    heap := frontXH L sv siv ws kvs r2 r8 r10 ++ tail, nextAddr := na }

/-- X1H: loop exit → the `best` read of `$res0 := best`. 6 steps. -/
private theorem wcH_segX1_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 6 (σXH L sv siv ws kvs r2 r8 r10 tail na) (.next (kRH B)) ch
      = .ok (.evalE (.var "best") (envRBH B)
            (.rhsK .vals [.chain (.addr (.base ⟨10⟩)) [] []] [] []
              (.seqn #[]) (envRBH B)
              (.seq [.returnStmt] (envRBH B) frameKH)),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
  have h1 : stepFnIter 1 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (kRH B)) ch
      = .ok (.exec retSeqn (envRBH B) (.seq [] (envRBH B) frameKH),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
    with_unfolding_all rfl
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH L sv siv ws kvs r2 r8 r10 tail na)
    (ss := #[.assign (.var "$res0") (.var "best"), .returnStmt])
    (env := envRBH B) (rest := []) (k := frameKH) (ch := ch))
  have h3 : stepFnIter 4 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (.seq
        ((#[.assign (.var "$res0") (.var "best"),
          .returnStmt] : Array Stmt).toList ++ [])
        (envRBH B) frameKH)) ch
      = .ok (.evalE (.var "best") (envRBH B)
            (.rhsK .vals [.chain (.addr (.base ⟨10⟩)) [] []] [] []
              (.seqn #[]) (envRBH B)
              (.seq [.returnStmt] (envRBH B) frameKH)),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
    with_unfolding_all rfl
  exact stepFnIter_chain (stepFnIter_chain h1 h2) h3

/-- X2aH: the `best` value delivered → stored into the subject's
`$res0` (cell 10). 2 steps. -/
private theorem wcH_segX2a_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 bvv : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.retV (.int bvv .uint64)
        (.rhsK .vals [.chain (.addr (.base ⟨10⟩)) [] []] [] [] (.seqn #[])
          (envRBH B) (.seq [.returnStmt] (envRBH B) frameKH))) ch
      = .ok (.next (.storeK [] [] (.seqn #[]) (envRBH B)
            (.seq [.returnStmt] (envRBH B) frameKH)),
          σXH L sv siv ws kvs r2 r8 (IntKind.normalize .uint64 bvv) tail na,
          ch) := by
  with_unfolding_all rfl

/-- X2bH: → the `returnStmt` dispatch point. 2 steps. -/
private theorem wcH_segX2b_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap) (B na : Nat)
    (ch : Choices) :
    stepFnIter 2 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (.storeK [] [] (.seqn #[]) (envRBH B)
        (.seq [.returnStmt] (envRBH B) frameKH))) ch
      = .ok (.next (.seq
            (((#[] : Array Stmt).toList) ++ [.returnStmt]) (envRBH B)
            frameKH),
          σXH L sv siv ws kvs r2 r8 r10 tail na, ch) := by
  have h1 := stepFnIter_one (stepFn_storeK_nil
    (σ := σXH L sv siv ws kvs r2 r8 r10 tail na) (body := .seqn #[])
    (env := envRBH B)
    (k := .seq [.returnStmt] (envRBH B) frameKH) (ch := ch))
  have h2 := stepFnIter_one (stepFn_seqn_splice
    (σ := σXH L sv siv ws kvs r2 r8 r10 tail na) (ss := #[])
    (env := envRBH B)
    (rest := [.returnStmt]) (k := frameKH) (ch := ch))
  exact stepFnIter_chain h1 h2

/-- X2cH: `return`, the subject frame's result read + `$c10`
write-back, the harness tail `$res0 := $c10; return`, the harness
frame exit → the driver terminal. 24 steps. -/
private theorem wcH_segX2c_raw (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) (tail : Heap) (na : Nat)
    (B : Nat) (ch : Choices) :
    stepFnIter 24 (σXH L sv siv ws kvs r2 r8 r10 tail na)
      (.next (.seq (((#[] : Array Stmt).toList) ++ [.returnStmt])
        (envRBH B) frameKH)) ch
      = .ok (.next .stop,
          σXH L sv siv ws kvs
            (IntKind.normalize .uint64 (IntKind.normalize .uint64 r10))
            (IntKind.normalize .uint64 r10) r10 tail na, ch) := by
  with_unfolding_all rfl

private theorem lookup_frontXH_none (L : Nat) (sv siv : Int) (ws : List Int)
    (kvs : List (Int × Nat)) (r2 r8 r10 : Int) {x : Nat} (hx : 16 ≤ x) :
    Heap.lookup (frontXH L sv siv ws kvs r2 r8 r10) (.base ⟨x⟩) = none := by
  simp only [frontXH, Heap.lookup,
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
    Bool.false_eq_true, if_false]

/-- **The harness run, end to end** (gap G1's composition): from the
machine entry's post-prelude state, through setup, the subject's
counting and range phases, and the harness return path, to the driver
terminal — with `⌈n/3⌉` in the harness result cell. -/
private theorem wcH_runs (n seed : Nat) (hn : n < 2 ^ 63) (ch : Choices) :
    ∃ (k : Nat) (ch' : Choices) (tail : Heap) (na : Nat),
      k ≤ 229 + 165 * n ∧
      stepFnIter k (σWH0 ((n : Nat) : Int) ((seed : Nat) : Int))
          (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
        = .ok (.next .stop,
            σXH n ((seed : Nat) : Int) ((n : Nat) : Int)
              (wcFamily n seed) (countsList (wcFamily n seed))
              (((n + 2) / 3 : Nat) : Int) (((n + 2) / 3 : Nat) : Int)
              (((n + 2) / 3 : Nat) : Int) tail na, ch') := by
  have hws := wcFamily_range n seed
  have hLen : (wcFamily n seed).length = n := wcFamily_length n seed
  have hlen : (wcFamily n seed).length < 2 ^ 63 := by omega
  have hM : maxMultiplicity (wcFamily n seed) = (n + 2) / 3 :=
    wcFamily_maxMult n seed
  have hMle : (n + 2) / 3 ≤ n ∨ n = 0 := by omega
  have hMlt : (n + 2) / 3 < 2 ^ 64 := by omega
  have hMnorm : IntKind.normalize .uint64 (((n + 2) / 3 : Nat) : Int)
      = (((n + 2) / 3 : Nat) : Int) := by
    refine unorm_of_range (by omega) ?_
    exact_mod_cast hMlt
  -- entry: E1 → makeSlice → E2
  have hE := stepFnIter_chain
    (stepFnIter_chain (wcH_E1_raw n seed ch)
      (stepFnIter_one (wcH_makeSlice n seed ch)))
    (wcH_E2_raw n seed ch)
  -- setup: first dispatch, the fill loop, the exit
  have hA0 := wcH_suA0_raw n ((seed : Nat) : Int) 0
    (List.replicate n 0) ch
  have hSU := wcH_setup_loop n seed hn (n - 0) 0 rfl (by omega) ch
  have hS1 := stepFnIter_chain (stepFnIter_chain hE hA0) hSU
  rw [show (decide (((n : Nat) : Int) < ((n : Nat) : Int))) = false from
    decide_eq_false (by omega)] at hS1
  have hX := wcH_X_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) ch
  have hS2 := stepFnIter_chain hS1 hX
  have hES := wcH_entryS_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) ch
  have hS3 := stepFnIter_chain hS2 hES
  -- the subject's first dispatch to the exit-test delivery
  have hA0c := wcH_segA0_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) [] 0 [] 16 ch
  have hlenap := stepFnIter_one
    (stepFn_strict_apply (done := []) (env := env2H)
      (k := .strictK .lessCmp [.int (0 : Int) .int] [] env2H cmpContCH)
      (ch := ch)
      (applyStrictOp_len_slice
        (σ := σH n ((seed : Nat) : Int) ((n : Nat) : Int)
          (wcFamily n seed) [] 0 false [] 16)
        (b := .base ⟨4⟩) (off := 0) (len := n) (cap := n) (elem := tU64)
        (Nat.le_refl n)))
  have hCmp := wcH_cmp_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) [] 0 0 [] 16 ch
  have hS4 := stepFnIter_chain (stepFnIter_chain (stepFnIter_chain hS3 hA0c)
    hlenap) hCmp
  -- the counting loop (instantiated at ws := wcFamily n seed, then the
  -- length rewritten to n)
  obtain ⟨k₁, tail₁, hk₁, htail₁, hbest₁, hrun₁⟩ :=
    wcH_count_loop (wcFamily n seed) ((seed : Nat) : Int) ((n : Nat) : Int)
      hws hlen ((wcFamily n seed).length - 0) 0 rfl (by omega) [] 16
      (by omega) (fun _ _ => rfl) ch
  rw [hLen] at hrun₁ hbest₁ htail₁ hk₁
  have hS5 := stepFnIter_chain hS4 hrun₁
  -- the range loop
  obtain ⟨k₂, ch₂, tail₂, na₂, hk₂, hna₂, hbest₂, htail₂, hrun₂⟩ :=
    wcH_range_loop (wcFamily n seed) ((seed : Nat) : Int) ((n : Nat) : Int)
      (countsList (wcFamily n seed)) (countsList (wcFamily n seed)).length
      (countsList (wcFamily n seed)) rfl 0 (16 + 2 * (n - 0))
      (16 + 2 * (n - 0) + 1) tail₁ ch
      (fun p hp => by
        have := countsList_val_le (wcFamily n seed) hp
        omega)
      hlen (by omega) (by omega) (by omega) hbest₁ htail₁
  rw [hLen] at hrun₂
  have hS6 := stepFnIter_chain hS5 hrun₂
  rw [show max 0 (maxOf ((countsList (wcFamily n seed)).map Prod.snd))
      = (n + 2) / 3 from by
    rw [Nat.zero_max, maxOf_countsList (wcFamily n seed), hM]] at hbest₂
  -- the return path
  have hX1 := wcH_segX1_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) (countsList (wcFamily n seed)) 0 0 0 tail₂
    (16 + 2 * (n - 0)) na₂ ch₂
  have hS7 := stepFnIter_chain hS6 hX1
  have hlkB : Heap.lookup
      (σXH n ((seed : Nat) : Int) ((n : Nat) : Int) (wcFamily n seed)
        (countsList (wcFamily n seed)) 0 0 0 tail₂ na₂).heap
      (.base ⟨16 + 2 * (n - 0)⟩)
      = some (u64cell (((n + 2) / 3 : Nat) : Int)) := by
    show Heap.lookup
      (frontXH n ((seed : Nat) : Int) ((n : Nat) : Int) (wcFamily n seed)
        (countsList (wcFamily n seed)) 0 0 0 ++ tail₂)
      (.base ⟨16 + 2 * (n - 0)⟩)
      = some (u64cell (((n + 2) / 3 : Nat) : Int))
    rw [lookup_append_right
      (lookup_frontXH_none n ((seed : Nat) : Int) ((n : Nat) : Int)
        (wcFamily n seed) (countsList (wcFamily n seed)) 0 0 0 (by omega))]
    exact hbest₂
  have hS8 := stepFnIter_chain hS7 (stepFnIter_one
    (stepFn_var (x := "best") (env := envRBH (16 + 2 * (n - 0)))
      (a := ⟨16 + 2 * (n - 0)⟩) (ch := ch₂) rfl hlkB))
  have hX2a := wcH_segX2a_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) (countsList (wcFamily n seed)) 0 0 0
    (((n + 2) / 3 : Nat) : Int) tail₂ (16 + 2 * (n - 0)) na₂ ch₂
  rw [hMnorm] at hX2a
  have hS9 := stepFnIter_chain hS8 hX2a
  have hS10 := stepFnIter_chain hS9
    (wcH_segX2b_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
      (wcFamily n seed) (countsList (wcFamily n seed)) 0 0
      (((n + 2) / 3 : Nat) : Int) tail₂ (16 + 2 * (n - 0)) na₂ ch₂)
  have hX2c := wcH_segX2c_raw n ((seed : Nat) : Int) ((n : Nat) : Int)
    (wcFamily n seed) (countsList (wcFamily n seed)) 0 0
    (((n + 2) / 3 : Nat) : Int) tail₂ na₂ (16 + 2 * (n - 0)) ch₂
  rw [hMnorm, hMnorm] at hX2c
  have hS11 := stepFnIter_chain hS10 hX2c
  refine ⟨_, ch₂, tail₂, na₂, ?_, hS11⟩
  have hm : (countsList (wcFamily n seed)).length ≤ n := by
    have := countsList_length_le (wcFamily n seed)
    omega
  omega

/-- **The parameterized-harness headline (gap G1 CLOSED, consolidation
slice 2026-08-13)** — the §11 harness form over `wordcount_harness`:
for every `n < 2^63` and every uint64 `seed`, past fuel `229 + 165·n`,
at EVERY nondeterminism-choice stream (every map-iteration order), the
harness run completes with EXACTLY `⌈n/3⌉ = (n+2)/3` as its returned
value — the closed form `wcFamily_maxMult` proves for the setup family
`w[i] = seed + i%3` at every seed (the refuted seed-wrap caveat,
finding 20). -/
theorem wordcount_ok (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
          wordCountLowered.funcs wordcountHarnessFunc
          #[.int ((n : Nat) : Int) .uint64, .int ((seed : Nat) : Int) .uint64]
          wordCountLowered.methods ch
        = .ok ⟨#[.int (((n + 2) / 3 : Nat) : Int) .uint64]⟩ := by
  refine ⟨229 + 165 * n, fun fuel hfuel ch => ?_⟩
  obtain ⟨k, ch', tail, na, hk, hrun⟩ := wcH_runs n seed hn ch
  have hentry := wcH_entry_eq ((n : Nat) : Int) ((seed : Nat) : Int) fuel ch
  rw [unorm_nat_of_lt (show n < 2 ^ 64 by omega),
    unorm_nat_of_lt hseed] at hentry
  have hfold := runConfig_of_stepFnIter hrun (fuel - k)
  rw [show k + (fuel - k) = fuel from by omega] at hfold
  have hfull : runConfig fuel
      (σWH0 ((n : Nat) : Int) ((seed : Nat) : Int))
      (.exec wordcountHarnessFunc.body [hWScope0] hWFrame0) ch
      = .ok (σXH n ((seed : Nat) : Int) ((n : Nat) : Int)
          (wcFamily n seed) (countsList (wcFamily n seed))
          (((n + 2) / 3 : Nat) : Int) (((n + 2) / 3 : Nat) : Int)
          (((n + 2) / 3 : Nat) : Int) tail na, ch') := by
    rw [hfold, runConfig_next_stop]
  rw [hentry, hfull]
  with_unfolding_all rfl

/-- The D1 run-conditioned twin, derived (`harness_readout_of_total`):
ANY successful completion, at any fuel and any choice stream, returns
exactly `⌈n/3⌉`. -/
theorem wordcount_readout (n seed : Nat) (hn : n < 2 ^ 63)
    (hseed : seed < 2 ^ 64) :
    ∀ (fuel : Nat) (ch : Choices) (r : Result),
      runFunctionWithContextM fuel wordCountLowered.typeDefs.toList
          wordCountLowered.funcs wordcountHarnessFunc
          #[.int ((n : Nat) : Int) .uint64, .int ((seed : Nat) : Int) .uint64]
          wordCountLowered.methods ch
        = .ok r →
      r = ⟨#[.int (((n + 2) / 3 : Nat) : Int) .uint64]⟩ :=
  harness_readout_of_total (wordcount_ok n seed hn hseed)

end GoLean.Examples.WordCount
