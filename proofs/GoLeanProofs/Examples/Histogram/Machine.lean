import GoLeanProofs.Examples.Histogram.Pure
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# Histogram — Machine

The machine-facing layer: the two `Func` records transcribed from the
pinned lowering (each tied to it by an `rfl` pin), the statement pieces
the continuations mention, the address layout, and the choice-pick step
for the VARIABLE-FREE map range.

Address layout (probe-measured at `(n, seed, q) = (4, 7, 8)`;
`.tmp/probe2.lean` traced every `nextAddr` bump, and every raw segment
downstream re-checks the transcription by `rfl`):

```
0 = n            1 = seed          2 = q
3 = $res0 ([8])  4 = $res1         5 = $res2
6 = $c12 handle  7 = v backing     8 = v
9 = setup i     10 = setup flag   11 = vals ([8])
12 = copy i     13 = copy flag    14 = hits (harness)
15 = distinct (harness)
-- the `histogram` frame --
16 = vals param 17 = q param      18 = its $res0   19 = its $res1
20 = $c0        21 = map DATA     22 = counts
23 = subject i  24 = subject flag  -- base0 = 25
-- two fresh `$c1`/`$c2` cells per counting iteration, from 25 --
25+2n = hits (subject)   26+2n = distinct (subject)
-- the range loop allocates NOTHING (see `stepFn_pick_novars`) --
```

## Kit gap witnessed here (campaign log `g1.md`)

**GAP-M1 the choice-pick step.** `stepFn_pick` — the `mapIterK` pick —
lives in `Examples/WordCount/Machine.lean`, not in the kit, and is
specialized to the `none`/`some "c"` binder shape. This example needs
the `none`/`none` shape (`for range m {}`), so it re-derives the step
as `stepFn_pick_novars` below. Nothing in either proof is
example-specific: both are statements about `mapIterK`, `Choices`, and
`MapMem.toEntries`. Shape wanted: ONE kit lemma in `MapMem` (or a
`MapIter` sibling) parameterized over the two binder options, with the
per-binder allocation described by `bindIterVars`. Two consumers exist
today (wordcount, histogram) and fibonacci-memo is chartered.
-/

namespace GoLean.Examples.Histogram

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.MapMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64
abbrev tMap : Ty := .map tU64 tU64

/-! ## The two `Func` records, verbatim from the pinned lowering -/

/-- The subject `Func`, verbatim from the pinned lowering (the pin
below ties it by `rfl`): count the values into a map, read the queried
key, then count the map's entries with a variable-free `for range`. -/
def histogramFunc : Func :=
  { id := { key := "histogram" },
    args := #[{ id := "vals", typ := .slice (.int .uint64) },
              { id := "q", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 },
                 { id := "$res1", typ := .int .uint64 }],
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
                .while (.boolLit true) whileBody]],
        .seqn
          #[.initialization { id := "hits", typ := .int .uint64 },
            .assign (.var "hits")
              (.mapGet (.var "counts") (.var "q")
                (.int .uint64) (.int .uint64))],
        .seqn
          #[.initialization { id := "distinct", typ := .int .uint64 },
            .assign (.var "distinct") (.intLit 0 .uint64)],
        .mapRange none none (.var "counts") (.int .uint64) (.int .uint64)
          rangeBody,
        .seqn
          #[.assign (.var "$res0") (.var "hits"),
            .assign (.var "$res1") (.var "distinct"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- One counting step: `counts[vals[i]]++` in its desugared
    temp-and-`mapAssign` form. -/
    countBody : Stmt :=
      .block
        #[]
        #[.seqn
            #[.initialization
                { id := "$c1", typ := .map (.int .uint64) (.int .uint64) },
              .assign (.var "$c1") (.var "counts")],
          .seqn
            #[.initialization { id := "$c2", typ := .int .uint64 },
              .assign (.var "$c2")
                (.indexGet (.var "vals") (.var "i"))],
          .mapAssign (.var "$c1") (.var "$c2")
            (.add
              (.mapGet (.var "$c1") (.var "$c2")
                (.int .uint64) (.int .uint64))
              (.intLit 1 .uint64))
            (.int .uint64) (.int .uint64)]
    /-- The counting loop's desugared body. -/
    whileBody : Stmt :=
      .block
        #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
          .seqn #[],
          .ifThenElse
            (.lessCmp (.var "i")
              (.length (.var "vals") (some (.slice (.int .uint64)))))
            (.seqn #[])
            .breakStmt,
          countBody]
    /-- The range loop's body: `distinct++`, and NOTHING else — no key
    binder, no value binder, so the iteration allocates no cell. -/
    rangeBody : Stmt :=
      .block
        #[]
        #[.assign (.var "distinct")
            (.add (.var "distinct") (.intLit 1 .uint64))]

/-- The lowering pin: the proof subject IS the frontend's lowering. -/
theorem histogram_pin :
    findFunctionIn? histogramLowered.funcs ⟨"histogram"⟩
    = some histogramFunc := rfl

/-- The returned fixed-cap array: the observed value list, zero-padded
to the harness's `histogramCapN = 8` slots. Statement vocabulary —
deliberately NOT shared with the identically shaped `WordCount.goArr8`
or `MinMax.goArr8`, since unifying them would change what these
statements say (the §11 closure rule). -/
def histArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-- The S3 relational harness `Func`, verbatim from the pinned
lowering: setup `v := make([]uint64, n)` filled with `v[i] = seed+i%3`,
a copy loop into the fixed-cap `vals` array, then the call under test
`histogram(v, q)` with both summaries returned as data. -/
def histHarnessRFunc : Func :=
  { id := { key := "histogram_harness_r" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 },
              { id := "q", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .array 8 (.int .uint64) },
                 { id := "$res1", typ := .int .uint64 },
                 { id := "$res2", typ := .int .uint64 }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c12", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c12") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "v", typ := .slice (.int .uint64) },
            .assign (.var "v") (.var "$c12")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) suBody]],
        .seqn
          #[.initialization { id := "vals", typ := .array 8 (.int .uint64) }],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .seqn
          #[.initialization { id := "hits", typ := .int .uint64 },
            .initialization { id := "distinct", typ := .int .uint64 },
            .call #[.var "hits", .var "distinct"] ⟨"histogram"⟩
              #[.var "v", .var "q"]],
        .seqn
          #[.assign (.var "$res0") (.var "vals"),
            .assign (.var "$res1") (.var "hits"),
            .assign (.var "$res2") (.var "distinct"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The SETUP loop's desugared body: the `$forFirst` dispatch, the
    exit test, the fill block `{ v[i] = seed + i%3 }`. -/
    suBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn
                #[.assign (.addr (.indexAddr (.var "v") (.var "i")))
                    (.add (.var "seed")
                      (.mod (.var "i") (.intLit 3 .uint64)))]]]
    /-- The COPY loop's desugared body: `vals[i] = v[i]` — the store
    target is an ADDRESS-rooted index chain (`.ref "vals"`), because
    `vals` is an array-typed LOCAL, not a slice handle. -/
    cpBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn
                #[.assign (.addr (.indexAddr (.ref "vals") (.var "i")))
                    (.indexGet (.var "v") (.var "i"))]]]

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem histogramHarnessR_pin :
    findFunctionIn? histogramLowered.funcs ⟨"histogram_harness_r"⟩
    = some histHarnessRFunc := rfl

/-! ## Statement pieces the continuations mention -/

abbrev hCountBody : Stmt := histogramFunc.countBody
abbrev hWhileBody : Stmt := histogramFunc.whileBody
abbrev hRangeBody : Stmt := histogramFunc.rangeBody

abbrev hMapRangeStmt : Stmt :=
  .mapRange none none (.var "counts") tU64 tU64 hRangeBody

abbrev hitsSeqn : Stmt :=
  .seqn
    #[.initialization { id := "hits", typ := tU64 },
      .assign (.var "hits") (.mapGet (.var "counts") (.var "q") tU64 tU64)]

abbrev distinctSeqn : Stmt :=
  .seqn
    #[.initialization { id := "distinct", typ := tU64 },
      .assign (.var "distinct") (.intLit 0 .uint64)]

abbrev hRetSeqn : Stmt :=
  .seqn
    #[.assign (.var "$res0") (.var "hits"),
      .assign (.var "$res1") (.var "distinct"),
      .returnStmt]

/-! ## Heap cells -/

abbrev u64cell (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev intcell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev bcell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev arrCell (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev mdCell (kvs : List (Int × Nat)) : HeapCell :=
  ⟨none, .mapData (toEntries kvs)⟩

/-- The PROGRAM-generic state form (the reverse/minmax/wordcount `vSt`
/ `rSt` convention). -/
abbrev hSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## The variable-free choice-pick step (GAP-M1) -/

/-- **The choice-pick step at a variable-free `for range m`** (§10b):
at a nonempty snapshot ONE choice is consumed (`idx < size` from
`Choices.consume`'s `% bound` contract) and the picked entry is erased
— and, because neither a key nor a value binder is present,
`bindIterVars` allocates NOTHING: the state is unchanged and only the
scope is pushed.

That is the whole reason this example's range loop is cheap, and it is
also why order-invariance is so visible here: the machine's only
per-iteration effect is "one fewer entry", so a claim about the number
of iterations cannot depend on the pick. -/
theorem stepFn_pick_novars {σ : ExecState} {rem : List (Int × Nat)}
    {idx : Nat} {ch ch' : Choices} {body : Stmt} {env : LocalEnv} {k : Cont}
    (hconsume : Choices.consume ch rem.length = (idx, ch'))
    (hidx : idx < rem.length) :
    stepFn σ
      (.next (.mapIterK none none tU64 tU64 body (toEntries rem) env k))
      ch
      = .ok (.exec body env.pushScope
          (.mapIterK none none tU64 tU64 body
            (toEntries (rem.eraseIdx idx)) env k),
        σ, ch') := by
  have hne : (toEntries rem).isEmpty = false := by
    cases rem with
    | nil => cases hidx
    | cons q rest => rfl
  have hsz : (toEntries rem).size = rem.length := toEntries_size rem
  have hidx' : idx < (toEntries rem).size := by rw [hsz]; exact hidx
  obtain ⟨p, hp⟩ : ∃ p, rem[idx]? = some p :=
    ⟨rem[idx]'hidx, List.getElem?_eq_getElem hidx⟩
  have hget : (toEntries rem)[idx]?
      = some (.int p.1 .uint64, .int (p.2 : Int) .uint64) :=
    toEntries_getElem? rem idx hp
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
    simp only [bindIterVars, Bind.bind, Except.bind, pure, Except.pure, hsz,
      hconsume, toEntries_eraseIdx rem idx hidx']

/-- Erasing the picked entry shortens the snapshot by exactly one — the
whole per-iteration content of the range loop, and the reason
`distinct` counts entries at every choice stream. -/
theorem eraseIdx_length_of_lt {kvs : List (Int × Nat)} {idx : Nat}
    (h : idx < kvs.length) : (kvs.eraseIdx idx).length = kvs.length - 1 := by
  rw [List.length_eraseIdx]
  simp [h]

/-- `Choices.consume`'s `% bound` contract: the pick is in range. -/
theorem consume_lt (ch : Choices) {n : Nat} (hn : 0 < n) :
    (Choices.consume ch n).1 < n := by
  cases ch with
  | nil => simpa [Choices.consume] using hn
  | cons c rest =>
      simp only [Choices.consume]
      have : max 1 n = n := by omega
      rw [this]
      exact Nat.mod_lt _ hn

/-! ## The pinned program and the entry equation -/

/-- The pinned program as an empty-heap state — with the
`derive_entry_eq` invocation below, the one place this module carries
`histogramLowered`. -/
def hProg : ExecState :=
  { types := histogramLowered.typeDefs.toList,
    functions := histogramLowered.funcs,
    methods := histogramLowered.methods,
    heap := [], nextAddr := 0 }

/- The post-prelude state (`hHSeed`), the start configuration
(`hHC0`), and the entry equation (`hH_entry_eq`) are DERIVED by the P4
entry-equation macro in its PROGRAM-GENERIC form (G0 item 3c): the
emitted state is the record update `{ hProg with … }`, so the
headline's show-bridge to the compositional `hSt hProg (hHeap0 …) 6`
spelling is structural. -/
derive_entry_eq hH_entry_eq histogramLowered histHarnessRFunc hHSeed hHC0 hProg

end GoLean.Examples.Histogram
