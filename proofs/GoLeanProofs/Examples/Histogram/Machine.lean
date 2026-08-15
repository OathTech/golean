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

-- (`eraseIdx_length_of_lt` and `consume_lt` are the kit's, via
-- `open GoLean.MapLoops` at the use sites — the re-derived copies were
-- deleted in the GAP-R1 closure.)

/-! ## The placement: environments, continuations, heap fronts

Every definition in this section is SHARED between the run shards
(`Histogram.CountLoop`, `Histogram.HarnessR`), which is why it lives
here rather than in either. Names follow the wordcount `*R` convention
with an `H` suffix. -/

abbrev zeros8 : List Int := List.replicate 8 0

abbrev hSliceV (n : Nat) : GoValue := .slice ⟨some (.base ⟨7⟩), 0, n, n⟩
abbrev hHandleV (n : Nat) : HeapCell := ⟨some (.slice tU64), hSliceV n⟩
abbrev hNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩
abbrev mhCellH : HeapCell := ⟨some tMap, .map ⟨some (.base ⟨21⟩)⟩⟩

/-! ### The harness body's top-level statement pieces -/

def hS2 : Stmt :=
  .seqn #[.initialization { id := "v", typ := .slice (.int .uint64) },
          .assign (.var "v") (.var "$c12")]
def hS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) histHarnessRFunc.suBody]]
def hS4 : Stmt :=
  .seqn #[.initialization { id := "vals", typ := .array 8 (.int .uint64) }]
def hS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .uint64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) histHarnessRFunc.cpBody]]
def hS6 : Stmt :=
  .seqn #[.initialization { id := "hits", typ := .int .uint64 },
          .initialization { id := "distinct", typ := .int .uint64 },
          .call #[.var "hits", .var "distinct"] ⟨"histogram"⟩
            #[.var "v", .var "q"]]
def hS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "vals"),
          .assign (.var "$res1") (.var "hits"),
          .assign (.var "$res2") (.var "distinct"),
          .returnStmt]

/-! ### Harness environments -/

def baseEnvH : Scope :=
  [("$res2", .base ⟨5⟩), ("$res1", .base ⟨4⟩), ("$res0", .base ⟨3⟩),
   ("q", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC12H : LocalEnv := [[("$c12", .base ⟨6⟩)], baseEnvH]
def vScopeH : Scope := [("v", .base ⟨8⟩), ("$c12", .base ⟨6⟩)]
def valsScopeH : Scope :=
  [("vals", .base ⟨11⟩), ("v", .base ⟨8⟩), ("$c12", .base ⟨6⟩)]
def callScopeH : Scope :=
  [("distinct", .base ⟨15⟩), ("hits", .base ⟨14⟩), ("vals", .base ⟨11⟩),
   ("v", .base ⟨8⟩), ("$c12", .base ⟨6⟩)]
def callEnvH : LocalEnv := [callScopeH, baseEnvH]

def suEnvH : LocalEnv :=
  [[("$forFirst", .base ⟨10⟩)], [("i", .base ⟨9⟩)], vScopeH, baseEnvH]
def suEnvH2 : LocalEnv := [] :: [] :: suEnvH
def cpEnvH : LocalEnv :=
  [[("$forFirst", .base ⟨13⟩)], [("i", .base ⟨12⟩)], valsScopeH, baseEnvH]
def cpEnvH2 : LocalEnv := [] :: [] :: cpEnvH

/-! ### Harness continuations -/

def hTailAfterSetup : Cont :=
  .seq [hS4, hS5, hS6, hS7] [vScopeH, baseEnvH] (.frame [] [] [] [] .stop)
def suHeadTailH : Cont :=
  .seq [] suEnvH
    (.seq [] [[("i", .base ⟨9⟩)], vScopeH, baseEnvH] hTailAfterSetup)
def suHeadCfgH : Config :=
  .exec (.while (.boolLit true) histHarnessRFunc.suBody) suEnvH suHeadTailH
def suLoopKH : Cont :=
  .loop (.boolLit true) histHarnessRFunc.suBody suEnvH suHeadTailH
def suStoreBlockH : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "v") (.var "i")))
        (.add (.var "seed") (.mod (.var "i") (.intLit 3 .uint64)))]]
def suCmpKH : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvH)
    (.seq [suStoreBlockH] ([] :: suEnvH) suLoopKH)
def suRefH (n : Nat) (iv : Int) : TargetRef :=
  .chain (hSliceV n) [.int iv .uint64] [.index]
def suStTailH : Cont :=
  .seq [] suEnvH2 (.seq [] ([] :: suEnvH) suLoopKH)
def suRhsKH (n : Nat) (iv : Int) : Cont :=
  .rhsK .vals [suRefH n iv] [] [] (.seqn #[]) suEnvH2 suStTailH
def suAddKH (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] suEnvH2 (suRhsKH n iv)
def suModKH (n : Nat) (sv iv : Int) : Cont :=
  .strictK .mod [.int iv .uint64] [] suEnvH2 (suAddKH n sv iv)

def hTailAfterCopy : Cont :=
  .seq [hS6, hS7] [valsScopeH, baseEnvH] (.frame [] [] [] [] .stop)
def cpHeadTailH : Cont :=
  .seq [] cpEnvH
    (.seq [] [[("i", .base ⟨12⟩)], valsScopeH, baseEnvH] hTailAfterCopy)
def cpHeadCfgH : Config :=
  .exec (.while (.boolLit true) histHarnessRFunc.cpBody) cpEnvH cpHeadTailH
def cpLoopKH : Cont :=
  .loop (.boolLit true) histHarnessRFunc.cpBody cpEnvH cpHeadTailH
def cpStoreBlockH : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "vals") (.var "i")))
        (.indexGet (.var "v") (.var "i"))]]
def cpCmpKH : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvH)
    (.seq [cpStoreBlockH] ([] :: cpEnvH) cpLoopKH)
def cpRefH (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨11⟩)) [.int iv .uint64] [.index]
def cpStTailH : Cont :=
  .seq [] cpEnvH2 (.seq [] ([] :: cpEnvH) cpLoopKH)
def cpRhsKH (iv : Int) : Cont :=
  .rhsK .vals [cpRefH iv] [] [] (.seqn #[]) cpEnvH2 cpStTailH

/-! ### The `histogram` call: TWO arguments, TWO results -/

def hAfterCall : Cont := .seq [hS7] callEnvH (.frame [] [] [] [] .stop)
def hCallPlans : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "hits"]), (.chain [], [.ref "distinct"])]
/-- The `callArgsK` after `v` is delivered and `q` still pending. -/
def hCallArgsK2 (n : Nat) : Cont :=
  .callArgsK ⟨"histogram"⟩ hCallPlans [hSliceV n] [] callEnvH hAfterCall
/-- The subject's call frame: result locs 18/19, write-back targets
`hits`/`distinct`, returning into the harness's epilogue. -/
def frameKH : Cont :=
  .frame hCallPlans callEnvH [.base ⟨18⟩, .base ⟨19⟩] [] hAfterCall
def hFrameEnv : LocalEnv :=
  [[("$res1", .base ⟨19⟩), ("$res0", .base ⟨18⟩), ("q", .base ⟨17⟩),
    ("vals", .base ⟨16⟩)]]

/-! ### Subject environments and continuations -/

def sc0H : Scope :=
  [("$res1", .base ⟨19⟩), ("$res0", .base ⟨18⟩), ("q", .base ⟨17⟩),
   ("vals", .base ⟨16⟩)]
def sc1H : Scope := [("counts", .base ⟨22⟩), ("$c0", .base ⟨20⟩)]
def envR0H : LocalEnv := [sc1H, sc0H]
def envBH : LocalEnv :=
  [[("$forFirst", .base ⟨24⟩)], [("i", .base ⟨23⟩)], sc1H, sc0H]
def envB1H : LocalEnv := [[("i", .base ⟨23⟩)], sc1H, sc0H]
def env2H : LocalEnv := [] :: envBH
def env3H : LocalEnv := [] :: env2H
def u1EnvH (na : Nat) : LocalEnv := [("$c1", .base ⟨na⟩)] :: env2H
def uEnvH (na : Nat) : LocalEnv :=
  [("$c2", .base ⟨na + 1⟩), ("$c1", .base ⟨na⟩)] :: env2H

abbrev asgnC1H : Stmt := .assign (.var "$c1") (.var "counts")
abbrev seqnC2H : Stmt :=
  .seqn
    #[.initialization { id := "$c2", typ := tU64 },
      .assign (.var "$c2") (.indexGet (.var "vals") (.var "i"))]
abbrev mapAsgnStmtH : Stmt :=
  .mapAssign (.var "$c1") (.var "$c2")
    (.add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64))
    tU64 tU64

def tailBH : Cont :=
  .seq [] envBH (.seq [] envB1H
    (.seq [hitsSeqn, distinctSeqn, hMapRangeStmt, hRetSeqn] envR0H frameKH))
/-- The counting-loop head configuration. -/
def headCH : Config := .exec (.while (.boolLit true) hWhileBody) envBH tailBH
def loopKCH : Cont := .loop (.boolLit true) hWhileBody envBH tailBH
def bodyTailH : Cont := .seq [hCountBody] env2H loopKCH
def cmpContCH : Cont := .ifK (.seqn #[]) .breakStmt env2H bodyTailH
def lenKH (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] env2H
    (.strictK .lessCmp [.int iv .int] [] env2H cmpContCH)
def postBodyKH : Cont := .seq [] env2H loopKCH

def stK0H (na : Nat) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0 []
    [.var "$c2",
     .add (.mapGet (.var "$c1") (.var "$c2") tU64 tU64) (.intLit 1 .uint64)]
    (uEnvH na) (.seq [] (uEnvH na) postBodyKH)
def stK2H (na : Nat) (w : Int) : Cont :=
  .stmtOpK (.mapAssign tU64 tU64) 0
    [.int w .uint64, .map ⟨some (.base ⟨21⟩)⟩] []
    (uEnvH na) (.seq [] (uEnvH na) postBodyKH)
def addKH (na : Nat) (w : Int) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (uEnvH na) (stK2H na w)
def mapGetKH (na : Nat) (w : Int) : Cont :=
  .strictK (.mapGet tU64 tU64) [.map ⟨some (.base ⟨21⟩)⟩] [] (uEnvH na)
    (addKH na w)

/-! ### The query / range / return tail, at `hits = B`, `distinct = B+1` -/

def envRBH (B : Nat) : LocalEnv := (("hits", .base ⟨B⟩) :: sc1H) :: [sc0H]
def envRBDH (B : Nat) : LocalEnv :=
  (("distinct", .base ⟨B + 1⟩) :: ("hits", .base ⟨B⟩) :: sc1H) :: [sc0H]
def kRH (B : Nat) : Cont := .seq [hRetSeqn] (envRBDH B) frameKH
def iterKH (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .mapIterK none none tU64 tU64 hRangeBody (toEntries rem) (envRBDH B) (kRH B)
def envIt1 (B : Nat) : LocalEnv := [] :: envRBDH B
def envIt2 (B : Nat) : LocalEnv := [] :: envIt1 B
def rngRef (B : Nat) : TargetRef := .chain (.addr (.base ⟨B + 1⟩)) [] []
def rngStoreK (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .seq [] (envIt2 B) (iterKH B rem)
def rngRhsK (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .rhsK .vals [rngRef B] [] [] (.seqn #[]) (envIt2 B) (rngStoreK B rem)
def rngAddK (B : Nat) (rem : List (Int × Nat)) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (envIt2 B) (rngRhsK B rem)

/-! ### Heap fronts (program-generic) -/

def hHeap0 (nv sv qv : Int) : Heap :=
  [(.base ⟨0⟩, u64cell nv), (.base ⟨1⟩, u64cell sv), (.base ⟨2⟩, u64cell qv),
   (.base ⟨3⟩, arrCell 8 zeros8), (.base ⟨4⟩, u64cell 0),
   (.base ⟨5⟩, u64cell 0)]

def hHeapC12 (nv sv qv : Int) : Heap :=
  hHeap0 nv sv qv ++ [(.base ⟨6⟩, hNilSlice)]

def hHeapMake (nv sv qv : Int) (n : Nat) : Heap :=
  hHeap0 nv sv qv ++
    [(.base ⟨6⟩, hHandleV n), (.base ⟨7⟩, arrCell n (List.replicate n 0))]

def hHeapSu (nv sv qv : Int) (n : Nat) (l : List Int) (iv : Int) (ff : Bool) :
    Heap :=
  hHeap0 nv sv qv ++
    [(.base ⟨6⟩, hHandleV n), (.base ⟨7⟩, arrCell n l),
     (.base ⟨8⟩, hHandleV n), (.base ⟨9⟩, u64cell iv), (.base ⟨10⟩, bcell ff)]

def hHeapCp (nv sv qv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ff : Bool) : Heap :=
  hHeapSu nv sv qv n l siv false ++
    [(.base ⟨11⟩, arrCell 8 lp), (.base ⟨12⟩, u64cell civ),
     (.base ⟨13⟩, bcell ff)]

def hHeapCall (nv sv qv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  hHeapCp nv sv qv n l lp siv civ false ++
    [(.base ⟨14⟩, u64cell 0), (.base ⟨15⟩, u64cell 0)]

def hHeapHFrame (nv sv qv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  hHeapCall nv sv qv n l lp siv civ ++
    [(.base ⟨16⟩, hHandleV n), (.base ⟨17⟩, u64cell qv),
     (.base ⟨18⟩, u64cell 0), (.base ⟨19⟩, u64cell 0)]

/-- The twenty-five concrete front cells during the subject's counting
and range phases. -/
def frontH (L : Nat) (sv qv siv civ : Int) (ws lp : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, u64cell qv), (.base ⟨3⟩, arrCell 8 zeros8),
   (.base ⟨4⟩, u64cell 0), (.base ⟨5⟩, u64cell 0),
   (.base ⟨6⟩, hHandleV L), (.base ⟨7⟩, arrCell L ws),
   (.base ⟨8⟩, hHandleV L), (.base ⟨9⟩, u64cell siv),
   (.base ⟨10⟩, bcell false), (.base ⟨11⟩, arrCell 8 lp),
   (.base ⟨12⟩, u64cell civ), (.base ⟨13⟩, bcell false),
   (.base ⟨14⟩, u64cell 0), (.base ⟨15⟩, u64cell 0),
   (.base ⟨16⟩, hHandleV L), (.base ⟨17⟩, u64cell qv),
   (.base ⟨18⟩, u64cell 0), (.base ⟨19⟩, u64cell 0),
   (.base ⟨20⟩, mhCellH), (.base ⟨21⟩, mdCell kvs), (.base ⟨22⟩, mhCellH),
   (.base ⟨23⟩, intcell iv), (.base ⟨24⟩, bcell ff)]

/-- The subject-phase state: concrete front + the symbolic dead-cell
tail, over an ABSTRACT program context. -/
def σH (σ : ExecState) (L : Nat) (sv qv siv civ : Int) (ws lp : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) (dead : Heap)
    (na : Nat) : ExecState :=
  hSt σ (frontH L sv qv siv civ ws lp kvs iv ff ++ dead) na

theorem lookup_frontH_none (L : Nat) (sv qv siv civ : Int) (ws lp : List Int)
    (kvs : List (Int × Nat)) (iv : Int) (ff : Bool) {x : Nat} (hx : 25 ≤ x) :
    Heap.lookup (frontH L sv qv siv civ ws lp kvs iv ff) (.base ⟨x⟩)
      = none := by
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
    base_beq_false (by omega : (16 : Nat) ≠ x),
    base_beq_false (by omega : (17 : Nat) ≠ x),
    base_beq_false (by omega : (18 : Nat) ≠ x),
    base_beq_false (by omega : (19 : Nat) ≠ x),
    base_beq_false (by omega : (20 : Nat) ≠ x),
    base_beq_false (by omega : (21 : Nat) ≠ x),
    base_beq_false (by omega : (22 : Nat) ≠ x),
    base_beq_false (by omega : (23 : Nat) ≠ x),
    base_beq_false (by omega : (24 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

/-- The exit-phase front: the harness results (3/4/5), the harness
`hits`/`distinct` (14/15) and the subject results (18/19) generalized;
the counting counter parked at `L`. -/
def frontXH (L : Nat) (sv qv siv civ : Int) (ws lp r3 : List Int)
    (kvs : List (Int × Nat)) (r4 r5 r14 r15 r18 r19 : Int) : Heap :=
  [(.base ⟨0⟩, u64cell (L : Int)), (.base ⟨1⟩, u64cell sv),
   (.base ⟨2⟩, u64cell qv), (.base ⟨3⟩, arrCell 8 r3),
   (.base ⟨4⟩, u64cell r4), (.base ⟨5⟩, u64cell r5),
   (.base ⟨6⟩, hHandleV L), (.base ⟨7⟩, arrCell L ws),
   (.base ⟨8⟩, hHandleV L), (.base ⟨9⟩, u64cell siv),
   (.base ⟨10⟩, bcell false), (.base ⟨11⟩, arrCell 8 lp),
   (.base ⟨12⟩, u64cell civ), (.base ⟨13⟩, bcell false),
   (.base ⟨14⟩, u64cell r14), (.base ⟨15⟩, u64cell r15),
   (.base ⟨16⟩, hHandleV L), (.base ⟨17⟩, u64cell qv),
   (.base ⟨18⟩, u64cell r18), (.base ⟨19⟩, u64cell r19),
   (.base ⟨20⟩, mhCellH), (.base ⟨21⟩, mdCell kvs), (.base ⟨22⟩, mhCellH),
   (.base ⟨23⟩, intcell ((L : Nat) : Int)), (.base ⟨24⟩, bcell false)]

def σXH (σ : ExecState) (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) (tail : Heap) (na : Nat) : ExecState :=
  hSt σ (frontXH L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19 ++ tail)
    na

theorem lookup_frontXH_none (L : Nat) (sv qv siv civ : Int)
    (ws lp r3 : List Int) (kvs : List (Int × Nat))
    (r4 r5 r14 r15 r18 r19 : Int) {x : Nat} (hx : 25 ≤ x) :
    Heap.lookup (frontXH L sv qv siv civ ws lp r3 kvs r4 r5 r14 r15 r18 r19)
        (.base ⟨x⟩) = none := by
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
    base_beq_false (by omega : (16 : Nat) ≠ x),
    base_beq_false (by omega : (17 : Nat) ≠ x),
    base_beq_false (by omega : (18 : Nat) ≠ x),
    base_beq_false (by omega : (19 : Nat) ≠ x),
    base_beq_false (by omega : (20 : Nat) ≠ x),
    base_beq_false (by omega : (21 : Nat) ≠ x),
    base_beq_false (by omega : (22 : Nat) ≠ x),
    base_beq_false (by omega : (23 : Nat) ≠ x),
    base_beq_false (by omega : (24 : Nat) ≠ x),
    Bool.false_eq_true, if_false]

-- GAP-M2 CLOSED (kit-gap closure, 2026-08-15): the re-derived
-- `DeadFrom` + `push`/`push2` copies this module carried as
-- gap-witness code are DELETED; the kit forms live in
-- `GoLeanProofs/StepKit.lean` (visible via `open GoLean.Surface`).

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
