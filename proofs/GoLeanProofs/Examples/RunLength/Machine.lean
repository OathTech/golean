import GoLeanProofs.Examples.RunLength.Pure
import GoLeanProofs.Examples.RunLengthProgram
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# RunLength — Machine

The machine-facing layer: the two `Func` records transcribed from the
pinned lowering (each tied to it by an `rfl` pin), the statement
pieces, the address layout, the environments/continuations and the
heap fronts, and the derived entry equation.

The guardrails wave landed the harness `Func` in the example ROOT in
the mechanically-extracted spelling. It is restated here in the
readable dot-notation form — the wave's recorded allowance ("a proof
lane may restate it readably; the pin must keep holding by `rfl`") —
and `rleHarnessRFunc_pin` is the check that the restatement says
exactly what the lowering says.

Address layout (probe-measured at `(n, seed) = (3, 7)` with the lane's
generic tracer `.tmp/Probe.lean`; every raw segment downstream
re-checks the transcription by `rfl`, so a mis-read layout fails
loudly rather than silently):

```
 0 = n            1 = seed        2 = $res0 ([8]u64)   3 = $res1 ([8]u64)
 4 = $res2 ([8])  5 = $res3       6 = $c10 handle      7 = s backing
 8 = s            9 = setup i    10 = setup flag
11 = pre ([8])   12 = copy i     13 = copy flag
14 = vals        15 = counts
-- the `rle` frame (entered at nextAddr 16) --
16 = s param     17 = its $res0  18 = its $res1
19 = $c0         20 = $c0 backing ([]— empty)          21 = runVals
22 = $c1         23 = $c1 backing                      24 = runCounts
25 = i           26 = $forFirst
-- subject iteration i=0 (the new-run event; ALWAYS two spills:
-- both slices have cap 0) --
27 = k           28 = extended   29 = $c2   30 = $c2 backing
31 = $c3         32 = runVals SPILL backing (cap `capV`, CHOICE-dependent)
33 = $c4         34 = $c4 backing
35 = $c5         36 = runCounts SPILL backing (cap `capC`, CHOICE-dependent)
-- each extend iteration (i = 1, 2): k at 37+2j, extended at 38+2j --
-- after the frame returns (n = 3): 41 = runVals [8]u64,
-- 42 = runCounts [8]u64, 43 = final-copy i, 44 = final-copy flag
-- (for n = 1/2 those four sit at 37../39.. — the exit layout is
-- per-`n`, which is why the exit segments below come in instances)
```

**The append-spill capacities are nondeterministic.** On a spill the
machine draws `extra` from the choice stream and allocates a fresh
backing of `newCap = newLen + ((appendGrowthCap − newLen + extra) %
width)` — for this example's two spills (cap 0 → len 1) the envelope is
`capV, capC ∈ [1, 32]`. Both spilled caps are carried SYMBOLICALLY
through every downstream front; nothing the harness returns depends on
them, which is what the headline's `∀ ch` quantifier means here.
-/

namespace GoLean.Examples.RunLength

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The subject `Func`, verbatim from the pinned lowering -/

/-- The subject `Func`: walk `s`, extending the current run while the
value repeats (`runCounts[k-1]++`), opening a new run otherwise — the
new-run arm builds a one-element slice and `append`s it onto each of
the two output slices. -/
def rleFunc : Func :=
  { id := { key := "rle" },
    args := #[{ id := "s", typ := .slice tU64 }],
    results := #[{ id := "$res0", typ := .slice tU64 },
                 { id := "$res1", typ := .slice tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c0", typ := .slice tU64 },
                .makeSlice (.var "$c0") tU64 (.intLit 0 .int)
                  (some (.intLit 0 .int))],
        .seqn #[.initialization { id := "runVals", typ := .slice tU64 },
                .assign (.var "runVals") (.var "$c0")],
        .seqn #[.initialization { id := "$c1", typ := .slice tU64 },
                .makeSlice (.var "$c1") tU64 (.intLit 0 .int)
                  (some (.intLit 0 .int))],
        .seqn #[.initialization { id := "runCounts", typ := .slice tU64 },
                .assign (.var "runCounts") (.var "$c1")],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := .int .int },
                    .assign (.var "i") (.intLit 0 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) rlBody]],
        .seqn #[.assign (.var "$res0") (.var "runVals"),
                .assign (.var "$res1") (.var "runCounts"),
                .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The extend arm: `runCounts[k-1]++`. -/
    rlExtendBlock : Stmt :=
      .block #[]
        #[.assign (.addr (.indexAddr (.var "runCounts")
              (.sub (.var "k") (.intLit 1 .int))))
            (.add (.indexGet (.var "runCounts")
              (.sub (.var "k") (.intLit 1 .int))) (.intLit 1 .uint64)),
          .seqn #[.assign (.var "extended") (.boolLit true)]]
    /-- The new-run arm: `runVals = append(runVals, s[i])`;
    `runCounts = append(runCounts, 1)` — each `append` desugared to a
    one-element `make` + `appendSlice`. -/
    rlNewRunBlock : Stmt :=
      .block #[]
        #[.seqn #[.initialization { id := "$c2", typ := .slice tU64 },
                  .makeSlice (.var "$c2") tU64 (.intLit 1 .int)
                    (some (.intLit 1 .int)),
                  .assign (.addr (.indexAddr (.var "$c2") (.intLit 0 .int)))
                    (.indexGet (.var "s") (.var "i"))],
          .seqn #[.initialization { id := "$c3", typ := .slice tU64 },
                  .appendSlice (.var "$c3") tU64 (.var "runVals")
                    (.var "$c2")],
          .seqn #[.assign (.var "runVals") (.var "$c3")],
          .seqn #[.initialization { id := "$c4", typ := .slice tU64 },
                  .makeSlice (.var "$c4") tU64 (.intLit 1 .int)
                    (some (.intLit 1 .int)),
                  .assign (.addr (.indexAddr (.var "$c4") (.intLit 0 .int)))
                    (.intLit 1 .uint64)],
          .seqn #[.initialization { id := "$c5", typ := .slice tU64 },
                  .appendSlice (.var "$c5") tU64 (.var "runCounts")
                    (.var "$c4")],
          .seqn #[.assign (.var "runCounts") (.var "$c5")]]
    /-- The loop body: first-pass flag / `i++`, exit test
    `i < len(s)`, then `k := len(runVals)`, `extended := false`, the
    guarded extend test, and the `!extended` new-run arm. -/
    rlBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i")
              (.length (.var "s") (some (.slice tU64))))
            (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn #[.initialization { id := "k", typ := .int .int },
                      .assign (.var "k")
                        (.length (.var "runVals") (some (.slice tU64)))],
              .seqn #[.initialization { id := "extended", typ := .bool },
                      .assign (.var "extended") (.boolLit false)],
              .ifThenElse (.greaterCmp (.var "k") (.intLit 0 .int))
                (.block #[]
                  #[.ifThenElse (.eqCmp tU64
                        (.indexGet (.var "runVals")
                          (.sub (.var "k") (.intLit 1 .int)))
                        (.indexGet (.var "s") (.var "i")))
                      rlExtendBlock (.seqn #[])])
                (.seqn #[]),
              .ifThenElse (.not (.var "extended"))
                rlNewRunBlock (.seqn #[])]]

/-- The harness `Func`, restated readably from the guardrails wave's
mechanically-extracted spelling; `rleHarnessRFunc_pin` ties it to the
lowering by `rfl`. -/
def rleHarnessRFunc : Func :=
  { id := { key := "rle_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := .array 8 tU64 },
                 { id := "$res2", typ := .array 8 tU64 },
                 { id := "$res3", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c10", typ := .slice tU64 },
                .makeSlice (.var "$c10") tU64 (.var "n") none],
        .seqn #[.initialization { id := "s", typ := .slice tU64 },
                .assign (.var "s") (.var "$c10")],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) suBody]],
        .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .seqn #[.initialization { id := "vals", typ := .slice tU64 },
                .initialization { id := "counts", typ := .slice tU64 },
                .call #[.var "vals", .var "counts"] ⟨"rle"⟩ #[.var "s"]],
        .seqn #[.initialization { id := "runVals", typ := .array 8 tU64 }],
        .seqn #[.initialization { id := "runCounts", typ := .array 8 tU64 }],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := .int .int },
                    .assign (.var "i") (.intLit 0 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) fcBody]],
        .seqn #[.assign (.var "$res0") (.var "pre"),
                .assign (.var "$res1") (.var "runVals"),
                .assign (.var "$res2") (.var "runCounts"),
                .assign (.var "$res3")
                  (.convert tU64
                    (.length (.var "vals") (some (.slice tU64)))),
                .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The setup loop's body: `s[i] = seed + i/3`. -/
    suBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
                (.add (.var "seed") (.div (.var "i") (.intLit 3 .uint64)))]]]
    /-- The copy loop's body: `pre[i] = s[i]`. -/
    cpBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
                (.indexGet (.var "s") (.var "i"))]]]
    /-- The final copy loop's body: `runVals[i] = vals[i];
    runCounts[i] = counts[i]` — its trip count is `len(vals)`, the
    DATA-dependent run count. -/
    fcBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i")
              (.length (.var "vals") (some (.slice tU64))))
            (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn #[.assign
                (.addr (.indexAddr (.ref "runVals") (.var "i")))
                (.indexGet (.var "vals") (.var "i"))],
              .seqn #[.assign
                (.addr (.indexAddr (.ref "runCounts") (.var "i")))
                (.indexGet (.var "counts") (.var "i"))]]]

/-- The subject lowering pin. -/
theorem rle_pin :
    findFunctionIn? rleLowered.funcs ⟨"rle"⟩ = some rleFunc := rfl

/-- The harness lowering pin: the readable restatement IS the
frontend's lowering (the guardrails-wave pin, kept under its name). -/
theorem rleHarnessRFunc_pin :
    findFunctionIn? rleLowered.funcs ⟨"rle_harness_r"⟩
      = some rleHarnessRFunc := rfl

/-! ## The S3 statement adapter -/

/-- The returned fixed-cap array, zero-padded past the live prefix —
statement vocabulary (what "the returned `[rleCapN]uint64`" means as a
`GoValue`). -/
def rleArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-! ## The PROGRAM-generic state form -/

abbrev qSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## Cells and handles at the rle layout -/

abbrev qu64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev qint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev qbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
/-- The `s` slice value: base 7, the harness backing. -/
abbrev qSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨7⟩), 0, n, n⟩
abbrev qHandle (n : Nat) : HeapCell := ⟨some (.slice tU64), qSliceS n⟩
abbrev qBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev qArr8C (l : List Int) : HeapCell :=
  ⟨some (.array 8 tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev qNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩
/-- An EMPTY slice over an (empty) backing at `b` — the `make([]uint64,
0, 0)` result. -/
abbrev qESliceV (b : Nat) : GoValue := .slice ⟨some (.base ⟨b⟩), 0, 0, 0⟩
abbrev qESlice (b : Nat) : HeapCell := ⟨some (.slice tU64), qESliceV b⟩
abbrev qEmptyBack : HeapCell :=
  ⟨some (.array 0 tU64), .array ⟨([] : List Int).map (fun v => .int v .uint64)⟩⟩
/-- A one-element slice over backing `b` (`make([]uint64, 1, 1)`). -/
abbrev qC1SliceV (b : Nat) : GoValue := .slice ⟨some (.base ⟨b⟩), 0, 1, 1⟩
abbrev qC1Slice (b : Nat) : HeapCell := ⟨some (.slice tU64), qC1SliceV b⟩
abbrev qBack1 (v : Int) : HeapCell :=
  ⟨some (.array 1 tU64), .array ⟨[v].map (fun x => .int x .uint64)⟩⟩
/-- A length-1 run slice over a SPILLED backing at `b` with symbolic
cap. -/
abbrev qRunSliceV (b cap : Nat) : GoValue := .slice ⟨some (.base ⟨b⟩), 0, 1, cap⟩
abbrev qRunSlice (b cap : Nat) : HeapCell := ⟨some (.slice tU64), qRunSliceV b cap⟩
/-- The spilled backing's content list: the one live element, then the
capacity pad. -/
abbrev qPadL (cap : Nat) (v : Int) : List Int := v :: List.replicate (cap - 1) 0
abbrev qBackPad (cap : Nat) (v : Int) : HeapCell :=
  ⟨some (.array cap tU64), .array ⟨(qPadL cap v).map (fun x => .int x .uint64)⟩⟩

def zeros8 : List Int := List.replicate 8 0

/-! ## Statement pieces (the harness body's tail lists) -/

def qS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice tU64 },
          .assign (.var "s") (.var "$c10")]
def qS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) rleHarnessRFunc.suBody]]
def qS4 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }]
def qS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) rleHarnessRFunc.cpBody]]
def qS6 : Stmt :=
  .seqn #[.initialization { id := "vals", typ := .slice tU64 },
          .initialization { id := "counts", typ := .slice tU64 },
          .call #[.var "vals", .var "counts"] ⟨"rle"⟩ #[.var "s"]]
def qS7 : Stmt :=
  .seqn #[.initialization { id := "runVals", typ := .array 8 tU64 }]
def qS8 : Stmt :=
  .seqn #[.initialization { id := "runCounts", typ := .array 8 tU64 }]
def qS9 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) rleHarnessRFunc.fcBody]]
def qS10 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "runVals"),
          .assign (.var "$res2") (.var "runCounts"),
          .assign (.var "$res3")
            (.convert tU64 (.length (.var "vals") (some (.slice tU64)))),
          .returnStmt]

/-! ## Environments — the harness half -/

def baseEnvQ : Scope :=
  [("$res3", .base ⟨5⟩), ("$res2", .base ⟨4⟩), ("$res1", .base ⟨3⟩),
   ("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC10Q : LocalEnv := [[("$c10", .base ⟨6⟩)], baseEnvQ]
def sScopeQ : Scope := [("s", .base ⟨8⟩), ("$c10", .base ⟨6⟩)]
def preScopeQ : Scope :=
  [("pre", .base ⟨11⟩), ("s", .base ⟨8⟩), ("$c10", .base ⟨6⟩)]
def callScopeQ : Scope :=
  [("counts", .base ⟨15⟩), ("vals", .base ⟨14⟩), ("pre", .base ⟨11⟩),
   ("s", .base ⟨8⟩), ("$c10", .base ⟨6⟩)]
def callEnvQ : LocalEnv := [callScopeQ, baseEnvQ]

def suEnvQ : LocalEnv :=
  [[("$forFirst", .base ⟨10⟩)], [("i", .base ⟨9⟩)], sScopeQ, baseEnvQ]
def suEnvQ2 : LocalEnv := [] :: [] :: suEnvQ
def cpEnvQ : LocalEnv :=
  [[("$forFirst", .base ⟨13⟩)], [("i", .base ⟨12⟩)], preScopeQ, baseEnvQ]
def cpEnvQ2 : LocalEnv := [] :: [] :: cpEnvQ

/-! ## Continuations — the setup loop -/

def qTailAfterSetup : Cont :=
  .seq [qS4, qS5, qS6, qS7, qS8, qS9, qS10] [sScopeQ, baseEnvQ]
    (.frame [] [] [] [] .stop)
def suHeadTailQ : Cont :=
  .seq [] suEnvQ
    (.seq [] [[("i", .base ⟨9⟩)], sScopeQ, baseEnvQ] qTailAfterSetup)
def suHeadCfgQ : Config :=
  .exec (.while (.boolLit true) rleHarnessRFunc.suBody) suEnvQ suHeadTailQ
def suLoopKQ : Cont :=
  .loop (.boolLit true) rleHarnessRFunc.suBody suEnvQ suHeadTailQ
def suStoreBlockQ : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.div (.var "i") (.intLit 3 .uint64)))]]
def suCmpKQ : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvQ)
    (.seq [suStoreBlockQ] ([] :: suEnvQ) suLoopKQ)
def suRefQ (n : Nat) (iv : Int) : TargetRef :=
  .chain (qSliceS n) [.int iv .uint64] [.index]
def suStTailQ : Cont :=
  .seq [] suEnvQ2 (.seq [] ([] :: suEnvQ) suLoopKQ)
def suAddKQ (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] suEnvQ2
    (.rhsK .vals [suRefQ n iv] [] [] (.seqn #[]) suEnvQ2 suStTailQ)
/-- The `/` apply point inside the setup body (`seed + i/3`). -/
def suDivKQ (n : Nat) (sv iv : Int) : Cont :=
  .strictK .div [.int iv .uint64] [] suEnvQ2 (suAddKQ n sv iv)

/-! ## Continuations — the copy loop -/

def qTailAfterCopy : Cont :=
  .seq [qS6, qS7, qS8, qS9, qS10] [preScopeQ, baseEnvQ]
    (.frame [] [] [] [] .stop)
def cpHeadTailQ : Cont :=
  .seq [] cpEnvQ
    (.seq [] [[("i", .base ⟨12⟩)], preScopeQ, baseEnvQ] qTailAfterCopy)
def cpHeadCfgQ : Config :=
  .exec (.while (.boolLit true) rleHarnessRFunc.cpBody) cpEnvQ cpHeadTailQ
def cpLoopKQ : Cont :=
  .loop (.boolLit true) rleHarnessRFunc.cpBody cpEnvQ cpHeadTailQ
def cpStoreBlockQ : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpKQ : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvQ)
    (.seq [cpStoreBlockQ] ([] :: cpEnvQ) cpLoopKQ)
def cpRefQ (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨11⟩)) [.int iv .uint64] [.index]
def cpStTailQ : Cont :=
  .seq [] cpEnvQ2 (.seq [] ([] :: cpEnvQ) cpLoopKQ)
def cpRhsKQ (iv : Int) : Cont :=
  .rhsK .vals [cpRefQ iv] [] [] (.seqn #[]) cpEnvQ2 cpStTailQ

/-! ## Continuations — the `rle` call and frame -/

def qShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "vals"]), (.chain [], [.ref "counts"])]
def qAfterCall : Cont :=
  .seq [qS7, qS8, qS9, qS10] callEnvQ (.frame [] [] [] [] .stop)
def qCallArgsK : Cont :=
  .callArgsK ⟨"rle"⟩ qShapes [] [] callEnvQ qAfterCall
def rFrameScope : Scope :=
  [("$res1", .base ⟨18⟩), ("$res0", .base ⟨17⟩), ("s", .base ⟨16⟩)]
def rFrameEnv : LocalEnv := [rFrameScope]
def rFrameK : Cont :=
  .frame qShapes callEnvQ [.base ⟨17⟩, .base ⟨18⟩] [] qAfterCall false

/-! ## The `rle` frame's environments and continuations -/

def rScope : Scope :=
  [("runCounts", .base ⟨24⟩), ("$c1", .base ⟨22⟩),
   ("runVals", .base ⟨21⟩), ("$c0", .base ⟨19⟩)]
/-- Mid-prologue scope: `runCounts` not yet declared. -/
def rMidScope : Scope :=
  [("$c1", .base ⟨22⟩), ("runVals", .base ⟨21⟩), ("$c0", .base ⟨19⟩)]
def rMidEnv : LocalEnv := [rMidScope, rFrameScope]
/-- The body statements still pending at the `$c1` make apply point. -/
def rS4 : Stmt :=
  .seqn #[.initialization { id := "runCounts", typ := .slice tU64 },
          .assign (.var "runCounts") (.var "$c1")]
def rS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) rleFunc.rlBody]]
def rEnvI : LocalEnv := [("i", .base ⟨25⟩)] :: rScope :: rFrameEnv
def rEnvIn : LocalEnv := [("$forFirst", .base ⟨26⟩)] :: rEnvI

/-- The subject's epilogue. -/
def rTailSeqn : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "runVals"),
          .assign (.var "$res1") (.var "runCounts"),
          .returnStmt]

def rHeadTailQ : Cont :=
  .seq [] rEnvIn (.seq [] rEnvI (.seq [rTailSeqn] (rScope :: rFrameEnv) rFrameK))
def rHeadCfgQ : Config :=
  .exec (.while (.boolLit true) rleFunc.rlBody) rEnvIn rHeadTailQ
def rLoopKQ : Cont :=
  .loop (.boolLit true) rleFunc.rlBody rEnvIn rHeadTailQ
/-- The subject's exit-test continuation (`i < len(s)` delivered). -/
def rCmpKQ : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: rEnvIn)
    (.seq [.block #[]
        #[.seqn #[.initialization { id := "k", typ := .int .int },
                  .assign (.var "k")
                    (.length (.var "runVals") (some (.slice tU64)))],
          .seqn #[.initialization { id := "extended", typ := .bool },
                  .assign (.var "extended") (.boolLit false)],
          .ifThenElse (.greaterCmp (.var "k") (.intLit 0 .int))
            (.block #[]
              #[.ifThenElse (.eqCmp tU64
                    (.indexGet (.var "runVals")
                      (.sub (.var "k") (.intLit 1 .int)))
                    (.indexGet (.var "s") (.var "i")))
                  rleFunc.rlExtendBlock (.seqn #[])])
            (.seqn #[]),
          .ifThenElse (.not (.var "extended"))
            rleFunc.rlNewRunBlock (.seqn #[])]]
      ([] :: rEnvIn) rLoopKQ)

/-! ## Continuations — inside the subject loop

The loop-body block pushes a scope, the `k`/`extended` block another;
`k`'s cell address advances by 2 per iteration, so the pieces are
parameterized by `ka` (this iteration's `k`-cell address). -/

def rBodyEnv : LocalEnv := [] :: rEnvIn
def rKEnv (ka : Nat) : LocalEnv := [("k", .base ⟨ka⟩)] :: rBodyEnv
def rKEEnv (ka : Nat) : LocalEnv :=
  [("extended", .base ⟨ka + 1⟩), ("k", .base ⟨ka⟩)] :: rBodyEnv
def rSeqExtInit : Stmt :=
  .seqn #[.initialization { id := "extended", typ := .bool },
          .assign (.var "extended") (.boolLit false)]
def rIfGuard : Stmt :=
  .ifThenElse (.greaterCmp (.var "k") (.intLit 0 .int))
    (.block #[]
      #[.ifThenElse (.eqCmp tU64
            (.indexGet (.var "runVals")
              (.sub (.var "k") (.intLit 1 .int)))
            (.indexGet (.var "s") (.var "i")))
          rleFunc.rlExtendBlock (.seqn #[])])
    (.seqn #[])
def rIfNew : Stmt :=
  .ifThenElse (.not (.var "extended")) rleFunc.rlNewRunBlock (.seqn #[])
def rBlockTail : Cont := .seq [] rBodyEnv rLoopKQ
def rKTailK (ka : Nat) : Cont :=
  .seq [rSeqExtInit, rIfGuard, rIfNew] (rKEnv ka) rBlockTail
/-- The `len(runVals)` apply point (the `k :=` assignment). -/
def rKLenK (ka : Nat) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] (rKEnv ka)
    (.rhsK .vals [.chain (.addr (.base ⟨ka⟩)) [] []] [] [] (.seqn #[])
      (rKEnv ka) (rKTailK ka))
/-- The head-test `len(s)` apply point (`i < len(s)`). -/
def rLenSK (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] rBodyEnv
    (.strictK .lessCmp [.int iv .int] [] rBodyEnv rCmpKQ)

/-! ### The new-run event's pieces (iteration `i = 0`; every address
literal — the event always runs at `k` cell 27) -/

def rNRs3 : Stmt :=
  .seqn #[.initialization { id := "$c3", typ := .slice tU64 },
          .appendSlice (.var "$c3") tU64 (.var "runVals") (.var "$c2")]
def rNRs4 : Stmt := .seqn #[.assign (.var "runVals") (.var "$c3")]
def rNRs5 : Stmt :=
  .seqn #[.initialization { id := "$c4", typ := .slice tU64 },
          .makeSlice (.var "$c4") tU64 (.intLit 1 .int)
            (some (.intLit 1 .int)),
          .assign (.addr (.indexAddr (.var "$c4") (.intLit 0 .int)))
            (.intLit 1 .uint64)]
def rNRs6 : Stmt :=
  .seqn #[.initialization { id := "$c5", typ := .slice tU64 },
          .appendSlice (.var "$c5") tU64 (.var "runCounts") (.var "$c4")]
def rNRs7 : Stmt := .seqn #[.assign (.var "runCounts") (.var "$c5")]

def rNREnv1 : LocalEnv := [("$c2", .base ⟨29⟩)] :: rKEEnv 27
def rNREnv2 : LocalEnv :=
  [("$c3", .base ⟨31⟩), ("$c2", .base ⟨29⟩)] :: rKEEnv 27
def rNREnv3 : LocalEnv :=
  [("$c4", .base ⟨33⟩), ("$c3", .base ⟨31⟩), ("$c2", .base ⟨29⟩)]
    :: rKEEnv 27
def rNREnv4 : LocalEnv :=
  [("$c5", .base ⟨35⟩), ("$c4", .base ⟨33⟩), ("$c3", .base ⟨31⟩),
   ("$c2", .base ⟨29⟩)] :: rKEEnv 27

/-- After the new-run block: pop it, pop the `k` block, back to the
loop. -/
def rNRAfter : Cont := .seq [] (rKEEnv 27) rBlockTail
def rNRTail1 : Cont :=
  .seq [rNRs3, rNRs4, rNRs5, rNRs6, rNRs7] rNREnv1 rNRAfter
def rNRTail2 : Cont := .seq [rNRs4, rNRs5, rNRs6, rNRs7] rNREnv2 rNRAfter
def rNRTail4 : Cont := .seq [rNRs7] rNREnv4 rNRAfter
/-- The `$c2[0] = s[i]` store target. -/
def rC2Ref : TargetRef := .chain (qC1SliceV 30) [.int 0 .int] [.index]
/-- The extend arm's `runCounts[k-1]` store target. -/
def rCntRef (capC : Nat) : TargetRef :=
  .chain (qRunSliceV 36 capC) [.int 0 .int] [.index]

/-! ### The extend iteration's pieces (parameterized by `ka` and the
symbolic caps) -/

def rExtGuardEnv (ka : Nat) : LocalEnv := [] :: rKEEnv ka
/-- The extend test's `ifK`, with what follows it. -/
def rExtIfK (ka : Nat) : Cont :=
  .ifK rleFunc.rlExtendBlock (.seqn #[]) (rExtGuardEnv ka)
    (.seq [] (rExtGuardEnv ka)
      (.seq [rIfNew] (rKEEnv ka) rBlockTail))
/-- The `runVals[k-1]` read point inside the extend test. -/
def rExtEqK (ka : Nat) (capV : Nat) : Cont :=
  .strictK .indexGet [qRunSliceV 32 capV] [] (rExtGuardEnv ka)
    (.strictK (.eqCmp tU64) [] [.indexGet (.var "s") (.var "i")]
      (rExtGuardEnv ka) (rExtIfK ka))
/-- The second operand's (`s[i]`) read point. -/
def rExtEq2K (n ka : Nat) (a : Int) : Cont :=
  .strictK .indexGet [qSliceS n] [] (rExtGuardEnv ka)
    (.strictK (.eqCmp tU64) [.int a .uint64] [] (rExtGuardEnv ka)
      (rExtIfK ka))

/-! ### The extend arm's store pieces -/

def rExtBEnv (ka : Nat) : LocalEnv := [] :: rExtGuardEnv ka
def rExtStTail (ka : Nat) : Cont :=
  .seq [.seqn #[.assign (.var "extended") (.boolLit true)]] (rExtBEnv ka)
    (.seq [] (rExtGuardEnv ka) (.seq [rIfNew] (rKEEnv ka) rBlockTail))
def rExtRhsK (ka capC : Nat) : Cont :=
  .rhsK .vals [rCntRef capC] [] [] (.seqn #[]) (rExtBEnv ka)
    (rExtStTail ka)
/-- The `runCounts[k-1]` READ point (the `++`'s left operand). -/
def rExtCntReadK (ka capC : Nat) : Cont :=
  .strictK .indexGet [qRunSliceV 36 capC] [] (rExtBEnv ka)
    (.strictK .add [] [.intLit 1 .uint64] (rExtBEnv ka)
      (rExtRhsK ka capC))

/-! ## Continuations — the final copy loop and the epilogue
(parameterized by `A`, the per-`n` address of the `runVals` array;
raw segments instantiate `A` at a literal) -/

def fcTopScope (A : Nat) : Scope :=
  [("runCounts", .base ⟨A + 1⟩), ("runVals", .base ⟨A⟩),
   ("counts", .base ⟨15⟩), ("vals", .base ⟨14⟩), ("pre", .base ⟨11⟩),
   ("s", .base ⟨8⟩), ("$c10", .base ⟨6⟩)]
def fcTopEnv (A : Nat) : LocalEnv := [fcTopScope A, baseEnvQ]
def fcEnv (A : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨A + 3⟩)] :: [("i", .base ⟨A + 2⟩)] :: fcTopEnv A
def fcEnvB (A : Nat) : LocalEnv := [] :: fcEnv A
def fcEnvB2 (A : Nat) : LocalEnv := [] :: fcEnvB A
def fcTailQ (A : Nat) : Cont :=
  .seq [] (fcEnv A)
    (.seq [] ([("i", .base ⟨A + 2⟩)] :: fcTopEnv A)
      (.seq [qS10] (fcTopEnv A) (.frame [] [] [] [] .stop)))
def fcHeadCfg (A : Nat) : Config :=
  .exec (.while (.boolLit true) rleHarnessRFunc.fcBody) (fcEnv A)
    (fcTailQ A)
def fcLoopK (A : Nat) : Cont :=
  .loop (.boolLit true) rleHarnessRFunc.fcBody (fcEnv A) (fcTailQ A)
def fcStoreBlock : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "runVals") (.var "i")))
        (.indexGet (.var "vals") (.var "i"))],
      .seqn #[.assign (.addr (.indexAddr (.ref "runCounts") (.var "i")))
        (.indexGet (.var "counts") (.var "i"))]]
def fcCmpK (A : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (fcEnvB A)
    (.seq [fcStoreBlock] (fcEnvB A) (fcLoopK A))
/-- The `len(vals)` apply point in the final copy loop's test. -/
def fcLenSK (A : Nat) (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] (fcEnvB A)
    (.strictK .lessCmp [.int iv .int] [] (fcEnvB A) (fcCmpK A))
def fcVRef (A : Nat) (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨A⟩)) [.int iv .int] [.index]
def fcCRef (A : Nat) (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨A + 1⟩)) [.int iv .int] [.index]
/-- After the FIRST fc store: the second store's seqn, then out. -/
def fcStTail1 (A : Nat) : Cont :=
  .seq [.seqn #[.assign (.addr (.indexAddr (.ref "runCounts") (.var "i")))
        (.indexGet (.var "counts") (.var "i"))]] (fcEnvB2 A)
    (.seq [] (fcEnvB A) (fcLoopK A))
/-- After the SECOND fc store: out to the loop head. -/
def fcStTail2 (A : Nat) : Cont :=
  .seq [] (fcEnvB2 A) (.seq [] (fcEnvB A) (fcLoopK A))
def fcVRhsK (A : Nat) (iv : Int) : Cont :=
  .rhsK .vals [fcVRef A iv] [] [] (.seqn #[]) (fcEnvB2 A) (fcStTail1 A)
def fcCRhsK (A : Nat) (iv : Int) : Cont :=
  .rhsK .vals [fcCRef A iv] [] [] (.seqn #[]) (fcEnvB2 A) (fcStTail2 A)
/-- The `vals[i]` read point (first fc store's RHS). -/
def fcVReadK (A capV : Nat) (iv : Int) : Cont :=
  .strictK .indexGet [qRunSliceV 32 capV] [] (fcEnvB2 A) (fcVRhsK A iv)
/-- The `counts[i]` read point (second fc store's RHS). -/
def fcCReadK (A capC : Nat) (iv : Int) : Cont :=
  .strictK .indexGet [qRunSliceV 36 capC] [] (fcEnvB2 A) (fcCRhsK A iv)
def qRes0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []
def qRes1Ref : TargetRef := .chain (.addr (.base ⟨3⟩)) [] []
def qRes2Ref : TargetRef := .chain (.addr (.base ⟨4⟩)) [] []
/-- The epilogue's remaining-statement continuation (the spliced
`seqn[5]`'s tail; stores pop back into it). -/
def epK (A : Nat) (ss : List Stmt) : Cont :=
  .seq ss (fcTopEnv A) (.frame [] [] [] [] .stop)
def epA1 : Stmt := .assign (.var "$res1") (.var "runVals")
def epA2 : Stmt := .assign (.var "$res2") (.var "runCounts")
def epA3 : Stmt :=
  .assign (.var "$res3")
    (.convert tU64 (.length (.var "vals") (some (.slice tU64))))
/-- The `k`/`extended` garbage cells the extend iterations leave. -/
def ke1 : Heap := [(.base ⟨37⟩, qint 1), (.base ⟨38⟩, qbool true)]
def ke2 : Heap := ke1 ++ [(.base ⟨39⟩, qint 1), (.base ⟨40⟩, qbool true)]

/-! ## Heap fronts — the harness half (program-generic) -/

def qHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, qu64 nv), (.base ⟨1⟩, qu64 sv), (.base ⟨2⟩, qArr8C zeros8),
   (.base ⟨3⟩, qArr8C zeros8), (.base ⟨4⟩, qArr8C zeros8),
   (.base ⟨5⟩, qu64 0)]

def qHeapC8 (nv sv : Int) : Heap :=
  qHeap0 nv sv ++ [(.base ⟨6⟩, qNilSlice)]

def qHeapMake (nv sv : Int) (n : Nat) : Heap :=
  qHeap0 nv sv ++
    [(.base ⟨6⟩, qHandle n), (.base ⟨7⟩, qBack n (List.replicate n 0))]

def qHeapSu (nv sv : Int) (n : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    Heap :=
  qHeap0 nv sv ++
    [(.base ⟨6⟩, qHandle n), (.base ⟨7⟩, qBack n l), (.base ⟨8⟩, qHandle n),
     (.base ⟨9⟩, qu64 iv), (.base ⟨10⟩, qbool ffv)]

def qHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ffv : Bool) : Heap :=
  qHeapSu nv sv n l siv false ++
    [(.base ⟨11⟩, qArr8C lp), (.base ⟨12⟩, qu64 civ), (.base ⟨13⟩, qbool ffv)]

/-- `vals`/`counts` declared (nil defaults), the call argument being
delivered. -/
def qHeapCall (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  qHeapCp nv sv n l lp siv civ false ++
    [(.base ⟨14⟩, qNilSlice), (.base ⟨15⟩, qNilSlice)]

/-- The `rle` frame entered: `s` bound, both results at their nil
defaults. -/
def qHeapFrame (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  qHeapCall nv sv n l lp siv civ ++
    [(.base ⟨16⟩, qHandle n), (.base ⟨17⟩, qNilSlice), (.base ⟨18⟩, qNilSlice)]

/-- Mid-prologue: `$c0`/`runVals` set up, `$c1` still at its nil
default (its make not yet applied). -/
def qHeapR1Mid (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  qHeapFrame nv sv n l lp siv civ ++
    [(.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
     (.base ⟨21⟩, qESlice 20), (.base ⟨22⟩, qNilSlice)]

/-- The subject's loop-head state BEFORE any iteration: both output
slices empty over empty backings. -/
def qHeapRle0 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (iv : Int) (ffv : Bool) : Heap :=
  qHeapFrame nv sv n l lp siv civ ++
    [(.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
     (.base ⟨21⟩, qESlice 20), (.base ⟨22⟩, qESlice 23),
     (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qESlice 23),
     (.base ⟨25⟩, qint iv), (.base ⟨26⟩, qbool ffv)]

/-- Mid-event: `runVals` (21) already redirected to its spilled
backing, `runCounts` (24) still empty; `i = 0`, flag consumed. -/
def qHeapRle0' (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (capV : Nat) : Heap :=
  qHeapFrame nv sv n l lp siv civ ++
    [(.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
     (.base ⟨21⟩, qRunSlice 32 capV), (.base ⟨22⟩, qESlice 23),
     (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qESlice 23),
     (.base ⟨25⟩, qint 0), (.base ⟨26⟩, qbool false)]

/-- The subject's loop-head state AFTER the `i = 0` new-run event:
both output slices length 1 over their SPILLED backings (symbolic caps
`capV`/`capC`), the run count so far in `cnt`, plus the `ke` suffix of
this-and-later iterations' `k`/`extended` cells (always instantiated
with a LITERAL list downstream, so raw segments keep reducing). -/
def qHeapRun (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (capV capC : Nat) (v cnt : Int) (iv : Int) (ffv : Bool) (ke : Heap) :
    Heap :=
  qHeapFrame nv sv n l lp siv civ ++
    [(.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
     (.base ⟨21⟩, qRunSlice 32 capV), (.base ⟨22⟩, qESlice 23),
     (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qRunSlice 36 capC),
     (.base ⟨25⟩, qint iv), (.base ⟨26⟩, qbool ffv),
     (.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
     (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
     (.base ⟨31⟩, qRunSlice 32 capV), (.base ⟨32⟩, qBackPad capV v),
     (.base ⟨33⟩, qC1Slice 34), (.base ⟨34⟩, qBack1 1),
     (.base ⟨35⟩, qRunSlice 36 capC), (.base ⟨36⟩, qBackPad capC cnt)] ++ ke

/-- The post-`rle`-return front: `vals`/`counts` (14/15) hold the run
slices, the frame cells 16–18 remain, the run cells 19–36 as the
new-run event left them (`cnt` = the final count), plus the `ke`
suffix of extend-iteration `k`/`extended` cells. -/
def qHeapPost (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (capV capC : Nat) (v cnt : Int) (iv : Int) (ke : Heap) : Heap :=
  qHeapCp nv sv n l lp siv civ false ++
    [(.base ⟨14⟩, qRunSlice 32 capV), (.base ⟨15⟩, qRunSlice 36 capC),
     (.base ⟨16⟩, qHandle n), (.base ⟨17⟩, qRunSlice 32 capV),
     (.base ⟨18⟩, qRunSlice 36 capC),
     (.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
     (.base ⟨21⟩, qRunSlice 32 capV), (.base ⟨22⟩, qESlice 23),
     (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qRunSlice 36 capC),
     (.base ⟨25⟩, qint iv), (.base ⟨26⟩, qbool false),
     (.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
     (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
     (.base ⟨31⟩, qRunSlice 32 capV), (.base ⟨32⟩, qBackPad capV v),
     (.base ⟨33⟩, qC1Slice 34), (.base ⟨34⟩, qBack1 1),
     (.base ⟨35⟩, qRunSlice 36 capC), (.base ⟨36⟩, qBackPad capC cnt)]
    ++ ke

/-- The final-copy front: `qHeapPost` plus the two `[8]uint64` arrays
and the loop's counter/flag at the per-`n` base address `A`. -/
def qHeapFC (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (capV capC : Nat) (v cnt : Int) (iv : Int) (ke : Heap)
    (rv rc : List Int) (fiv : Int) (fb : Bool) (A : Nat) : Heap :=
  qHeapPost nv sv n l lp siv civ capV capC v cnt iv ke ++
    [(.base ⟨A⟩, qArr8C rv), (.base ⟨A + 1⟩, qArr8C rc),
     (.base ⟨A + 2⟩, qint fiv), (.base ⟨A + 3⟩, qbool fb)]

/-- The epilogue-phase heap for `n ≥ 1`: like `qHeapFC` but with the
four result cells' contents explicit (`a2`/`a3`/`a4`/`kres`) — the
epilogue's four stores walk them in. -/
def qHeapEp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (capV capC : Nat) (v cnt kres : Int) (iv : Int) (ke : Heap)
    (rv rc : List Int) (fiv : Int) (A : Nat)
    (a2 a3 a4 : List Int) : Heap :=
  [(.base ⟨0⟩, qu64 nv), (.base ⟨1⟩, qu64 sv), (.base ⟨2⟩, qArr8C a2),
   (.base ⟨3⟩, qArr8C a3), (.base ⟨4⟩, qArr8C a4),
   (.base ⟨5⟩, qu64 kres),
   (.base ⟨6⟩, qHandle n), (.base ⟨7⟩, qBack n l), (.base ⟨8⟩, qHandle n),
   (.base ⟨9⟩, qu64 siv), (.base ⟨10⟩, qbool false),
   (.base ⟨11⟩, qArr8C lp), (.base ⟨12⟩, qu64 civ), (.base ⟨13⟩, qbool false),
   (.base ⟨14⟩, qRunSlice 32 capV), (.base ⟨15⟩, qRunSlice 36 capC),
   (.base ⟨16⟩, qHandle n), (.base ⟨17⟩, qRunSlice 32 capV),
   (.base ⟨18⟩, qRunSlice 36 capC),
   (.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
   (.base ⟨21⟩, qRunSlice 32 capV), (.base ⟨22⟩, qESlice 23),
   (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qRunSlice 36 capC),
   (.base ⟨25⟩, qint iv), (.base ⟨26⟩, qbool false),
   (.base ⟨27⟩, qint 0), (.base ⟨28⟩, qbool false),
   (.base ⟨29⟩, qC1Slice 30), (.base ⟨30⟩, qBack1 v),
   (.base ⟨31⟩, qRunSlice 32 capV), (.base ⟨32⟩, qBackPad capV v),
   (.base ⟨33⟩, qC1Slice 34), (.base ⟨34⟩, qBack1 1),
   (.base ⟨35⟩, qRunSlice 36 capC), (.base ⟨36⟩, qBackPad capC cnt)]
  ++ ke ++
    [(.base ⟨A⟩, qArr8C rv), (.base ⟨A + 1⟩, qArr8C rc),
     (.base ⟨A + 2⟩, qint fiv), (.base ⟨A + 3⟩, qbool false)]

/-- The terminal heap for `n ≥ 1`. -/
def qHeapEnd1 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (capV capC : Nat) (v cnt kres : Int) (iv : Int) (ke : Heap)
    (rv rc : List Int) (fiv : Int) (A : Nat) : Heap :=
  qHeapEp nv sv n l lp siv civ capV capC v cnt kres iv ke rv rc fiv A
    lp rv rc

/-- The `n = 0` post-return front: no run event ever fired — both
returned slices are the empty `make`s. -/
def qHeapPost0 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (fiv : Int) (fb : Bool) : Heap :=
  qHeapCp nv sv n l lp siv civ false ++
    [(.base ⟨14⟩, qESlice 20), (.base ⟨15⟩, qESlice 23),
     (.base ⟨16⟩, qHandle n), (.base ⟨17⟩, qESlice 20),
     (.base ⟨18⟩, qESlice 23),
     (.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
     (.base ⟨21⟩, qESlice 20), (.base ⟨22⟩, qESlice 23),
     (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qESlice 23),
     (.base ⟨25⟩, qint 0), (.base ⟨26⟩, qbool false),
     (.base ⟨27⟩, qArr8C zeros8), (.base ⟨28⟩, qArr8C zeros8),
     (.base ⟨29⟩, qint fiv), (.base ⟨30⟩, qbool fb)]

/-- The `n = 0` terminal heap. -/
def qHeapEnd0 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (kres : Int) : Heap :=
  [(.base ⟨0⟩, qu64 nv), (.base ⟨1⟩, qu64 sv), (.base ⟨2⟩, qArr8C lp),
   (.base ⟨3⟩, qArr8C zeros8), (.base ⟨4⟩, qArr8C zeros8),
   (.base ⟨5⟩, qu64 kres),
   (.base ⟨6⟩, qHandle n), (.base ⟨7⟩, qBack n l), (.base ⟨8⟩, qHandle n),
   (.base ⟨9⟩, qu64 siv), (.base ⟨10⟩, qbool false),
   (.base ⟨11⟩, qArr8C lp), (.base ⟨12⟩, qu64 civ), (.base ⟨13⟩, qbool false),
   (.base ⟨14⟩, qESlice 20), (.base ⟨15⟩, qESlice 23),
   (.base ⟨16⟩, qHandle n), (.base ⟨17⟩, qESlice 20),
   (.base ⟨18⟩, qESlice 23),
   (.base ⟨19⟩, qESlice 20), (.base ⟨20⟩, qEmptyBack),
   (.base ⟨21⟩, qESlice 20), (.base ⟨22⟩, qESlice 23),
   (.base ⟨23⟩, qEmptyBack), (.base ⟨24⟩, qESlice 23),
   (.base ⟨25⟩, qint 0), (.base ⟨26⟩, qbool false),
   (.base ⟨27⟩, qArr8C zeros8), (.base ⟨28⟩, qArr8C zeros8),
   (.base ⟨29⟩, qint 0), (.base ⟨30⟩, qbool false)]

/-! ## The entry equation -/

def qProg : ExecState :=
  { types := rleLowered.typeDefs.toList,
    functions := rleLowered.funcs,
    methods := rleLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq q_entry_eq rleLowered rleHarnessRFunc qHSeed qHC0 qProg

/-! ## Heap-lookup facts -/

theorem lookup_suQ (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (qSt σ (qHeapSu nv sv n l iv ffv) na).heap (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [qHeapSu, qHeap0, Heap.lookup]

theorem lookup_cpS_Q (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (qSt σ (qHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [qHeapCp, qHeapSu, qHeap0, Heap.lookup]

theorem lookup_cpPre_Q (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (qSt σ (qHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨11⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [qHeapCp, qHeapSu, qHeap0, Heap.lookup]

end GoLean.Examples.RunLength
