import GoLeanProofs.Examples.TwoSum.Pure
import GoLeanProofs.Examples.TwoSumProgram
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# TwoSum — Machine

The machine-facing layer: the two `Func` records transcribed from the
pinned lowering (each tied to it by an `rfl` pin), the statement
pieces the continuations mention, the address layout, the heap fronts,
and the derived entry equation.

The guardrails wave landed the harness `Func` in the example ROOT in
the mechanically-extracted spelling. It is restated here in the
readable dot-notation form — the wave's recorded allowance ("a proof
lane may restate it readably; the pin must keep holding by `rfl`") —
and `twosumHarnessRFunc_pin` is the check that the restatement says
exactly what the lowering says.

Address layout (probe-measured at `(n, seed, target) = (2, 5, 9)` with
the lane's generic tracer `.tmp/Probe.lean`; every raw segment
downstream re-checks the transcription by `rfl`, so a mis-read layout
fails loudly rather than silently):

```
0 = n            1 = seed         2 = target
3 = $res0 ([8]uint64)   4 = $res1        5 = $res2
6 = $c9 handle   7 = s backing    8 = s
9 = setup i     10 = setup flag
11 = vals ([8]) 12 = copy i      13 = copy flag
14 = i          15 = j                       -- the call's receivers
-- the `twoSum` frame (entered at nextAddr 16) --
16 = s param    17 = target param
18 = its $res0  19 = its $res1
20 = n local    21 = outer i     22 = outer $forFirst  -- nextAddr = 23
-- PER OUTER ITERATION t (the nested loop's signature cost):
23+2t = inner j          24+2t = inner $forFirst
```

**The nested loop allocates.** Each outer iteration declares a fresh
inner `j` and a fresh loop flag, so the heap GROWS by two cells per
outer round and the inner loop's live cells sit at SYMBOLIC addresses
past a growing region of dead cells. The machinery for that is the
abstract dead-region parameter `D` (with `StepKit.DeadFrom` freshness)
threaded through every subject-phase segment: raw `rfl` segments keep
working because every address they must actually RESOLVE lives in the
concrete front BEFORE `D`, and the four inner-cell accesses per
iteration (`$forFirst` read, `j` read/write, exit-test `j` read) go
through conditioned kit steps (`stepFn_var`, `stepFn_store_step`,
`stepFn_init_seq`) instead.

Everything below is PROGRAM-generic: the raw segments are proven over
an abstract `σ` with only `heap`/`nextAddr` pinned, and the single
step that consults the program (the `twoSum` frame entry) is
conditioned through `StepKit.stepFn_call_enter`.
-/

namespace GoLean.Examples.TwoSum

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The two `Func` records, verbatim from the pinned lowering -/

/-- The subject `Func`: the O(n²) double loop with the early
`return i, j` on the first hitting pair. -/
def twoSumFunc : Func :=
  { id := { key := "twoSum" },
    args := #[{ id := "s", typ := .slice tU64 },
              { id := "target", typ := tU64 }],
    results := #[{ id := "$res0", typ := tU64 },
                 { id := "$res1", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "n", typ := tU64 },
                .assign (.var "n")
                  (.convert tU64
                    (.length (.var "s") (some (.slice tU64))))],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) outerBody]],
        tsTailSeqn],
    variadic := false,
    wrapper := false }
  where
    /-- The `return i, j` arm: the first hitting pair ends the run. -/
    foundBlock : Stmt :=
      .block #[]
        #[.seqn #[.assign (.var "$res0") (.var "i"),
                  .assign (.var "$res1") (.var "j"),
                  .returnStmt]]
    /-- The inner test-and-return, wrapped in the loop body's block. -/
    matchBlock : Stmt :=
      .block #[]
        #[.ifThenElse
            (.eqCmp tU64
              (.add (.indexGet (.var "s") (.var "i"))
                    (.indexGet (.var "s") (.var "j")))
              (.var "target"))
            foundBlock (.seqn #[])]
    /-- The desugared inner `for j := i+1; j < n; j++`. -/
    innerBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "j")
              (.add (.var "j") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "j") (.var "n")) (.seqn #[])
            .breakStmt,
          matchBlock]
    /-- The inner loop with its own `j`/flag declarations — allocated
    FRESH each outer round (the layout note above). -/
    innerWrap : Stmt :=
      .block #[]
        #[.block #[]
            #[.seqn #[.initialization { id := "j", typ := tU64 },
                      .assign (.var "j")
                        (.add (.var "i") (.intLit 1 .uint64))],
              .block #[]
                #[.initialization { id := "$forFirst", typ := .bool },
                  .assign (.var "$forFirst") (.boolLit true),
                  .while (.boolLit true) innerBody]]]
    /-- The desugared outer `for i := 0; i < n; i++`. -/
    outerBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i")
              (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[])
            .breakStmt,
          innerWrap]
    /-- The fall-through sentinel: no pair, return `(n, n)`. -/
    tsTailSeqn : Stmt :=
      .seqn #[.assign (.var "$res0") (.var "n"),
              .assign (.var "$res1") (.var "n"),
              .returnStmt]

/-- The harness `Func`, restated readably from the guardrails wave's
mechanically-extracted spelling; `twosumHarnessRFunc_pin` ties it to
the lowering by `rfl`. -/
def twosumHarnessRFunc : Func :=
  { id := { key := "twosum_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 },
              { id := "target", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := tU64 },
                 { id := "$res2", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c9", typ := .slice tU64 },
                .makeSlice (.var "$c9") tU64 (.var "n") none],
        .seqn #[.initialization { id := "s", typ := .slice tU64 },
                .assign (.var "s") (.var "$c9")],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) shBody]],
        .seqn #[.initialization { id := "vals", typ := .array 8 tU64 }],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .seqn #[.initialization { id := "i", typ := tU64 },
                .initialization { id := "j", typ := tU64 },
                .call #[.var "i", .var "j"] ⟨"twoSum"⟩
                  #[.var "s", .var "target"]],
        .seqn #[.assign (.var "$res0") (.var "vals"),
                .assign (.var "$res1") (.var "i"),
                .assign (.var "$res2") (.var "j"),
                .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The setup loop's body: `s[i] = seed + i`. -/
    shBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[])
            .breakStmt,
          .block #[]
            #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
                (.add (.var "seed") (.var "i"))]]]
    /-- The copy loop's body: `vals[i] = s[i]`. -/
    cpBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[])
            .breakStmt,
          .block #[]
            #[.seqn #[.assign (.addr (.indexAddr (.ref "vals") (.var "i")))
                (.indexGet (.var "s") (.var "i"))]]]

/-- The subject lowering pin. -/
theorem twoSum_pin :
    findFunctionIn? twosumLowered.funcs ⟨"twoSum"⟩ = some twoSumFunc := rfl

/-- The harness lowering pin: the readable restatement IS the
frontend's lowering. -/
theorem twosumHarnessRFunc_pin :
    findFunctionIn? twosumLowered.funcs ⟨"twosum_harness_r"⟩
      = some twosumHarnessRFunc := rfl

/-! ## The S3 statement adapter -/

/-- The returned fixed-cap array, zero-padded past the live prefix. -/
def tsArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-! ## The PROGRAM-generic state form -/

abbrev tSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## Cells and handles at the twosum layout -/

abbrev tsu64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev tsbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev tsSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨7⟩), 0, n, n⟩
abbrev tsHandle (n : Nat) : HeapCell := ⟨some (.slice tU64), tsSliceS n⟩
abbrev tsBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev tsArr8c (l : List Int) : HeapCell :=
  ⟨some (.array 8 tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev tsNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩

/-! ## Statement pieces — the harness half -/

def tS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice tU64 },
          .assign (.var "s") (.var "$c9")]
def tS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) twosumHarnessRFunc.shBody]]
def tS4 : Stmt :=
  .seqn #[.initialization { id := "vals", typ := .array 8 tU64 }]
def tS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) twosumHarnessRFunc.cpBody]]
def tS6 : Stmt :=
  .seqn #[.initialization { id := "i", typ := tU64 },
          .initialization { id := "j", typ := tU64 },
          .call #[.var "i", .var "j"] ⟨"twoSum"⟩
            #[.var "s", .var "target"]]
def tS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "vals"),
          .assign (.var "$res1") (.var "i"),
          .assign (.var "$res2") (.var "j"),
          .returnStmt]

/-! ## Environments — the harness half -/

def baseEnvT : Scope :=
  [("$res2", .base ⟨5⟩), ("$res1", .base ⟨4⟩), ("$res0", .base ⟨3⟩),
   ("target", .base ⟨2⟩), ("seed", .base ⟨1⟩), ("n", .base ⟨0⟩)]
def envC9T : LocalEnv := [[("$c9", .base ⟨6⟩)], baseEnvT]
def sScopeT : Scope := [("s", .base ⟨8⟩), ("$c9", .base ⟨6⟩)]
def valsScopeT : Scope :=
  [("vals", .base ⟨11⟩), ("s", .base ⟨8⟩), ("$c9", .base ⟨6⟩)]
def callScopeT : Scope :=
  [("j", .base ⟨15⟩), ("i", .base ⟨14⟩), ("vals", .base ⟨11⟩),
   ("s", .base ⟨8⟩), ("$c9", .base ⟨6⟩)]
def callEnvT : LocalEnv := [callScopeT, baseEnvT]

def suEnvT : LocalEnv :=
  [[("$forFirst", .base ⟨10⟩)], [("i", .base ⟨9⟩)], sScopeT, baseEnvT]
def suEnvT2 : LocalEnv := [] :: [] :: suEnvT
def cpEnvT : LocalEnv :=
  [[("$forFirst", .base ⟨13⟩)], [("i", .base ⟨12⟩)], valsScopeT, baseEnvT]
def cpEnvT2 : LocalEnv := [] :: [] :: cpEnvT

/-! ## Continuations — the harness half -/

def tTailAfterSetup : Cont :=
  .seq [tS4, tS5, tS6, tS7] [sScopeT, baseEnvT] (.frame [] [] [] [] .stop)
def suHeadTailT : Cont :=
  .seq [] suEnvT
    (.seq [] [[("i", .base ⟨9⟩)], sScopeT, baseEnvT] tTailAfterSetup)
def suHeadCfgT : Config :=
  .exec (.while (.boolLit true) twosumHarnessRFunc.shBody) suEnvT suHeadTailT
def suLoopKT : Cont :=
  .loop (.boolLit true) twosumHarnessRFunc.shBody suEnvT suHeadTailT
def suStoreBlockT : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.var "i"))]]
def suCmpKT : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvT)
    (.seq [suStoreBlockT] ([] :: suEnvT) suLoopKT)
def suRefT (n : Nat) (iv : Int) : TargetRef :=
  .chain (tsSliceS n) [.int iv .uint64] [.index]
def suStTailT : Cont :=
  .seq [] suEnvT2 (.seq [] ([] :: suEnvT) suLoopKT)

def tTailAfterCopy : Cont :=
  .seq [tS6, tS7] [valsScopeT, baseEnvT] (.frame [] [] [] [] .stop)
def cpHeadTailT : Cont :=
  .seq [] cpEnvT
    (.seq [] [[("i", .base ⟨12⟩)], valsScopeT, baseEnvT] tTailAfterCopy)
def cpHeadCfgT : Config :=
  .exec (.while (.boolLit true) twosumHarnessRFunc.cpBody) cpEnvT cpHeadTailT
def cpLoopKT : Cont :=
  .loop (.boolLit true) twosumHarnessRFunc.cpBody cpEnvT cpHeadTailT
def cpStoreBlockT : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "vals") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpKT : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvT)
    (.seq [cpStoreBlockT] ([] :: cpEnvT) cpLoopKT)
def cpRefT (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨11⟩)) [.int iv .uint64] [.index]
def cpStTailT : Cont :=
  .seq [] cpEnvT2 (.seq [] ([] :: cpEnvT) cpLoopKT)
def cpRhsKT (iv : Int) : Cont :=
  .rhsK .vals [cpRefT iv] [] [] (.seqn #[]) cpEnvT2 cpStTailT

/-! ## Environments and continuations — the `twoSum` frame -/

def fScopeT : Scope :=
  [("$res1", .base ⟨19⟩), ("$res0", .base ⟨18⟩), ("target", .base ⟨17⟩),
   ("s", .base ⟨16⟩)]
def tFrameEnv : LocalEnv := [fScopeT]
def envNT : LocalEnv := [[("n", .base ⟨20⟩)], fScopeT]
def outEnvT : LocalEnv :=
  [[("$forFirst", .base ⟨22⟩)], [("i", .base ⟨21⟩)], [("n", .base ⟨20⟩)],
   fScopeT]
def outEnvCT : LocalEnv := [] :: outEnvT
/-- The env at the inner `j` declaration: the if-branch scope, the
body block's, and the inner wrap's — three empties over the outer
env. -/
def bodyEnvT : LocalEnv := [] :: [] :: [] :: outEnvT
def jEnvT (ja : Nat) : LocalEnv :=
  [("j", .base ⟨ja⟩)] :: [] :: [] :: outEnvT
def inEnvT (ja : Nat) : LocalEnv :=
  [("$forFirst", .base ⟨ja + 1⟩)] :: jEnvT ja
def inEnvCT (ja : Nat) : LocalEnv := [] :: inEnvT ja
def inEnvB2T (ja : Nat) : LocalEnv := [] :: [] :: inEnvT ja

def tShapes : List (TargetShape × List Expr) :=
  [(.chain [], [.ref "i"]), (.chain [], [.ref "j"])]
def tAfterCall : Cont :=
  .seq [tS7] callEnvT (.frame [] [] [] [] .stop)
def tCallArgsK (n : Nat) : Cont :=
  .callArgsK ⟨"twoSum"⟩ tShapes [tsSliceS n] [] callEnvT tAfterCall
def tFrameK : Cont :=
  .frame tShapes callEnvT [.base ⟨18⟩, .base ⟨19⟩] [] tAfterCall false

/-- The continuation under the subject's tail sentinel. -/
def tTailK : Cont := .seq [twoSumFunc.tsTailSeqn] envNT tFrameK
def tOutHeadTail : Cont :=
  .seq [] outEnvT
    (.seq [] [[("i", .base ⟨21⟩)], [("n", .base ⟨20⟩)], fScopeT] tTailK)
def tOutHeadCfg : Config :=
  .exec (.while (.boolLit true) twoSumFunc.outerBody) outEnvT tOutHeadTail
def tOutLoopK : Cont :=
  .loop (.boolLit true) twoSumFunc.outerBody outEnvT tOutHeadTail
def tOutCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt outEnvCT
    (.seq [twoSumFunc.innerWrap] outEnvCT tOutLoopK)

/-- The subject's outer-loop statement (its body's second element). -/
def tSOuter : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) twoSumFunc.outerBody]]
/-- The prologue's continuation below the `n :=` store. -/
def tProTail : Cont :=
  .seq [tSOuter, twoSumFunc.tsTailSeqn] envNT tFrameK
/-- The `uint64(…)` conversion's apply point over the `n :=` store. -/
def tConvK : Cont :=
  .strictK (.convert tU64) [] [] envNT
    (.rhsK .vals [.chain (.addr (.base ⟨20⟩)) [] []] [] [] (.seqn #[])
      envNT tProTail)
/-- The `n := uint64(len(s))` apply point: the length op under the
conversion's strict frame, under the store into cell 20. -/
def tLenKP : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] envNT tConvK

/-- The tail below the inner-wrap blocks (fixed across iterations). -/
def tJSeqTail : Cont :=
  .seq [] ([] :: [] :: outEnvT) (.seq [] outEnvCT tOutLoopK)

/-- The inner `j := i + 1` statement (the init's sibling). -/
def tJAssign : Stmt :=
  .assign (.var "j") (.add (.var "i") (.intLit 1 .uint64))
/-- The inner loop block (`$forFirst` + the inner `while`). -/
def tInnerLoopBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) twoSumFunc.innerBody]

def tInHeadTail (ja : Nat) : Cont :=
  .seq [] (inEnvT ja) (.seq [] (jEnvT ja) tJSeqTail)
def tInHeadCfg (ja : Nat) : Config :=
  .exec (.while (.boolLit true) twoSumFunc.innerBody) (inEnvT ja)
    (tInHeadTail ja)
def tInLoopK (ja : Nat) : Cont :=
  .loop (.boolLit true) twoSumFunc.innerBody (inEnvT ja) (tInHeadTail ja)
def tInCmpK (ja : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt (inEnvCT ja)
    (.seq [twoSumFunc.matchBlock] (inEnvCT ja) (tInLoopK ja))
def tInIfK (ja : Nat) : Cont :=
  .ifK twoSumFunc.foundBlock (.seqn #[]) (inEnvB2T ja)
    (.seq [] (inEnvB2T ja) (.seq [] (inEnvCT ja) (tInLoopK ja)))

/-! ### The inner dispatch's conditioned points (probe-measured at
steps 540/546/551/559 of the `(2, 5, 9)` trace) -/

/-- The inner exit test statement. -/
def tIfJN : Stmt :=
  .ifThenElse (.lessCmp (.var "j") (.var "n")) (.seqn #[]) .breakStmt
/-- The loop body's remaining statements after the first-pass `if`. -/
def tInBodyTail (ja : Nat) : Cont :=
  .seq [.seqn #[], tIfJN, twoSumFunc.matchBlock] (inEnvCT ja)
    (tInLoopK ja)
/-- The first-pass dispatch `if` inside the inner loop. -/
def tFFIfK (ja : Nat) : Cont :=
  .ifK (.assign (.var "$forFirst") (.boolLit false))
    (.assign (.var "j") (.add (.var "j") (.intLit 1 .uint64)))
    (inEnvCT ja) (tInBodyTail ja)
def tJRef (ja : Nat) : TargetRef := .chain (.addr (.base ⟨ja⟩)) [] []
def tFFRef (ja : Nat) : TargetRef :=
  .chain (.addr (.base ⟨ja + 1⟩)) [] []
/-- The `j++` add's apply chain over the store into the live `j`. -/
def tJIncrK (ja : Nat) : Cont :=
  .strictK .add [] [.intLit 1 .uint64] (inEnvCT ja)
    (.rhsK .vals [tJRef ja] [] [] (.seqn #[]) (inEnvCT ja)
      (tInBodyTail ja))
/-- The `$forFirst := false` store's continuation (first pass). -/
def tFFStoreTail (ja : Nat) : Cont :=
  .rhsK .vals [tFFRef ja] [] [] (.seqn #[]) (inEnvCT ja)
    (tInBodyTail ja)
/-- The inner exit test's `<` frame. -/
def tJTestK (ja : Nat) : Cont :=
  .strictK .lessCmp [] [.var "n"] (inEnvCT ja) (tInCmpK ja)

/-- The FIRST index read's apply point (`s[i]`), the add and the
comparison pending. -/
def tIdx1K (n ja : Nat) : Cont :=
  .strictK .indexGet [tsSliceS n] [] (inEnvB2T ja)
    (.strictK .add [] [.indexGet (.var "s") (.var "j")] (inEnvB2T ja)
      (.strictK (.eqCmp tU64) [] [.var "target"] (inEnvB2T ja)
        (tInIfK ja)))
/-- The SECOND index read's apply point (`s[j]`), the first value
banked. -/
def tIdx2K (n ja : Nat) (a : Int) : Cont :=
  .strictK .indexGet [tsSliceS n] [] (inEnvB2T ja)
    (.strictK .add [.int a .uint64] [] (inEnvB2T ja)
      (.strictK (.eqCmp tU64) [] [.var "target"] (inEnvB2T ja)
        (tInIfK ja)))

/-! ## Heap fronts (program-generic)

`nv sv tv` are the three argument cells; `mv` is the subject's local
`n` copy (cell 20); `iv` the outer counter. The subject-phase fronts
stop at cell 22 — the growing dead region and the live inner cells are
appended as explicit list arguments by the segments that use them. -/

def zeros8 : List Int := List.replicate 8 0

def tsHeap0 (nv sv tv : Int) : Heap :=
  [(.base ⟨0⟩, tsu64 nv), (.base ⟨1⟩, tsu64 sv), (.base ⟨2⟩, tsu64 tv),
   (.base ⟨3⟩, tsArr8c zeros8), (.base ⟨4⟩, tsu64 0), (.base ⟨5⟩, tsu64 0)]

def tsHeapC9 (nv sv tv : Int) : Heap :=
  tsHeap0 nv sv tv ++ [(.base ⟨6⟩, tsNilSlice)]

def tsHeapMake (nv sv tv : Int) (n : Nat) : Heap :=
  tsHeap0 nv sv tv ++
    [(.base ⟨6⟩, tsHandle n), (.base ⟨7⟩, tsBack n (List.replicate n 0))]

def tsHeapSu (nv sv tv : Int) (n : Nat) (l : List Int) (iv : Int)
    (ffv : Bool) : Heap :=
  tsHeap0 nv sv tv ++
    [(.base ⟨6⟩, tsHandle n), (.base ⟨7⟩, tsBack n l),
     (.base ⟨8⟩, tsHandle n), (.base ⟨9⟩, tsu64 iv),
     (.base ⟨10⟩, tsbool ffv)]

def tsHeapCp (nv sv tv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ffv : Bool) : Heap :=
  tsHeapSu nv sv tv n l siv false ++
    [(.base ⟨11⟩, tsArr8c lp), (.base ⟨12⟩, tsu64 civ),
     (.base ⟨13⟩, tsbool ffv)]

def tsHeapCall (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ : Int) : Heap :=
  tsHeapCp nv sv tv n l lp siv civ false ++
    [(.base ⟨14⟩, tsu64 0), (.base ⟨15⟩, tsu64 0)]

/-- The subject frame: parameters bound (`tvp` is the target cell's
value — the frame entry writes it normalize-wrapped; the composer
rewrites it to `tv` once), results at their defaults. -/
def tsHeapFrame (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp : Int) : Heap :=
  tsHeapCall nv sv tv n l lp siv civ ++
    [(.base ⟨16⟩, tsHandle n), (.base ⟨17⟩, tsu64 tvp),
     (.base ⟨18⟩, tsu64 0), (.base ⟨19⟩, tsu64 0)]

/-- Mid-prologue: the subject's `n` declared (still at default `0`). -/
def tsHeapPro (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp : Int) : Heap :=
  tsHeapFrame nv sv tv n l lp siv civ tvp ++ [(.base ⟨20⟩, tsu64 0)]

/-- The outer-loop front: everything through cell 22. `mv` is the
subject's `n` copy, `iv` the outer counter. -/
def tsHeapOut (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (ffv : Bool) : Heap :=
  tsHeapFrame nv sv tv n l lp siv civ tvp ++
    [(.base ⟨20⟩, tsu64 mv), (.base ⟨21⟩, tsu64 iv),
     (.base ⟨22⟩, tsbool ffv)]

/-- The live inner pair at symbolic addresses `ja`, `ja+1`. -/
def tsLive (ja : Nat) (jv : Int) (ffv : Bool) : Heap :=
  [(.base ⟨ja⟩, tsu64 jv), (.base ⟨ja + 1⟩, tsbool ffv)]

/-- The inner-phase heap: the concrete front, the abstract dead
region, the live inner pair. -/
def tsHeapIn (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv : Int)
    (ffv : Bool) : Heap :=
  tsHeapOut nv sv tv n l lp siv civ tvp mv iv false
    ++ (D ++ tsLive ja jv ffv)

/-- The subject-phase front with the RESULT cells delivered (`riv` in
18, `rjv` in 19) — the state right after the subject's `return`, both
exits. -/
def tsHeapRet (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv riv rjv : Int) : Heap :=
  tsHeapCall nv sv tv n l lp siv civ ++
    [(.base ⟨16⟩, tsHandle n), (.base ⟨17⟩, tsu64 tvp),
     (.base ⟨18⟩, tsu64 riv), (.base ⟨19⟩, tsu64 rjv),
     (.base ⟨20⟩, tsu64 mv), (.base ⟨21⟩, tsu64 iv),
     (.base ⟨22⟩, tsbool false)]

/-- The epilogue front: the harness receivers (14/15) delivered, the
`$res0 = vals` array store PENDING. Cells 0…22 fully explicit. -/
def tsHeapEpi (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv riv rjv hiv hjv : Int) : Heap :=
  tsHeapCp nv sv tv n l lp siv civ false ++
    [(.base ⟨14⟩, tsu64 hiv), (.base ⟨15⟩, tsu64 hjv),
     (.base ⟨16⟩, tsHandle n), (.base ⟨17⟩, tsu64 tvp),
     (.base ⟨18⟩, tsu64 riv), (.base ⟨19⟩, tsu64 rjv),
     (.base ⟨20⟩, tsu64 mv), (.base ⟨21⟩, tsu64 iv),
     (.base ⟨22⟩, tsbool false)]

/-- The terminal front: results in 3/4/5, everything else as the run
left it. The readback reads cells 3, 4, 5 from HERE — everything past
cell 22 (the dead region and the last live pair) is junk the theorem
existentially forgets. -/
def tsHeapEnd (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv riv rjv hiv hjv r1v r2v : Int) : Heap :=
  [(.base ⟨0⟩, tsu64 nv), (.base ⟨1⟩, tsu64 sv), (.base ⟨2⟩, tsu64 tv),
   (.base ⟨3⟩, tsArr8c lp), (.base ⟨4⟩, tsu64 r1v),
   (.base ⟨5⟩, tsu64 r2v),
   (.base ⟨6⟩, tsHandle n), (.base ⟨7⟩, tsBack n l),
   (.base ⟨8⟩, tsHandle n), (.base ⟨9⟩, tsu64 siv),
   (.base ⟨10⟩, tsbool false),
   (.base ⟨11⟩, tsArr8c lp), (.base ⟨12⟩, tsu64 civ),
   (.base ⟨13⟩, tsbool false),
   (.base ⟨14⟩, tsu64 hiv), (.base ⟨15⟩, tsu64 hjv),
   (.base ⟨16⟩, tsHandle n), (.base ⟨17⟩, tsu64 tvp),
   (.base ⟨18⟩, tsu64 riv), (.base ⟨19⟩, tsu64 rjv),
   (.base ⟨20⟩, tsu64 mv), (.base ⟨21⟩, tsu64 iv),
   (.base ⟨22⟩, tsbool false)]

/-- The epilogue continuation after the pending `$res0 = vals` store. -/
def tEpiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "i"),
        .assign (.var "$res2") (.var "j"), .returnStmt] callEnvT
    (.frame [] [] [] [] .stop)
def tRes0Ref : TargetRef := .chain (.addr (.base ⟨3⟩)) [] []

/-! ## The entry equation -/

def tProg : ExecState :=
  { types := twosumLowered.typeDefs.toList,
    functions := twosumLowered.funcs,
    methods := twosumLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq tH_entry_eq twosumLowered twosumHarnessRFunc tHSeed tHC0 tProg

/-! ## Heap-lookup facts -/

theorem lookup_suT (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (tSt σ (tsHeapSu nv sv tv n l iv ffv) na).heap (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [tsHeapSu, tsHeap0, Heap.lookup]

theorem lookup_cpS_T (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (tSt σ (tsHeapCp nv sv tv n l lp siv civ ffv) na).heap
        (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [tsHeapCp, tsHeapSu, tsHeap0, Heap.lookup]

theorem lookup_cpVals_T (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (tSt σ (tsHeapCp nv sv tv n l lp siv civ ffv) na).heap
        (.base ⟨11⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [tsHeapCp, tsHeapSu, tsHeap0, Heap.lookup]

/-- The backing under the FULL inner-phase heap: the read resolves in
the concrete front, past nothing symbolic. -/
theorem lookup_inS_T (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat)
    (jv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup
        (tSt σ (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
          na).heap (.base ⟨7⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [tsHeapIn, tsHeapOut, tsHeapFrame, tsHeapCall, tsHeapCp, tsHeapSu,
    tsHeap0, Heap.lookup]

theorem lookup_epiVals_T (σ : ExecState) (nv sv tv : Int) (n : Nat)
    (l lp : List Int) (siv civ tvp mv iv riv rjv hiv hjv : Int)
    (na : Nat) :
    Heap.lookup
        (tSt σ (tsHeapEpi nv sv tv n l lp siv civ tvp mv iv riv rjv
          hiv hjv) na).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
  simp [tsHeapEpi, tsHeapCp, tsHeapSu, tsHeap0, Heap.lookup]

/-! ### The live-cell facts through the abstract dead region

Every inner-loop access to `j`/`$forFirst` resolves through these:
the concrete front (cells 0…22) misses, the dead region misses by
`DeadFrom`, the live pair answers.

-- GAP-WITNESS (see docs/gallery-campaign-log/g1.md § KIT-GAP LIST (twosum), [lane B] KIT GAP —
-- growing-heap loop support): the front-none rewrite chain and the
-- live-cell lookup/set family below are the per-example price of a
-- loop body that declares variables; the shape wanted is a kit-level
-- `lookup_front_none` discharge + `storeTarget_live`. -/

/-- The front misses any address ≥ 23. -/
theorem lookup_out_none (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (ffv : Bool) {x : Nat} (hx : 23 ≤ x) :
    Heap.lookup (tsHeapOut nv sv tv n l lp siv civ tvp mv iv ffv)
      (.base ⟨x⟩) = none := by
  simp only [tsHeapOut, tsHeapFrame, tsHeapCall, tsHeapCp, tsHeapSu,
    tsHeap0, List.append_assoc, List.cons_append, List.nil_append]
  rw [lookup_cons_ne (base_beq_false (show 0 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 1 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 2 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 3 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 4 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 5 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 6 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 7 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 8 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 9 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 10 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 11 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 12 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 13 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 14 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 15 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 16 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 17 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 18 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 19 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 20 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 21 ≠ x by omega)),
    lookup_cons_ne (base_beq_false (show 22 ≠ x by omega))]
  rfl

/-- Reading the live `j` cell through the dead region. -/
theorem lookup_liveJ (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv : Int)
    (ffv : Bool) (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.lookup (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
      (.base ⟨ja⟩) = some (tsu64 jv) := by
  rw [tsHeapIn,
    lookup_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv
      iv false hja),
    lookup_append_right (hD ja (Nat.le_refl _))]
  simp [tsLive, Heap.lookup]

/-- Reading the live `$forFirst` cell through the dead region. -/
theorem lookup_liveFF (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv : Int)
    (ffv : Bool) (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.lookup (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
      (.base ⟨ja + 1⟩) = some (tsbool ffv) := by
  rw [tsHeapIn,
    lookup_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv
      iv false (by omega)),
    lookup_append_right (hD (ja + 1) (by omega))]
  simp [tsLive, Heap.lookup, lookup_cons_ne (base_beq_false
    (show ja ≠ ja + 1 by omega))]

/-- Writing the live `j` cell through the dead region. -/
theorem set_liveJ (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv jv' : Int)
    (ffv : Bool) (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.set (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
      (.base ⟨ja⟩) (tsu64 jv')
      = tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv' ffv := by
  rw [tsHeapIn, tsHeapIn,
    set_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv iv
      false hja),
    set_append_right (hD ja (Nat.le_refl _))]
  simp [tsLive, Heap.set]

/-- Writing the live `$forFirst` cell through the dead region. -/
theorem set_liveFF (nv sv tv : Int) (n : Nat) (l lp : List Int)
    (siv civ tvp mv iv : Int) (D : Heap) (ja : Nat) (jv : Int)
    (ffv ffv' : Bool) (hja : 23 ≤ ja) (hD : DeadFrom D ja) :
    Heap.set (tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv)
      (.base ⟨ja + 1⟩) (tsbool ffv')
      = tsHeapIn nv sv tv n l lp siv civ tvp mv iv D ja jv ffv' := by
  rw [tsHeapIn, tsHeapIn,
    set_append_right (lookup_out_none nv sv tv n l lp siv civ tvp mv iv
      false (by omega)),
    set_append_right (hD (ja + 1) (by omega))]
  simp [tsLive, Heap.set, base_beq_false (show ja ≠ ja + 1 by omega)]

end GoLean.Examples.TwoSum
