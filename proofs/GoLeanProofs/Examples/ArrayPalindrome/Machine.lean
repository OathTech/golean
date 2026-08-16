import GoLeanProofs.Examples.ArrayPalindrome.Pure
import GoLeanProofs.Examples.ArrayPalindromeProgram
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# ArrayPalindrome — Machine

The machine-facing layer: the two `Func` records transcribed from the
pinned lowering (each tied to it by an `rfl` pin), the statement pieces
the continuations mention, the address layout, the heap fronts, and the
derived entry equation.

The guardrails wave landed the harness `Func` in the example ROOT in
the mechanically-extracted spelling. It is restated here in the
readable dot-notation form — the wave's recorded allowance ("a proof
lane may restate it readably; the pin must keep holding by `rfl`") —
and `palinHarnessRFunc_pin` is the check that the restatement says exactly
what the lowering says.

Address layout (probe-measured at `(n, seed) = (4, 7)` with the lane's
generic tracer `.tmp/Probe.lean`; every raw segment downstream
re-checks the transcription by `rfl`, so a mis-read layout fails
loudly rather than silently):

```
0 = n            1 = seed         2 = $res0 ([8]uint64)   3 = $res1
4 = $c8 handle   5 = s backing    6 = s
7 = setup i      8 = setup flag
9 = pre ([8])   10 = copy i      11 = copy flag
12 = v
-- the `isPalindrome` frame (entered at nextAddr 13) --
13 = s param    14 = its $res0
15 = i          16 = j           17 = $forFirst   -- nextAddr = 18
```

Everything below is PROGRAM-generic: the raw segments are proven over
an abstract `σ` with only `heap`/`nextAddr` pinned, and the single step
that consults the program (the `isPalindrome` frame entry) is
conditioned through `StepKit.stepFn_call_enter`. The pinned program is
unfolded exactly TWICE in this example — the two lowering pins and the
one `enterFrame` discharge.
-/

namespace GoLean.Examples.ArrayPalindrome

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The two `Func` records, verbatim from the pinned lowering -/

/-- The subject `Func`: the two-index inward walk, with the early
`return 0` on the first mismatched pair. -/
def isPalindromeFunc : Func :=
  { id := { key := "isPalindrome" },
    args := #[{ id := "s", typ := .slice tU64 }],
    results := #[{ id := "$res0", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "i", typ := .int .int },
                .assign (.var "i") (.intLit 0 .int)],
        .seqn #[.initialization { id := "j", typ := .int .int },
                .assign (.var "j")
                  (.sub (.length (.var "s") (some (.slice tU64)))
                        (.intLit 1 .int))],
        .block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) palWhileBody],
        palTailSeqn],
    variadic := false,
    wrapper := false }
  where
    /-- The `return 0` arm: the first mismatched pair ends the run. -/
    palRet0Block : Stmt :=
      .block #[]
        #[.seqn #[.assign (.var "$res0") (.intLit 0 .uint64), .returnStmt]]
    /-- The loop body proper: compare `s[i]` with `s[j]`, then step both
    indices inward. -/
    palBodyBlock : Stmt :=
      .block #[]
        #[.ifThenElse
            (.neqCmp tU64 (.indexGet (.var "s") (.var "i"))
                          (.indexGet (.var "s") (.var "j")))
            palRet0Block (.seqn #[]),
          .assign (.var "i") (.add (.var "i") (.intLit 1 .int)),
          .assign (.var "j") (.sub (.var "j") (.intLit 1 .int))]
    /-- The desugared `for i < j { … }`: the first-pass flag, the
    (EMPTY) post statement — both index steps live in the body — the
    exit test, then the body. -/
    palWhileBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.seqn #[]),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "j")) (.seqn #[]) .breakStmt,
          palBodyBlock]
    /-- The fall-through verdict: the walk met in the middle. -/
    palTailSeqn : Stmt :=
      .seqn #[.assign (.var "$res0") (.intLit 1 .uint64), .returnStmt]

/-- The harness `Func`, restated readably from the guardrails wave's
mechanically-extracted spelling; `palinHarnessRFunc_pin` ties it to the
lowering by `rfl`. -/
def palinHarnessRFunc : Func :=
  { id := { key := "palin_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c8", typ := .slice tU64 },
                .makeSlice (.var "$c8") tU64 (.var "n") none],
        .seqn #[.initialization { id := "s", typ := .slice tU64 },
                .assign (.var "s") (.var "$c8")],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) shBody]],
        .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }],
        .block #[]
          #[.seqn #[.initialization { id := "i", typ := tU64 },
                    .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .seqn #[.initialization { id := "v", typ := tU64 },
                .call #[.var "v"] ⟨"isPalindrome"⟩ #[.var "s"]],
        .seqn #[.assign (.var "$res0") (.var "pre"),
                .assign (.var "$res1") (.var "v"),
                .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The setup loop's body: `s[i] = seed + i%2`. -/
    shBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
                (.add (.var "seed") (.mod (.var "i") (.intLit 2 .uint64)))]]]
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

/-- The subject lowering pin. -/
theorem palin_pin :
    findFunctionIn? palinLowered.funcs ⟨"isPalindrome"⟩
      = some isPalindromeFunc := rfl

/-- The harness lowering pin: the readable restatement IS the
frontend's lowering. -/
theorem palinHarnessRFunc_pin :
    findFunctionIn? palinLowered.funcs ⟨"palin_harness_r"⟩
      = some palinHarnessRFunc := rfl

/-! ## The S3 statement adapter

`palArr8` is STATEMENT vocabulary: what "the returned `[palinCapN]uint64`"
means as a `GoValue`. Under the §11 closure rules it is never a
proof-kit definition — it belongs to the example. -/

/-- The returned fixed-cap array, zero-padded past the live prefix. -/
def palArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-! ## The PROGRAM-generic state form -/

abbrev pSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## Cells and handles at the palin layout -/

abbrev pu64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev pint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev pbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev pSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨5⟩), 0, n, n⟩
abbrev pHandle (n : Nat) : HeapCell := ⟨some (.slice tU64), pSliceS n⟩
abbrev pBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev pArr8 (l : List Int) : HeapCell :=
  ⟨some (.array 8 tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev pNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩

/-! ## Statement pieces -/

def pS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice tU64 },
          .assign (.var "s") (.var "$c8")]
def pS3 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) palinHarnessRFunc.shBody]]
def pS4 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }]
def pS5 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) palinHarnessRFunc.cpBody]]
def pS6 : Stmt :=
  .seqn #[.initialization { id := "v", typ := tU64 },
          .call #[.var "v"] ⟨"isPalindrome"⟩ #[.var "s"]]
def pS7 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "v"),
          .returnStmt]

/-! ## Environments -/

def baseEnvP : Scope :=
  [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩),
   ("n", .base ⟨0⟩)]
def envC8P : LocalEnv := [[("$c8", .base ⟨4⟩)], baseEnvP]
def sScopeP : Scope := [("s", .base ⟨6⟩), ("$c8", .base ⟨4⟩)]
def preScopeP : Scope :=
  [("pre", .base ⟨9⟩), ("s", .base ⟨6⟩), ("$c8", .base ⟨4⟩)]
def callScopeP : Scope :=
  [("v", .base ⟨12⟩), ("pre", .base ⟨9⟩), ("s", .base ⟨6⟩),
   ("$c8", .base ⟨4⟩)]
def callEnvP : LocalEnv := [callScopeP, baseEnvP]

def suEnvP : LocalEnv :=
  [[("$forFirst", .base ⟨8⟩)], [("i", .base ⟨7⟩)], sScopeP, baseEnvP]
def suEnvP2 : LocalEnv := [] :: [] :: suEnvP
def cpEnvP : LocalEnv :=
  [[("$forFirst", .base ⟨11⟩)], [("i", .base ⟨10⟩)], preScopeP, baseEnvP]
def cpEnvP2 : LocalEnv := [] :: [] :: cpEnvP

/-! ## Continuations — the harness half -/

def pTailAfterSetup : Cont :=
  .seq [pS4, pS5, pS6, pS7] [sScopeP, baseEnvP] (.frame [] [] [] [] .stop)
def suHeadTailP : Cont :=
  .seq [] suEnvP
    (.seq [] [[("i", .base ⟨7⟩)], sScopeP, baseEnvP] pTailAfterSetup)
def suHeadCfgP : Config :=
  .exec (.while (.boolLit true) palinHarnessRFunc.shBody) suEnvP suHeadTailP
def suLoopKP : Cont :=
  .loop (.boolLit true) palinHarnessRFunc.shBody suEnvP suHeadTailP
def suStoreBlockP : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.add (.var "seed") (.mod (.var "i") (.intLit 2 .uint64)))]]
def suCmpKP : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvP)
    (.seq [suStoreBlockP] ([] :: suEnvP) suLoopKP)
def suRefP (n : Nat) (iv : Int) : TargetRef :=
  .chain (pSliceS n) [.int iv .uint64] [.index]
def suStTailP : Cont :=
  .seq [] suEnvP2 (.seq [] ([] :: suEnvP) suLoopKP)
def suAddKP (n : Nat) (sv iv : Int) : Cont :=
  .strictK .add [.int sv .uint64] [] suEnvP2
    (.rhsK .vals [suRefP n iv] [] [] (.seqn #[]) suEnvP2 suStTailP)
def suModKP (n : Nat) (sv iv : Int) : Cont :=
  .strictK .mod [.int iv .uint64] [] suEnvP2 (suAddKP n sv iv)

def pTailAfterCopy : Cont :=
  .seq [pS6, pS7] [preScopeP, baseEnvP] (.frame [] [] [] [] .stop)
def cpHeadTailP : Cont :=
  .seq [] cpEnvP
    (.seq [] [[("i", .base ⟨10⟩)], preScopeP, baseEnvP] pTailAfterCopy)
def cpHeadCfgP : Config :=
  .exec (.while (.boolLit true) palinHarnessRFunc.cpBody) cpEnvP cpHeadTailP
def cpLoopKP : Cont :=
  .loop (.boolLit true) palinHarnessRFunc.cpBody cpEnvP cpHeadTailP
def cpStoreBlockP : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpKP : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvP)
    (.seq [cpStoreBlockP] ([] :: cpEnvP) cpLoopKP)
def cpRefP (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨9⟩)) [.int iv .uint64] [.index]
def cpStTailP : Cont :=
  .seq [] cpEnvP2 (.seq [] ([] :: cpEnvP) cpLoopKP)
def cpRhsKP (iv : Int) : Cont :=
  .rhsK .vals [cpRefP iv] [] [] (.seqn #[]) cpEnvP2 cpStTailP

/-! ## Continuations — the `isPalindrome` frame -/

def pShapes : List (TargetShape × List Expr) := [(.chain [], [.ref "v"])]
def pAfterCall : Cont :=
  .seq [pS7] callEnvP (.frame [] [] [] [] .stop)
def pCallArgsK : Cont :=
  .callArgsK ⟨"isPalindrome"⟩ pShapes [] [] callEnvP pAfterCall
def pFrameEnv : LocalEnv :=
  [[("$res0", .base ⟨14⟩), ("s", .base ⟨13⟩)]]
def pFrameK : Cont :=
  .frame pShapes callEnvP [.base ⟨14⟩] [] pAfterCall false

def pEnvIJ : LocalEnv :=
  [("j", .base ⟨16⟩), ("i", .base ⟨15⟩)] :: pFrameEnv
def pEnvIn : LocalEnv := [("$forFirst", .base ⟨17⟩)] :: pEnvIJ

/-- The `$forFirst`-and-loop block, the subject body's third statement. -/
def pFFBlock : Stmt :=
  .block #[]
    #[.initialization { id := "$forFirst", typ := .bool },
      .assign (.var "$forFirst") (.boolLit true),
      .while (.boolLit true) isPalindromeFunc.palWhileBody]

/-- The continuation under `j := len(s) - 1`. -/
def pJTailP : Cont :=
  .seq [pFFBlock, isPalindromeFunc.palTailSeqn] pEnvIJ pFrameK
/-- The subtraction's continuation, once `len(s)` has been applied. -/
def pJSubKP : Cont :=
  .strictK .sub [] [.intLit 1 .int] pEnvIJ
    (.rhsK .vals [.chain (.addr (.base ⟨16⟩)) [] []] [] [] (.seqn #[])
      pEnvIJ pJTailP)
/-- The `len(s)` apply point inside the subject's prologue. -/
def pJLenKP : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] pEnvIJ pJSubKP
def pEnvC : LocalEnv := [] :: pEnvIn
def pEnvB2 : LocalEnv := [] :: pEnvC

def pHeadTailP : Cont :=
  .seq [] pEnvIn (.seq [isPalindromeFunc.palTailSeqn] pEnvIJ pFrameK)
def pHeadCfgP : Config :=
  .exec (.while (.boolLit true) isPalindromeFunc.palWhileBody) pEnvIn
    pHeadTailP
def pLoopKP : Cont :=
  .loop (.boolLit true) isPalindromeFunc.palWhileBody pEnvIn pHeadTailP
def pCmpIfKP : Cont :=
  .ifK (.seqn #[]) .breakStmt pEnvC
    (.seq [isPalindromeFunc.palBodyBlock] pEnvC pLoopKP)
def pNeIfKP : Cont :=
  .ifK isPalindromeFunc.palRet0Block (.seqn #[]) pEnvB2
    (.seq [.assign (.var "i") (.add (.var "i") (.intLit 1 .int)),
           .assign (.var "j") (.sub (.var "j") (.intLit 1 .int))] pEnvB2
      (.seq [] pEnvC pLoopKP))
/-- The FIRST index read's apply point (`s[i]`), with the second
operand still pending. -/
def pIdx1KP (n : Nat) : Cont :=
  .strictK .indexGet [pSliceS n] [] pEnvB2
    (.strictK (.neqCmp tU64) [] [.indexGet (.var "s") (.var "j")] pEnvB2
      pNeIfKP)
/-- The SECOND index read's apply point (`s[j]`), the first value
banked. -/
def pIdx2KP (n : Nat) (a : Int) : Cont :=
  .strictK .indexGet [pSliceS n] [] pEnvB2
    (.strictK (.neqCmp tU64) [.int a .uint64] [] pEnvB2 pNeIfKP)

/-! ## Heap fronts (program-generic) -/

def zeros8 : List Int := List.replicate 8 0

def pHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, pu64 nv), (.base ⟨1⟩, pu64 sv), (.base ⟨2⟩, pArr8 zeros8),
   (.base ⟨3⟩, pu64 0)]

def pHeapC8 (nv sv : Int) : Heap :=
  pHeap0 nv sv ++ [(.base ⟨4⟩, pNilSlice)]

def pHeapMake (nv sv : Int) (n : Nat) : Heap :=
  pHeap0 nv sv ++
    [(.base ⟨4⟩, pHandle n), (.base ⟨5⟩, pBack n (List.replicate n 0))]

def pHeapSu (nv sv : Int) (n : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    Heap :=
  pHeap0 nv sv ++
    [(.base ⟨4⟩, pHandle n), (.base ⟨5⟩, pBack n l), (.base ⟨6⟩, pHandle n),
     (.base ⟨7⟩, pu64 iv), (.base ⟨8⟩, pbool ffv)]

def pHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (ffv : Bool) : Heap :=
  pHeapSu nv sv n l siv false ++
    [(.base ⟨9⟩, pArr8 lp), (.base ⟨10⟩, pu64 civ), (.base ⟨11⟩, pbool ffv)]

def pHeapCall (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  pHeapCp nv sv n l lp siv civ false ++ [(.base ⟨12⟩, pu64 0)]

def pHeapPFrame (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  pHeapCall nv sv n l lp siv civ ++
    [(.base ⟨13⟩, pHandle n), (.base ⟨14⟩, pu64 0)]

/-- Mid-prologue: `i` and `j` declared (both still at their `int`
default), the first-pass flag not yet allocated. -/
def pHeapP1 (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int) :
    Heap :=
  pHeapPFrame nv sv n l lp siv civ ++
    [(.base ⟨15⟩, pint 0), (.base ⟨16⟩, pint 0)]

/-- The subject's loop state: `i`/`j` at their `int` cells and the
first-pass flag. -/
def pHeapP (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (iv jv : Int) (ffv : Bool) : Heap :=
  pHeapPFrame nv sv n l lp siv civ ++
    [(.base ⟨15⟩, pint iv), (.base ⟨16⟩, pint jv), (.base ⟨17⟩, pbool ffv)]

/-- The state just before the `$res0 = pre` store — the ONE epilogue
step that cannot reduce definitionally (the array's contents are
symbolic). `vv` is the verdict, already delivered into both the
subject's result cell and the harness's `v`. -/
def pHeapPreStore (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (iv jv vv : Int) : Heap :=
  pHeapCp nv sv n l lp siv civ false ++
    [(.base ⟨12⟩, pu64 vv), (.base ⟨13⟩, pHandle n), (.base ⟨14⟩, pu64 vv),
     (.base ⟨15⟩, pint iv), (.base ⟨16⟩, pint jv), (.base ⟨17⟩, pbool false)]

/-- Same, with `pre` delivered into `$res0`. -/
def pHeapStored (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (iv jv vv : Int) : Heap :=
  [(.base ⟨0⟩, pu64 nv), (.base ⟨1⟩, pu64 sv), (.base ⟨2⟩, pArr8 lp),
   (.base ⟨3⟩, pu64 0),
   (.base ⟨4⟩, pHandle n), (.base ⟨5⟩, pBack n l), (.base ⟨6⟩, pHandle n),
   (.base ⟨7⟩, pu64 siv), (.base ⟨8⟩, pbool false),
   (.base ⟨9⟩, pArr8 lp), (.base ⟨10⟩, pu64 civ), (.base ⟨11⟩, pbool false),
   (.base ⟨12⟩, pu64 vv), (.base ⟨13⟩, pHandle n), (.base ⟨14⟩, pu64 vv),
   (.base ⟨15⟩, pint iv), (.base ⟨16⟩, pint jv), (.base ⟨17⟩, pbool false)]

/-- The terminal heap. -/
def pHeapEnd (nv sv : Int) (n : Nat) (l lp : List Int) (siv civ : Int)
    (iv jv vv : Int) : Heap :=
  [(.base ⟨0⟩, pu64 nv), (.base ⟨1⟩, pu64 sv), (.base ⟨2⟩, pArr8 lp),
   (.base ⟨3⟩, pu64 (IntKind.normalize .uint64 vv)),
   (.base ⟨4⟩, pHandle n), (.base ⟨5⟩, pBack n l), (.base ⟨6⟩, pHandle n),
   (.base ⟨7⟩, pu64 siv), (.base ⟨8⟩, pbool false),
   (.base ⟨9⟩, pArr8 lp), (.base ⟨10⟩, pu64 civ), (.base ⟨11⟩, pbool false),
   (.base ⟨12⟩, pu64 vv), (.base ⟨13⟩, pHandle n), (.base ⟨14⟩, pu64 vv),
   (.base ⟨15⟩, pint iv), (.base ⟨16⟩, pint jv), (.base ⟨17⟩, pbool false)]

def pEpiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "v"), .returnStmt] callEnvP
    (.frame [] [] [] [] .stop)
def pRes0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []

/-! ## The entry equation

The pinned program as an empty-heap state — with the `derive_entry_eq`
invocation below, the one place this module carries `palinLowered`
outside the two lowering pins. -/

def pProg : ExecState :=
  { types := palinLowered.typeDefs.toList,
    functions := palinLowered.funcs,
    methods := palinLowered.methods,
    heap := [], nextAddr := 0 }

derive_entry_eq pH_entry_eq palinLowered palinHarnessRFunc pHSeed pHC0 pProg

/-! ## Heap-lookup facts -/

theorem lookup_suP (σ : ExecState) (nv sv : Int) (n : Nat) (l : List Int)
    (iv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (pSt σ (pHeapSu nv sv n l iv ffv) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [pHeapSu, pHeap0, Heap.lookup]

theorem lookup_cpS_P (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (pSt σ (pHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [pHeapCp, pHeapSu, pHeap0, Heap.lookup]

theorem lookup_cpPre_P (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (pSt σ (pHeapCp nv sv n l lp siv civ ffv) na).heap
        (.base ⟨9⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [pHeapCp, pHeapSu, pHeap0, Heap.lookup]

theorem lookup_pP (σ : ExecState) (nv sv : Int) (n : Nat) (l lp : List Int)
    (siv civ iv jv : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (pSt σ (pHeapP nv sv n l lp siv civ iv jv ffv) na).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [pHeapP, pHeapPFrame, pHeapCall, pHeapCp, pHeapSu, pHeap0, Heap.lookup]

theorem lookup_preStoreP (σ : ExecState) (nv sv : Int) (n : Nat)
    (l lp : List Int) (siv civ iv jv vv : Int) (na : Nat) :
    Heap.lookup
        (pSt σ (pHeapPreStore nv sv n l lp siv civ iv jv vv) na).heap
        (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := by
  simp [pHeapPreStore, pHeapCp, pHeapSu, pHeap0, Heap.lookup]

end GoLean.Examples.ArrayPalindrome
