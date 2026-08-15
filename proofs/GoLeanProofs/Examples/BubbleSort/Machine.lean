import GoLeanProofs.Examples.BubbleSortProgram
import GoLeanProofs.Examples.SortShared
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId
import GoLeanProofs.Laws.StmtOps

/-!
# BubbleSort — Machine

The machine-facing layer of the `bubble` example (Gallery Campaign G1,
proof lane B): the two `Func` records transcribed from the pinned
lowering (each tied to it by an `rfl` pin), the statement pieces the
continuations mention, the address layout, the heap fronts, and the
derived entry equation.

The guardrails wave landed the harness `Func` in the example ROOT in
the mechanically-extracted spelling. It is restated here in the
readable dot-notation form — the wave's recorded allowance ("a proof
lane may restate it readably; the pin must keep holding by `rfl`") —
and `bubbleHarnessRFunc_pin` is the check that the restatement says
exactly what the lowering says.

Address layout (probe-measured with the lane's generic tracer
`.tmp/Probe.lean` at `(n, seed) = (2, 3)`; every raw segment
downstream re-checks the transcription by `rfl`, so a mis-read layout
fails loudly rather than silently):

```
0 = n            1 = seed         2 = $res0 ([8]uint64)   3 = $res1
4 = $c4 handle   5 = s backing    6 = s
7 = x (the LCG accumulator)       8 = setup i     9 = setup flag
10 = pre ([8])  11 = copy i      12 = copy flag
-- the `bubbleSort` frame (entered at nextAddr 13) --
13 = s param    14 = end         15 = outer $forFirst   -- nextAddr = 16
-- per outer pass (3 cells, RE-ALLOCATED each pass):
16+3p = swapped   17+3p = inner i   18+3p = inner $forFirst
-- after the subject returns (true addresses depend on the pass count):
post ([8]), copy2 i, copy2 flag
```

The per-pass re-allocation is why this example carries a FRAME-REBASE
layer (threshold 16, retire 3 — the InsertionSort `ρ11`/`rebaseSim11`
pattern): `rfl` segments need address-concrete environments, so each
pass is proven ONCE at the tight placement and transferred to the true
(garbage-laden) placement by the executable frame theorem
(`BubbleSort.Frame`). The epilogue (the `post` copy loop and the two
result stores) is likewise proven once at the canonical placement and
transferred at the end.
-/

namespace GoLean.Examples.BubbleSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The subject `Func`, in readable pieces

Transcribed from the pinned lowering (`bubble_pin` below ties it by
`rfl`). The pieces are top-level so the continuations can mention
them. -/

/-- The element swap: `s[i-1], s[i] = s[i], s[i-1]` (an `assignMany`),
followed by `swapped = true`. -/
abbrev bSwapBlock : Stmt :=
  .block #[]
    #[.seqn
        #[.assignMany
            #[.addr (.indexAddr (.var "s")
                (.sub (.var "i") (.intLit 1 .int))),
              .addr (.indexAddr (.var "s") (.var "i"))]
            #[.indexGet (.var "s") (.var "i"),
              .indexGet (.var "s")
                (.sub (.var "i") (.intLit 1 .int))]],
      .seqn #[.assign (.var "swapped") (.boolLit true)]]

/-- The inner body's comparison-and-swap statement. -/
abbrev bIfSwap : Stmt :=
  .ifThenElse
    (.greaterCmp
      (.indexGet (.var "s") (.sub (.var "i") (.intLit 1 .int)))
      (.indexGet (.var "s") (.var "i")))
    bSwapBlock (.seqn #[])

/-- The inner `for`-desugar body (its own `$forFirst`, shadowing the
outer one). -/
abbrev bInnerBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "end"))
        (.seqn #[]) .breakStmt,
      .block #[] #[bIfSwap]]

/-- The inner `for i := 1; i < end; i++` as lowered. -/
abbrev bInnerFor : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 1 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) bInnerBody]]

/-- One outer pass's block: `swapped := false`, the inner `for`, and
the EARLY EXIT `if !swapped { return }`. -/
abbrev bPassBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "swapped", typ := .bool },
              .assign (.var "swapped") (.boolLit false)],
      bInnerFor,
      .ifThenElse (.not (.var "swapped"))
        (.block #[] #[.returnStmt]) (.seqn #[])]

/-- The outer `for`-desugar body: dispatch (`end--` on later passes),
the exit test `end > 1`, then the pass block. -/
abbrev bOuterBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "end")
          (.sub (.var "end") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.greaterCmp (.var "end") (.intLit 1 .int))
        (.seqn #[]) .breakStmt,
      bPassBlock]

/-- The subject `Func`: nested loops with per-pass `swapped` and the
early return. -/
def bubbleSortFunc : Func :=
  { id := { key := "bubbleSort" },
    args := #[{ id := "s", typ := .slice tU64 }],
    results := #[],
    body := .block #[]
      #[.block #[]
          #[.seqn
              #[.initialization { id := "end", typ := .int .int },
                .assign (.var "end")
                  (.length (.var "s") (some (.slice tU64)))],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) bOuterBody]]],
    variadic := false,
    wrapper := false }

/-! ## The harness `Func`, restated readably -/

/-- The setup loop's body: `x = x*2862933555777941757 + 3037000493;
s[i] = x`. -/
abbrev bSuBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.var "x")
            (.add (.mul (.var "x")
                (.intLit 2862933555777941757 .uint64))
              (.intLit 3037000493 .uint64))],
          .seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
            (.var "x")]]]

/-- A copy loop's body: `dst[i] = s[i]` for `dst ∈ {pre, post}`. -/
abbrev bCpBody (dst : String) : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.addr (.indexAddr (.ref dst) (.var "i")))
            (.indexGet (.var "s") (.var "i"))]]]

/-- A `for i := uint64(0); i < n; i++ { body }` block as lowered. -/
abbrev bForU64 (body : Stmt) : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) body]]

/-- The harness body's ten statements, named for the continuations. -/
abbrev bS1 : Stmt :=
  .seqn #[.initialization { id := "$c4", typ := .slice tU64 },
          .makeSlice (.var "$c4") tU64 (.var "n") none]
abbrev bS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice tU64 },
          .assign (.var "s") (.var "$c4")]
abbrev bS3 : Stmt :=
  .seqn #[.initialization { id := "x", typ := tU64 },
          .assign (.var "x") (.var "seed")]
abbrev bS4 : Stmt := bForU64 bSuBody
abbrev bS5 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }]
abbrev bS6 : Stmt := bForU64 (bCpBody "pre")
abbrev bS7 : Stmt := .call #[] ⟨"bubbleSort"⟩ #[.var "s"]
abbrev bS8 : Stmt :=
  .seqn #[.initialization { id := "post", typ := .array 8 tU64 }]
abbrev bS9 : Stmt := bForU64 (bCpBody "post")
abbrev bS10 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "post"),
          .returnStmt]

/-- The harness `Func`, restated readably from the guardrails wave's
mechanically-extracted spelling; `bubbleHarnessRFunc_pin` ties it to
the lowering by `rfl`. -/
def bubbleHarnessRFunc : Func :=
  { id := { key := "bubble_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := .array 8 tU64 }],
    body := .block #[]
      #[bS1, bS2, bS3, bS4, bS5, bS6, bS7, bS8, bS9, bS10],
    variadic := false,
    wrapper := false }

/-- The subject lowering pin. -/
theorem bubble_pin :
    findFunctionIn? bubbleLowered.funcs ⟨"bubbleSort"⟩
      = some bubbleSortFunc := rfl

/-- The harness lowering pin: the readable restatement IS the
frontend's lowering (the guardrails-wave pin, name preserved). -/
theorem bubbleHarnessRFunc_pin :
    findFunctionIn? bubbleLowered.funcs ⟨"bubble_harness_r"⟩
      = some bubbleHarnessRFunc := rfl

/-! ## The statement vocabulary of the S3 form -/

/-- The returned fixed-cap array, zero-padded past the live prefix. -/
def bArr8V (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-! ## Cells and values at the bubble layout -/

abbrev bu64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev bint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev bbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev bSliceS (n : Nat) : GoValue := .slice ⟨some (.base ⟨5⟩), 0, n, n⟩
abbrev bHandle (n : Nat) : HeapCell := ⟨some (.slice tU64), bSliceS n⟩
abbrev bBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev bArr8 (l : List Int) : HeapCell :=
  ⟨some (.array 8 tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev bNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩

def zeros8 : List Int := List.replicate 8 0

/-! ## The LCG family at the bubble constants -/

/-- The bubble LCG multiplier/increment (visible in the corpus Go). -/
abbrev bubA : Nat := 2862933555777941757
abbrev bubB : Nat := 3037000493

/-- The setup family: `s[i]` is the LCG's `(i+1)`-th iterate. -/
abbrev bubFam (n seed : Nat) : List Int :=
  SortShared.lcgFamily bubA bubB n seed

/-- The parked `x` accumulator after `m` setup iterations. -/
abbrev bubX (m seed : Nat) : Int :=
  ((SortShared.lcgStep bubA bubB m seed : Nat) : Int)

/-- The `pre`/`post` array after `m` copy steps (zero-padded cap 8). -/
abbrev bubPre (m seed : Nat) : List Int :=
  bubFam m seed ++ List.replicate (8 - m) 0

/-! ## The program wrapper -/

/-- The pinned program as an empty-heap state (the `derive_entry_eq`
base, and the program fields every state below carries). -/
def bProg : ExecState :=
  { types := bubbleLowered.typeDefs.toList,
    functions := bubbleLowered.funcs,
    methods := bubbleLowered.methods,
    heap := [], nextAddr := 0 }

/-- All machine states in this example: the pinned program with a heap
front and an allocator position. -/
abbrev σB (H : Heap) (na : Nat) : ExecState :=
  { bProg with heap := H, nextAddr := na }

/-! ## Heap fronts — the harness phases -/

def bHeap0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, bu64 nv), (.base ⟨1⟩, bu64 sv), (.base ⟨2⟩, bArr8 zeros8),
   (.base ⟨3⟩, bArr8 zeros8)]

def bHeapC4 (nv sv : Int) : Heap :=
  bHeap0 nv sv ++ [(.base ⟨4⟩, bNilSlice)]

def bHeapMake (nv sv : Int) (n : Nat) : Heap :=
  bHeap0 nv sv ++
    [(.base ⟨4⟩, bHandle n), (.base ⟨5⟩, bBack n (List.replicate n 0))]

/-- The setup loop's state: `x` at 7, the counter at 8, the flag
at 9. -/
def bHeapSu (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ffv : Bool) : Heap :=
  bHeap0 nv sv ++
    [(.base ⟨4⟩, bHandle n), (.base ⟨5⟩, bBack n l), (.base ⟨6⟩, bHandle n),
     (.base ⟨7⟩, bu64 xv), (.base ⟨8⟩, bu64 iv), (.base ⟨9⟩, bbool ffv)]

/-- The first copy loop's state: `pre` at 10, counter 11, flag 12. -/
def bHeapCp (nv sv : Int) (n : Nat) (l lp : List Int) (xv siv civ : Int)
    (ffv : Bool) : Heap :=
  bHeapSu nv sv n l xv siv false ++
    [(.base ⟨10⟩, bArr8 lp), (.base ⟨11⟩, bu64 civ), (.base ⟨12⟩, bbool ffv)]

/-! ## Heap fronts — the subject phase (parked harness values)

From the subject call on, the harness cells are PARKED at their final
values: `x` at the full LCG iterate, both counters at `n`, `pre` at
the full padded family. Only the backing list `l`, the `end` cell and
the flags evolve. -/

/-- The fixed 16-cell prefix of every subject-phase state. -/
def bHeapSubj (n seed : Nat) (l : List Int) (endv : Int) (ffv : Bool) :
    Heap :=
  bHeapCp ((n : Nat) : Int) ((seed : Nat) : Int) n l (bubPre n seed)
      (bubX n seed) ((n : Nat) : Int) ((n : Nat) : Int) false ++
    [(.base ⟨13⟩, bHandle n), (.base ⟨14⟩, bint endv),
     (.base ⟨15⟩, bbool ffv)]

/-- The subject-phase state family, TAIL-PARAMETRIC: the sixteen fixed
cells in front, an arbitrary inert tail behind. -/
def σBOutT (n seed : Nat) (l : List Int) (endv : Int) (ffv : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  σB (bHeapSubj n seed l endv ffv ++ tail) na

/-- The tight 16-cell outer state (canonical pass placement). -/
def σBOut (n seed : Nat) (l : List Int) (endv : Int) (ffv : Bool) :
    ExecState :=
  σBOutT n seed l endv ffv [] 16

/-- The tight 19-cell in-pass state: `swapped` at 16, the inner
counter at 17, the inner flag at 18. -/
def σBIn (n seed : Nat) (l : List Int) (endv iv : Int) (swv ffIv : Bool) :
    ExecState :=
  σBOutT n seed l endv false
    [(.base ⟨16⟩, bbool swv), (.base ⟨17⟩, bint iv),
     (.base ⟨18⟩, bbool ffIv)] 19

/-! ## Environments -/

def baseEnvB : Scope :=
  [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩),
   ("n", .base ⟨0⟩)]
def envC4B : LocalEnv := [[("$c4", .base ⟨4⟩)], baseEnvB]
/-- The harness main scope once `s` and `x` are declared. -/
def hScopeB : Scope :=
  [("x", .base ⟨7⟩), ("s", .base ⟨6⟩), ("$c4", .base ⟨4⟩)]
/-- … and once `pre` is declared. -/
def preScopeB : Scope := ("pre", .base ⟨10⟩) :: hScopeB

def suEnvB : LocalEnv :=
  [[("$forFirst", .base ⟨9⟩)], [("i", .base ⟨8⟩)], hScopeB, baseEnvB]
def suEnvB2 : LocalEnv := [] :: [] :: suEnvB
def cpEnvB : LocalEnv :=
  [[("$forFirst", .base ⟨12⟩)], [("i", .base ⟨11⟩)], preScopeB, baseEnvB]
def cpEnvB2 : LocalEnv := [] :: [] :: cpEnvB
def callEnvB : LocalEnv := [preScopeB, baseEnvB]

/-! ## Continuations — the harness half -/

/-- The post-call anchor's continuation: the harness resumes at
`var post`, the second copy loop, and the epilogue. -/
def bAfterCallK : Cont :=
  .seq [bS8, bS9, bS10] callEnvB (.frame [] [] [] [] .stop)

def bTailAfterSetup : Cont :=
  .seq [bS5, bS6, bS7, bS8, bS9, bS10] [hScopeB, baseEnvB]
    (.frame [] [] [] [] .stop)
def suHeadTailB : Cont :=
  .seq [] suEnvB
    (.seq [] [[("i", .base ⟨8⟩)], hScopeB, baseEnvB] bTailAfterSetup)
def suHeadCfgB : Config :=
  .exec (.while (.boolLit true) bSuBody) suEnvB suHeadTailB
def suLoopKB : Cont := .loop (.boolLit true) bSuBody suEnvB suHeadTailB
def suStoreBlockB : Stmt :=
  .block #[]
    #[.seqn #[.assign (.var "x")
        (.add (.mul (.var "x") (.intLit 2862933555777941757 .uint64))
          (.intLit 3037000493 .uint64))],
      .seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.var "x")]]
def suCmpKB : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnvB)
    (.seq [suStoreBlockB] ([] :: suEnvB) suLoopKB)
def suRefB (n : Nat) (iv : Int) : TargetRef :=
  .chain (bSliceS n) [.int iv .uint64] [.index]
def suStTailB : Cont :=
  .seq [] suEnvB2 (.seq [] ([] :: suEnvB) suLoopKB)

def bTailAfterCopy : Cont :=
  .seq [bS7, bS8, bS9, bS10] [preScopeB, baseEnvB]
    (.frame [] [] [] [] .stop)
def cpHeadTailB : Cont :=
  .seq [] cpEnvB
    (.seq [] [[("i", .base ⟨11⟩)], preScopeB, baseEnvB] bTailAfterCopy)
def cpHeadCfgB : Config :=
  .exec (.while (.boolLit true) (bCpBody "pre")) cpEnvB cpHeadTailB
def cpLoopKB : Cont :=
  .loop (.boolLit true) (bCpBody "pre") cpEnvB cpHeadTailB
def cpStoreBlockB : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpKB : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnvB)
    (.seq [cpStoreBlockB] ([] :: cpEnvB) cpLoopKB)
def cpRefB (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨10⟩)) [.int iv .uint64] [.index]
def cpStTailB : Cont :=
  .seq [] cpEnvB2 (.seq [] ([] :: cpEnvB) cpLoopKB)
def cpRhsKB (iv : Int) : Cont :=
  .rhsK .vals [cpRefB iv] [] [] (.seqn #[]) cpEnvB2 cpStTailB

/-- The call's argument spine (no results, one argument). -/
def bCallArgsK : Cont :=
  .callArgsK ⟨"bubbleSort"⟩ [] [] [] callEnvB bAfterCallK

/-! ## Continuations — the `bubbleSort` frame -/

def bFrameEnv : LocalEnv := [[("s", .base ⟨13⟩)]]
def bFrameK : Cont := .frame [] callEnvB [] [] bAfterCallK false

def bEnvEnd : LocalEnv := [("end", .base ⟨14⟩)] :: [] :: bFrameEnv
def bEnvO : LocalEnv := [("$forFirst", .base ⟨15⟩)] :: bEnvEnd

/-- The continuation under `end := len(s)`. -/
def bPreTailK : Cont :=
  .seq [.block #[]
          #[.initialization { id := "$forFirst", typ := .bool },
            .assign (.var "$forFirst") (.boolLit true),
            .while (.boolLit true) bOuterBody]] bEnvEnd
    (.seq [] ([] :: bFrameEnv) bFrameK)
/-- The `len(s)` apply point inside the subject's prologue: the length
op feeds the `end` store's rhs. -/
def bLenKB : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] bEnvEnd
    (.rhsK .vals [.chain (.addr (.base ⟨14⟩)) [] []] [] [] (.seqn #[])
      bEnvEnd bPreTailK)

def bHeadTailO : Cont :=
  .seq [] bEnvO
    (.seq [] bEnvEnd (.seq [] ([] :: bFrameEnv) bFrameK))
/-- The subject OUTER loop-head configuration. -/
def bOuterHeadCfg : Config :=
  .exec (.while (.boolLit true) bOuterBody) bEnvO bHeadTailO
def bLoopKO : Cont := .loop (.boolLit true) bOuterBody bEnvO bHeadTailO
/-- The outer exit test's (`end > 1`) delivery continuation. -/
def bOuterCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: bEnvO)
    (.seq [bPassBlock] ([] :: bEnvO) bLoopKO)

/-- The in-pass environments (tight placement: swapped 16, i 17,
flag 18). -/
def bEnvSw : LocalEnv := [("swapped", .base ⟨16⟩)] :: [] :: bEnvO
def bEnvI : LocalEnv :=
  [("$forFirst", .base ⟨18⟩)] :: [("i", .base ⟨17⟩)] :: bEnvSw
def bInnerTail : Cont :=
  .seq [] bEnvI
    (.seq [] ([("i", .base ⟨17⟩)] :: bEnvSw)
      (.seq [.ifThenElse (.not (.var "swapped"))
               (.block #[] #[.returnStmt]) (.seqn #[])] bEnvSw
        (.seq [] ([] :: bEnvO) bLoopKO)))
/-- The subject INNER loop-head configuration (tight placement). -/
def bInnerHeadCfg : Config :=
  .exec (.while (.boolLit true) bInnerBody) bEnvI bInnerTail
def bLoopKI : Cont := .loop (.boolLit true) bInnerBody bEnvI bInnerTail
/-- The inner exit test's (`i < end`) delivery continuation. -/
def bInnerCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: bEnvI)
    (.seq [.block #[] #[bIfSwap]] ([] :: bEnvI) bLoopKI)
def bEnvC : LocalEnv := [] :: [] :: bEnvI
/-- The comparison-and-swap `if`'s delivery continuation. -/
def bSwIfK : Cont :=
  .ifK bSwapBlock (.seqn #[]) bEnvC
    (.seq [] ([] :: bEnvI) bLoopKI)
/-- The FIRST condition read's apply point (`s[i-1]`), with the second
operand still pending. -/
def bGtK1 (n : Nat) : Cont :=
  .strictK .indexGet [bSliceS n] [] bEnvC
    (.strictK .greaterCmp [] [.indexGet (.var "s") (.var "i")] bEnvC
      bSwIfK)
/-- The SECOND condition read's apply point (`s[i]`), the first value
banked. -/
def bGtK2 (n : Nat) (a : Int) : Cont :=
  .strictK .indexGet [bSliceS n] [] bEnvC
    (.strictK .greaterCmp [.int a .uint64] [] bEnvC bSwIfK)

/-- The `!swapped` delivery continuation (the pass's third statement). -/
def bNotIfK : Cont :=
  .ifK (.block #[] #[.returnStmt]) (.seqn #[]) bEnvSw
    (.seq [] ([] :: bEnvO) bLoopKO)

/-! ### The swap's `assignMany` spine -/

def bEnvSw2 : LocalEnv := [] :: [] :: bEnvI
def bSwTail : Cont :=
  .seq [.seqn #[.assign (.var "swapped") (.boolLit true)]] bEnvSw2
    (.seq [] ([] :: bEnvI) bLoopKI)
def bRefj (n : Nat) (idx : Int) : TargetRef :=
  .chain (bSliceS n) [.int idx .int] [.index]
/-- The first rhs read's (`s[i]`) apply point: both target refs
resolved, no value banked. -/
def bRhsK1 (n : Nat) (idx1 iv : Int) : Cont :=
  .rhsK .vals [bRefj n idx1, bRefj n iv] []
    [.indexGet (.var "s") (.sub (.var "i") (.intLit 1 .int))]
    (.seqn #[]) bEnvSw2 bSwTail
/-- The second rhs read's (`s[i-1]`) apply point, the first banked. -/
def bRhsK2 (n : Nat) (idx1 iv : Int) (wj : GoValue) : Cont :=
  .rhsK .vals [bRefj n idx1, bRefj n iv] [wj] [] (.seqn #[]) bEnvSw2 bSwTail

/-! ## Continuations — the epilogue (canonical placement)

The second copy loop and the result stores, at the CANONICAL
post-subject placement: `post` at 16, its counter at 17, its flag at
18 (the true run has them shifted by the retired pass cells; the frame
theorem carries the difference). -/

def postScopeB : Scope := ("post", .base ⟨16⟩) :: preScopeB
def epEnvB : LocalEnv :=
  [[("$forFirst", .base ⟨18⟩)], [("i", .base ⟨17⟩)], postScopeB, baseEnvB]
def epEnvB2 : LocalEnv := [] :: [] :: epEnvB
def epEnvTail : LocalEnv := [postScopeB, baseEnvB]

def epHeadTailB : Cont :=
  .seq [] epEnvB
    (.seq [] [[("i", .base ⟨17⟩)], postScopeB, baseEnvB]
      (.seq [bS10] epEnvTail (.frame [] [] [] [] .stop)))
def epHeadCfgB : Config :=
  .exec (.while (.boolLit true) (bCpBody "post")) epEnvB epHeadTailB
def epLoopKB : Cont :=
  .loop (.boolLit true) (bCpBody "post") epEnvB epHeadTailB
def epStoreBlockB : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "post") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def epCmpKB : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: epEnvB)
    (.seq [epStoreBlockB] ([] :: epEnvB) epLoopKB)
def epRefB (iv : Int) : TargetRef :=
  .chain (.addr (.base ⟨16⟩)) [.int iv .uint64] [.index]
def epStTailB : Cont :=
  .seq [] epEnvB2 (.seq [] ([] :: epEnvB) epLoopKB)
def epRhsKB (iv : Int) : Cont :=
  .rhsK .vals [epRefB iv] [] [] (.seqn #[]) epEnvB2 epStTailB

/-- The `$res0 = pre` store's target and tail. -/
def bRes0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []
def bRes1Ref : TargetRef := .chain (.addr (.base ⟨3⟩)) [] []
def bEpiTail1 : Cont :=
  .seq [.assign (.var "$res1") (.var "post"), .returnStmt] epEnvTail
    (.frame [] [] [] [] .stop)
def bEpiTail2 : Cont :=
  .seq [.returnStmt] epEnvTail (.frame [] [] [] [] .stop)

/-! ## The entry equation -/

derive_entry_eq bH_entry_eq bubbleLowered bubbleHarnessRFunc bHSeed bHC0
  bProg

/-! ## Heap-lookup facts -/

theorem lookup_suB (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ffv : Bool) (na : Nat) :
    Heap.lookup (σB (bHeapSu nv sv n l xv iv ffv) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapSu, bHeap0, Heap.lookup]

theorem lookup_cpS_B (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (σB (bHeapCp nv sv n l lp xv siv civ ffv) na).heap
        (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapCp, bHeapSu, bHeap0, Heap.lookup]

theorem lookup_cpPre_B (nv sv : Int) (n : Nat) (l lp : List Int)
    (xv siv civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (σB (bHeapCp nv sv n l lp xv siv civ ffv) na).heap
        (.base ⟨10⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [bHeapCp, bHeapSu, bHeap0, Heap.lookup]

theorem lookup_σBIn5 (n seed : Nat) (l : List Int) (endv iv : Int)
    (swv ffIv : Bool) :
    Heap.lookup (σBIn n seed l endv iv swv ffIv).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [σBIn, σBOutT, σB, bHeapSubj, bHeapCp, bHeapSu, bHeap0, Heap.lookup]

end GoLean.Examples.BubbleSort
