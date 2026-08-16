import GoLeanProofs.Examples.SelectionSort.Pure
import GoLeanProofs.Examples.SelectionSortProgram
import GoLeanProofs.StepKit
import GoLeanProofs.FuelMeasure
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# SelectionSort — Machine

The machine-facing layer: the two `Func` records transcribed from the
pinned lowering (each tied to it by an `rfl` pin), the statement
pieces, the environments and continuations of every phase, the heap
fronts, and the derived entry equation.

The guardrails wave landed the harness `Func` in the example ROOT in
the mechanically-extracted spelling. It is restated here in the
readable dot-notation form — the wave's recorded allowance ("a proof
lane may restate it readably; the pin must keep holding by `rfl`") —
and `selsortHarnessRFunc_pin` checks the restatement against the
lowering.

Address layout (probe-measured at `(n, seed) = (3, 7)` with the lane's
generic tracer `.tmp/Probe.lean`; every raw segment downstream
re-checks the transcription by `rfl`):

```
 0 = n            1 = seed        2 = $res0 ([8]uint64)  3 = $res1
 4 = $c4 handle   5 = s backing   6 = s                  7 = x
 8 = setup i      9 = setup flag
10 = pre ([8])   11 = copy i     12 = copy flag
-- the `selectionSort` frame (entered at nextAddr 13) --
13 = s param     14 = subject i  15 = outer $forFirst    -- nextAddr 16
-- per-pass cells, CANONICAL (tight) placement --
16 = m           17 = j          18 = inner $forFirst    -- nextAddr 19
-- true run: pass p allocates them at 16+3p/17+3p/18+3p; the frame
-- layer in `SelectionSort/Frame.lean` carries the difference --
-- post-subject, CANONICAL: 16 = post, 17 = copy i, 18 = copy flag --
```

Unlike ArrayPalindrome (program-generic `pSt σ`), the states here are
CONCRETE over `selsortLowered` — the per-pass frame simulation
(`FrameSim`) constrains the program fields, so the InsertionSort
precedent (concrete states) is followed. The program is still only
UNFOLDED at the two lowering pins, the `enterFrame` discharge and the
`bodies` rename fact; raw segments never project the function table.
-/

namespace GoLean.Examples.SelectionSort

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Examples.SortShared

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev tU64 : Ty := .int .uint64

/-! ## The LCG family at THIS harness's constants -/

/-- The multiplier of the harness's wrapping LCG (PCG's default). -/
abbrev lcgA : Nat := 6364136223846793005
/-- The increment. -/
abbrev lcgB : Nat := 1442695040888963407

/-- The setup family: `x = x*lcgA + lcgB` iterated from `seed`,
`s[i]` = the `(i+1)`-st iterate (SortShared's shared family). -/
abbrev selFam (n seed : Nat) : List Int := lcgFamily lcgA lcgB n seed

/-- The zero-padded fixed-cap array the copy loops build. -/
abbrev selPad8 (xs : List Int) : List Int :=
  xs ++ List.replicate (8 - xs.length) 0

/-- The returned `[8]uint64` as a `GoValue` (statement vocabulary). -/
def selArr8 (xs : List Int) : GoValue :=
  .array ⟨(selPad8 xs).map (fun v => .int v .uint64)⟩

-- `unorm` on a `Nat` cast (`unorm_nat_mod`) — LIFTED (WP arc s1
-- lift 1), exactly as the GAP-WITNESS note asked: it now lives in
-- `SliceMem` as `unorm_nat`; the local copy is deleted and HarnessR's
-- call sites consume the kit form.

/-! ## The subject `Func`, in the readable spelling -/

/-- The swap: `s[i], s[m] = s[m], s[i]` — one `assignMany`, refs
resolved left-to-right, right-hand sides READ before either store,
stores in order. -/
abbrev selSwapSeqn : Stmt :=
  .seqn #[.assignMany
      #[.addr (.indexAddr (.var "s") (.var "i")),
        .addr (.indexAddr (.var "s") (.var "m"))]
      #[.indexGet (.var "s") (.var "m"),
        .indexGet (.var "s") (.var "i")]]

/-- The inner body's conditional: `if s[j] < s[m] { m = j }`. -/
abbrev selMIfBlock : Stmt :=
  .block #[]
    #[.ifThenElse
        (.lessCmp (.indexGet (.var "s") (.var "j"))
                  (.indexGet (.var "s") (.var "m")))
        (.block #[] #[.seqn #[.assign (.var "m") (.var "j")]])
        (.seqn #[])]

/-- The inner `for`-desugar body: dispatch, exit test `j < len(s)`,
then the conditional. -/
abbrev selInnerWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j") (.add (.var "j") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "j") (.length (.var "s") (some (.slice tU64))))
        (.seqn #[]) .breakStmt,
      selMIfBlock]

/-- The inner `for` as lowered: `j := i + 1`, then the `$forFirst`
block around the while. -/
abbrev selInnerForBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "j", typ := .int .int },
              .assign (.var "j") (.add (.var "i") (.intLit 1 .int))],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) selInnerWhileBody]]

/-- One outer pass's body: `m := i`, the inner `for`, the swap. -/
abbrev selPassBlock : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "m", typ := .int .int },
              .assign (.var "m") (.var "i")],
      selInnerForBlock,
      selSwapSeqn]

/-- The outer `for`-desugar body. -/
abbrev selOuterWhileBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse
        (.lessCmp (.var "i") (.length (.var "s") (some (.slice tU64))))
        (.seqn #[]) .breakStmt,
      selPassBlock]

/-- The subject `Func`: nested loops, no early exit, one unconditional
swap per outer pass (it swaps even when `m == i`). -/
def selectionSortFunc : Func :=
  { id := { key := "selectionSort" },
    args := #[{ id := "s", typ := .slice tU64 }],
    results := #[],
    body := .block #[]
      #[.block #[]
          #[.seqn #[.initialization { id := "i", typ := .int .int },
                    .assign (.var "i") (.intLit 0 .int)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) selOuterWhileBody]]],
    variadic := false,
    wrapper := false }

/-- The subject lowering pin. -/
theorem selectionSort_pin :
    findFunctionIn? selsortLowered.funcs ⟨"selectionSort"⟩
      = some selectionSortFunc := rfl

/-! ## The harness `Func`, restated readably -/

/-- The setup loop's body: `x = x*lcgA + lcgB; s[i] = x`. -/
abbrev selSuBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.var "x")
            (.add (.mul (.var "x") (.intLit 6364136223846793005 .uint64))
                  (.intLit 1442695040888963407 .uint64))],
          .seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
            (.var "x")]]]

/-- The first copy loop's body: `pre[i] = s[i]`. -/
abbrev selCpBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
            (.indexGet (.var "s") (.var "i"))]]]

/-- The second copy loop's body: `post[i] = s[i]`. -/
abbrev selCp2Body : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
      .block #[]
        #[.seqn #[.assign (.addr (.indexAddr (.ref "post") (.var "i")))
            (.indexGet (.var "s") (.var "i"))]]]

/-- Harness top-level statements 2…10 (statement pieces the
continuations mention; statement 1 is the `$c4` makeSlice seqn). -/
def sS2 : Stmt :=
  .seqn #[.initialization { id := "s", typ := .slice tU64 },
          .assign (.var "s") (.var "$c4")]
def sS3 : Stmt :=
  .seqn #[.initialization { id := "x", typ := tU64 },
          .assign (.var "x") (.var "seed")]
def sS4 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) selSuBody]]
def sS5 : Stmt :=
  .seqn #[.initialization { id := "pre", typ := .array 8 tU64 }]
def sS6 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) selCpBody]]
def sS7 : Stmt := .call #[] ⟨"selectionSort"⟩ #[.var "s"]
def sS8 : Stmt :=
  .seqn #[.initialization { id := "post", typ := .array 8 tU64 }]
def sS9 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := tU64 },
              .assign (.var "i") (.intLit 0 .uint64)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) selCp2Body]]
def sS10 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "pre"),
          .assign (.var "$res1") (.var "post"),
          .returnStmt]

/-- The harness `Func`, restated readably from the guardrails wave's
mechanically-extracted spelling; `selsortHarnessRFunc_pin` ties it to
the lowering by `rfl`. -/
def selsortHarnessRFunc : Func :=
  { id := { key := "selsort_harness_r" },
    args := #[{ id := "n", typ := tU64 }, { id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := .array 8 tU64 },
                 { id := "$res1", typ := .array 8 tU64 }],
    body := .block #[]
      #[.seqn #[.initialization { id := "$c4", typ := .slice tU64 },
                .makeSlice (.var "$c4") tU64 (.var "n") none],
        sS2, sS3, sS4, sS5, sS6, sS7, sS8, sS9, sS10],
    variadic := false,
    wrapper := false }

/-- The harness lowering pin: the readable restatement IS the
frontend's lowering (the name and the pin's shape are the guardrails
wave's; only the spelling changed, as the wave's allowance records). -/
theorem selsortHarnessRFunc_pin :
    findFunctionIn? selsortLowered.funcs ⟨"selsort_harness_r"⟩
      = some selsortHarnessRFunc := rfl

/-! ## Cells and the state builder -/

abbrev su64 (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev sint (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev sbool (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev sHandle (n : Nat) : GoValue := .slice ⟨some (.base ⟨5⟩), 0, n, n⟩
abbrev sHandleCell (n : Nat) : HeapCell := ⟨some (.slice tU64), sHandle n⟩
abbrev sBack (n : Nat) (l : List Int) : HeapCell :=
  ⟨some (.array n tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev sArr8 (l : List Int) : HeapCell :=
  ⟨some (.array 8 tU64), .array ⟨l.map (fun v => .int v .uint64)⟩⟩
abbrev sNilSlice : HeapCell := ⟨some (.slice tU64), .slice ⟨none, 0, 0, 0⟩⟩

def zeros8 : List Int := List.replicate 8 0

/-- The concrete state builder: the pinned program with a heap front
and an allocator position. -/
def σS (H : Heap) (na : Nat) : ExecState :=
  { types := selsortLowered.typeDefs.toList,
    functions := selsortLowered.funcs,
    methods := selsortLowered.methods,
    heap := H, nextAddr := na }

/-! ## Heap fronts — phase A (entry, setup, copy) -/

def hp0 (nv sv : Int) : Heap :=
  [(.base ⟨0⟩, su64 nv), (.base ⟨1⟩, su64 sv),
   (.base ⟨2⟩, sArr8 zeros8), (.base ⟨3⟩, sArr8 zeros8)]

def hpC4 (nv sv : Int) : Heap := hp0 nv sv ++ [(.base ⟨4⟩, sNilSlice)]

def hpMk (nv sv : Int) (n : Nat) : Heap :=
  hp0 nv sv ++
    [(.base ⟨4⟩, sHandleCell n), (.base ⟨5⟩, sBack n (List.replicate n 0))]

/-- The setup-loop front: backing `l`, LCG register `x = xv`, counter
`iv`, first-pass flag. -/
def hpSu (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ffv : Bool) : Heap :=
  hp0 nv sv ++
    [(.base ⟨4⟩, sHandleCell n), (.base ⟨5⟩, sBack n l),
     (.base ⟨6⟩, sHandleCell n), (.base ⟨7⟩, su64 xv),
     (.base ⟨8⟩, su64 iv), (.base ⟨9⟩, sbool ffv)]

/-- The copy-loop front: setup cells parked (`siv` = the setup
counter's final value), `pre` prefix `lp`, copy counter `civ`. -/
def hpCp (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ffv : Bool) : Heap :=
  hpSu nv sv n l xv siv false ++
    [(.base ⟨10⟩, sArr8 lp), (.base ⟨11⟩, su64 civ),
     (.base ⟨12⟩, sbool ffv)]

/-! ## Environments — phase A -/

def baseScope : Scope :=
  [("$res1", .base ⟨3⟩), ("$res0", .base ⟨2⟩), ("seed", .base ⟨1⟩),
   ("n", .base ⟨0⟩)]
def envC4 : LocalEnv := [[("$c4", .base ⟨4⟩)], baseScope]
def sxScope : Scope :=
  [("x", .base ⟨7⟩), ("s", .base ⟨6⟩), ("$c4", .base ⟨4⟩)]
def suEnv : LocalEnv :=
  [[("$forFirst", .base ⟨9⟩)], [("i", .base ⟨8⟩)], sxScope, baseScope]
def suEnv2 : LocalEnv := [] :: [] :: suEnv
def preScope : Scope :=
  [("pre", .base ⟨10⟩), ("x", .base ⟨7⟩), ("s", .base ⟨6⟩),
   ("$c4", .base ⟨4⟩)]
def cpEnv : LocalEnv :=
  [[("$forFirst", .base ⟨12⟩)], [("i", .base ⟨11⟩)], preScope, baseScope]
def cpEnv2 : LocalEnv := [] :: [] :: cpEnv
def callEnv : LocalEnv := [preScope, baseScope]

/-! ## Continuations — phase A -/

def sFrame0 : Cont := .frame [] [] [] [] .stop

/-- The continuation below the setup loop head. -/
def suHeadTail : Cont :=
  .seq [] suEnv
    (.seq [] [[("i", .base ⟨8⟩)], sxScope, baseScope]
      (.seq [sS5, sS6, sS7, sS8, sS9, sS10] [sxScope, baseScope] sFrame0))
def suHeadCfg : Config :=
  .exec (.while (.boolLit true) selSuBody) suEnv suHeadTail
def suLoopK : Cont := .loop (.boolLit true) selSuBody suEnv suHeadTail
/-- The setup body's store block (its 4th statement). -/
def suStoreBlk : Stmt :=
  .block #[]
    #[.seqn #[.assign (.var "x")
        (.add (.mul (.var "x") (.intLit 6364136223846793005 .uint64))
              (.intLit 1442695040888963407 .uint64))],
      .seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
        (.var "x")]]
def suCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: suEnv)
    (.seq [suStoreBlk] ([] :: suEnv) suLoopK)
def suRef (n : Nat) (iv : Int) : TargetRef :=
  .chain (sHandle n) [.int iv .uint64] [.index]
def suStTail : Cont :=
  .seq [] suEnv2 (.seq [] ([] :: suEnv) suLoopK)

def cpHeadTail : Cont :=
  .seq [] cpEnv
    (.seq [] [[("i", .base ⟨11⟩)], preScope, baseScope]
      (.seq [sS7, sS8, sS9, sS10] [preScope, baseScope] sFrame0))
def cpHeadCfg : Config :=
  .exec (.while (.boolLit true) selCpBody) cpEnv cpHeadTail
def cpLoopK : Cont := .loop (.boolLit true) selCpBody cpEnv cpHeadTail
def cpStoreBlk : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "pre") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cpCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cpEnv)
    (.seq [cpStoreBlk] ([] :: cpEnv) cpLoopK)
def cpRef (civ : Int) : TargetRef :=
  .chain (.addr (.base ⟨10⟩)) [.int civ .uint64] [.index]
def cpStTail : Cont :=
  .seq [] cpEnv2 (.seq [] ([] :: cpEnv) cpLoopK)
def cpRhsK (civ : Int) : Cont :=
  .rhsK .vals [cpRef civ] [] [] (.seqn #[]) cpEnv2 cpStTail

/-! ## The call boundary and the subject frame -/

def sAfterCallK : Cont := .seq [sS8, sS9, sS10] callEnv sFrame0
def sCallArgsK : Cont :=
  .callArgsK ⟨"selectionSort"⟩ [] [] [] callEnv sAfterCallK
def sSubjFrameK : Cont := .frame [] callEnv [] [] sAfterCallK
def sFrameEnv : LocalEnv := [[("s", .base ⟨13⟩)]]

/-! ## Environments and continuations — the subject (canonical) -/

def envO : LocalEnv :=
  [[("$forFirst", .base ⟨15⟩)], [("i", .base ⟨14⟩)], [],
   [("s", .base ⟨13⟩)]]
def headTailO : Cont :=
  .seq [] envO
    (.seq [] [[("i", .base ⟨14⟩)], [], [("s", .base ⟨13⟩)]]
      (.seq [] [[], [("s", .base ⟨13⟩)]] sSubjFrameK))
def outerHeadCfg : Config :=
  .exec (.while (.boolLit true) selOuterWhileBody) envO headTailO
def loopKO : Cont := .loop (.boolLit true) selOuterWhileBody envO headTailO
def outerCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envO)
    (.seq [selPassBlock] ([] :: envO) loopKO)
/-- The `len(s)` apply point of the OUTER exit test. -/
def lenKO (iv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] ([] :: envO)
    (.strictK .lessCmp [.int iv .int] [] ([] :: envO) outerCmpK)

def envI : LocalEnv :=
  [("$forFirst", .base ⟨18⟩)] :: [("j", .base ⟨17⟩)]
    :: [("m", .base ⟨16⟩)] :: [] :: envO
def innerTail : Cont :=
  .seq [] envI
    (.seq [] ([("j", .base ⟨17⟩)] :: [("m", .base ⟨16⟩)] :: [] :: envO)
      (.seq [selSwapSeqn] ([("m", .base ⟨16⟩)] :: [] :: envO)
        (.seq [] ([] :: envO) loopKO)))
def innerHeadCfg : Config :=
  .exec (.while (.boolLit true) selInnerWhileBody) envI innerTail
def loopKI : Cont := .loop (.boolLit true) selInnerWhileBody envI innerTail
def innerCmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: envI)
    (.seq [selMIfBlock] ([] :: envI) loopKI)
/-- The `len(s)` apply point of the INNER exit test. -/
def lenKI (jv : Int) : Cont :=
  .strictK (.lengthOf (some (.slice tU64))) [] [] ([] :: envI)
    (.strictK .lessCmp [.int jv .int] [] ([] :: envI) innerCmpK)

def envB2 : LocalEnv := [] :: [] :: envI
/-- The `if s[j] < s[m]` delivery continuation. -/
def mIfK : Cont :=
  .ifK (.block #[] #[.seqn #[.assign (.var "m") (.var "j")]]) (.seqn #[])
    envB2 (.seq [] envB2 (.seq [] ([] :: envI) loopKI))
/-- The `s[j]` read's apply point (the `s[m]` read still pending). -/
def idx1K (n : Nat) : Cont :=
  .strictK .indexGet [sHandle n] [] envB2
    (.strictK .lessCmp [] [.indexGet (.var "s") (.var "m")] envB2 mIfK)
/-- The `s[m]` read's apply point (`s[j]`'s value banked). -/
def idx2K (n : Nat) (a : Int) : Cont :=
  .strictK .indexGet [sHandle n] [] envB2
    (.strictK .lessCmp [.int a .uint64] [] envB2 mIfK)

/-! ## The swap's continuations -/

def envSw : LocalEnv := [("m", .base ⟨16⟩)] :: [] :: envO
def swTail : Cont := .seq [] envSw (.seq [] ([] :: envO) loopKO)
def refIdx (n : Nat) (idx : Int) : TargetRef :=
  .chain (sHandle n) [.int idx .int] [.index]
/-- Both targets resolved, the FIRST right-hand side (`s[m]`) pending. -/
def swRhsK1 (n : Nat) (iv mv : Int) : Cont :=
  .rhsK .vals [refIdx n iv, refIdx n mv] []
    [.indexGet (.var "s") (.var "i")] (.seqn #[]) envSw swTail
/-- The first value banked, the SECOND right-hand side (`s[i]`)
pending. -/
def swRhsK2 (n : Nat) (iv mv : Int) (wm : GoValue) : Cont :=
  .rhsK .vals [refIdx n iv, refIdx n mv] [wm] [] (.seqn #[]) envSw swTail

/-! ## Environments and continuations — the post phase (canonical) -/

def postScope : Scope :=
  [("post", .base ⟨16⟩), ("pre", .base ⟨10⟩), ("x", .base ⟨7⟩),
   ("s", .base ⟨6⟩), ("$c4", .base ⟨4⟩)]
def cp2Env : LocalEnv :=
  [[("$forFirst", .base ⟨18⟩)], [("i", .base ⟨17⟩)], postScope, baseScope]
def cp2Env2 : LocalEnv := [] :: [] :: cp2Env

def cp2HeadTail : Cont :=
  .seq [] cp2Env
    (.seq [] [[("i", .base ⟨17⟩)], postScope, baseScope]
      (.seq [sS10] [postScope, baseScope] sFrame0))
def cp2HeadCfg : Config :=
  .exec (.while (.boolLit true) selCp2Body) cp2Env cp2HeadTail
def cp2LoopK : Cont := .loop (.boolLit true) selCp2Body cp2Env cp2HeadTail
def cp2StoreBlk : Stmt :=
  .block #[]
    #[.seqn #[.assign (.addr (.indexAddr (.ref "post") (.var "i")))
        (.indexGet (.var "s") (.var "i"))]]
def cp2CmpK : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: cp2Env)
    (.seq [cp2StoreBlk] ([] :: cp2Env) cp2LoopK)
def cp2Ref (civ : Int) : TargetRef :=
  .chain (.addr (.base ⟨16⟩)) [.int civ .uint64] [.index]
def cp2StTail : Cont :=
  .seq [] cp2Env2 (.seq [] ([] :: cp2Env) cp2LoopK)
def cp2RhsK (civ : Int) : Cont :=
  .rhsK .vals [cp2Ref civ] [] [] (.seqn #[]) cp2Env2 cp2StTail

/-- The epilogue's `$res0`/`$res1` target refs. -/
def res0Ref : TargetRef := .chain (.addr (.base ⟨2⟩)) [] []
def res1Ref : TargetRef := .chain (.addr (.base ⟨3⟩)) [] []
/-- After the `$res0` store: `$res1 = post; return`. -/
def epiTail : Cont :=
  .seq [.assign (.var "$res1") (.var "post"), .returnStmt]
    [postScope, baseScope] sFrame0
/-- After the `$res1` store: `return`. -/
def epiTail2 : Cont := .seq [.returnStmt] [postScope, baseScope] sFrame0

/-! ## Heap fronts — the subject and the post phase (canonical)

The parked phase-A values are baked in: `x` at the final LCG iterate,
the setup and copy counters at `n`, both flags down, `pre` at the
padded family. -/

/-- The full 16-cell fixed front the subject phase sits on. -/
def hpSubj (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool) : Heap :=
  [(.base ⟨0⟩, su64 (n : Int)), (.base ⟨1⟩, su64 (seed : Int)),
   (.base ⟨2⟩, sArr8 zeros8), (.base ⟨3⟩, sArr8 zeros8),
   (.base ⟨4⟩, sHandleCell n), (.base ⟨5⟩, sBack n l),
   (.base ⟨6⟩, sHandleCell n),
   (.base ⟨7⟩, su64 ((lcgStep lcgA lcgB n seed : Nat) : Int)),
   (.base ⟨8⟩, su64 (n : Int)), (.base ⟨9⟩, sbool false),
   (.base ⟨10⟩, sArr8 (selPad8 (selFam n seed))),
   (.base ⟨11⟩, su64 (n : Int)), (.base ⟨12⟩, sbool false),
   (.base ⟨13⟩, sHandleCell n),
   (.base ⟨14⟩, sint iv), (.base ⟨15⟩, sbool ffv)]

/-- The tight OUTER state (canonical pass placement, `nextAddr 16`),
tail-parametric for the segments that never touch past cell 15. -/
def σOutT (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool)
    (tail : Heap) (na : Nat) : ExecState :=
  σS (hpSubj n seed l iv ffv ++ tail) na

def σOut (n seed : Nat) (l : List Int) (iv : Int) (ffv : Bool) :
    ExecState :=
  σOutT n seed l iv ffv [] 16

/-- The tight IN-PASS state: `m` at 16, `j` at 17, the inner flag at
18, `nextAddr 19`. The outer flag is down throughout a pass. -/
def σIn (n seed : Nat) (l : List Int) (iv mv jv : Int) (ffIv : Bool) :
    ExecState :=
  σOutT n seed l iv false
    [(.base ⟨16⟩, sint mv), (.base ⟨17⟩, sint jv),
     (.base ⟨18⟩, sbool ffIv)] 19

/-- The post phase's state: `post` prefix `lq` at 16, copy counter at
17, flag at 18 (canonical placement, `nextAddr 19`). -/
def σPost (n seed : Nat) (l : List Int) (iv : Int) (lq : List Int)
    (civ : Int) (ffv : Bool) : ExecState :=
  σOutT n seed l iv false
    [(.base ⟨16⟩, sArr8 lq), (.base ⟨17⟩, su64 civ),
     (.base ⟨18⟩, sbool ffv)] 19

/-- After the `$res0 = pre` store. -/
def σRes0 (n seed : Nat) (l : List Int) (iv : Int) (lq : List Int) :
    ExecState :=
  σS ([(.base ⟨0⟩, su64 (n : Int)), (.base ⟨1⟩, su64 (seed : Int)),
       (.base ⟨2⟩, sArr8 (selPad8 (selFam n seed))),
       (.base ⟨3⟩, sArr8 zeros8),
       (.base ⟨4⟩, sHandleCell n), (.base ⟨5⟩, sBack n l),
       (.base ⟨6⟩, sHandleCell n),
       (.base ⟨7⟩, su64 ((lcgStep lcgA lcgB n seed : Nat) : Int)),
       (.base ⟨8⟩, su64 (n : Int)), (.base ⟨9⟩, sbool false),
       (.base ⟨10⟩, sArr8 (selPad8 (selFam n seed))),
       (.base ⟨11⟩, su64 (n : Int)), (.base ⟨12⟩, sbool false),
       (.base ⟨13⟩, sHandleCell n),
       (.base ⟨14⟩, sint iv), (.base ⟨15⟩, sbool false),
       (.base ⟨16⟩, sArr8 lq), (.base ⟨17⟩, su64 (n : Int)),
       (.base ⟨18⟩, sbool false)]) 19

/-- The canonical TERMINAL state: both results delivered. -/
def σEnd (n seed : Nat) (l : List Int) (iv : Int) (lq : List Int) :
    ExecState :=
  σS ([(.base ⟨0⟩, su64 (n : Int)), (.base ⟨1⟩, su64 (seed : Int)),
       (.base ⟨2⟩, sArr8 (selPad8 (selFam n seed))),
       (.base ⟨3⟩, sArr8 lq),
       (.base ⟨4⟩, sHandleCell n), (.base ⟨5⟩, sBack n l),
       (.base ⟨6⟩, sHandleCell n),
       (.base ⟨7⟩, su64 ((lcgStep lcgA lcgB n seed : Nat) : Int)),
       (.base ⟨8⟩, su64 (n : Int)), (.base ⟨9⟩, sbool false),
       (.base ⟨10⟩, sArr8 (selPad8 (selFam n seed))),
       (.base ⟨11⟩, su64 (n : Int)), (.base ⟨12⟩, sbool false),
       (.base ⟨13⟩, sHandleCell n),
       (.base ⟨14⟩, sint iv), (.base ⟨15⟩, sbool false),
       (.base ⟨16⟩, sArr8 lq), (.base ⟨17⟩, su64 (n : Int)),
       (.base ⟨18⟩, sbool false)]) 19

/-! ## The entry equation -/

derive_entry_eq selsH_entry_eq selsortLowered selsortHarnessRFunc
  σSeed sHC₀

/-- The seed bridge: the macro-emitted state IS the phase-A start
front. -/
theorem σSeed_eq (nv sv : Int) : σSeed nv sv = σS (hp0 nv sv) 4 := by
  simp only [σSeed, σS, hp0, su64, sArr8, zeros8]
  rfl

/-! ## Heap-lookup facts (the conditioned steps' inputs) -/

theorem lookup_su5 (nv sv : Int) (n : Nat) (l : List Int) (xv iv : Int)
    (ffv : Bool) (na : Nat) :
    Heap.lookup (σS (hpSu nv sv n l xv iv ffv) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hpSu, hp0, σS, Heap.lookup]

theorem lookup_cp5 (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (σS (hpCp nv sv n l xv siv lp civ ffv) na).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hpCp, hpSu, hp0, σS, Heap.lookup]

theorem lookup_cp10 (nv sv : Int) (n : Nat) (l : List Int) (xv siv : Int)
    (lp : List Int) (civ : Int) (ffv : Bool) (na : Nat) :
    Heap.lookup (σS (hpCp nv sv n l xv siv lp civ ffv) na).heap
        (.base ⟨10⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lp.map (fun v => .int v .uint64)⟩⟩ := by
  simp [hpCp, hpSu, hp0, σS, Heap.lookup]

theorem lookup_σIn5 (n seed : Nat) (l : List Int) (iv mv jv : Int)
    (ffIv : Bool) :
    Heap.lookup (σIn n seed l iv mv jv ffIv).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := rfl

theorem lookup_σPost5 (n seed : Nat) (l : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ffv : Bool) :
    Heap.lookup (σPost n seed l iv lq civ ffv).heap (.base ⟨5⟩)
      = some ⟨some (.array n tU64),
          .array ⟨l.map (fun v => .int v .uint64)⟩⟩ := rfl

theorem lookup_σPost16 (n seed : Nat) (l : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ffv : Bool) :
    Heap.lookup (σPost n seed l iv lq civ ffv).heap (.base ⟨16⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨lq.map (fun v => .int v .uint64)⟩⟩ := by
  simp [σPost, σOutT, hpSubj, σS, Heap.lookup]

theorem lookup_σPost2 (n seed : Nat) (l : List Int) (iv : Int)
    (lq : List Int) (civ : Int) (ffv : Bool) :
    Heap.lookup (σPost n seed l iv lq civ ffv).heap (.base ⟨2⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := rfl

theorem lookup_σRes0_3 (n seed : Nat) (l : List Int) (iv : Int)
    (lq : List Int) :
    Heap.lookup (σRes0 n seed l iv lq).heap (.base ⟨3⟩)
      = some ⟨some (.array 8 tU64),
          .array ⟨zeros8.map (fun v => .int v .uint64)⟩⟩ := rfl

end GoLean.Examples.SelectionSort
