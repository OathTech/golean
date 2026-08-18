import GoLeanProofs.Examples.MatMulProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Sym.Refine

/-!
# MatMul — the `matmul` example (Gallery Campaign G1 unit G1.9;
COMPLETED by WP arc slice 4 phase 3, the chartered acceptance)

Go source: `Corpus/coverage/exec/examples/matmul/main.go` (11 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/matmul-lowered.repr`
and carried in `GoLeanProofs.Examples.MatMulProgram`.

The subject is the textbook triple loop `sum += a[i][k] * b[k][j]` over
`[3][3]uint64`, WRAPPING mod 2^64. The harness `matmul_harness_r(seed)`
is the S3 RELATIONAL shape: `a := seedMat(seed)` (`a[i][j] = seed +
(3i+j)`, wrapping), `b := seedMat(1)` (the CONSTANT matrix
`[[1,2,3],[4,5,6],[7,8,9]]`), and the observable is `(a, b, matMul(a,
b))` — the postcondition is a relation over the RETURNED DATA. Go
arrays are VALUES (copied on call and return), which is why this 2-D
example fits the pass-by-value fragment with no cap workaround; it is
the gallery's FIRST 2-D example.

THE HEADLINE (`matmul_ok`) is stated HERE, in the root, so the
aggregator's `import GoLeanProofs.Examples.MatMul` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

## Proof shape (no loop induction) — and the GAP-RFL-COST closure

All three loop bounds are the compile-time constant `matN = 3`, so the
control flow is fully concrete and the run is a straight line of
EXACTLY 5247 steps at every seed; only the seed-derived DATA is
symbolic. The proof is a chain of per-window segments over
scalar-parameterized heap fronts (every index concrete, every value an
opaque `Int`), split only to bound elaboration cost, plus the three
`enterFrame` facts (the only program-consulting steps, the only places
`matmulLowered` unfolds outside the pins and the entry equation).

HISTORY: this module is the artifact that DISCOVERED the GAP-RFL-COST
class (gallery campaign, `docs/gallery-campaign-log/g1.md` unit G1.9):
as an all-`with_unfolding_all rfl` segment layer it was withdrawn
unelaborated — store-class segments measured 61–326 s each, one hit
the 16M-heartbeat `whnf` ceiling, and three whole-file elaborations
were cut at 57–114 min. Landing it produced TWO closures, both
recorded in `docs/wp-arc-log/s4.md` unit S4.11:

* **The chartered one** — the three measured blocker segments (the
  291-step `seedMat(seed)` outer iterations, 61.4 s each re-measured
  at this tree) are discharged through the mirror symbolic evaluator
  (`symEvalWindow_refines'`, WP arc slice 4 — the mirror-layer
  section below) at ~1.3 s each, statements byte-identical.
* **The root cause** — the class was a MetaM SMART-UNFOLDING
  pathology, found while landing this file: under
  `set_option smartUnfolding false` (file-level below) the same
  291-step raw `rfl` takes 1.09 s, and every other window is
  seconds-scale raw. The kernel re-checked these proofs in
  milliseconds all along; only the elaborator stormed. The evaluator
  remains the general lever (it is also what a `derive_seg` emission
  path needs), but the measured blocker here was an elaborator
  configuration, and this file says so rather than crediting the
  evaluator with the whole win.

The closure record is g1.md unit G1.9 (marked CLOSED).

The machine's nested-array store is captured by `mmSet` (measured
against the interpreter, not assumed): a store to `m[i][j]` normalizes
the written leaf THREE extra times (row-level `coerceStoredValue`,
matrix-level `coerceStoredValue` over the replaced row, cell-level
`normalizeValueForTy`) and every other slot once or twice — `mmSet`
IS that composite, so the segment right-hand sides are checked by
the transported windows (and the remaining `rfl` segments) rather than
by hand-counted normalize depths.
-/

namespace GoLean.Examples.MatMul

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface
open GoLean.SliceMem
open GoLean.Sym (SymInt SymBool SymValue SymHeapCell SymHeap SymState
  SymCont SymConfig Valuation symEvalWindow symEvalWindow_refines'
  γS γC)

set_option maxRecDepth 4000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
-- GAP-RFL-COST root cause (WP arc slice 4 phase 3, 2026-08-18): the
-- 61–326 s / never-terminating `with_unfolding_all rfl` segments that
-- kept this module out of the gallery were a MetaM SMART-UNFOLDING
-- pathology, not intrinsic term-growth cost — the kernel always
-- re-checked the same proofs in milliseconds. Under this option the
-- worst measured segment (291 steps, 61.4 s default) elaborates in
-- 1.09 s. Elaboration-performance only; the kernel is untouched.
-- Record: docs/wp-arc-log/s4.md unit S4.11.
set_option smartUnfolding false

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def matmulHarnessRFunc : Func :=
{ id := { key := "matmul_harness_r" },
  args := #[{ id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0",
                 typ := GoLean.GoCore.Ty.array
                          3
                          (GoLean.GoCore.Ty.array
                            3
                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
               { id := "$res1",
                 typ := GoLean.GoCore.Ty.array
                          3
                          (GoLean.GoCore.Ty.array
                            3
                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
               { id := "$res2",
                 typ := GoLean.GoCore.Ty.array
                          3
                          (GoLean.GoCore.Ty.array
                            3
                            (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "a",
                      typ := GoLean.GoCore.Ty.array
                               3
                               (GoLean.GoCore.Ty.array
                                 3
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "a"]
                    { key := "seedMat" }
                    #[GoLean.GoCore.Expr.var "seed"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "b",
                      typ := GoLean.GoCore.Ty.array
                               3
                               (GoLean.GoCore.Ty.array
                                 3
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "b"]
                    { key := "seedMat" }
                    #[GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c8",
                      typ := GoLean.GoCore.Ty.array
                               3
                               (GoLean.GoCore.Ty.array
                                 3
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c8"]
                    { key := "matMul" }
                    #[GoLean.GoCore.Expr.var "a", GoLean.GoCore.Expr.var "b"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "a"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res1")
                    (GoLean.GoCore.Expr.var "b"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res2")
                    (GoLean.GoCore.Expr.var "$c8"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem matmulHarnessRFunc_pin :
    findFunctionIn? matmulLowered.funcs ⟨"matmul_harness_r"⟩
    = some matmulHarnessRFunc := rfl

/-! ## The statement vocabulary -/

/-- Matrix entry lookup on the row-list representation. -/
def mmGet (m : List (List Int)) (i j : Nat) : Int := (m.getD i []).getD j 0

/-- The OBVIOUS triple-loop matrix product, each entry the mathematical
sum `Σₖ aᵢₖ·bₖⱼ` reduced ONCE mod 2^64. A reader can check it against the
Go loop by eye. -/
def matSpec (a b : List (List Int)) : List (List Int) :=
  (List.range 3).map (fun i =>
    (List.range 3).map (fun j =>
      ((List.range 3).map (fun l => mmGet a i l * mmGet b l j)).sum
        % (2 ^ 64 : Int)))

/-- The returned `[3][3]uint64` as a `GoValue`: a nested array, three rows
of three. Deliberately NOT shared with any other example's array builder
(the §11 closure rule). -/
def mmArr3 (m : List (List Int)) : GoValue :=
  .array ⟨m.map (fun row => GoValue.array ⟨row.map (fun v => .int v .uint64)⟩)⟩

/-! ## Type abbreviations and the two subject `Func`s -/

abbrev tU64 : Ty := .int .uint64
abbrev tRow : Ty := .array 3 tU64
abbrev tMat : Ty := .array 3 tRow

/-! ### `seedMat`, verbatim from the pinned lowering (readable form) -/

def smStore : Stmt :=
  .seqn #[.assign
    (.addr (.indexAddr (.indexAddr (.ref "m") (.var "i")) (.var "j")))
    (.add (.var "seed")
      (.convert tU64 (.add (.mul (.var "i") (.intLit 3 .int)) (.var "j"))))]
def smInnerFill : Stmt := .block #[] #[smStore]
def smInnerBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j") (.add (.var "j") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "j") (.intLit 3 .int))
        (.seqn #[]) .breakStmt,
      smInnerFill]
def smInnerLoop : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "j", typ := .int .int },
              .assign (.var "j") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) smInnerBody]]
def smOuterFill : Stmt := .block #[] #[smInnerLoop]
def smOuterBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.intLit 3 .int))
        (.seqn #[]) .breakStmt,
      smOuterFill]
def smT1 : Stmt := .seqn #[.initialization { id := "m", typ := tMat }]
def smT2 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) smOuterBody]]
def smT3 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "m"), .returnStmt]

/-- The `seedMat` subject `Func`, verbatim from the pinned lowering. -/
def seedMatFunc : Func :=
  { id := { key := "seedMat" },
    args := #[{ id := "seed", typ := tU64 }],
    results := #[{ id := "$res0", typ := tMat }],
    body := .block #[] #[smT1, smT2, smT3],
    variadic := false,
    wrapper := false }

/-- The `seedMat` subject pin. -/
theorem seedMat_pin :
    findFunctionIn? matmulLowered.funcs ⟨"seedMat"⟩ = some seedMatFunc := rfl

/-! ### `matMul`, verbatim from the pinned lowering (readable form) -/

def mmKFill : Stmt :=
  .block #[]
    #[.assign (.var "sum")
      (.add (.var "sum")
        (.mul (.indexGet (.indexGet (.var "a") (.var "i")) (.var "k"))
          (.indexGet (.indexGet (.var "b") (.var "k")) (.var "j"))))]
def mmKBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "k") (.add (.var "k") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "k") (.intLit 3 .int))
        (.seqn #[]) .breakStmt,
      mmKFill]
def mmCStore : Stmt :=
  .seqn #[.assign
    (.addr (.indexAddr (.indexAddr (.ref "c") (.var "i")) (.var "j")))
    (.var "sum")]
def mmJFill : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "sum", typ := tU64 }],
      .block #[]
        #[.seqn #[.initialization { id := "k", typ := .int .int },
                  .assign (.var "k") (.intLit 0 .int)],
          .block #[]
            #[.initialization { id := "$forFirst", typ := .bool },
              .assign (.var "$forFirst") (.boolLit true),
              .while (.boolLit true) mmKBody]],
      mmCStore]
def mmJBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "j") (.add (.var "j") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "j") (.intLit 3 .int))
        (.seqn #[]) .breakStmt,
      mmJFill]
def mmJLoop : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "j", typ := .int .int },
              .assign (.var "j") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) mmJBody]]
def mmOuterFill : Stmt := .block #[] #[mmJLoop]
def mmOuterBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i") (.add (.var "i") (.intLit 1 .int))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.intLit 3 .int))
        (.seqn #[]) .breakStmt,
      mmOuterFill]
def mmT1 : Stmt := .seqn #[.initialization { id := "c", typ := tMat }]
def mmT2 : Stmt :=
  .block #[]
    #[.seqn #[.initialization { id := "i", typ := .int .int },
              .assign (.var "i") (.intLit 0 .int)],
      .block #[]
        #[.initialization { id := "$forFirst", typ := .bool },
          .assign (.var "$forFirst") (.boolLit true),
          .while (.boolLit true) mmOuterBody]]
def mmT3 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "c"), .returnStmt]

/-- The `matMul` subject `Func`: the textbook triple loop, verbatim from
the pinned lowering. -/
def matMulFunc : Func :=
  { id := { key := "matMul" },
    args := #[{ id := "a", typ := tMat }, { id := "b", typ := tMat }],
    results := #[{ id := "$res0", typ := tMat }],
    body := .block #[] #[mmT1, mmT2, mmT3],
    variadic := false,
    wrapper := false }

/-- The `matMul` subject pin. -/
theorem matMul_pin :
    findFunctionIn? matmulLowered.funcs ⟨"matMul"⟩ = some matMulFunc := rfl

/-! ### The harness body's top-level statement pieces -/

def hS2 : Stmt :=
  .seqn #[.initialization { id := "b", typ := tMat },
          .call #[.var "b"] ⟨"seedMat"⟩ #[.intLit 1 .uint64]]
def hS3 : Stmt :=
  .seqn #[.initialization { id := "$c8", typ := tMat },
          .call #[.var "$c8"] ⟨"matMul"⟩ #[.var "a", .var "b"]]
def hS4 : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "a"),
          .assign (.var "$res1") (.var "b"),
          .assign (.var "$res2") (.var "$c8"),
          .returnStmt]

/-! ## Proof vocabulary: the machine's value shapes

`un` is one uint64 normalization; `mmSet` is the machine's OBSERVED
nested-array store composite (`arraySet`'s `coerceStoredValue` at row
and matrix level plus the cell-level `normalizeValueForTy` — verified
by the `rfl` segments below, never assumed); `mmNorm` is one
whole-matrix normalization (a plain `var`-target store of a matrix);
`mmAcc` is one k-iteration of the subject's accumulator cell (multiply
wrapped, sum wrapped, cell store wrapped). -/

abbrev un (v : Int) : Int := IntKind.normalize .uint64 v

/-- `k`-fold iterated uint64 normalization (the segment right-hand
sides' compact spelling for the machine's normalize nests). -/
def unn : Nat → Int → Int
  | 0, v => v
  | k + 1, v => un (unn k v)

/-- One whole-matrix value normalization (matrix store to a `var`
target, `bindParams`, frame write-back). -/
def mmNorm (M : List (List Int)) : List (List Int) :=
  M.map (fun r => r.map un)

/-- The machine's nested-array store `m[i][j] = w`: the written leaf is
normalized at row-`coerce`, then the whole replaced row at
matrix-`coerce`, then everything at the cell's declared type. -/
def mmSet (M : List (List Int)) (i j : Nat) (w : Int) : List (List Int) :=
  (M.set i (((M.getD i []).set j (un w)).map un)).map (fun r => r.map un)

/-- One k-iteration of the subject's accumulator CELL:
`sum = un(un(sum + un(p·q)))` — the multiply wraps, the add wraps, and
the store into the uint64 cell wraps once more. -/
def mmAcc (s p q : Int) : Int := un (un (s + un (p * q)))

/-! ## Heap-cell and state forms -/

abbrev uCell (v : Int) : HeapCell := ⟨some tU64, .int v .uint64⟩
abbrev iCell (v : Int) : HeapCell := ⟨some (.int .int), .int v .int⟩
abbrev bCell (b : Bool) : HeapCell := ⟨some .bool, .bool b⟩
abbrev mCell (v : GoValue) : HeapCell := ⟨some tMat, v⟩

abbrev zRowL : List Int := [0, 0, 0]
abbrev zMatL : List (List Int) := [zRowL, zRowL, zRowL]
abbrev zMatV : GoValue := mmArr3 zMatL
abbrev bMatL : List (List Int) := [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
abbrev bMatV : GoValue := mmArr3 bMatL

/-- The pinned program as an empty-heap state — with the entry equation
and the three `enterFrame` facts, the only places this module carries
`matmulLowered` outside the pins. -/
def mmProg : ExecState :=
  { types := matmulLowered.typeDefs.toList,
    functions := matmulLowered.funcs,
    methods := matmulLowered.methods,
    heap := [], nextAddr := 0 }

/-- The PROGRAM-generic state form. -/
abbrev mmSt (σ : ExecState) (H : Heap) (na : Nat) : ExecState :=
  { σ with heap := H, nextAddr := na }

/-! ## Address layout

Probe-measured at `seed = 700001` (`.tmp/mmprobe.lean` traced every
`nextAddr` bump; every raw segment below re-checks the transcription by
`rfl`):

```
0 = seed        1 = $res0 ([3][3])  2 = $res1  3 = $res2
4 = harness a
-- seedMat(seed) frame --
5 = seed param  6 = its $res0  7 = m  8 = i  9 = $forFirst
10/11, 12/13, 14/15 = per-outer-iteration inner j / $forFirst pairs
16 = harness b
-- seedMat(1) frame --
17 = seed param 18 = its $res0 19 = m 20 = i 21 = $forFirst
22/23, 24/25, 26/27 = inner j / $forFirst pairs
28 = harness $c8
-- matMul frame --
29 = a param    30 = b param   31 = its $res0
32 = c  33 = i  34 = $forFirst
35/36, 46/47, 57/58 = per-outer-iteration j / $forFirst pairs
37-39, 40-42, 43-45, 48-50, 51-53, 54-56, 59-61, 62-64, 65-67
  = per-(i,j) sum / k / $forFirst triples
-- nextAddr = 68 at the driver terminal --
```
-/

def baseEnvM : Scope :=
  [("$res2", .base ⟨3⟩), ("$res1", .base ⟨2⟩), ("$res0", .base ⟨1⟩),
   ("seed", .base ⟨0⟩)]
def mmStop : Cont := .frame [] [] [] [] .stop
def envA : LocalEnv := [[("a", .base ⟨4⟩)], baseEnvM]
def envB : LocalEnv := [[("b", .base ⟨16⟩), ("a", .base ⟨4⟩)], baseEnvM]
def envC : LocalEnv :=
  [[("$c8", .base ⟨28⟩), ("b", .base ⟨16⟩), ("a", .base ⟨4⟩)], baseEnvM]

/-! ## The symbolic mirror layer (WP arc slice 4, phase 3)

The three 291-step `seedMat(seed)` outer-iteration segments below —
the segments the campaign MEASURED as the GAP-RFL-COST blockers
(61–326 s each under default elaboration; the withdrawal record is
g1.md unit G1.9) — are discharged through **`symEvalWindow_refines'`**
(`Sym/Refine.lean`, THE REFINEMENT THEOREM's projection corollary):
a compiled `#guard` of the window's step count (the
#eval-before-decide rule), one kernel `rfl` on the count projection,
the refinement theorem, and a defeq `exact` landing on the statement's
own spelling. Statements are BYTE-IDENTICAL to the withdrawn,
probe-confirmed raw forms; only the proofs changed. The fixtures
mirror the concrete heap front and continuations 1:1 — symbolic
scalars as `.var i` (symbol table below), program syntax and
environments shared verbatim with the concrete definitions. Every
other window stays raw `rfl` (cheap once the smart-unfolding
pathology is off — the two-stage cost record is
`docs/wp-arc-log/s4.md` unit S4.11). -/

def sUCell (t : SymInt) : SymHeapCell := .mk (some tU64) (.int t .uint64)
def sICell (t : SymInt) : SymHeapCell := .mk (some (.int .int)) (.int t .int)
def sBCell (b : SymBool) : SymHeapCell := .mk (some .bool) (.bool b)
def sMCell (v : SymValue) : SymHeapCell := .mk (some tMat) v
def sArr3 (m : List (List SymInt)) : SymValue :=
  .array ⟨m.map fun r => .array ⟨r.map (.int · .uint64)⟩⟩
def sZMat : SymValue := sArr3 [[.lit 0, .lit 0, .lit 0],
  [.lit 0, .lit 0, .lit 0], [.lit 0, .lit 0, .lit 0]]
def sDead (j ff : Nat) : SymHeap :=
  [(.base ⟨j⟩, sICell (.lit 3)), (.base ⟨ff⟩, sBCell (.lit false))]

/-- The window valuation: symbol `i` reads slot `i` of the binder
list (missing slots default to `0`/`.nil` and are never read by the
window). -/
def mkρ (is : List Int) (vs : List GoValue) : Valuation where
  ints := fun i => is.getD i 0
  bools := fun _ => false
  vals := fun i => vs.getD i .nil
  cells := fun _ => ⟨none, .nil⟩

/-! ## The entry equation

Written BY HAND: the `derive_entry_eq` macro fails closed on this
harness (its quoter covers one aggregate level over scalars, and these
results are `[3][3]uint64` — a NESTED aggregate; recorded kit gap).
The layout rule it would have used: parameter cells at addresses
`0…p−1` in `bindParams` order; result cells at `p…p+r−1` at their
`defaultValue`s in `allocDecls` order; ONE scope in
reverse-declaration order. -/

def mmHeap0 (sv : Int) : Heap :=
  [(.base ⟨0⟩, uCell sv), (.base ⟨1⟩, mCell zMatV),
   (.base ⟨2⟩, mCell zMatV), (.base ⟨3⟩, mCell zMatV)]

def mmSeed (seed : Int) : ExecState := mmSt mmProg (mmHeap0 seed) 4

def mmC0 : Config :=
  Config.exec matmulHarnessRFunc.body
    [[("$res2", Loc.base ⟨3⟩), ("$res1", Loc.base ⟨2⟩), ("$res0", Loc.base ⟨1⟩),
      ("seed", Loc.base ⟨0⟩)]]
    (Cont.frame [] [] [] [] Cont.stop)

theorem mm_entry_eq (seed : Int) (fuel : Nat) (ch : Choices) :
    runFunctionWithContextM fuel matmulLowered.typeDefs.toList matmulLowered.funcs
        matmulHarnessRFunc #[.int seed .uint64] matmulLowered.methods ch
      = (do
          let r ← runConfig fuel (mmSeed (IntKind.uint64.normalize seed)) mmC0 ch
          let vs ← loadMany r.fst [Loc.base ⟨1⟩, Loc.base ⟨2⟩, Loc.base ⟨3⟩]
          pure { values := vs.toArray }) := by
  with_unfolding_all rfl

/-! ## Phase 0: harness entry (cells 0–4) -/

def mmHeapA (sv : Int) : Heap :=
  mmHeap0 sv ++ [(.base ⟨4⟩, mCell zMatV)]

/-- The seedMat(seed) call point: seed argument delivered. -/
def call1K : Cont :=
  .callArgsK ⟨"seedMat"⟩ [(.chain [], [.ref "a"])] [] [] envA
    (.seq [hS2, hS3, hS4] envA mmStop)

/-- E1: entry → the `seedMat(seed)` call point. 8 steps. -/
theorem mm_E1_raw (σ : ExecState) (sv : Int) (ch : Choices) :
    stepFnIter 8 (mmSt σ (mmHeap0 sv) 4) mmC0 ch
      = .ok (.retV (.int sv .uint64) call1K, mmSt σ (mmHeapA sv) 5, ch) := by
  with_unfolding_all rfl

def mmHeapSM1 (sv svp : Int) : Heap :=
  mmHeapA sv ++ [(.base ⟨5⟩, uCell svp), (.base ⟨6⟩, mCell zMatV)]

/-- `enterFrame` fact 1 (program-consulting; at the pinned program). -/
theorem mm_enterFrame1 (sv svp : Int) :
    enterFrame (mmSt mmProg (mmHeapA sv) 5) ⟨"seedMat"⟩ [.int svp .uint64]
      = .ok (seedMatFunc, [[("$res0", Loc.base ⟨6⟩), ("seed", Loc.base ⟨5⟩)]],
          [.base ⟨6⟩],
          mmSt mmProg (mmHeapSM1 sv (IntKind.uint64.normalize svp)) 7) := by
  with_unfolding_all rfl

/-! ## Phase 1: `seedMat(seed)` (cells 5–15)

Environments and continuations transcribed from the probe dumps at
steps 68/126/156 and re-checked by the segments' `rfl`s. -/

def smBase1 : Scope := [("$res0", .base ⟨6⟩), ("seed", .base ⟨5⟩)]
def smEnv4 : LocalEnv :=
  [[("$forFirst", .base ⟨9⟩)], [("i", .base ⟨8⟩)], [("m", .base ⟨7⟩)], smBase1]
def smEnv5 : LocalEnv := [] :: smEnv4
def smFrameK1 : Cont :=
  .frame [(.chain [], [.ref "a"])] envA [.base ⟨6⟩] []
    (.seq [hS2, hS3, hS4] envA mmStop)
def smHeadTail1 : Cont :=
  .seq [] smEnv4
    (.seq [] [[("i", .base ⟨8⟩)], [("m", .base ⟨7⟩)], smBase1]
      (.seq [smT3] [[("m", .base ⟨7⟩)], smBase1] smFrameK1))
def smLoopK1 : Cont := .loop (.boolLit true) smOuterBody smEnv4 smHeadTail1
def smCmpK1 : Cont :=
  .ifK (.seqn #[]) .breakStmt smEnv5 (.seq [smOuterFill] smEnv5 smLoopK1)

/-- Phase-1 front: cells 0–9 (matrix and counters symbolic). -/
def smHeap1 (sv sp : Int) (m : GoValue) (iv : Int) (ff : Bool) : Heap :=
  mmHeapA sv
    ++ [(.base ⟨5⟩, uCell sp), (.base ⟨6⟩, mCell zMatV),
        (.base ⟨7⟩, mCell m), (.base ⟨8⟩, iCell iv), (.base ⟨9⟩, bCell ff)]

/-- A retired inner-loop cell pair (`j = 3`, `$forFirst = false`). -/
def smDead (j ff : Nat) : Heap := [(.base ⟨j⟩, iCell 3), (.base ⟨ff⟩, bCell false)]

/-! ### sm1 mirror fixtures (symbols: ints 0 = sv, 1 = sp, 2–10 = x0–x8) -/

def symFrameK1 : SymCont :=
  .frame [(.chain [], [.ref "a"])] envA [.base ⟨6⟩] []
    (.seq [hS2, hS3, hS4] envA (.frame [] [] [] [] .stop))
def symHeadTail1 : SymCont :=
  .seq [] smEnv4
    (.seq [] [[("i", .base ⟨8⟩)], [("m", .base ⟨7⟩)], smBase1]
      (.seq [smT3] [[("m", .base ⟨7⟩)], smBase1] symFrameK1))
def symLoopK1 : SymCont := .loop (.boolLit true) smOuterBody smEnv4 symHeadTail1
def symCmpK1 : SymCont :=
  .ifK (.seqn #[]) .breakStmt smEnv5 (.seq [smOuterFill] smEnv5 symLoopK1)

def symHeap1 (m : SymValue) (ivT : SymInt) : SymHeap :=
  [(.base ⟨0⟩, sUCell (.var 0)), (.base ⟨1⟩, sMCell sZMat),
   (.base ⟨2⟩, sMCell sZMat), (.base ⟨3⟩, sMCell sZMat),
   (.base ⟨4⟩, sMCell sZMat),
   (.base ⟨5⟩, sUCell (.var 1)), (.base ⟨6⟩, sMCell sZMat),
   (.base ⟨7⟩, sMCell m), (.base ⟨8⟩, sICell ivT),
   (.base ⟨9⟩, sBCell (.lit false))]
def symXMat1 : SymValue := sArr3
  [[.var 2, .var 3, .var 4], [.var 5, .var 6, .var 7], [.var 8, .var 9, .var 10]]

/-- SM1 entry: frame body → the first outer test delivered. 59 steps. -/
theorem sm1_E_raw (σ : ExecState) (sv svp : Int) (ch : Choices) :
    stepFnIter 59 (mmSt σ (mmHeapSM1 sv svp) 7)
      (.exec seedMatFunc.body [[("$res0", Loc.base ⟨6⟩), ("seed", Loc.base ⟨5⟩)]]
        smFrameK1) ch
      = .ok (.retV (.bool true) smCmpK1,
          mmSt σ (smHeap1 sv svp zMatV 0 false) 10, ch) := by
  with_unfolding_all rfl

-- Compiled-evaluation guard BEFORE the kernel rfl (#eval-before-decide).
#guard (symEvalWindow 291 (⟨symHeap1 symXMat1 (.lit 0), 10⟩ : SymState) (.retV (.bool (.lit true)) symCmpK1)).1 == 291

/-- SM1 outer iteration `i = 0` (row-0 stores, inner loop unrolled
inside the `rfl`). 291 steps. -/
theorem sm1_I0_raw (σ : ExecState) (sv sp x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (ch : Choices) :
    stepFnIter 291
      (mmSt σ (smHeap1 sv sp (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]])
        0 false) 10)
      (.retV (.bool true) smCmpK1) ch
      = .ok (.retV (.bool true) smCmpK1,
          mmSt σ (smHeap1 sv sp
            (mmArr3 (mmSet (mmSet (mmSet
                [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]
                0 0 (un (sp + 0))) 0 1 (un (sp + 1))) 0 2 (un (sp + 2))))
            1 false ++ smDead 10 11) 12, ch) := by
  have ht := symEvalWindow_refines' (budget := 291) (n := 291)
    (S := (⟨symHeap1 symXMat1 (.lit 0), 10⟩ : SymState))
    (C := .retV (.bool (.lit true)) symCmpK1)
    (by with_unfolding_all rfl)
    (mkρ [sv, sp, x0, x1, x2, x3, x4, x5, x6, x7, x8] []) σ ch
  with_unfolding_all exact ht

-- Compiled-evaluation guard BEFORE the kernel rfl (#eval-before-decide).
#guard (symEvalWindow 291 (⟨symHeap1 symXMat1 (.lit 1) ++ sDead 10 11, 12⟩ : SymState) (.retV (.bool (.lit true)) symCmpK1)).1 == 291

/-- SM1 outer iteration `i = 1`. 291 steps. -/
theorem sm1_I1_raw (σ : ExecState) (sv sp x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (ch : Choices) :
    stepFnIter 291
      (mmSt σ (smHeap1 sv sp (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]])
        1 false ++ smDead 10 11) 12)
      (.retV (.bool true) smCmpK1) ch
      = .ok (.retV (.bool true) smCmpK1,
          mmSt σ (smHeap1 sv sp
            (mmArr3 (mmSet (mmSet (mmSet
                [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]
                1 0 (un (sp + 3))) 1 1 (un (sp + 4))) 1 2 (un (sp + 5))))
            2 false ++ smDead 10 11 ++ smDead 12 13) 14, ch) := by
  have ht := symEvalWindow_refines' (budget := 291) (n := 291)
    (S := (⟨symHeap1 symXMat1 (.lit 1) ++ sDead 10 11, 12⟩ : SymState))
    (C := .retV (.bool (.lit true)) symCmpK1)
    (by with_unfolding_all rfl)
    (mkρ [sv, sp, x0, x1, x2, x3, x4, x5, x6, x7, x8] []) σ ch
  with_unfolding_all exact ht

-- Compiled-evaluation guard BEFORE the kernel rfl (#eval-before-decide).
#guard (symEvalWindow 291 (⟨symHeap1 symXMat1 (.lit 2) ++ sDead 10 11 ++ sDead 12 13, 14⟩ : SymState) (.retV (.bool (.lit true)) symCmpK1)).1 == 291

/-- SM1 outer iteration `i = 2` (the exit test delivers `false`). 291
steps. -/
theorem sm1_I2_raw (σ : ExecState) (sv sp x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (ch : Choices) :
    stepFnIter 291
      (mmSt σ (smHeap1 sv sp (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]])
        2 false ++ smDead 10 11 ++ smDead 12 13) 14)
      (.retV (.bool true) smCmpK1) ch
      = .ok (.retV (.bool false) smCmpK1,
          mmSt σ (smHeap1 sv sp
            (mmArr3 (mmSet (mmSet (mmSet
                [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]
                2 0 (un (sp + 6))) 2 1 (un (sp + 7))) 2 2 (un (sp + 8))))
            3 false ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15) 16,
          ch) := by
  have ht := symEvalWindow_refines' (budget := 291) (n := 291)
    (S := (⟨symHeap1 symXMat1 (.lit 2) ++ sDead 10 11 ++ sDead 12 13, 14⟩ : SymState))
    (C := .retV (.bool (.lit true)) symCmpK1)
    (by with_unfolding_all rfl)
    (mkρ [sv, sp, x0, x1, x2, x3, x4, x5, x6, x7, x8] []) σ ch
  with_unfolding_all exact ht

/-! Phase-1 exit and the `seedMat(1)` call point. -/

/-- Heap at the seedMat(1) call point: `$res0 = m` landed in cell 6
(one whole-matrix normalization), the frame write-back landed in cell 4
(another), `b` declared at 16. -/
def smHeap1X (sv sp : Int) (M : List (List Int)) : Heap :=
  [(.base ⟨0⟩, uCell sv), (.base ⟨1⟩, mCell zMatV),
   (.base ⟨2⟩, mCell zMatV), (.base ⟨3⟩, mCell zMatV),
   (.base ⟨4⟩, mCell (mmArr3 (mmNorm (mmNorm M)))),
   (.base ⟨5⟩, uCell sp), (.base ⟨6⟩, mCell (mmArr3 (mmNorm M))),
   (.base ⟨7⟩, mCell (mmArr3 M)), (.base ⟨8⟩, iCell 3),
   (.base ⟨9⟩, bCell false)]
  ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15
  ++ [(.base ⟨16⟩, mCell zMatV)]

/-- The seedMat(1) call point: the literal `1` argument delivered. -/
def call2K : Cont :=
  .callArgsK ⟨"seedMat"⟩ [(.chain [], [.ref "b"])] [] [] envB
    (.seq [hS3, hS4] envB mmStop)

/-- SM1 exit: outer test false → break, `$res0 = m`, return, frame
write-back into `a`, `b` declared, the literal `1` argument delivered
at the seedMat(1) call point. 33 steps. -/
theorem sm1_X_raw (σ : ExecState) (sv sp x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (ch : Choices) :
    stepFnIter 33
      (mmSt σ (smHeap1 sv sp (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]])
        3 false ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15) 16)
      (.retV (.bool false) smCmpK1) ch
      = .ok (.retV (.int 1 .uint64) call2K,
          mmSt σ (smHeap1X sv sp [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]])
            17, ch) := by
  with_unfolding_all rfl

/-! ## Phase 2: `seedMat(1)` (cells 17–27)

Fully concrete data, so the segment right-hand sides carry the CLEAN
literal matrices (`rfl` reduces the store towers); the phase-1 cells 4,
6, 7 ride through as opaque `GoValue` parameters. -/

/-- The phase-1 leftover heap, cells 0–16, matrices opaque. -/
def smHeapPre2 (sv sp : Int) (a4 a6 a7 : GoValue) : Heap :=
  [(.base ⟨0⟩, uCell sv), (.base ⟨1⟩, mCell zMatV),
   (.base ⟨2⟩, mCell zMatV), (.base ⟨3⟩, mCell zMatV),
   (.base ⟨4⟩, mCell a4), (.base ⟨5⟩, uCell sp),
   (.base ⟨6⟩, mCell a6), (.base ⟨7⟩, mCell a7),
   (.base ⟨8⟩, iCell 3), (.base ⟨9⟩, bCell false)]
  ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15
  ++ [(.base ⟨16⟩, mCell zMatV)]

theorem smHeap1X_eq (sv sp : Int) (M : List (List Int)) :
    smHeap1X sv sp M
      = smHeapPre2 sv sp (mmArr3 (mmNorm (mmNorm M))) (mmArr3 (mmNorm M))
          (mmArr3 M) := rfl

def mmHeapSM2 (sv sp sp2 : Int) (a4 a6 a7 : GoValue) : Heap :=
  smHeapPre2 sv sp a4 a6 a7
    ++ [(.base ⟨17⟩, uCell sp2), (.base ⟨18⟩, mCell zMatV)]

/-- `enterFrame` fact 2. -/
theorem mm_enterFrame2 (sv sp : Int) (a4 a6 a7 : GoValue) :
    enterFrame (mmSt mmProg (smHeapPre2 sv sp a4 a6 a7) 17) ⟨"seedMat"⟩
        [.int 1 .uint64]
      = .ok (seedMatFunc,
          [[("$res0", Loc.base ⟨18⟩), ("seed", Loc.base ⟨17⟩)]],
          [.base ⟨18⟩], mmSt mmProg (mmHeapSM2 sv sp 1 a4 a6 a7) 19) := by
  with_unfolding_all rfl

def smBase2 : Scope := [("$res0", .base ⟨18⟩), ("seed", .base ⟨17⟩)]
def smEnv4b : LocalEnv :=
  [[("$forFirst", .base ⟨21⟩)], [("i", .base ⟨20⟩)], [("m", .base ⟨19⟩)],
   smBase2]
def smEnv5b : LocalEnv := [] :: smEnv4b
def smFrameK2 : Cont :=
  .frame [(.chain [], [.ref "b"])] envB [.base ⟨18⟩] []
    (.seq [hS3, hS4] envB mmStop)
def smHeadTail2 : Cont :=
  .seq [] smEnv4b
    (.seq [] [[("i", .base ⟨20⟩)], [("m", .base ⟨19⟩)], smBase2]
      (.seq [smT3] [[("m", .base ⟨19⟩)], smBase2] smFrameK2))
def smLoopK2 : Cont := .loop (.boolLit true) smOuterBody smEnv4b smHeadTail2
def smCmpK2 : Cont :=
  .ifK (.seqn #[]) .breakStmt smEnv5b (.seq [smOuterFill] smEnv5b smLoopK2)

/-- Phase-2 front: cells 0–16 opaque, cells 17–21 live. -/
def smHeap2 (sv sp sp2 : Int) (a4 a6 a7 : GoValue) (m2 : GoValue) (iv : Int)
    (ff : Bool) : Heap :=
  smHeapPre2 sv sp a4 a6 a7
    ++ [(.base ⟨17⟩, uCell sp2), (.base ⟨18⟩, mCell zMatV),
        (.base ⟨19⟩, mCell m2), (.base ⟨20⟩, iCell iv),
        (.base ⟨21⟩, bCell ff)]

/-- SM2 entry. 59 steps. -/
theorem sm2_E_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 : GoValue)
    (ch : Choices) :
    stepFnIter 59 (mmSt σ (mmHeapSM2 sv sp sp2 a4 a6 a7) 19)
      (.exec seedMatFunc.body
        [[("$res0", Loc.base ⟨18⟩), ("seed", Loc.base ⟨17⟩)]] smFrameK2) ch
      = .ok (.retV (.bool true) smCmpK2,
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7 zMatV 0 false) 22, ch) := by
  with_unfolding_all rfl

/-! ### The call-2 inner-loop continuations (parameterized by the
per-outer-iteration `j`/`$forFirst` cell pair) -/

def smInEnv2 (jc jf : Nat) : LocalEnv :=
  [[("$forFirst", .base ⟨jf⟩)], [("j", .base ⟨jc⟩)], [], []] ++ smEnv4b
def smInHeadTail2 (jc jf : Nat) : Cont :=
  .seq [] (smInEnv2 jc jf)
    (.seq [] ([[("j", .base ⟨jc⟩)], [], []] ++ smEnv4b)
      (.seq [] ([] :: smEnv5b)
        (.seq [] smEnv5b smLoopK2)))
def smInLoopK2 (jc jf : Nat) : Cont :=
  .loop (.boolLit true) smInnerBody (smInEnv2 jc jf) (smInHeadTail2 jc jf)
def smInCmpK2 (jc jf : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: smInEnv2 jc jf)
    (.seq [smInnerFill] ([] :: smInEnv2 jc jf) (smInLoopK2 jc jf))

/-- SM2 i=0: outer test true → inner `j = 0` test delivered. 58 steps. -/
theorem sm2_IH0_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 58
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 0 false) 22)
      (.retV (.bool true) smCmpK2) ch
      = .ok (.retV (.bool true) (smInCmpK2 22 23),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 0 false
            ++ [(.base ⟨22⟩, iCell 0), (.base ⟨23⟩, bCell false)]) 24,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=0: inner iteration j=0 (store `m[0][0]`). 65 steps. -/
theorem sm2_IS00_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 0 false
        ++ [(.base ⟨22⟩, iCell 0), (.base ⟨23⟩, bCell false)]) 24)
      (.retV (.bool true) (smInCmpK2 22 23)) ch
      = .ok (.retV (.bool true) (smInCmpK2 22 23),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 4 (sp2 + 0), unn 2 x1, unn 2 x2], [unn 1 x3, unn 1 x4, unn 1 x5], [unn 1 x6, unn 1 x7, unn 1 x8]]) 0 false
            ++ [(.base ⟨22⟩, iCell 1), (.base ⟨23⟩, bCell false)]) 24,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=0: inner iteration j=1 (store `m[0][1]`). 65 steps. -/
theorem sm2_IS01_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 0 false
        ++ [(.base ⟨22⟩, iCell 1), (.base ⟨23⟩, bCell false)]) 24)
      (.retV (.bool true) (smInCmpK2 22 23)) ch
      = .ok (.retV (.bool true) (smInCmpK2 22 23),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 2 x0, unn 4 (sp2 + 1), unn 2 x2], [unn 1 x3, unn 1 x4, unn 1 x5], [unn 1 x6, unn 1 x7, unn 1 x8]]) 0 false
            ++ [(.base ⟨22⟩, iCell 2), (.base ⟨23⟩, bCell false)]) 24,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=0: inner iteration j=2 (store `m[0][2]`). 65 steps. -/
theorem sm2_IS02_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 0 false
        ++ [(.base ⟨22⟩, iCell 2), (.base ⟨23⟩, bCell false)]) 24)
      (.retV (.bool true) (smInCmpK2 22 23)) ch
      = .ok (.retV (.bool false) (smInCmpK2 22 23),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 2 x0, unn 2 x1, unn 4 (sp2 + 2)], [unn 1 x3, unn 1 x4, unn 1 x5], [unn 1 x6, unn 1 x7, unn 1 x8]]) 0 false
            ++ [(.base ⟨22⟩, iCell 3), (.base ⟨23⟩, bCell false)]) 24,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=0: inner exit → outer head → outer test. 38 steps. -/
theorem sm2_IX0_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 38
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 0 false
        ++ [(.base ⟨22⟩, iCell 3), (.base ⟨23⟩, bCell false)]) 24)
      (.retV (.bool false) (smInCmpK2 22 23)) ch
      = .ok (.retV (.bool true) smCmpK2,
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false
            ++ smDead 22 23) 24, ch) := by
  with_unfolding_all rfl

/-- SM2 i=1: outer test true → inner `j = 0` test delivered. 58 steps. -/
theorem sm2_IH1_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 58
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false ++ smDead 22 23) 24)
      (.retV (.bool true) smCmpK2) ch
      = .ok (.retV (.bool true) (smInCmpK2 24 25),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false ++ smDead 22 23
            ++ [(.base ⟨24⟩, iCell 0), (.base ⟨25⟩, bCell false)]) 26,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=1: inner iteration j=0 (store `m[1][0]`). 65 steps. -/
theorem sm2_IS10_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false ++ smDead 22 23
        ++ [(.base ⟨24⟩, iCell 0), (.base ⟨25⟩, bCell false)]) 26)
      (.retV (.bool true) (smInCmpK2 24 25)) ch
      = .ok (.retV (.bool true) (smInCmpK2 24 25),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 1 x0, unn 1 x1, unn 1 x2], [unn 4 (sp2 + 3), unn 2 x4, unn 2 x5], [unn 1 x6, unn 1 x7, unn 1 x8]]) 1 false ++ smDead 22 23
            ++ [(.base ⟨24⟩, iCell 1), (.base ⟨25⟩, bCell false)]) 26,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=1: inner iteration j=1 (store `m[1][1]`). 65 steps. -/
theorem sm2_IS11_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false ++ smDead 22 23
        ++ [(.base ⟨24⟩, iCell 1), (.base ⟨25⟩, bCell false)]) 26)
      (.retV (.bool true) (smInCmpK2 24 25)) ch
      = .ok (.retV (.bool true) (smInCmpK2 24 25),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 1 x0, unn 1 x1, unn 1 x2], [unn 2 x3, unn 4 (sp2 + 4), unn 2 x5], [unn 1 x6, unn 1 x7, unn 1 x8]]) 1 false ++ smDead 22 23
            ++ [(.base ⟨24⟩, iCell 2), (.base ⟨25⟩, bCell false)]) 26,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=1: inner iteration j=2 (store `m[1][2]`). 65 steps. -/
theorem sm2_IS12_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false ++ smDead 22 23
        ++ [(.base ⟨24⟩, iCell 2), (.base ⟨25⟩, bCell false)]) 26)
      (.retV (.bool true) (smInCmpK2 24 25)) ch
      = .ok (.retV (.bool false) (smInCmpK2 24 25),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 1 x0, unn 1 x1, unn 1 x2], [unn 2 x3, unn 2 x4, unn 4 (sp2 + 5)], [unn 1 x6, unn 1 x7, unn 1 x8]]) 1 false ++ smDead 22 23
            ++ [(.base ⟨24⟩, iCell 3), (.base ⟨25⟩, bCell false)]) 26,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=1: inner exit → outer head → outer test. 38 steps. -/
theorem sm2_IX1_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 38
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 1 false ++ smDead 22 23
        ++ [(.base ⟨24⟩, iCell 3), (.base ⟨25⟩, bCell false)]) 26)
      (.retV (.bool false) (smInCmpK2 24 25)) ch
      = .ok (.retV (.bool true) smCmpK2,
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23
            ++ smDead 24 25) 26, ch) := by
  with_unfolding_all rfl

/-- SM2 i=2: outer test true → inner `j = 0` test delivered. 58 steps. -/
theorem sm2_IH2_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 58
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25) 26)
      (.retV (.bool true) smCmpK2) ch
      = .ok (.retV (.bool true) (smInCmpK2 26 27),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
            ++ [(.base ⟨26⟩, iCell 0), (.base ⟨27⟩, bCell false)]) 28,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=2: inner iteration j=0 (store `m[2][0]`). 65 steps. -/
theorem sm2_IS20_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
        ++ [(.base ⟨26⟩, iCell 0), (.base ⟨27⟩, bCell false)]) 28)
      (.retV (.bool true) (smInCmpK2 26 27)) ch
      = .ok (.retV (.bool true) (smInCmpK2 26 27),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 1 x0, unn 1 x1, unn 1 x2], [unn 1 x3, unn 1 x4, unn 1 x5], [unn 4 (sp2 + 6), unn 2 x7, unn 2 x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
            ++ [(.base ⟨26⟩, iCell 1), (.base ⟨27⟩, bCell false)]) 28,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=2: inner iteration j=1 (store `m[2][1]`). 65 steps. -/
theorem sm2_IS21_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
        ++ [(.base ⟨26⟩, iCell 1), (.base ⟨27⟩, bCell false)]) 28)
      (.retV (.bool true) (smInCmpK2 26 27)) ch
      = .ok (.retV (.bool true) (smInCmpK2 26 27),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 1 x0, unn 1 x1, unn 1 x2], [unn 1 x3, unn 1 x4, unn 1 x5], [unn 2 x6, unn 4 (sp2 + 7), unn 2 x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
            ++ [(.base ⟨26⟩, iCell 2), (.base ⟨27⟩, bCell false)]) 28,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=2: inner iteration j=2 (store `m[2][2]`). 65 steps. -/
theorem sm2_IS22_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 65
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
        ++ [(.base ⟨26⟩, iCell 2), (.base ⟨27⟩, bCell false)]) 28)
      (.retV (.bool true) (smInCmpK2 26 27)) ch
      = .ok (.retV (.bool false) (smInCmpK2 26 27),
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[unn 1 x0, unn 1 x1, unn 1 x2], [unn 1 x3, unn 1 x4, unn 1 x5], [unn 2 x6, unn 2 x7, unn 4 (sp2 + 8)]]) 2 false ++ smDead 22 23 ++ smDead 24 25
            ++ [(.base ⟨26⟩, iCell 3), (.base ⟨27⟩, bCell false)]) 28,
          ch) := by
  with_unfolding_all rfl

/-- SM2 i=2: inner exit → outer head → outer test. 38 steps. -/
theorem sm2_IX2_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 38
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 2 false ++ smDead 22 23 ++ smDead 24 25
        ++ [(.base ⟨26⟩, iCell 3), (.base ⟨27⟩, bCell false)]) 28)
      (.retV (.bool false) (smInCmpK2 26 27)) ch
      = .ok (.retV (.bool false) smCmpK2,
          mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
            (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 3 false ++ smDead 22 23 ++ smDead 24 25
            ++ smDead 26 27) 28, ch) := by
  with_unfolding_all rfl

/-! Phase-2 exit and the `matMul` call point. -/

/-- Heap at the matMul call point (`M2` is the m-matrix left in cell 19;
cells 18 and 16 carry its one- and two-fold normalizations). -/
def smHeap2X (sv sp sp2 : Int) (a4 a6 a7 : GoValue) (M2 : List (List Int)) : Heap :=
  [(.base ⟨0⟩, uCell sv), (.base ⟨1⟩, mCell zMatV),
   (.base ⟨2⟩, mCell zMatV), (.base ⟨3⟩, mCell zMatV),
   (.base ⟨4⟩, mCell a4), (.base ⟨5⟩, uCell sp),
   (.base ⟨6⟩, mCell a6), (.base ⟨7⟩, mCell a7),
   (.base ⟨8⟩, iCell 3), (.base ⟨9⟩, bCell false)]
  ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15
  ++ [(.base ⟨16⟩, mCell (mmArr3 (mmNorm (mmNorm M2)))),
      (.base ⟨17⟩, uCell sp2),
      (.base ⟨18⟩, mCell (mmArr3 (mmNorm M2))),
      (.base ⟨19⟩, mCell (mmArr3 M2)),
      (.base ⟨20⟩, iCell 3), (.base ⟨21⟩, bCell false)]
  ++ smDead 22 23 ++ smDead 24 25 ++ smDead 26 27
  ++ [(.base ⟨28⟩, mCell zMatV)]

/-- The matMul call point: `a` delivered, `b` in flight. -/
def call3K (av : GoValue) : Cont :=
  .callArgsK ⟨"matMul"⟩ [(.chain [], [.ref "$c8"])] [av] [] envC
    (.seq [hS4] envC mmStop)

/-- SM2 exit: outer test false → break, `$res0 = m`, return, frame
write-back into `b`, `$c8` declared, both matMul arguments read. 35
steps. -/
theorem sm2_X_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
    (a4 a6 a7 : GoValue) (ch : Choices) :
    stepFnIter 35
      (mmSt σ (smHeap2 sv sp sp2 a4 a6 a7
        (mmArr3 [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 3 false
        ++ smDead 22 23 ++ smDead 24 25 ++ smDead 26 27) 28)
      (.retV (.bool false) smCmpK2) ch
      = .ok (.retV
            (mmArr3 (mmNorm (mmNorm
              [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]])))
            (call3K a4),
          mmSt σ (smHeap2X sv sp sp2 a4 a6 a7
            [[x0, x1, x2], [x3, x4, x5], [x6, x7, x8]]) 29, ch) := by
  with_unfolding_all rfl


/-! ## Phase 3: `matMul(a, b)` (cells 28–67)

Environments and continuations transcribed from the probe dumps at
steps 2002/2060/2121 and re-checked by the segments' `rfl`s. The
per-(i,j) `sum`/`k`/`$forFirst` cell triples make the k-level
continuations a three-parameter family. -/

def mmBase3 : Scope :=
  [("$res0", .base ⟨31⟩), ("b", .base ⟨30⟩), ("a", .base ⟨29⟩)]
def mmEnv4c : LocalEnv :=
  [[("$forFirst", .base ⟨34⟩)], [("i", .base ⟨33⟩)], [("c", .base ⟨32⟩)],
   mmBase3]
def mmEnv5c : LocalEnv := [] :: mmEnv4c
def mmFrameK3 : Cont :=
  .frame [(.chain [], [.ref "$c8"])] envC [.base ⟨31⟩] []
    (.seq [hS4] envC mmStop)
def mmHeadTail3 : Cont :=
  .seq [] mmEnv4c
    (.seq [] [[("i", .base ⟨33⟩)], [("c", .base ⟨32⟩)], mmBase3]
      (.seq [mmT3] [[("c", .base ⟨32⟩)], mmBase3] mmFrameK3))
def mmLoopK3 : Cont := .loop (.boolLit true) mmOuterBody mmEnv4c mmHeadTail3
def mmCmpK3 : Cont :=
  .ifK (.seqn #[]) .breakStmt mmEnv5c (.seq [mmOuterFill] mmEnv5c mmLoopK3)

def mmJEnv (jc jf : Nat) : LocalEnv :=
  [[("$forFirst", .base ⟨jf⟩)], [("j", .base ⟨jc⟩)], [], []] ++ mmEnv4c
def mmJHeadTail (jc jf : Nat) : Cont :=
  .seq [] (mmJEnv jc jf)
    (.seq [] ([[("j", .base ⟨jc⟩)], [], []] ++ mmEnv4c)
      (.seq [] ([] :: mmEnv5c)
        (.seq [] mmEnv5c mmLoopK3)))
def mmJLoopK (jc jf : Nat) : Cont :=
  .loop (.boolLit true) mmJBody (mmJEnv jc jf) (mmJHeadTail jc jf)
def mmJCmpK (jc jf : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: mmJEnv jc jf)
    (.seq [mmJFill] ([] :: mmJEnv jc jf) (mmJLoopK jc jf))

def mmKEnv (sc kc kf jc jf : Nat) : LocalEnv :=
  [[("$forFirst", .base ⟨kf⟩)], [("k", .base ⟨kc⟩)], [("sum", .base ⟨sc⟩)],
   []] ++ mmJEnv jc jf
def mmKHeadTail (sc kc kf jc jf : Nat) : Cont :=
  .seq [] (mmKEnv sc kc kf jc jf)
    (.seq [] ([[("k", .base ⟨kc⟩)], [("sum", .base ⟨sc⟩)], []] ++ mmJEnv jc jf)
      (.seq [mmCStore] ([[("sum", .base ⟨sc⟩)], []] ++ mmJEnv jc jf)
        (.seq [] ([] :: mmJEnv jc jf) (mmJLoopK jc jf))))
def mmKLoopK (sc kc kf jc jf : Nat) : Cont :=
  .loop (.boolLit true) mmKBody (mmKEnv sc kc kf jc jf)
    (mmKHeadTail sc kc kf jc jf)
def mmKCmpK (sc kc kf jc jf : Nat) : Cont :=
  .ifK (.seqn #[]) .breakStmt ([] :: mmKEnv sc kc kf jc jf)
    (.seq [mmKFill] ([] :: mmKEnv sc kc kf jc jf)
      (mmKLoopK sc kc kf jc jf))

/-- `enterFrame` fact 3: both `[3][3]uint64` arguments bind BY VALUE,
normalized once each at the declared parameter type. -/
theorem mm_enterFrame3 (sv sp sp2 : Int) (a6 a7 : GoValue)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int) :
    enterFrame
      (mmSt mmProg
        (smHeap2X sv sp sp2
          (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) a6 a7
          [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) 29)
      ⟨"matMul"⟩
      [mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]],
       mmArr3 (mmNorm (mmNorm [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]))]
      = .ok (matMulFunc,
          [[("$res0", Loc.base ⟨31⟩), ("b", Loc.base ⟨30⟩),
            ("a", Loc.base ⟨29⟩)]],
          [.base ⟨31⟩],
          mmSt mmProg
            (smHeap2X sv sp sp2
              (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) a6 a7
              [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]
              ++ [(.base ⟨29⟩, mCell (mmArr3 (mmNorm
                    [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]))),
                  (.base ⟨30⟩, mCell (mmArr3 (mmNorm (mmNorm (mmNorm
                    [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]))))),
                  (.base ⟨31⟩, mCell zMatV)]) 32) := by
  with_unfolding_all rfl

/-- Phase-3 heap front, cells 0–34 (everything the matMul loops never
touch is opaque; `Cv` is the `c` matrix, `iv`/`iff` the outer counter
pair). Per-boundary live/retired tails are appended explicitly in the
segment statements. -/
def mmHeap3 (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue)
    (iv : Int) (iff : Bool) : Heap :=
  [(.base ⟨0⟩, uCell sv), (.base ⟨1⟩, mCell zMatV),
   (.base ⟨2⟩, mCell zMatV), (.base ⟨3⟩, mCell zMatV),
   (.base ⟨4⟩, mCell a4), (.base ⟨5⟩, uCell sp),
   (.base ⟨6⟩, mCell a6), (.base ⟨7⟩, mCell a7),
   (.base ⟨8⟩, iCell 3), (.base ⟨9⟩, bCell false)]
  ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15
  ++ [(.base ⟨16⟩, mCell b16), (.base ⟨17⟩, uCell sp2),
      (.base ⟨18⟩, mCell b18), (.base ⟨19⟩, mCell b19),
      (.base ⟨20⟩, iCell 3), (.base ⟨21⟩, bCell false)]
  ++ smDead 22 23 ++ smDead 24 25 ++ smDead 26 27
  ++ [(.base ⟨28⟩, mCell c8v), (.base ⟨29⟩, mCell Ap),
      (.base ⟨30⟩, mCell Bp), (.base ⟨31⟩, mCell zMatV),
      (.base ⟨32⟩, mCell Cv), (.base ⟨33⟩, iCell iv),
      (.base ⟨34⟩, bCell iff)]

/-- A retired k-loop cell triple (`sum` kept at its final value). -/
def mmDeadK (s : Nat) (v : Int) : Heap :=
  [(.base ⟨s⟩, uCell v), (.base ⟨s + 1⟩, iCell 3), (.base ⟨s + 2⟩, bCell false)]

/-- Phase-3 entry front: cells 0–31 (before `c`/`i`/`$forFirst`). -/
def mmHeap3E (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) : Heap :=
  [(.base ⟨0⟩, uCell sv), (.base ⟨1⟩, mCell zMatV),
   (.base ⟨2⟩, mCell zMatV), (.base ⟨3⟩, mCell zMatV),
   (.base ⟨4⟩, mCell a4), (.base ⟨5⟩, uCell sp),
   (.base ⟨6⟩, mCell a6), (.base ⟨7⟩, mCell a7),
   (.base ⟨8⟩, iCell 3), (.base ⟨9⟩, bCell false)]
  ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15
  ++ [(.base ⟨16⟩, mCell b16), (.base ⟨17⟩, uCell sp2),
      (.base ⟨18⟩, mCell b18), (.base ⟨19⟩, mCell b19),
      (.base ⟨20⟩, iCell 3), (.base ⟨21⟩, bCell false)]
  ++ smDead 22 23 ++ smDead 24 25 ++ smDead 26 27
  ++ [(.base ⟨28⟩, mCell c8v), (.base ⟨29⟩, mCell Ap),
      (.base ⟨30⟩, mCell Bp), (.base ⟨31⟩, mCell zMatV)]

/-- MM entry: frame body → first outer test delivered. 59 steps. -/
theorem mm_E_raw (σ : ExecState) (sv sp sp2 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (ch : Choices) :
    stepFnIter 59 (mmSt σ (mmHeap3E sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v) 32)
      (.exec matMulFunc.body
        [[("$res0", Loc.base ⟨31⟩), ("b", Loc.base ⟨30⟩), ("a", Loc.base ⟨29⟩)]]
        mmFrameK3) ch
      = .ok (.retV (.bool true) mmCmpK3,
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            zMatV 0 false) 35, ch) := by
  with_unfolding_all rfl

/-- MM i=0: outer test true → inner `j = 0` test delivered. 58 steps. -/
theorem mm_JH0_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (ch : Choices) :
    stepFnIter 58
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false ) 35)
      (.retV (.bool true) mmCmpK3) ch
      = .ok (.retV (.bool true) (mmJCmpK 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false 
            ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]) 37,
          ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(0,0): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 37–39). 62 steps. -/
theorem mm_A00_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]) 37)
      (.retV (.bool true) (mmJCmpK 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 37 38 39 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
            ++ [(.base ⟨37⟩, uCell 0), (.base ⟨38⟩, iCell 0),
                (.base ⟨39⟩, bCell false)]) 40, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,0,0): one k-iteration —
`sum = mmAcc sum a[0][0] b[0][0]`. 69 steps. -/
theorem mm_K000_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
        ++ [(.base ⟨37⟩, uCell s), (.base ⟨38⟩, iCell 0),
            (.base ⟨39⟩, bCell false)]) 40)
      (.retV (.bool true) (mmKCmpK 37 38 39 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 37 38 39 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
            ++ [(.base ⟨37⟩, uCell (mmAcc s ax0 bx0)),
                (.base ⟨38⟩, iCell 1),
                (.base ⟨39⟩, bCell false)]) 40, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,0,1): one k-iteration —
`sum = mmAcc sum a[0][1] b[1][0]`. 69 steps. -/
theorem mm_K001_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
        ++ [(.base ⟨37⟩, uCell s), (.base ⟨38⟩, iCell 1),
            (.base ⟨39⟩, bCell false)]) 40)
      (.retV (.bool true) (mmKCmpK 37 38 39 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 37 38 39 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
            ++ [(.base ⟨37⟩, uCell (mmAcc s ax1 bx3)),
                (.base ⟨38⟩, iCell 2),
                (.base ⟨39⟩, bCell false)]) 40, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,0,2): one k-iteration —
`sum = mmAcc sum a[0][2] b[2][0]`. 69 steps. -/
theorem mm_K002_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
        ++ [(.base ⟨37⟩, uCell s), (.base ⟨38⟩, iCell 2),
            (.base ⟨39⟩, bCell false)]) 40)
      (.retV (.bool true) (mmKCmpK 37 38 39 35 36)) ch
      = .ok (.retV (.bool false) (mmKCmpK 37 38 39 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
            ++ [(.base ⟨37⟩, uCell (mmAcc s ax2 bx6)),
                (.base ⟨38⟩, iCell 3),
                (.base ⟨39⟩, bCell false)]) 40, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(0,0): k exit → `c[0][0] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C00_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 0 false  ++ [(.base ⟨35⟩, iCell 0), (.base ⟨36⟩, bCell false)]
        ++ [(.base ⟨37⟩, uCell s), (.base ⟨38⟩, iCell 3),
            (.base ⟨39⟩, bCell false)]) 40)
      (.retV (.bool false) (mmKCmpK 37 38 39 35 36)) ch
      = .ok (.retV (.bool true) (mmJCmpK 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 3 s, unn 2 c1, unn 2 c2], [unn 1 c3, unn 1 c4, unn 1 c5], [unn 1 c6, unn 1 c7, unn 1 c8]]) 0 false
             ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)]
            ++ mmDeadK 37 s) 40, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(0,1): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 40–42). 62 steps. -/
theorem mm_A01_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (e0 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0) 40)
      (.retV (.bool true) (mmJCmpK 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 40 41 42 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
            ++ [(.base ⟨40⟩, uCell 0), (.base ⟨41⟩, iCell 0),
                (.base ⟨42⟩, bCell false)]) 43, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,1,0): one k-iteration —
`sum = mmAcc sum a[0][0] b[0][1]`. 69 steps. -/
theorem mm_K010_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
        ++ [(.base ⟨40⟩, uCell s), (.base ⟨41⟩, iCell 0),
            (.base ⟨42⟩, bCell false)]) 43)
      (.retV (.bool true) (mmKCmpK 40 41 42 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 40 41 42 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
            ++ [(.base ⟨40⟩, uCell (mmAcc s ax0 bx1)),
                (.base ⟨41⟩, iCell 1),
                (.base ⟨42⟩, bCell false)]) 43, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,1,1): one k-iteration —
`sum = mmAcc sum a[0][1] b[1][1]`. 69 steps. -/
theorem mm_K011_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
        ++ [(.base ⟨40⟩, uCell s), (.base ⟨41⟩, iCell 1),
            (.base ⟨42⟩, bCell false)]) 43)
      (.retV (.bool true) (mmKCmpK 40 41 42 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 40 41 42 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
            ++ [(.base ⟨40⟩, uCell (mmAcc s ax1 bx4)),
                (.base ⟨41⟩, iCell 2),
                (.base ⟨42⟩, bCell false)]) 43, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,1,2): one k-iteration —
`sum = mmAcc sum a[0][2] b[2][1]`. 69 steps. -/
theorem mm_K012_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
        ++ [(.base ⟨40⟩, uCell s), (.base ⟨41⟩, iCell 2),
            (.base ⟨42⟩, bCell false)]) 43)
      (.retV (.bool true) (mmKCmpK 40 41 42 35 36)) ch
      = .ok (.retV (.bool false) (mmKCmpK 40 41 42 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
            ++ [(.base ⟨40⟩, uCell (mmAcc s ax2 bx7)),
                (.base ⟨41⟩, iCell 3),
                (.base ⟨42⟩, bCell false)]) 43, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(0,1): k exit → `c[0][1] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C01_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (e0 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 0 false  ++ [(.base ⟨35⟩, iCell 1), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
        ++ [(.base ⟨40⟩, uCell s), (.base ⟨41⟩, iCell 3),
            (.base ⟨42⟩, bCell false)]) 43)
      (.retV (.bool false) (mmKCmpK 40 41 42 35 36)) ch
      = .ok (.retV (.bool true) (mmJCmpK 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 2 c0, unn 3 s, unn 2 c2], [unn 1 c3, unn 1 c4, unn 1 c5], [unn 1 c6, unn 1 c7, unn 1 c8]]) 0 false
             ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0
            ++ mmDeadK 40 s) 43, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(0,2): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 43–45). 62 steps. -/
theorem mm_A02_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1) 43)
      (.retV (.bool true) (mmJCmpK 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 43 44 45 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
            ++ [(.base ⟨43⟩, uCell 0), (.base ⟨44⟩, iCell 0),
                (.base ⟨45⟩, bCell false)]) 46, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,2,0): one k-iteration —
`sum = mmAcc sum a[0][0] b[0][2]`. 69 steps. -/
theorem mm_K020_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
        ++ [(.base ⟨43⟩, uCell s), (.base ⟨44⟩, iCell 0),
            (.base ⟨45⟩, bCell false)]) 46)
      (.retV (.bool true) (mmKCmpK 43 44 45 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 43 44 45 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
            ++ [(.base ⟨43⟩, uCell (mmAcc s ax0 bx2)),
                (.base ⟨44⟩, iCell 1),
                (.base ⟨45⟩, bCell false)]) 46, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,2,1): one k-iteration —
`sum = mmAcc sum a[0][1] b[1][2]`. 69 steps. -/
theorem mm_K021_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
        ++ [(.base ⟨43⟩, uCell s), (.base ⟨44⟩, iCell 1),
            (.base ⟨45⟩, bCell false)]) 46)
      (.retV (.bool true) (mmKCmpK 43 44 45 35 36)) ch
      = .ok (.retV (.bool true) (mmKCmpK 43 44 45 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
            ++ [(.base ⟨43⟩, uCell (mmAcc s ax1 bx5)),
                (.base ⟨44⟩, iCell 2),
                (.base ⟨45⟩, bCell false)]) 46, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(0,2,2): one k-iteration —
`sum = mmAcc sum a[0][2] b[2][2]`. 69 steps. -/
theorem mm_K022_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
        ++ [(.base ⟨43⟩, uCell s), (.base ⟨44⟩, iCell 2),
            (.base ⟨45⟩, bCell false)]) 46)
      (.retV (.bool true) (mmKCmpK 43 44 45 35 36)) ch
      = .ok (.retV (.bool false) (mmKCmpK 43 44 45 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
            ++ [(.base ⟨43⟩, uCell (mmAcc s ax2 bx8)),
                (.base ⟨44⟩, iCell 3),
                (.base ⟨45⟩, bCell false)]) 46, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(0,2): k exit → `c[0][2] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C02_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 0 false  ++ [(.base ⟨35⟩, iCell 2), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
        ++ [(.base ⟨43⟩, uCell s), (.base ⟨44⟩, iCell 3),
            (.base ⟨45⟩, bCell false)]) 46)
      (.retV (.bool false) (mmKCmpK 43 44 45 35 36)) ch
      = .ok (.retV (.bool false) (mmJCmpK 35 36),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 2 c0, unn 2 c1, unn 3 s], [unn 1 c3, unn 1 c4, unn 1 c5], [unn 1 c6, unn 1 c7, unn 1 c8]]) 0 false
             ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1
            ++ mmDeadK 43 s) 46, ch) := by
  with_unfolding_all rfl

/-- MM i=0: j exit → outer head → outer test. 38 steps. -/
theorem mm_G0_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (e0 e1 e2 : Int) (ch : Choices) :
    stepFnIter 38
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 0 false  ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1 ++ mmDeadK 43 e2) 46)
      (.retV (.bool false) (mmJCmpK 35 36)) ch
      = .ok (.retV (.bool true) mmCmpK3,
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false  ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 e0 ++ mmDeadK 40 e1 ++ mmDeadK 43 e2) 46,
          ch) := by
  with_unfolding_all rfl

/-- MM i=1: outer test true → inner `j = 0` test delivered. 58 steps. -/
theorem mm_JH1_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 : Int) (ch : Choices) :
    stepFnIter 58
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2) 46)
      (.retV (.bool true) mmCmpK3) ch
      = .ok (.retV (.bool true) (mmJCmpK 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2
            ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]) 48,
          ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(1,0): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 48–50). 62 steps. -/
theorem mm_A10_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]) 48)
      (.retV (.bool true) (mmJCmpK 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 48 49 50 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
            ++ [(.base ⟨48⟩, uCell 0), (.base ⟨49⟩, iCell 0),
                (.base ⟨50⟩, bCell false)]) 51, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,0,0): one k-iteration —
`sum = mmAcc sum a[1][0] b[0][0]`. 69 steps. -/
theorem mm_K100_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
        ++ [(.base ⟨48⟩, uCell s), (.base ⟨49⟩, iCell 0),
            (.base ⟨50⟩, bCell false)]) 51)
      (.retV (.bool true) (mmKCmpK 48 49 50 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 48 49 50 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
            ++ [(.base ⟨48⟩, uCell (mmAcc s ax3 bx0)),
                (.base ⟨49⟩, iCell 1),
                (.base ⟨50⟩, bCell false)]) 51, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,0,1): one k-iteration —
`sum = mmAcc sum a[1][1] b[1][0]`. 69 steps. -/
theorem mm_K101_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
        ++ [(.base ⟨48⟩, uCell s), (.base ⟨49⟩, iCell 1),
            (.base ⟨50⟩, bCell false)]) 51)
      (.retV (.bool true) (mmKCmpK 48 49 50 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 48 49 50 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
            ++ [(.base ⟨48⟩, uCell (mmAcc s ax4 bx3)),
                (.base ⟨49⟩, iCell 2),
                (.base ⟨50⟩, bCell false)]) 51, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,0,2): one k-iteration —
`sum = mmAcc sum a[1][2] b[2][0]`. 69 steps. -/
theorem mm_K102_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
        ++ [(.base ⟨48⟩, uCell s), (.base ⟨49⟩, iCell 2),
            (.base ⟨50⟩, bCell false)]) 51)
      (.retV (.bool true) (mmKCmpK 48 49 50 46 47)) ch
      = .ok (.retV (.bool false) (mmKCmpK 48 49 50 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
            ++ [(.base ⟨48⟩, uCell (mmAcc s ax5 bx6)),
                (.base ⟨49⟩, iCell 3),
                (.base ⟨50⟩, bCell false)]) 51, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(1,0): k exit → `c[1][0] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C10_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (d0 d1 d2 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 0), (.base ⟨47⟩, bCell false)]
        ++ [(.base ⟨48⟩, uCell s), (.base ⟨49⟩, iCell 3),
            (.base ⟨50⟩, bCell false)]) 51)
      (.retV (.bool false) (mmKCmpK 48 49 50 46 47)) ch
      = .ok (.retV (.bool true) (mmJCmpK 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 1 c0, unn 1 c1, unn 1 c2], [unn 3 s, unn 2 c4, unn 2 c5], [unn 1 c6, unn 1 c7, unn 1 c8]]) 1 false
            ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)]
            ++ mmDeadK 48 s) 51, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(1,1): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 51–53). 62 steps. -/
theorem mm_A11_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0) 51)
      (.retV (.bool true) (mmJCmpK 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 51 52 53 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
            ++ [(.base ⟨51⟩, uCell 0), (.base ⟨52⟩, iCell 0),
                (.base ⟨53⟩, bCell false)]) 54, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,1,0): one k-iteration —
`sum = mmAcc sum a[1][0] b[0][1]`. 69 steps. -/
theorem mm_K110_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
        ++ [(.base ⟨51⟩, uCell s), (.base ⟨52⟩, iCell 0),
            (.base ⟨53⟩, bCell false)]) 54)
      (.retV (.bool true) (mmKCmpK 51 52 53 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 51 52 53 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
            ++ [(.base ⟨51⟩, uCell (mmAcc s ax3 bx1)),
                (.base ⟨52⟩, iCell 1),
                (.base ⟨53⟩, bCell false)]) 54, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,1,1): one k-iteration —
`sum = mmAcc sum a[1][1] b[1][1]`. 69 steps. -/
theorem mm_K111_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
        ++ [(.base ⟨51⟩, uCell s), (.base ⟨52⟩, iCell 1),
            (.base ⟨53⟩, bCell false)]) 54)
      (.retV (.bool true) (mmKCmpK 51 52 53 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 51 52 53 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
            ++ [(.base ⟨51⟩, uCell (mmAcc s ax4 bx4)),
                (.base ⟨52⟩, iCell 2),
                (.base ⟨53⟩, bCell false)]) 54, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,1,2): one k-iteration —
`sum = mmAcc sum a[1][2] b[2][1]`. 69 steps. -/
theorem mm_K112_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
        ++ [(.base ⟨51⟩, uCell s), (.base ⟨52⟩, iCell 2),
            (.base ⟨53⟩, bCell false)]) 54)
      (.retV (.bool true) (mmKCmpK 51 52 53 46 47)) ch
      = .ok (.retV (.bool false) (mmKCmpK 51 52 53 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
            ++ [(.base ⟨51⟩, uCell (mmAcc s ax5 bx7)),
                (.base ⟨52⟩, iCell 3),
                (.base ⟨53⟩, bCell false)]) 54, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(1,1): k exit → `c[1][1] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C11_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (d0 d1 d2 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 1), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
        ++ [(.base ⟨51⟩, uCell s), (.base ⟨52⟩, iCell 3),
            (.base ⟨53⟩, bCell false)]) 54)
      (.retV (.bool false) (mmKCmpK 51 52 53 46 47)) ch
      = .ok (.retV (.bool true) (mmJCmpK 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 1 c0, unn 1 c1, unn 1 c2], [unn 2 c3, unn 3 s, unn 2 c5], [unn 1 c6, unn 1 c7, unn 1 c8]]) 1 false
            ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0
            ++ mmDeadK 51 s) 54, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(1,2): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 54–56). 62 steps. -/
theorem mm_A12_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1) 54)
      (.retV (.bool true) (mmJCmpK 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 54 55 56 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
            ++ [(.base ⟨54⟩, uCell 0), (.base ⟨55⟩, iCell 0),
                (.base ⟨56⟩, bCell false)]) 57, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,2,0): one k-iteration —
`sum = mmAcc sum a[1][0] b[0][2]`. 69 steps. -/
theorem mm_K120_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
        ++ [(.base ⟨54⟩, uCell s), (.base ⟨55⟩, iCell 0),
            (.base ⟨56⟩, bCell false)]) 57)
      (.retV (.bool true) (mmKCmpK 54 55 56 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 54 55 56 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
            ++ [(.base ⟨54⟩, uCell (mmAcc s ax3 bx2)),
                (.base ⟨55⟩, iCell 1),
                (.base ⟨56⟩, bCell false)]) 57, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,2,1): one k-iteration —
`sum = mmAcc sum a[1][1] b[1][2]`. 69 steps. -/
theorem mm_K121_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
        ++ [(.base ⟨54⟩, uCell s), (.base ⟨55⟩, iCell 1),
            (.base ⟨56⟩, bCell false)]) 57)
      (.retV (.bool true) (mmKCmpK 54 55 56 46 47)) ch
      = .ok (.retV (.bool true) (mmKCmpK 54 55 56 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
            ++ [(.base ⟨54⟩, uCell (mmAcc s ax4 bx5)),
                (.base ⟨55⟩, iCell 2),
                (.base ⟨56⟩, bCell false)]) 57, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(1,2,2): one k-iteration —
`sum = mmAcc sum a[1][2] b[2][2]`. 69 steps. -/
theorem mm_K122_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
        ++ [(.base ⟨54⟩, uCell s), (.base ⟨55⟩, iCell 2),
            (.base ⟨56⟩, bCell false)]) 57)
      (.retV (.bool true) (mmKCmpK 54 55 56 46 47)) ch
      = .ok (.retV (.bool false) (mmKCmpK 54 55 56 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
            ++ [(.base ⟨54⟩, uCell (mmAcc s ax5 bx8)),
                (.base ⟨55⟩, iCell 3),
                (.base ⟨56⟩, bCell false)]) 57, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(1,2): k exit → `c[1][2] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C12_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (d0 d1 d2 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 2), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
        ++ [(.base ⟨54⟩, uCell s), (.base ⟨55⟩, iCell 3),
            (.base ⟨56⟩, bCell false)]) 57)
      (.retV (.bool false) (mmKCmpK 54 55 56 46 47)) ch
      = .ok (.retV (.bool false) (mmJCmpK 46 47),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 1 c0, unn 1 c1, unn 1 c2], [unn 2 c3, unn 2 c4, unn 3 s], [unn 1 c6, unn 1 c7, unn 1 c8]]) 1 false
            ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1
            ++ mmDeadK 54 s) 57, ch) := by
  with_unfolding_all rfl

/-- MM i=1: j exit → outer head → outer test. 38 steps. -/
theorem mm_G1_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 : Int) (e0 e1 e2 : Int) (ch : Choices) :
    stepFnIter 38
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 1 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1 ++ mmDeadK 54 e2) 57)
      (.retV (.bool false) (mmJCmpK 46 47)) ch
      = .ok (.retV (.bool true) mmCmpK3,
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 e0 ++ mmDeadK 51 e1 ++ mmDeadK 54 e2) 57,
          ch) := by
  with_unfolding_all rfl

/-- MM i=2: outer test true → inner `j = 0` test delivered. 58 steps. -/
theorem mm_JH2_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (ch : Choices) :
    stepFnIter 58
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5) 57)
      (.retV (.bool true) mmCmpK3) ch
      = .ok (.retV (.bool true) (mmJCmpK 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5
            ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]) 59,
          ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(2,0): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 59–61). 62 steps. -/
theorem mm_A20_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]) 59)
      (.retV (.bool true) (mmJCmpK 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 59 60 61 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
            ++ [(.base ⟨59⟩, uCell 0), (.base ⟨60⟩, iCell 0),
                (.base ⟨61⟩, bCell false)]) 62, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,0,0): one k-iteration —
`sum = mmAcc sum a[2][0] b[0][0]`. 69 steps. -/
theorem mm_K200_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
        ++ [(.base ⟨59⟩, uCell s), (.base ⟨60⟩, iCell 0),
            (.base ⟨61⟩, bCell false)]) 62)
      (.retV (.bool true) (mmKCmpK 59 60 61 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 59 60 61 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
            ++ [(.base ⟨59⟩, uCell (mmAcc s ax6 bx0)),
                (.base ⟨60⟩, iCell 1),
                (.base ⟨61⟩, bCell false)]) 62, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,0,1): one k-iteration —
`sum = mmAcc sum a[2][1] b[1][0]`. 69 steps. -/
theorem mm_K201_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
        ++ [(.base ⟨59⟩, uCell s), (.base ⟨60⟩, iCell 1),
            (.base ⟨61⟩, bCell false)]) 62)
      (.retV (.bool true) (mmKCmpK 59 60 61 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 59 60 61 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
            ++ [(.base ⟨59⟩, uCell (mmAcc s ax7 bx3)),
                (.base ⟨60⟩, iCell 2),
                (.base ⟨61⟩, bCell false)]) 62, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,0,2): one k-iteration —
`sum = mmAcc sum a[2][2] b[2][0]`. 69 steps. -/
theorem mm_K202_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
        ++ [(.base ⟨59⟩, uCell s), (.base ⟨60⟩, iCell 2),
            (.base ⟨61⟩, bCell false)]) 62)
      (.retV (.bool true) (mmKCmpK 59 60 61 57 58)) ch
      = .ok (.retV (.bool false) (mmKCmpK 59 60 61 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
            ++ [(.base ⟨59⟩, uCell (mmAcc s ax8 bx6)),
                (.base ⟨60⟩, iCell 3),
                (.base ⟨61⟩, bCell false)]) 62, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(2,0): k exit → `c[2][0] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C20_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 0), (.base ⟨58⟩, bCell false)]
        ++ [(.base ⟨59⟩, uCell s), (.base ⟨60⟩, iCell 3),
            (.base ⟨61⟩, bCell false)]) 62)
      (.retV (.bool false) (mmKCmpK 59 60 61 57 58)) ch
      = .ok (.retV (.bool true) (mmJCmpK 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 1 c0, unn 1 c1, unn 1 c2], [unn 1 c3, unn 1 c4, unn 1 c5], [unn 3 s, unn 2 c7, unn 2 c8]]) 2 false
            ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)]
            ++ mmDeadK 59 s) 62, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(2,1): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 62–64). 62 steps. -/
theorem mm_A21_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0) 62)
      (.retV (.bool true) (mmJCmpK 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 62 63 64 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
            ++ [(.base ⟨62⟩, uCell 0), (.base ⟨63⟩, iCell 0),
                (.base ⟨64⟩, bCell false)]) 65, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,1,0): one k-iteration —
`sum = mmAcc sum a[2][0] b[0][1]`. 69 steps. -/
theorem mm_K210_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
        ++ [(.base ⟨62⟩, uCell s), (.base ⟨63⟩, iCell 0),
            (.base ⟨64⟩, bCell false)]) 65)
      (.retV (.bool true) (mmKCmpK 62 63 64 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 62 63 64 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
            ++ [(.base ⟨62⟩, uCell (mmAcc s ax6 bx1)),
                (.base ⟨63⟩, iCell 1),
                (.base ⟨64⟩, bCell false)]) 65, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,1,1): one k-iteration —
`sum = mmAcc sum a[2][1] b[1][1]`. 69 steps. -/
theorem mm_K211_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
        ++ [(.base ⟨62⟩, uCell s), (.base ⟨63⟩, iCell 1),
            (.base ⟨64⟩, bCell false)]) 65)
      (.retV (.bool true) (mmKCmpK 62 63 64 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 62 63 64 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
            ++ [(.base ⟨62⟩, uCell (mmAcc s ax7 bx4)),
                (.base ⟨63⟩, iCell 2),
                (.base ⟨64⟩, bCell false)]) 65, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,1,2): one k-iteration —
`sum = mmAcc sum a[2][2] b[2][1]`. 69 steps. -/
theorem mm_K212_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
        ++ [(.base ⟨62⟩, uCell s), (.base ⟨63⟩, iCell 2),
            (.base ⟨64⟩, bCell false)]) 65)
      (.retV (.bool true) (mmKCmpK 62 63 64 57 58)) ch
      = .ok (.retV (.bool false) (mmKCmpK 62 63 64 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
            ++ [(.base ⟨62⟩, uCell (mmAcc s ax8 bx7)),
                (.base ⟨63⟩, iCell 3),
                (.base ⟨64⟩, bCell false)]) 65, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(2,1): k exit → `c[2][1] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C21_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 1), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
        ++ [(.base ⟨62⟩, uCell s), (.base ⟨63⟩, iCell 3),
            (.base ⟨64⟩, bCell false)]) 65)
      (.retV (.bool false) (mmKCmpK 62 63 64 57 58)) ch
      = .ok (.retV (.bool true) (mmJCmpK 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 1 c0, unn 1 c1, unn 1 c2], [unn 1 c3, unn 1 c4, unn 1 c5], [unn 2 c6, unn 3 s, unn 2 c8]]) 2 false
            ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0
            ++ mmDeadK 62 s) 65, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(2,2): j test true → `k = 0` test delivered
(`sum`/`k`/`$forFirst` allocated at 65–67). 62 steps. -/
theorem mm_A22_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 62
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1) 65)
      (.retV (.bool true) (mmJCmpK 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 65 66 67 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
            ++ [(.base ⟨65⟩, uCell 0), (.base ⟨66⟩, iCell 0),
                (.base ⟨67⟩, bCell false)]) 68, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,2,0): one k-iteration —
`sum = mmAcc sum a[2][0] b[0][2]`. 69 steps. -/
theorem mm_K220_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
        ++ [(.base ⟨65⟩, uCell s), (.base ⟨66⟩, iCell 0),
            (.base ⟨67⟩, bCell false)]) 68)
      (.retV (.bool true) (mmKCmpK 65 66 67 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 65 66 67 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
            ++ [(.base ⟨65⟩, uCell (mmAcc s ax6 bx2)),
                (.base ⟨66⟩, iCell 1),
                (.base ⟨67⟩, bCell false)]) 68, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,2,1): one k-iteration —
`sum = mmAcc sum a[2][1] b[1][2]`. 69 steps. -/
theorem mm_K221_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
        ++ [(.base ⟨65⟩, uCell s), (.base ⟨66⟩, iCell 1),
            (.base ⟨67⟩, bCell false)]) 68)
      (.retV (.bool true) (mmKCmpK 65 66 67 57 58)) ch
      = .ok (.retV (.bool true) (mmKCmpK 65 66 67 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
            ++ [(.base ⟨65⟩, uCell (mmAcc s ax7 bx5)),
                (.base ⟨66⟩, iCell 2),
                (.base ⟨67⟩, bCell false)]) 68, ch) := by
  with_unfolding_all rfl

/-- MM (i,j,k)=(2,2,2): one k-iteration —
`sum = mmAcc sum a[2][2] b[2][2]`. 69 steps. -/
theorem mm_K222_raw (σ : ExecState) (sv sp sp2 s : Int)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 : Int)
    (a4 a6 a7 b16 b18 b19 c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 69
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
        (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
        ++ [(.base ⟨65⟩, uCell s), (.base ⟨66⟩, iCell 2),
            (.base ⟨67⟩, bCell false)]) 68)
      (.retV (.bool true) (mmKCmpK 65 66 67 57 58)) ch
      = .ok (.retV (.bool false) (mmKCmpK 65 66 67 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19
            (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
            ++ [(.base ⟨65⟩, uCell (mmAcc s ax8 bx8)),
                (.base ⟨66⟩, iCell 3),
                (.base ⟨67⟩, bCell false)]) 68, ch) := by
  with_unfolding_all rfl

/-- MM (i,j)=(2,2): k exit → `c[2][2] = sum` (the 2-level
nested-array store), j head, next j test. 53 steps. -/
theorem mm_C22_raw (σ : ExecState) (sv sp sp2 s : Int)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Int)
    (a4 a6 a7 b16 b18 b19 Ap Bp c8v : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 e1 : Int) (ch : Choices) :
    stepFnIter 53
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 2), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
        ++ [(.base ⟨65⟩, uCell s), (.base ⟨66⟩, iCell 3),
            (.base ⟨67⟩, bCell false)]) 68)
      (.retV (.bool false) (mmKCmpK 65 66 67 57 58)) ch
      = .ok (.retV (.bool false) (mmJCmpK 57 58),
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v
            (mmArr3 [[unn 1 c0, unn 1 c1, unn 1 c2], [unn 1 c3, unn 1 c4, unn 1 c5], [unn 2 c6, unn 2 c7, unn 3 s]]) 2 false
            ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 3), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1
            ++ mmDeadK 65 s) 68, ch) := by
  with_unfolding_all rfl

/-- MM i=2: j exit → outer head → outer test. 38 steps. -/
theorem mm_G2_raw (σ : ExecState) (sv sp sp2 : Int) (a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv : GoValue) (d0 d1 d2 d3 d4 d5 : Int) (e0 e1 e2 : Int) (ch : Choices) :
    stepFnIter 38
      (mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 2 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 3), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1 ++ mmDeadK 65 e2) 68)
      (.retV (.bool false) (mmJCmpK 57 58)) ch
      = .ok (.retV (.bool false) mmCmpK3,
          mmSt σ (mmHeap3 sv sp sp2 a4 a6 a7 b16 b18 b19 Ap Bp c8v Cv 3 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 3), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 e0 ++ mmDeadK 62 e1 ++ mmDeadK 65 e2) 68,
          ch) := by
  with_unfolding_all rfl

/-- The driver-terminal heap: everything after the epilogue's five
stores (`$res0 = c` at 31, the `$c8` write-back at 28, and the three
harness result stores at 1/2/3). -/
def mmHeapX (sv sp sp2 : Int) (a6 a7 b18 b19 Ap Bp : GoValue)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8
     c0 c1 c2 c3 c4 c5 c6 c7 c8
     d0 d1 d2 d3 d4 d5 d6 d7 d8 : Int) : Heap :=
  [(.base ⟨0⟩, uCell sv),
   (.base ⟨1⟩, mCell (mmArr3 (mmNorm [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]))),
   (.base ⟨2⟩, mCell (mmArr3 (mmNorm [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]))),
   (.base ⟨3⟩, mCell (mmArr3 (mmNorm (mmNorm (mmNorm [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]))))),
   (.base ⟨4⟩, mCell (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]])), (.base ⟨5⟩, uCell sp),
   (.base ⟨6⟩, mCell a6), (.base ⟨7⟩, mCell a7),
   (.base ⟨8⟩, iCell 3), (.base ⟨9⟩, bCell false)]
  ++ smDead 10 11 ++ smDead 12 13 ++ smDead 14 15
  ++ [(.base ⟨16⟩, mCell (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]])), (.base ⟨17⟩, uCell sp2),
      (.base ⟨18⟩, mCell b18), (.base ⟨19⟩, mCell b19),
      (.base ⟨20⟩, iCell 3), (.base ⟨21⟩, bCell false)]
  ++ smDead 22 23 ++ smDead 24 25 ++ smDead 26 27
  ++ [(.base ⟨28⟩, mCell (mmArr3 (mmNorm (mmNorm [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]])))),
      (.base ⟨29⟩, mCell Ap), (.base ⟨30⟩, mCell Bp),
      (.base ⟨31⟩, mCell (mmArr3 (mmNorm [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]))),
      (.base ⟨32⟩, mCell (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]])),
      (.base ⟨33⟩, iCell 3), (.base ⟨34⟩, bCell false)]
  ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 3), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 d6 ++ mmDeadK 62 d7 ++ mmDeadK 65 d8

/-- MM exit: outer test false → break, `$res0 = c`, return, `$c8`
write-back, the harness epilogue's three result stores, return, the
driver terminal. 59 steps. -/
theorem mm_X_raw (σ : ExecState) (sv sp sp2 : Int) (a6 a7 Ap Bp c8v : GoValue)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8
     c0 c1 c2 c3 c4 c5 c6 c7 c8
     d0 d1 d2 d3 d4 d5 d6 d7 d8 : Int) (ch : Choices) :
    stepFnIter 59
      (mmSt σ (mmHeap3 sv sp sp2 (mmArr3 [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]) a6 a7 (mmArr3 [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]) b18 b19
        Ap Bp c8v (mmArr3 [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]]) 3 false ++ [(.base ⟨35⟩, iCell 3), (.base ⟨36⟩, bCell false)] ++ mmDeadK 37 d0 ++ mmDeadK 40 d1 ++ mmDeadK 43 d2 ++ [(.base ⟨46⟩, iCell 3), (.base ⟨47⟩, bCell false)] ++ mmDeadK 48 d3 ++ mmDeadK 51 d4 ++ mmDeadK 54 d5 ++ [(.base ⟨57⟩, iCell 3), (.base ⟨58⟩, bCell false)] ++ mmDeadK 59 d6 ++ mmDeadK 62 d7 ++ mmDeadK 65 d8) 68)
      (.retV (.bool false) mmCmpK3) ch
      = .ok (.next .stop,
          mmSt σ (mmHeapX sv sp sp2 a6 a7 b18 b19 Ap Bp
            ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8 bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 c0 c1 c2 c3 c4 c5 c6 c7 c8 d0 d1 d2 d3 d4 d5 d6 d7 d8) 68, ch) := by
  with_unfolding_all rfl

/-- The final-state readback: the three result cells. -/
theorem mm_readback (σ : ExecState) (sv sp sp2 : Int) (a6 a7 b18 b19 Ap Bp : GoValue)
    (ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8
     bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8
     c0 c1 c2 c3 c4 c5 c6 c7 c8
     d0 d1 d2 d3 d4 d5 d6 d7 d8 : Int) :
    loadMany
      (mmSt σ (mmHeapX sv sp sp2 a6 a7 b18 b19 Ap Bp
        ax0 ax1 ax2 ax3 ax4 ax5 ax6 ax7 ax8 bx0 bx1 bx2 bx3 bx4 bx5 bx6 bx7 bx8 c0 c1 c2 c3 c4 c5 c6 c7 c8 d0 d1 d2 d3 d4 d5 d6 d7 d8) 68)
      [Loc.base ⟨1⟩, Loc.base ⟨2⟩, Loc.base ⟨3⟩]
      = .ok [mmArr3 (mmNorm [[ax0, ax1, ax2], [ax3, ax4, ax5], [ax6, ax7, ax8]]),
             mmArr3 (mmNorm [[bx0, bx1, bx2], [bx3, bx4, bx5], [bx6, bx7, bx8]]),
             mmArr3 (mmNorm (mmNorm (mmNorm [[c0, c1, c2], [c3, c4, c5], [c6, c7, c8]])))] := by
  with_unfolding_all rfl

/-! ## Machine-integer cleanup

`un` (uint64 normalization) is idempotent, so every `unn`-tower the run
builds collapses to a single normalization; the remaining arithmetic is
linear (every multiplication in THIS run has the constant matrix `b`'s
literal entries on one side), so `omega` closes each entry once the
normalizer is unfolded. -/

theorem un_idem (v : Int) : un (un v) = un v :=
  intKind_normalize_idem .uint64 v

theorem unn_collapse : ∀ (k : Nat) (x : Int), unn (k + 1) x = un x
  | 0, _ => rfl
  | k + 1, x => by
      show un (unn (k + 1) x) = un x
      rw [unn_collapse k x, un_idem]

/-! ## The witnesses and the bridges -/

/-- The `a`-witness: `a[i][j] = (seed + (3i+j)) mod 2^64` — the seeded
family, wrapped, spelled out. -/
def aClean (seed : Nat) : List (List Int) :=
  [[(((seed + 0) % 2 ^ 64 : Nat) : Int), (((seed + 1) % 2 ^ 64 : Nat) : Int), (((seed + 2) % 2 ^ 64 : Nat) : Int)],
   [(((seed + 3) % 2 ^ 64 : Nat) : Int), (((seed + 4) % 2 ^ 64 : Nat) : Int), (((seed + 5) % 2 ^ 64 : Nat) : Int)],
   [(((seed + 6) % 2 ^ 64 : Nat) : Int), (((seed + 7) % 2 ^ 64 : Nat) : Int), (((seed + 8) % 2 ^ 64 : Nat) : Int)]]

/-- Bridge 1: the machine's `a`-result value IS `aClean seed`. -/
theorem mm_a_final (seed : Nat) (hseed : seed < 2 ^ 64) :
    mmNorm
      [[unn 16 ((seed : Int) + 0),
        unn 14 ((seed : Int) + 1),
        unn 12 ((seed : Int) + 2)],
       [unn 13 ((seed : Int) + 3),
        unn 11 ((seed : Int) + 4),
        unn 9 ((seed : Int) + 5)],
       [unn 10 ((seed : Int) + 6),
        unn 8 ((seed : Int) + 7),
        unn 6 ((seed : Int) + 8)]]
      = aClean seed := by
  simp only [mmNorm, List.map_cons, List.map_nil, aClean,
    show ∀ x, unn 3 x = un x from fun x => unn_collapse 2 x,
    show ∀ x, unn 5 x = un x from fun x => unn_collapse 4 x,
    show ∀ x, unn 6 x = un x from fun x => unn_collapse 5 x,
    show ∀ x, unn 7 x = un x from fun x => unn_collapse 6 x,
    show ∀ x, unn 8 x = un x from fun x => unn_collapse 7 x,
    show ∀ x, unn 9 x = un x from fun x => unn_collapse 8 x,
    show ∀ x, unn 10 x = un x from fun x => unn_collapse 9 x,
    show ∀ x, unn 11 x = un x from fun x => unn_collapse 10 x,
    show ∀ x, unn 12 x = un x from fun x => unn_collapse 11 x,
    show ∀ x, unn 13 x = un x from fun x => unn_collapse 12 x,
    show ∀ x, unn 14 x = un x from fun x => unn_collapse 13 x,
    show ∀ x, unn 15 x = un x from fun x => unn_collapse 14 x,
    show ∀ x, unn 16 x = un x from fun x => unn_collapse 15 x,
    show ∀ x, unn 17 x = un x from fun x => unn_collapse 16 x]
  simp only [un, IntKind.normalize, IntKind.bits?, IntKind.signed]
  simp only [Bool.false_eq_true, if_false, List.cons.injEq, and_true]
  omega

/-- Bridge 2: the machine's `b`-result value IS the constant matrix. -/
theorem mm_b_final :
    mmNorm [[(1 : Int), 2, 3], [4, 5, 6], [7, 8, 9]] = bMatL := by
  with_unfolding_all rfl

/-- Bridge 3 — THE WRAP BRIDGE: the machine's per-step wrapping
(`mmAcc`: multiply wrapped, sum wrapped, store wrapped, plus the value
copies' re-normalizations) equals `matSpec`'s ONE reduction of the true
integer sum per entry. Proved, not assumed: `unn_collapse` collapses the
towers (normalization is idempotent) and `omega` discharges the nine
modular-arithmetic equalities — linear because `b`'s entries are
literals. -/
theorem mm_c_final (seed : Nat) (hseed : seed < 2 ^ 64) :
    mmNorm (mmNorm (mmNorm
      [[unn 13 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7),
        unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8),
        unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)],
       [unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7),
        unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8),
        unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)],
       [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7),
        unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8),
        unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 7 ((seed : Int) + 8)) 9)]]))
      = matSpec (aClean seed) bMatL := by
  simp only [matSpec, mmGet, aClean,
    show List.range 3 = [0, 1, 2] from rfl,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    List.sum_cons, List.sum_nil]
  simp only [mmNorm, List.map_cons, List.map_nil, mmAcc,
    show ∀ x, unn 3 x = un x from fun x => unn_collapse 2 x,
    show ∀ x, unn 5 x = un x from fun x => unn_collapse 4 x,
    show ∀ x, unn 6 x = un x from fun x => unn_collapse 5 x,
    show ∀ x, unn 7 x = un x from fun x => unn_collapse 6 x,
    show ∀ x, unn 8 x = un x from fun x => unn_collapse 7 x,
    show ∀ x, unn 9 x = un x from fun x => unn_collapse 8 x,
    show ∀ x, unn 10 x = un x from fun x => unn_collapse 9 x,
    show ∀ x, unn 11 x = un x from fun x => unn_collapse 10 x,
    show ∀ x, unn 12 x = un x from fun x => unn_collapse 11 x,
    show ∀ x, unn 13 x = un x from fun x => unn_collapse 12 x,
    show ∀ x, unn 14 x = un x from fun x => unn_collapse 13 x,
    show ∀ x, unn 15 x = un x from fun x => unn_collapse 14 x,
    show ∀ x, unn 16 x = un x from fun x => unn_collapse 15 x,
    show ∀ x, unn 17 x = un x from fun x => unn_collapse 16 x]
  simp only [un, IntKind.normalize, IntKind.bits?, IntKind.signed]
  simp only [Bool.false_eq_true, if_false, List.cons.injEq, and_true]
  omega

/-! ## The headline -/

/-- **THE HEADLINE (S3 RELATIONAL)**: for EVERY `seed < 2^64` — the
wrap region included — running the Go harness `matmul_harness_r(seed)`
through the machine's native function entry completes normally past the
fuel bound 5247, at every nondeterminism-choice stream, and returns
THREE `[3][3]uint64` values `(a, b, c)` with `c = matSpec a b` — the
mathematical matrix product of the returned matrices, each entry the
sum `Σₖ aᵢₖ·bₖⱼ` reduced ONCE mod 2^64. The postcondition is a relation
over the RETURNED DATA; no family function appears in it.

Honesty clauses, recorded rather than hidden:

* **THE ARITHMETIC WRAPS, AND THE CLAIM SAYS SO.** Every multiply and
  every accumulation in `matMul` is uint64 and genuinely reduces mod
  2^64; `matSpec` is the true integer sum with ONE final reduction, and
  the theorem covers the FULL `seed < 2^64` domain — no hypothesis
  excludes the wrap region. The per-step wrapping equals the single
  reduction because normalization is idempotent and mod distributes
  over sum and product (`mm_c_final` — proved, not assumed). The corpus
  wrap rows `scalar-diag-wrap`, `seed-trace-wrap`, `harness-wrap` pin
  the wrap differentially, but only up to `seed = 2^63−1` (the
  differential driver's arguments are int64-limited); the region
  `2^63 ≤ seed < 2^64` is claimed by this theorem and was probe-checked
  by `#eval` (at `2^64−1`, `2^64−2`, `2^64−6`), not oracle-pinned.
* **`∃ a b` is family-determined.** The witnesses are `aClean seed`
  (`a[i][j] = seed + (3i+j)`, wrapped) and the CONSTANT
  `b = [[1,2,3],[4,5,6],[7,8,9]]` — `b` is `seedMat 1`, a constant
  matrix, and a reader should not have to discover that; the statement
  merely avoids SAYING so. Genuinely ∀-quantified input matrices need
  the ghost rung-1 annotation, which is designed and not built.
* **Attribution:** the `3×3` shape is the PROGRAM's own `matN`
  constant; `seed < 2^64` is Go's uint64 domain; the matrix product is
  mathematics.
* **The fuel bound `N = 5247` is EXACT and constant** — `matN = 3` is a
  compile-time constant, so the control flow is fully concrete and
  every run takes exactly 5247 steps; the triple loop contributes
  `matN³ = 27` inner iterations, so the constant is cubic in the
  (fixed) dimension — a dimension-generic version of this program would
  have a cubic bound. The bound is a NUMBER rather than a formula only
  because the dimension is fixed. Bound and probe measurement COINCIDE
  here (both 5247, measured at `seed = 0`, `5`, `2^63−1`), and the
  proof's segment counts sum to it — neither is presented as the other.
* **`∀ ch` is vacuous here and stated anyway.** The run consumes no
  nondeterminism choice; the quantifier records that rather than hiding
  a `Choices` argument.
* **Machine idealization** as in the other gallery entries: entry from
  an empty heap, an unbounded heap, allocation always succeeds. -/
theorem matmul_ok (seed : Nat) (hseed : seed < 2 ^ 64) :
    ∃ a b : List (List Int),
      a.length = 3 ∧ b.length = 3 ∧
      (∀ r ∈ a, r.length = 3) ∧ (∀ r ∈ b, r.length = 3) ∧
      ∃ N : Nat, ∀ fuel : Nat, N ≤ fuel → ∀ ch : Choices,
        runFunctionWithContextM fuel matmulLowered.typeDefs.toList
            matmulLowered.funcs matmulHarnessRFunc
            #[.int (seed : Int) .uint64]
            matmulLowered.methods ch
          = .ok { values := #[mmArr3 a, mmArr3 b, mmArr3 (matSpec a b)] } := by
  refine ⟨aClean seed, bMatL, rfl, rfl, ?_, ?_, 5247, fun fuel hfuel ch => ?_⟩
  · intro r hr
    simp only [aClean, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl
  · intro r hr
    simp only [bMatL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rfl
  have h1 := mm_E1_raw mmProg (seed : Int) ch
  have hef1 := mm_enterFrame1 (seed : Int) (seed : Int)
  rw [unorm_nat_of_lt hseed] at hef1
  have h2 := stepFnIter_chain h1
    (stepFnIter_one (stepFn_call_enter (vals := []) (v := .int (seed : Int) .uint64) hef1))
  have h3 := stepFnIter_chain h2
    (sm1_E_raw mmProg (seed : Int) (seed : Int) ch)
  have h4 := stepFnIter_chain h3
    (sm1_I0_raw mmProg (seed : Int) (seed : Int) 0 0 0 0 0 0 0 0 0 ch)
  have h5 := stepFnIter_chain h4
    (sm1_I1_raw mmProg (seed : Int) (seed : Int) (unn 8 ((seed : Int) + 0)) (unn 6 ((seed : Int) + 1)) (unn 4 ((seed : Int) + 2)) (0) (0) (0) (0) (0) (0) ch)
  have h6 := stepFnIter_chain h5
    (sm1_I2_raw mmProg (seed : Int) (seed : Int) (unn 11 ((seed : Int) + 0)) (unn 9 ((seed : Int) + 1)) (unn 7 ((seed : Int) + 2)) (unn 8 ((seed : Int) + 3)) (unn 6 ((seed : Int) + 4)) (unn 4 ((seed : Int) + 5)) (0) (0) (0) ch)
  have h7 := stepFnIter_chain h6
    (sm1_X_raw mmProg (seed : Int) (seed : Int) (unn 14 ((seed : Int) + 0)) (unn 12 ((seed : Int) + 1)) (unn 10 ((seed : Int) + 2)) (unn 11 ((seed : Int) + 3)) (unn 9 ((seed : Int) + 4)) (unn 7 ((seed : Int) + 5)) (unn 8 ((seed : Int) + 6)) (unn 6 ((seed : Int) + 7)) (unn 4 ((seed : Int) + 8)) ch)
  have h8 := stepFnIter_chain h7
    (stepFnIter_one (stepFn_call_enter (vals := []) (v := .int 1 .uint64)
      (mm_enterFrame2 (seed : Int) (seed : Int) (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))))
  have h9 := stepFnIter_chain h8
    (sm2_E_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h10 := stepFnIter_chain h9
    (sm2_IH0_raw mmProg (seed : Int) (seed : Int) 1 0 0 0 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h11 := stepFnIter_chain h10
    (sm2_IS00_raw mmProg (seed : Int) (seed : Int) 1 0 0 0 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h12 := stepFnIter_chain h11
    (sm2_IS01_raw mmProg (seed : Int) (seed : Int) 1 1 0 0 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h13 := stepFnIter_chain h12
    (sm2_IS02_raw mmProg (seed : Int) (seed : Int) 1 1 2 0 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h14 := stepFnIter_chain h13
    (sm2_IX0_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h15 := stepFnIter_chain h14
    (sm2_IH1_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h16 := stepFnIter_chain h15
    (sm2_IS10_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 0 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h17 := stepFnIter_chain h16
    (sm2_IS11_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 0 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h18 := stepFnIter_chain h17
    (sm2_IS12_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 0 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h19 := stepFnIter_chain h18
    (sm2_IX1_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h20 := stepFnIter_chain h19
    (sm2_IH2_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h21 := stepFnIter_chain h20
    (sm2_IS20_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 0 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h22 := stepFnIter_chain h21
    (sm2_IS21_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 7 0 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h23 := stepFnIter_chain h22
    (sm2_IS22_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 7 8 0 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h24 := stepFnIter_chain h23
    (sm2_IX2_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 7 8 9 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h25 := stepFnIter_chain h24
    (sm2_X_raw mmProg (seed : Int) (seed : Int) 1 1 2 3 4 5 6 7 8 9 (mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) ch)
  have h26 := stepFnIter_chain h25
    (stepFnIter_one (stepFn_call_enter (vals := [mmArr3 (mmNorm (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]))])
      (v := mmArr3 (mmNorm (mmNorm [[1, 2, 3], [4, 5, 6], [7, 8, 9]])))
      (mm_enterFrame3 (seed : Int) (seed : Int) 1 (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) (unn 16 ((seed : Int) + 0)) (unn 14 ((seed : Int) + 1)) (unn 12 ((seed : Int) + 2)) (unn 13 ((seed : Int) + 3)) (unn 11 ((seed : Int) + 4)) (unn 9 ((seed : Int) + 5)) (unn 10 ((seed : Int) + 6)) (unn 8 ((seed : Int) + 7)) (unn 6 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9)))
  have h27 := stepFnIter_chain h26
    (mm_E_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV ch)
  have h28 := stepFnIter_chain h27
    (mm_JH0_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[0, 0, 0], [0, 0, 0], [0, 0, 0]])  ch)
  have h29 := stepFnIter_chain h28
    (mm_A00_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[0, 0, 0], [0, 0, 0], [0, 0, 0]])   ch)
  have h30 := stepFnIter_chain h29
    (mm_K000_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[0, 0, 0], [0, 0, 0], [0, 0, 0]])   ch)
  have h31 := stepFnIter_chain h30
    (mm_K001_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[0, 0, 0], [0, 0, 0], [0, 0, 0]])   ch)
  have h32 := stepFnIter_chain h31
    (mm_K002_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[0, 0, 0], [0, 0, 0], [0, 0, 0]])   ch)
  have h33 := stepFnIter_chain h32
    (mm_C00_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (0) (0) (0) (0) (0) (0) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV   ch)
  have h34 := stepFnIter_chain h33
    (mm_A01_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), 0, 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) ch)
  have h35 := stepFnIter_chain h34
    (mm_K010_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), 0, 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) ch)
  have h36 := stepFnIter_chain h35
    (mm_K011_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), 0, 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) ch)
  have h37 := stepFnIter_chain h36
    (mm_K012_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), 0, 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) ch)
  have h38 := stepFnIter_chain h37
    (mm_C01_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (0) (0) (0) (0) (0) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) ch)
  have h39 := stepFnIter_chain h38
    (mm_A02_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) ch)
  have h40 := stepFnIter_chain h39
    (mm_K020_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) ch)
  have h41 := stepFnIter_chain h40
    (mm_K021_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) ch)
  have h42 := stepFnIter_chain h41
    (mm_K022_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), 0], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) ch)
  have h43 := stepFnIter_chain h42
    (mm_C02_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (0) (0) (0) (0) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) ch)
  have h44 := stepFnIter_chain h43
    (mm_G0_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [0, 0, 0], [0, 0, 0]])  (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) ch)
  have h45 := stepFnIter_chain h44
    (mm_JH1_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [0, 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) ch)
  have h46 := stepFnIter_chain h45
    (mm_A10_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [0, 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)  ch)
  have h47 := stepFnIter_chain h46
    (mm_K100_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [0, 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)  ch)
  have h48 := stepFnIter_chain h47
    (mm_K101_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [0, 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)  ch)
  have h49 := stepFnIter_chain h48
    (mm_K102_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [0, 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)  ch)
  have h50 := stepFnIter_chain h49
    (mm_C10_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (0) (0) (0) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)  ch)
  have h51 := stepFnIter_chain h50
    (mm_A11_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) ch)
  have h52 := stepFnIter_chain h51
    (mm_K110_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) ch)
  have h53 := stepFnIter_chain h52
    (mm_K111_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) ch)
  have h54 := stepFnIter_chain h53
    (mm_K112_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), 0, 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) ch)
  have h55 := stepFnIter_chain h54
    (mm_C11_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7)) (0) (0) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) ch)
  have h56 := stepFnIter_chain h55
    (mm_A12_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) ch)
  have h57 := stepFnIter_chain h56
    (mm_K120_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) ch)
  have h58 := stepFnIter_chain h57
    (mm_K121_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) ch)
  have h59 := stepFnIter_chain h58
    (mm_K122_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), 0], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) ch)
  have h60 := stepFnIter_chain h59
    (mm_C12_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8)) (0) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) ch)
  have h61 := stepFnIter_chain h60
    (mm_G1_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) ch)
  have h62 := stepFnIter_chain h61
    (mm_JH2_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) ch)
  have h63 := stepFnIter_chain h62
    (mm_A20_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)  ch)
  have h64 := stepFnIter_chain h63
    (mm_K200_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)  ch)
  have h65 := stepFnIter_chain h64
    (mm_K201_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)  ch)
  have h66 := stepFnIter_chain h65
    (mm_K202_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [0, 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)  ch)
  have h67 := stepFnIter_chain h66
    (mm_C20_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)) (0) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)  ch)
  have h68 := stepFnIter_chain h67
    (mm_A21_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) ch)
  have h69 := stepFnIter_chain h68
    (mm_K210_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) ch)
  have h70 := stepFnIter_chain h69
    (mm_K211_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) ch)
  have h71 := stepFnIter_chain h70
    (mm_K212_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), 0, 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) ch)
  have h72 := stepFnIter_chain h71
    (mm_C21_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) (unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7)) (unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8)) (unn 4 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7)) (0) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) ch)
  have h73 := stepFnIter_chain h72
    (mm_A22_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 12 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8), 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) ch)
  have h74 := stepFnIter_chain h73
    (mm_K220_raw mmProg (seed : Int) (seed : Int) 1 (0) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 12 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8), 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) ch)
  have h75 := stepFnIter_chain h74
    (mm_K221_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 12 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8), 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) ch)
  have h76 := stepFnIter_chain h75
    (mm_K222_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 17 ((seed : Int) + 0)) (unn 15 ((seed : Int) + 1)) (unn 13 ((seed : Int) + 2)) (unn 14 ((seed : Int) + 3)) (unn 12 ((seed : Int) + 4)) (unn 10 ((seed : Int) + 5)) (unn 11 ((seed : Int) + 6)) (unn 9 ((seed : Int) + 7)) (unn 7 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV zMatV (mmArr3 [[unn 12 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8), 0]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) ch)
  have h77 := stepFnIter_chain h76
    (mm_C22_raw mmProg (seed : Int) (seed : Int) 1 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 7 ((seed : Int) + 8)) 9) (unn 12 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7)) (unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8)) (0) (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) ch)
  have h78 := stepFnIter_chain h77
    (mm_G2_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 [[unn 16 ((seed : Int) + 0), unn 14 ((seed : Int) + 1), unn 12 ((seed : Int) + 2)], [unn 13 ((seed : Int) + 3), unn 11 ((seed : Int) + 4), unn 9 ((seed : Int) + 5)], [unn 10 ((seed : Int) + 6), unn 8 ((seed : Int) + 7), unn 6 ((seed : Int) + 8)]]) (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) bMatV bMatV bMatV (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (mmArr3 [[unn 13 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7), unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8), unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)], [unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7), unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8), unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)], [unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7), unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8), unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 7 ((seed : Int) + 8)) 9)]]) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 7 ((seed : Int) + 8)) 9) ch)
  have h79 := stepFnIter_chain h78
    (mm_X_raw mmProg (seed : Int) (seed : Int) 1 (mmArr3 (mmNorm [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]])) (mmArr3 [[unn 14 ((seed : Int) + 0), unn 12 ((seed : Int) + 1), unn 10 ((seed : Int) + 2)], [unn 11 ((seed : Int) + 3), unn 9 ((seed : Int) + 4), unn 7 ((seed : Int) + 5)], [unn 8 ((seed : Int) + 6), unn 6 ((seed : Int) + 7), unn 4 ((seed : Int) + 8)]]) (mmArr3 [[unn 17 ((seed : Int) + 0), unn 15 ((seed : Int) + 1), unn 13 ((seed : Int) + 2)], [unn 14 ((seed : Int) + 3), unn 12 ((seed : Int) + 4), unn 10 ((seed : Int) + 5)], [unn 11 ((seed : Int) + 6), unn 9 ((seed : Int) + 7), unn 7 ((seed : Int) + 8)]]) bMatV zMatV (unn 16 ((seed : Int) + 0)) (unn 14 ((seed : Int) + 1)) (unn 12 ((seed : Int) + 2)) (unn 13 ((seed : Int) + 3)) (unn 11 ((seed : Int) + 4)) (unn 9 ((seed : Int) + 5)) (unn 10 ((seed : Int) + 6)) (unn 8 ((seed : Int) + 7)) (unn 6 ((seed : Int) + 8)) 1 2 3 4 5 6 7 8 9 (unn 13 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7)) (unn 11 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8)) (unn 9 (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9)) (unn 10 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7)) (unn 8 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8)) (unn 6 (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9)) (unn 7 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7)) (unn 5 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8)) (unn 3 (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 7 ((seed : Int) + 8)) 9)) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 1) (unn 15 ((seed : Int) + 1)) 4) (unn 13 ((seed : Int) + 2)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 2) (unn 15 ((seed : Int) + 1)) 5) (unn 13 ((seed : Int) + 2)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 17 ((seed : Int) + 0)) 3) (unn 15 ((seed : Int) + 1)) 6) (unn 13 ((seed : Int) + 2)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 1) (unn 12 ((seed : Int) + 4)) 4) (unn 10 ((seed : Int) + 5)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 2) (unn 12 ((seed : Int) + 4)) 5) (unn 10 ((seed : Int) + 5)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 14 ((seed : Int) + 3)) 3) (unn 12 ((seed : Int) + 4)) 6) (unn 10 ((seed : Int) + 5)) 9) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 1) (unn 9 ((seed : Int) + 7)) 4) (unn 7 ((seed : Int) + 8)) 7) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 2) (unn 9 ((seed : Int) + 7)) 5) (unn 7 ((seed : Int) + 8)) 8) (mmAcc (mmAcc (mmAcc (0) (unn 11 ((seed : Int) + 6)) 3) (unn 9 ((seed : Int) + 7)) 6) (unn 7 ((seed : Int) + 8)) 9) ch)
  rw [show (8 + 1 + 59 + 291 + 291 + 291 + 33 + 1 + 59 + 58 + 65 + 65 + 65 + 38 + 58 + 65 + 65 + 65 + 38 + 58 + 65 + 65 + 65 + 38 + 35 + 1 + 59 + 58 + 62 + 69 + 69 + 69 + 53 + 62 + 69 + 69 + 69 + 53 + 62 + 69 + 69 + 69 + 53 + 38 + 58 + 62 + 69 + 69 + 69 + 53 + 62 + 69 + 69 + 69 + 53 + 62 + 69 + 69 + 69 + 53 + 38 + 58 + 62 + 69 + 69 + 69 + 53 + 62 + 69 + 69 + 69 + 53 + 62 + 69 + 69 + 69 + 53 + 38 + 59 : Nat) = 5247 from by omega] at h79
  have hfold := runConfig_of_stepFnIter h79 (fuel - 5247)
  rw [show 5247 + (fuel - 5247) = fuel from by omega] at hfold
  rw [mm_entry_eq (seed : Int) fuel ch, unorm_nat_of_lt hseed,
    show mmSeed (seed : Int) = mmSt mmProg (mmHeap0 (seed : Int)) 4 from rfl,
    hfold, runConfig_next_stop]
  simp only [bind, Except.bind, mm_readback, pure, Except.pure]
  rw [mm_a_final seed hseed, mm_b_final, mm_c_final seed hseed]

/-- **The D1 run-conditioned twin**: ANY successful completion of the
harness entry, at any fuel and any choice stream, returns exactly those
three values — derived from `matmul_ok` through the shared
`harness_readout_of_total` bridge; nothing is re-proven. -/
theorem matmul_readout (seed : Nat) (hseed : seed < 2 ^ 64) :
    ∃ a b : List (List Int),
      a.length = 3 ∧ b.length = 3 ∧
      (∀ r ∈ a, r.length = 3) ∧ (∀ r ∈ b, r.length = 3) ∧
      ∀ (fuel : Nat) (ch : Choices) (r : Result),
        runFunctionWithContextM fuel matmulLowered.typeDefs.toList
            matmulLowered.funcs matmulHarnessRFunc
            #[.int (seed : Int) .uint64]
            matmulLowered.methods ch
          = .ok r →
        r = { values := #[mmArr3 a, mmArr3 b, mmArr3 (matSpec a b)] } := by
  obtain ⟨a, b, hla, hlb, hra, hrb, htot⟩ := matmul_ok seed hseed
  exact ⟨a, b, hla, hlb, hra, hrb, harness_readout_of_total htot⟩

end GoLean.Examples.MatMul
