import GoLeanProofs.Examples.MatMulProgram
import GoLeanProofs.SliceMem
import GoLeanProofs.FuelMeasure
import GoLeanProofs.StepKit
import GoLeanProofs.EntryEq
import GoLeanProofs.Laws.StmtOps

/-!
# MatMul — the `matmul` example (Gallery Campaign G1, unit G1.9)

**STATUS (2026-08-15, lane A2 finisher): GROUNDWORK ONLY — NO HEADLINE.
This is an HONEST GAP, recorded in `docs/gallery-campaign-log/g1.md`
under unit G1.9; nothing below is a verified claim about the subject's
behaviour.** What this root carries is the corpus half of the G1
checklist, one step further than the guardrails wave left it: the
pinned harness transcription AND both subject `Func`s (`seedMat`,
`matMul`) restated in the readable compositional form and tied to the
pinned lowering by `rfl`, plus the statement vocabulary a headline
would be written in (`matSpec`, `mmArr3`, `mmGet`).

Go source: `Corpus/coverage/exec/examples/matmul/main.go` (11 rows,
differentially green against `go run`). The lowering is pinned by
`scripts/check-golden` against `baselines/golden/matmul-lowered.repr`
and carried in `GoLeanProofs.Examples.MatMulProgram`.

The subject is the textbook triple loop `sum += a[i][k] * b[k][j]` over
`[3][3]uint64`, WRAPPING mod 2^64. The harness `matmul_harness_r(seed)`
is the S3 RELATIONAL shape: `a := seedMat(seed)` (`a[i][j] = seed +
(3i+j)`, wrapping), `b := seedMat(1)` (the CONSTANT matrix
`[[1,2,3],[4,5,6],[7,8,9]]`), and the observable is `(a, b, matMul(a,
b))`. Go arrays are VALUES (copied on call and return), which is why
this 2-D example fits the pass-by-value fragment with no cap
workaround; it would be the gallery's FIRST 2-D example.

WHEN THE HEADLINE IS WRITTEN it goes HERE, in the root, so the
aggregator's `import GoLeanProofs.Examples.MatMul` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

## Why the machine layer is NOT in this file

A ~2,375-line segment layer for the whole run (entry equation, both
`seedMat` frames unrolled, all nine `matMul` accumulator cells, the
final readback) was WRITTEN and is preserved in the git ref
`refs/snapshots/gc-proofs-a/matmul-machine-layer` — recover it with
`git show refs/snapshots/gc-proofs-a/matmul-machine-layer:MatMul.lean`.
It is not carried here because its ELABORATION COST is prohibitive and
it was never shown to close: individual `with_unfolding_all rfl`
segments over the 291-step `seedMat` inner loops measured 61 s / 129 s
/ 307 s / 310 s / 326 s across five reformulations, one probe hit the
16M-heartbeat `whnf` ceiling outright, and two independent whole-file
elaborations were still running at 57 and 66 minutes when they were
cut. Carrying a module of that cost in `scripts/ci` — for zero claims,
since no assembly and no headline were ever written — taxes every
later gate run in the campaign.

The pickup plan is in the campaign log (unit G1.9): the blocker is
segment COST, not a missing fact, and the lever is segment SHAPE (the
291-step `seedMat` iterations want splitting at the store boundaries,
or a conditioned store lemma in place of raw `rfl`), not more
unrolling.
-/

namespace GoLean.Examples.MatMul

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

set_option maxRecDepth 4000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

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

end GoLean.Examples.MatMul
