import GoLean.GoCore.Syntax
import GoLean.GoCore.Value
import GoLeanProofs.Examples.FibProgram
import GoLeanProofs.Examples.GcdProgram
import GoLeanProofs.Examples.ReverseProgram
import GoLeanProofs.Examples.MinMaxProgram
import GoLeanProofs.Examples.BinSearchProgram
import GoLeanProofs.Examples.InsertionSortProgram
import GoLeanProofs.Examples.WordCountProgram

/-!
# The gallery examples' STATEMENT vocabulary — a def-only targets module

The seven gallery headlines (`docs/verified-examples.md`) joined the
statement-TCB gate's designated list on 2026-08-14 (user ruling, quoted
in the designation commit: *"in order to state the theorems we need
definitions of what fib and whatever mean. That's in the TCB
necessarily. So what we're doing here is hoisting things into the
Comparator set which are definitionally part of the TCB."*).

Designation forces this module's existence. The Comparator judge's
trusted root (`proofs/Challenge.lean`) must be able to STATE each
designated theorem, so every constant a designated statement mentions
has to be reachable from Challenge's import closure — and `scripts/ci`
step 1c3 forbids any designated theorem from being *declared* anywhere
in that closure. The example modules declare the headlines, so their
statement vocabulary is hoisted here instead: the established
`ForkJoinTargets` / `GooseParityTargets` pattern (channels-arc audit
F4, 2026-08-07; spec-parity D3, 2026-08-10).

**Nothing here is new or changed.** Every definition below is the
VERBATIM text from the example module it came from, in its original
namespace, so every downstream reference resolves unchanged through the
import. No statement and no proof was touched by the hoist.

**Why this file lives under `Examples/`, not `Specs/`** (deviation from
the two precedents, recorded deliberately): `scripts/ci` step 1d — the
import-direction lint — forbids every module under
`proofs/GoLeanProofs/` outside `Specs/` from importing
`GoLeanProofs.Specs.*`, with `Exceptions: NONE`. The example modules
must import their own hoisted vocabulary, so a `Specs/ExampleTargets`
would have required punching a hole in that lint. The `Examples/` tree
is target-layer material already (per-example program pins, walks and
witnesses) that predates the lint's `Specs/`-path proxy; siting the
targets module inside it keeps the lint intact and costs nothing the
judge cares about — what Challenge's closure actually requires is
def-only, Iris-free, and declaring no designated theorem, all of which
hold here.

The contents are exactly the transitive DEFINITION closure of the eight
designated headline statements, computed mechanically (not by reading):
the two specification functions per numeric example, the harness `Func`
records with their `where`-bound loop bodies, the two `goArr8` return
adapters (kept as TWO defs in their two namespaces — unifying them
would change what the statements say), and the input families the
statements name.
-/

set_option maxRecDepth 1000000

open GoLean GoLean.GoCore


namespace GoLean.Examples.Fib

/-- **The specification function**: the Fibonacci sequence, defined the
way a mathematician would write it. This is the entire mathematical
content of the example's claim — the theorems below say the Go program
computes THIS function. -/
def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec n + fibSpec (n + 1)

/-- The harness `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def fibHarnessFunc : Func :=
  { id := { key := "fib_harness" },
    args := #[{ id := "n", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "r", typ := .int .uint64 },
            .call #[.var "r"] ⟨"fib"⟩ #[.var "n"]],
        .seqn
          #[.assign (.var "$res0") (.var "r"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

end GoLean.Examples.Fib

namespace GoLean.Examples.Gcd

/-- The harness's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def gcdHarnessFunc : Func :=
  { id := { key := "gcd_harness" },
    args := #[{ id := "a", typ := .int .uint64 },
              { id := "b", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "r", typ := .int .uint64 },
            .call #[.var "r"] ⟨"gcd"⟩ #[.var "a", .var "b"]],
        .seqn
          #[.assign (.var "$res0") (.var "r"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

end GoLean.Examples.Gcd

namespace GoLean.Examples.Reverse

/-- The harness `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def reverseHarnessFunc : Func :=
  { id := { key := "reverse_harness" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "$c4", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c4") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c4")],
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
        .call #[] ⟨"reverse"⟩ #[.var "s"],
        .seqn
          #[.initialization { id := "ok", typ := .int .uint64 },
            .assign (.var "ok") (.intLit 1 .uint64)],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) tstBody]],
        .seqn
          #[.assign (.var "$res0") (.var "ok"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The setup loop's desugared body: the `$forFirst` dispatch, the
    exit test, the fill block `{ s[i] = seed + i }`. -/
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
                #[.assign
                    (.addr (.indexAddr (.var "s") (.var "i")))
                    (.add (.var "seed") (.var "i"))]]]
    /-- The test loop's desugared body: dispatch, exit test, the check
    block `{ if s[i] != seed+((n-1)-i) { ok = 0 } }`. -/
    tstBody : Stmt :=
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
            #[.ifThenElse
                (.neqCmp (.int .uint64)
                  (.indexGet (.var "s") (.var "i"))
                  (.add (.var "seed")
                    (.sub (.sub (.var "n") (.intLit 1 .uint64))
                      (.var "i"))))
                (.block #[] #[.seqn
                    #[.assign (.var "ok") (.intLit 0 .uint64)]])
                (.seqn #[])]]

/-- The copy-relational harness's `Func` record, verbatim from the
pinned lowering (the pin below ties it by `rfl`). The setup loop body
is literally the one `reverse_harness` uses, so it is shared rather
than restated. -/
def reverseHarnessVFunc : Func :=
  { id := { key := "reverse_harness_v" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 }],
    body := .block
      #[]
      #[.seqn
          #[.initialization { id := "$c5", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c5") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c5")],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) reverseHarnessFunc.suBody]],
        .seqn
          #[.initialization { id := "$c6", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c6") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "t", typ := .slice (.int .uint64) },
            .assign (.var "t") (.var "$c6")],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .call #[] ⟨"reverse"⟩ #[.var "s"],
        .seqn
          #[.initialization { id := "ok", typ := .int .uint64 },
            .assign (.var "ok") (.intLit 1 .uint64)],
        .block
          #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block
              #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) tvBody]],
        .seqn
          #[.assign (.var "$res0") (.var "ok"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The COPY loop's desugared body: dispatch, exit test, the copy
    block `{ t[i] = s[i] }` (the history ghost being materialized). -/
    cpBody : Stmt :=
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
                #[.assign
                    (.addr (.indexAddr (.var "t") (.var "i")))
                    (.indexGet (.var "s") (.var "i"))]]]
    /-- The test loop's desugared body: dispatch, exit test, the
    RELATIONAL check block `{ if s[i] != t[n-1-i] { ok = 0 } }`. -/
    tvBody : Stmt :=
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
            #[.ifThenElse
                (.neqCmp (.int .uint64)
                  (.indexGet (.var "s") (.var "i"))
                  (.indexGet (.var "t")
                    (.sub (.sub (.var "n") (.intLit 1 .uint64))
                      (.var "i"))))
                (.block #[] #[.seqn
                    #[.assign (.var "ok") (.intLit 0 .uint64)]])
                (.seqn #[])]]

end GoLean.Examples.Reverse

namespace GoLean.Examples.MinMax

/-- Minimum of a list of `Int`s (0 on `[]` — the headline never
consumes that case, `hne` excludes it). -/
def minSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => min v (minSpec (w :: rest))

/-- Maximum of a list of `Int`s (0 on `[]` — never consumed, as
`minSpec`). -/
def maxSpec : List Int → Int
  | [] => 0
  | [v] => v
  | v :: w :: rest => max v (maxSpec (w :: rest))

/-- The harness's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def mmHarnessFunc : Func :=
  { id := { key := "minmax_harness" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .uint64 },
                 { id := "$res1", typ := .int .uint64 }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c12", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c12") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c12")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) shBody]],
        .seqn
          #[.initialization { id := "$c13", typ := .int .uint64 },
            .initialization { id := "$c14", typ := .int .uint64 },
            .call #[.var "$c13", .var "$c14"] ⟨"minMax"⟩ #[.var "s"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c13"),
            .assign (.var "$res1") (.var "$c14"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
where
  /-- The setup loop's `for`-desugar body. -/
  shBody : Stmt :=
    .block #[]
      #[.ifThenElse (.var "$forFirst")
          (.assign (.var "$forFirst") (.boolLit false))
          (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
        .seqn #[],
        .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
        .block #[]
          #[.seqn #[.assign (.addr (.indexAddr (.var "s") (.var "i")))
              (.add (.var "seed") (.var "i"))]]]

/-- The returned fixed-cap array: the observed list, zero-padded to the
harness's `minmaxCapN = 8` slots. -/
def goArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-- The relational harness's `Func` record, verbatim from the pinned
lowering. The setup loop body is `minmax_harness`'s, shared. -/
def mmHarnessRFunc : Func :=
  { id := { key := "minmax_harness_r" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .array 8 (.int .uint64) },
                 { id := "$res1", typ := .int .uint64 },
                 { id := "$res2", typ := .int .uint64 }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c15", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c15") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c15")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) mmHarnessFunc.shBody]],
        .seqn
          #[.initialization { id := "pre", typ := .array 8 (.int .uint64) }],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .seqn
          #[.initialization { id := "lo", typ := .int .uint64 },
            .initialization { id := "hi", typ := .int .uint64 },
            .call #[.var "lo", .var "hi"] ⟨"minMax"⟩ #[.var "s"]],
        .seqn
          #[.assign (.var "$res0") (.var "pre"),
            .assign (.var "$res1") (.var "lo"),
            .assign (.var "$res2") (.var "hi"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The COPY loop's desugared body: `pre[i] = s[i]` — the store
    target is an ADDRESS-rooted index chain (`.ref "pre"`), because
    `pre` is an array-typed LOCAL, not a slice handle. -/
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

end GoLean.Examples.MinMax

namespace GoLean.Examples.BinSearch

/-- **The specification function**: index of the FIRST occurrence of
`t` in `xs`, or `-1` — defined the way a functional programmer would
write it, by structural recursion on the list. The theorems below say
the Go program computes THIS function. -/
def findSpec (xs : List Int) (t : Int) : Int :=
  match xs with
  | [] => -1
  | v :: rest =>
      if v = t then 0
      else if findSpec rest t < 0 then -1 else findSpec rest t + 1

/-- **The input family**: the sorted, gapped sequence the harness's
setup phase materializes — `bsFamily n seed = [seed, seed+2, …,
seed+2(n-1)]` (as mathematical integers; `hnowrap` in the headline is
what makes the machine's wrapped uint64 stores agree with it). -/
def bsFamily (n seed : Nat) : List Int :=
  (List.range n).map (fun i => ((seed + 2 * i : Nat) : Int))

/-- The setup loop's `for`-desugar body: dispatch (`i++` on later
passes), exit test `i < n`, the store `s[i] = seed + 2*i`. -/
abbrev setupBody : Stmt :=
  .block #[]
    #[.ifThenElse (.var "$forFirst")
        (.assign (.var "$forFirst") (.boolLit false))
        (.assign (.var "i")
          (.add (.var "i") (.intLit 1 .uint64))),
      .seqn #[],
      .ifThenElse (.lessCmp (.var "i") (.var "n"))
        (.seqn #[])
        .breakStmt,
      .block #[]
        #[.seqn
            #[.assign
                (.addr (.indexAddr (.var "s") (.var "i")))
                (.add (.var "seed")
                  (.mul (.intLit 2 .uint64) (.var "i")))]]]

/-- The harness's `Func` record, verbatim from the pinned lowering (the
`example` pin below ties it by `rfl`). -/
def searchHarnessFunc : Func :=
  { id := { key := "search_harness" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 },
              { id := "t", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .int .int }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c6", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c6") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "s", typ := .slice (.int .uint64) },
            .assign (.var "s") (.var "$c6")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) setupBody]],
        .seqn
          #[.initialization { id := "$c7", typ := .int .int },
            .call #[.var "$c7"] ⟨"search"⟩ #[.var "s", .var "t"]],
        .seqn
          #[.assign (.var "$res0") (.var "$c7"),
            .returnStmt]],
    variadic := false,
    wrapper := false }

end GoLean.Examples.BinSearch

namespace GoLean.Examples.InsertionSort

/-- The harness's `Func` record, verbatim from the pinned lowering
(the `example` pin below ties it by `rfl`). -/
def isortHarnessFunc : Func :=
  { id := { key := "isort_harness" },
    args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
              { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
    results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
    body := GoLean.GoCore.Stmt.block
              #[]
              #[GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "$c4",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.makeSlice
                      (GoLean.GoCore.Assignee.var "$c4")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Expr.var "n")
                      none],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "s",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "s")
                      (GoLean.GoCore.Expr.var "$c4")],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.addr
                                          (GoLean.GoCore.Expr.indexAddr
                                            (GoLean.GoCore.Expr.var "s")
                                            (GoLean.GoCore.Expr.var "i")))
                                        (GoLean.GoCore.Expr.mul
                                          (GoLean.GoCore.Expr.var "seed")
                                          (GoLean.GoCore.Expr.add
                                            (GoLean.GoCore.Expr.var "i")
                                            (GoLean.GoCore.Expr.intLit
                                              1
                                              (GoLean.GoCore.IntKind.uint64))))]]])]],
                GoLean.GoCore.Stmt.call #[] { key := "insertionSort" } #[GoLean.GoCore.Expr.var "s"],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "ok", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                    GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "ok")
                      (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.ifThenElse
                                    (GoLean.GoCore.Expr.greaterCmp
                                      (GoLean.GoCore.Expr.indexGet
                                        (GoLean.GoCore.Expr.var "s")
                                        (GoLean.GoCore.Expr.sub
                                          (GoLean.GoCore.Expr.var "i")
                                          (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64))))
                                      (GoLean.GoCore.Expr.indexGet
                                        (GoLean.GoCore.Expr.var "s")
                                        (GoLean.GoCore.Expr.var "i")))
                                    (GoLean.GoCore.Stmt.block
                                      #[]
                                      #[GoLean.GoCore.Stmt.seqn
                                          #[GoLean.GoCore.Stmt.assign
                                              (GoLean.GoCore.Assignee.var "ok")
                                              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))]])
                                    (GoLean.GoCore.Stmt.seqn #[])]])]],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "$c5",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.makeSlice
                      (GoLean.GoCore.Assignee.var "$c5")
                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                      (GoLean.GoCore.Expr.var "n")
                      none],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.initialization
                      { id := "t",
                        typ := GoLean.GoCore.Ty.slice
                                 (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64)) },
                    GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "t")
                      (GoLean.GoCore.Expr.var "$c5")],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.addr
                                          (GoLean.GoCore.Expr.indexAddr
                                            (GoLean.GoCore.Expr.var "t")
                                            (GoLean.GoCore.Expr.var "i")))
                                        (GoLean.GoCore.Expr.mul
                                          (GoLean.GoCore.Expr.var "seed")
                                          (GoLean.GoCore.Expr.add
                                            (GoLean.GoCore.Expr.var "i")
                                            (GoLean.GoCore.Expr.intLit
                                              1
                                              (GoLean.GoCore.IntKind.uint64))))]]])]],
                GoLean.GoCore.Stmt.block
                  #[]
                  #[GoLean.GoCore.Stmt.seqn
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "i", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "i")
                          (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                    GoLean.GoCore.Stmt.block
                      #[]
                      #[GoLean.GoCore.Stmt.initialization
                          { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                        GoLean.GoCore.Stmt.assign
                          (GoLean.GoCore.Assignee.var "$forFirst")
                          (GoLean.GoCore.Expr.boolLit true),
                        GoLean.GoCore.Stmt.while
                          (GoLean.GoCore.Expr.boolLit true)
                          (GoLean.GoCore.Stmt.block
                            #[]
                            #[GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.var "$forFirst")
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "$forFirst")
                                  (GoLean.GoCore.Expr.boolLit false))
                                (GoLean.GoCore.Stmt.assign
                                  (GoLean.GoCore.Assignee.var "i")
                                  (GoLean.GoCore.Expr.add
                                    (GoLean.GoCore.Expr.var "i")
                                    (GoLean.GoCore.Expr.intLit 1 (GoLean.GoCore.IntKind.uint64)))),
                              GoLean.GoCore.Stmt.seqn #[],
                              GoLean.GoCore.Stmt.ifThenElse
                                (GoLean.GoCore.Expr.lessCmp
                                  (GoLean.GoCore.Expr.var "i")
                                  (GoLean.GoCore.Expr.var "n"))
                                (GoLean.GoCore.Stmt.seqn #[])
                                (GoLean.GoCore.Stmt.breakStmt),
                              GoLean.GoCore.Stmt.block
                                #[]
                                #[GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.initialization
                                        { id := "cs",
                                          typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                      GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.var "cs")
                                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                  GoLean.GoCore.Stmt.seqn
                                    #[GoLean.GoCore.Stmt.initialization
                                        { id := "ct",
                                          typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                      GoLean.GoCore.Stmt.assign
                                        (GoLean.GoCore.Assignee.var "ct")
                                        (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                  GoLean.GoCore.Stmt.block
                                    #[]
                                    #[GoLean.GoCore.Stmt.seqn
                                        #[GoLean.GoCore.Stmt.initialization
                                            { id := "j",
                                              typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                                          GoLean.GoCore.Stmt.assign
                                            (GoLean.GoCore.Assignee.var "j")
                                            (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))],
                                      GoLean.GoCore.Stmt.block
                                        #[]
                                        #[GoLean.GoCore.Stmt.initialization
                                            { id := "$forFirst", typ := GoLean.GoCore.Ty.bool },
                                          GoLean.GoCore.Stmt.assign
                                            (GoLean.GoCore.Assignee.var "$forFirst")
                                            (GoLean.GoCore.Expr.boolLit true),
                                          GoLean.GoCore.Stmt.while
                                            (GoLean.GoCore.Expr.boolLit true)
                                            (GoLean.GoCore.Stmt.block
                                              #[]
                                              #[GoLean.GoCore.Stmt.ifThenElse
                                                  (GoLean.GoCore.Expr.var "$forFirst")
                                                  (GoLean.GoCore.Stmt.assign
                                                    (GoLean.GoCore.Assignee.var "$forFirst")
                                                    (GoLean.GoCore.Expr.boolLit false))
                                                  (GoLean.GoCore.Stmt.assign
                                                    (GoLean.GoCore.Assignee.var "j")
                                                    (GoLean.GoCore.Expr.add
                                                      (GoLean.GoCore.Expr.var "j")
                                                      (GoLean.GoCore.Expr.intLit
                                                        1
                                                        (GoLean.GoCore.IntKind.uint64)))),
                                                GoLean.GoCore.Stmt.seqn #[],
                                                GoLean.GoCore.Stmt.ifThenElse
                                                  (GoLean.GoCore.Expr.lessCmp
                                                    (GoLean.GoCore.Expr.var "j")
                                                    (GoLean.GoCore.Expr.var "n"))
                                                  (GoLean.GoCore.Stmt.seqn #[])
                                                  (GoLean.GoCore.Stmt.breakStmt),
                                                GoLean.GoCore.Stmt.block
                                                  #[]
                                                  #[GoLean.GoCore.Stmt.ifThenElse
                                                      (GoLean.GoCore.Expr.eqCmp
                                                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "s")
                                                          (GoLean.GoCore.Expr.var "j"))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "t")
                                                          (GoLean.GoCore.Expr.var "i")))
                                                      (GoLean.GoCore.Stmt.block
                                                        #[]
                                                        #[GoLean.GoCore.Stmt.assign
                                                            (GoLean.GoCore.Assignee.var "cs")
                                                            (GoLean.GoCore.Expr.add
                                                              (GoLean.GoCore.Expr.var "cs")
                                                              (GoLean.GoCore.Expr.intLit
                                                                1
                                                                (GoLean.GoCore.IntKind.uint64)))])
                                                      (GoLean.GoCore.Stmt.seqn #[]),
                                                    GoLean.GoCore.Stmt.ifThenElse
                                                      (GoLean.GoCore.Expr.eqCmp
                                                        (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "t")
                                                          (GoLean.GoCore.Expr.var "j"))
                                                        (GoLean.GoCore.Expr.indexGet
                                                          (GoLean.GoCore.Expr.var "t")
                                                          (GoLean.GoCore.Expr.var "i")))
                                                      (GoLean.GoCore.Stmt.block
                                                        #[]
                                                        #[GoLean.GoCore.Stmt.assign
                                                            (GoLean.GoCore.Assignee.var "ct")
                                                            (GoLean.GoCore.Expr.add
                                                              (GoLean.GoCore.Expr.var "ct")
                                                              (GoLean.GoCore.Expr.intLit
                                                                1
                                                                (GoLean.GoCore.IntKind.uint64)))])
                                                      (GoLean.GoCore.Stmt.seqn #[])]])]],
                                  GoLean.GoCore.Stmt.ifThenElse
                                    (GoLean.GoCore.Expr.neqCmp
                                      (GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64))
                                      (GoLean.GoCore.Expr.var "cs")
                                      (GoLean.GoCore.Expr.var "ct"))
                                    (GoLean.GoCore.Stmt.block
                                      #[]
                                      #[GoLean.GoCore.Stmt.seqn
                                          #[GoLean.GoCore.Stmt.assign
                                              (GoLean.GoCore.Assignee.var "ok")
                                              (GoLean.GoCore.Expr.intLit 0 (GoLean.GoCore.IntKind.uint64))]])
                                    (GoLean.GoCore.Stmt.seqn #[])]])]],
                GoLean.GoCore.Stmt.seqn
                  #[GoLean.GoCore.Stmt.assign
                      (GoLean.GoCore.Assignee.var "$res0")
                      (GoLean.GoCore.Expr.var "ok"),
                    GoLean.GoCore.Stmt.returnStmt]],
    variadic := false,
    wrapper := false }

end GoLean.Examples.InsertionSort

namespace GoLean.Examples.WordCount

/-- Occurrences of `v` in `ws`. -/
def multiplicity (v : Int) (ws : List Int) : Nat :=
  (ws.filter (· = v)).length

/-- The largest multiplicity any value attains in `ws` (`0` for `[]`) —
a commutative-idempotent max-fold, so it is invariant under iteration
order: the shape the ∀-choices quantifier forces (§10b). -/
def maxMultiplicity (ws : List Int) : Nat :=
  ws.foldl (fun acc v => max acc (multiplicity v ws)) 0

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

/-- The returned fixed-cap array: the observed word list, zero-padded
to the harness's `wordcountCapN = 8` slots. -/
def goArr8 (xs : List Int) : GoValue :=
  .array ⟨(xs ++ List.replicate (8 - xs.length) 0).map
    (fun v => .int v .uint64)⟩

/-- The relational harness's `Func` record, verbatim from the pinned
lowering. The setup loop body is `wordcount_harness`'s, shared. -/
def wcHarnessRFunc : Func :=
  { id := { key := "wordcount_harness_r" },
    args := #[{ id := "n", typ := .int .uint64 },
              { id := "seed", typ := .int .uint64 }],
    results := #[{ id := "$res0", typ := .array 8 (.int .uint64) },
                 { id := "$res1", typ := .int .uint64 }],
    body := .block #[]
      #[.seqn
          #[.initialization { id := "$c11", typ := .slice (.int .uint64) },
            .makeSlice (.var "$c11") (.int .uint64) (.var "n") none],
        .seqn
          #[.initialization { id := "w", typ := .slice (.int .uint64) },
            .assign (.var "w") (.var "$c11")],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) wordcountHarnessFunc.suBody]],
        .seqn
          #[.initialization { id := "words", typ := .array 8 (.int .uint64) }],
        .block #[]
          #[.seqn
              #[.initialization { id := "i", typ := .int .uint64 },
                .assign (.var "i") (.intLit 0 .uint64)],
            .block #[]
              #[.initialization { id := "$forFirst", typ := .bool },
                .assign (.var "$forFirst") (.boolLit true),
                .while (.boolLit true) cpBody]],
        .seqn
          #[.initialization { id := "best", typ := .int .uint64 },
            .call #[.var "best"] ⟨"maxCount"⟩ #[.var "w"]],
        .seqn
          #[.assign (.var "$res0") (.var "words"),
            .assign (.var "$res1") (.var "best"),
            .returnStmt]],
    variadic := false,
    wrapper := false }
  where
    /-- The COPY loop's desugared body: `words[i] = w[i]` — the store
    target is an ADDRESS-rooted index chain (`.ref "words"`), because
    `words` is an array-typed LOCAL, not a slice handle. -/
    cpBody : Stmt :=
      .block #[]
        #[.ifThenElse (.var "$forFirst")
            (.assign (.var "$forFirst") (.boolLit false))
            (.assign (.var "i") (.add (.var "i") (.intLit 1 .uint64))),
          .seqn #[],
          .ifThenElse (.lessCmp (.var "i") (.var "n")) (.seqn #[]) .breakStmt,
          .block #[]
            #[.seqn #[.assign (.addr (.indexAddr (.ref "words") (.var "i")))
                (.indexGet (.var "w") (.var "i"))]]]

end GoLean.Examples.WordCount
