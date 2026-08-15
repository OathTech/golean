import GoLeanProofs.Examples.StringReverseProgram

/-!
# StringReverse — the `strrev` example (Gallery Campaign G1, guardrails wave)

**STATUS: GUARDRAILS ONLY — no headline theorem yet.** This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`StringReverseProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/strrev-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.StringReverse` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/strrev/main.go`,
differentially green against `go run` — those rows are the guardrail
that pins the target BEFORE the proof exists.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `strrevHarnessRFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
-/

namespace GoLean.Examples.StringReverse

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def strrevHarnessRFunc : Func :=
{ id := { key := "strrev_harness_r" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
            { id := "seed", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.string },
               { id := "$res1", typ := GoLean.GoCore.Ty.string },
               { id := "$res2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "pre", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "pre"]
                    { key := "buildStr" }
                    #[GoLean.GoCore.Expr.var "n", GoLean.GoCore.Expr.var "seed"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization { id := "post", typ := GoLean.GoCore.Ty.string },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "post"]
                    { key := "reverseString" }
                    #[GoLean.GoCore.Expr.var "pre"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "isPalin", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "isPalin"]
                    { key := "isStringPalindrome" }
                    #[GoLean.GoCore.Expr.var "pre"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "pre"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res1")
                    (GoLean.GoCore.Expr.var "post"),
                  GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res2")
                    (GoLean.GoCore.Expr.var "isPalin"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem strrevHarnessRFunc_pin :
    findFunctionIn? strrevLowered.funcs ⟨"strrev_harness_r"⟩
    = some strrevHarnessRFunc := rfl

end GoLean.Examples.StringReverse
