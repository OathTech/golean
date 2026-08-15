import GoLeanProofs.Examples.SieveProgram
import GoLeanProofs.Examples.Sieve.Pure

/-!
# Sieve — the `sieve` example (Gallery Campaign G1, guardrails wave)

**STATUS: GUARDRAILS + PURE SPEC LAYER — no headline theorem yet.**
The pure specification layer (`Examples/Sieve/Pure.lean`: trial-division
`isPrime`, the loop mirrors, and `sieveTable_spec`/`sieveAnswer_eq` — the
sieve computes primality and the count is `primeCount`) is landed and in
the audited closure via this import; the MACHINE half is the open work. This root carries
exactly the corpus half of the G1 checklist: the pinned lowering (via
`SieveProgram`, itself pinned by `scripts/check-golden` against
`baselines/golden/sieve-lowered.repr`) and the named harness
transcription below, tied to that lowering by `rfl`. The proof lane that
adopts this example states its headline HERE, in this root, so the
aggregator's `import GoLeanProofs.Examples.Sieve` reaches it by name
(the C-H4/C-H5 shape, adopted from birth).

Go source: `Corpus/coverage/exec/examples/sieve/main.go`,
differentially green against `go run` — those rows are the guardrail
that pins the target BEFORE the proof exists.

The harness `Func` below is EXTRACTED from the pinned repr rather than
hand-written, so `sieveHarnessFunc_pin` checks a transcription that is
byte-derived from the lowering. A proof lane may restate it in the
readable dot-notation form; the pin must keep holding by `rfl`.
-/

namespace GoLean.Examples.Sieve

open GoLean GoLean.GoCore

/-- The harness `Func`, verbatim from the pinned lowering (the pin below
ties it by `rfl`). -/
def sieveHarnessFunc : Func :=
{ id := { key := "sieve_harness" },
  args := #[{ id := "n", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  results := #[{ id := "$res0", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) }],
  body := GoLean.GoCore.Stmt.block
            #[]
            #[GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.initialization
                    { id := "$c2", typ := GoLean.GoCore.Ty.int (GoLean.GoCore.IntKind.uint64) },
                  GoLean.GoCore.Stmt.call
                    #[GoLean.GoCore.Assignee.var "$c2"]
                    { key := "countPrimes" }
                    #[GoLean.GoCore.Expr.var "n"]],
              GoLean.GoCore.Stmt.seqn
                #[GoLean.GoCore.Stmt.assign
                    (GoLean.GoCore.Assignee.var "$res0")
                    (GoLean.GoCore.Expr.var "$c2"),
                  GoLean.GoCore.Stmt.returnStmt]],
  variadic := false,
  wrapper := false }

/-- The lowering pin: the harness subject IS the frontend's lowering. -/
theorem sieveHarnessFunc_pin :
    findFunctionIn? sieveLowered.funcs ⟨"sieve_harness"⟩
    = some sieveHarnessFunc := rfl

end GoLean.Examples.Sieve
