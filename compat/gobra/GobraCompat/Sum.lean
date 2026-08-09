import GobraCompat.SumProgram
import GobraCompat.Contract

/-!
# The tutorial `sum` contract, end to end (spike stage 1)

The Gobra tutorial's first example, carried through the whole proposed
pipeline: annotated canonical Go (`testdata/sum/main.go`, valid Go with
`//@` clauses) → native frontend (annotations invisible) → pinned GoCore
lowering (`SumProgram.lean`) → the contract transcribed into the Lean
fragment (`sumContract`, below — stage 2 automates this transcription
via a `"specs"` wire key) → the elaborated Surface statement
(`SumContractStatement`) → witnesses.

Status ledger (honest, per house style):
- `SumContractStatement` is a STATEMENT-FIRST target: stated, not yet
  proved. Its proof is the recorded next milestone — a `go_walk` WP walk
  where `wp_while_inv`'s invariant is exactly `sumLoopInvariant` (the
  annotation), instantiated over the machine state. That walk is the
  load-bearing feasibility item for "Gobra as a Lean-backed proof
  language" and is sized by the quorum-pilot precedent.
- The SEED WITNESSES below are proved (kernel evaluation): the pinned
  machine and the contract agree at concrete arguments, on both sides
  (machine run = value; contract post at that value). This is the
  non-vacuity discipline: the elaborated statement demonstrably talks
  about the real program and the real contract.
-/

namespace GobraCompat

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- `sum`'s `Func`, by position in the pin (checked by the guard below). -/
def sumFn : Func := sumLowered.funcs[0]'(by decide)

example : sumFn.id.key = "sum" := rfl

/-- The contract of `testdata/sum/main.go`'s annotations, transcribed
1:1 (`requires 0 <= n`, `ensures sum == n * (n+1) / 2`, the two loop
invariants, `decreases`). -/
def sumContract : GobraContract where
  requires := [.le (.lit 0) (.evar "n")]
  ensures := [.eq (.evar "sum")
    (.div (.mul (.evar "n") (.add (.evar "n") (.lit 1))) (.lit 2))]
  loopInvariants :=
    [ .conj (.le (.lit 0) (.evar "i")) (.le (.evar "i") (.add (.evar "n") (.lit 1))),
      .eq (.evar "sum") (.div (.mul (.evar "i") (.sub (.evar "i") (.lit 1))) (.lit 2)) ]
  terminates := true

/-- The adequacy guard (divergence #1, `Contract.lean` header): Gobra's
default unbounded `int` vs GoCore's machine `int`. Within this range the
loop never leaves int64, so the mathematical contract and the machine
agree. The bound is spec content — visible, auditable, and exactly the
obligation Gobra's own `--overflow` mode would impose. -/
def sumGuard (n : Int) : Prop := 0 ≤ n ∧ n ≤ 2 ^ 31

/-- **THE elaborated contract statement** — what "Gobra verifies `sum`"
MEANS over golean's semantics. Proof: recorded next milestone (the
`go_walk`+`wp_while_inv` walk fed by `sumContract.loopInvariants`). -/
def SumContractStatement : Prop :=
  contractStatement sumLowered.typeDefs.toList sumLowered.funcs
    sumLowered.methods ⟨"sum"⟩ .int "n" "sum" sumContract sumGuard

/-! ## Seed witnesses: machine and contract agree at concrete arguments -/

/-- Machine runs of the pinned lowering (the differential runner's own
entry point) at the annotated seeds. -/
def runSum (n : Int) : Except GoError Result :=
  runFunctionWithContextM 100000 sumLowered.typeDefs.toList sumLowered.funcs
    sumFn #[.int n .int] sumLowered.methods

/-- Boolean check: the machine run delivered exactly `expected` (fail-closed:
any error, missing value, or wrong kind is `false`). -/
def runSumIs (n expected : Int) : Bool :=
  match runSum n with
  | .ok r =>
    match r.values[0]? with
    | some (GoValue.int v IntKind.int) => v == expected
    | _ => false
  | .error _ => false

example : runSumIs 0 0 := by decide +kernel
example : runSumIs 1 1 := by decide +kernel
example : runSumIs 5 15 := by decide +kernel
example : runSumIs 12 78 := by decide +kernel

/-- The contract's postcondition, evaluated at the same seeds — tying
the witness to the CONTRACT, not just to the machine. -/
example : postHolds sumContract (envRes (env1 "n" 5) "sum" 15) := by decide
example : postHolds sumContract (envRes (env1 "n" 12) "sum" 78) := by decide
example : preHolds sumContract (env1 "n" 5) := by decide

/-- Negative twin (witness discipline): a wrong result REFUTES the
postcondition — the contract is not vacuously satisfiable. -/
example : ¬ postHolds sumContract (envRes (env1 "n" 5) "sum" 14) := by decide

end GobraCompat
