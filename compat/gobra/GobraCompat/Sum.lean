import GobraCompat.SumProgram
import GobraCompat.Contract
import GobraCompat.Parser

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

/-- The VERBATIM clause texts of `testdata/sum/main.go`'s `//@` comments
(the stage-2 `"specs"` wire key ships exactly these strings; transcribing
them as literals is the one remaining manual step in the pipeline). -/
def sumClauseTexts : List String :=
  [ "requires 0 <= n",
    "ensures  sum == n * (n+1) / 2",
    "decreases",
    "invariant 0 <= i && i <= n + 1",
    "invariant sum == i * (i-1) / 2",
    "decreases n - i" ]

/-- **Round-trip**: parsing the annotation text yields EXACTLY the
transcribed contract the elaborated statement uses — the transcription
step is now machine-checked, not trusted (fail-closed: parse error or
any mismatch is `false`). -/
def sumRoundTripOk : Bool :=
  match parseContract sumClauseTexts with
  | .ok ct => decide (ct = sumContract)
  | .error _ => false

example : sumRoundTripOk := by decide +kernel

/-- The adequacy guard (divergence #1, `Contract.lean` header): Gobra's
default unbounded `int` vs GoCore's machine `int`. Within this range the
loop never leaves int64, so the mathematical contract and the machine
agree. The bound is spec content — visible and auditable.

CLAIM CORRECTED (pre-merge audit): this is NOT "exactly the obligation
Gobra's own `--overflow` mode would impose". `--overflow`
(`OverflowChecksTransform.scala`) assumes argument bounds at body entry
and asserts per-STATEMENT subexpression bounds over int64, and it
explicitly adds no checks to assertions or predicates. Our guard is an
input-range precondition, which is a different shape — sufficient here
(at `n ≤ 2^31`, `n(n+1)/2 ≈ 2.3e18 < 2^63`, so no intermediate leaves
int64) but not the same obligation. -/
def sumGuard (n : Int) : Prop := 0 ≤ n ∧ n ≤ 2 ^ 31

/-! The statement below names `"n"` and `"sum"` as the parameter and
result. Nothing in `contractStatement` can check those against the
lowered function — the connection was previously by eye, and getting it
wrong makes a clause read an unbound name (worth 0 under `env1`), which
is precisely the vacuity `scopedBy` exists to stop. These pin it. -/
#guard sumFn.args.map (·.id) == #["n"]
#guard sumFn.results.map (·.id) == #["sum"]
#guard sumContract.scopedFor "n" "sum"


/-- **THE elaborated contract statement** — what "Gobra verifies `sum`"
MEANS over golean's semantics: `sum`'s contract carries `decreases`, so
this is the TOTAL judgment (triple + safety + termination). Proof:
recorded next milestone (the `go_walk`+`wp_while_inv` walk fed by
`sumContract.loopInvariants`). -/
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
