# Minimal Iris customer

An opt-in test customer for the current GoLean machine, authorized by the
user on 2026-09-05. It builds a small separation logic on iris-lean and proves
a native-frontend GoCore program with a helper call, defer, recovery and a
named result. It is an interface experiment, outside the semantics default
build. It is not a general Go verification product.

Run from the repository root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 \
  bash spikes/iris-customer/check
```

The separate package pins Lean 4.32.2 and Iris
`e7a0a43814c4f1154ca0c8049883ca56c2288b86`. It consumes GoLean by relative
path and the reviewed A1 adapter in `../gate-a1`. First dependency installation
requires network access or exact, independently copied local checkouts.
Current evidence uses the latter; it does not certify a clean bootstrap.

## The exercise

`fixtures/recovery/main.go` contains three entry points:

```go
func Recovered() (result bool) {
    defer func() {
        if recover() != nil { result = true }
    }()
    fail() // panics; the ordinary return below is not reached
    return false
}
```

`Normal` returns `true` normally. `Uncaught` calls the same panicking helper
without installing a defer. All three run through the existing Go-vs-Lean
harness, including its choice-stream observation checks. They are opt-in
customer fixtures, not new entries in the semantics corpus baseline.

`Program.lean` records the actual lowered artifact, including the closure's
capture parameter, recovery temporary and type metadata. The gate freshly
emits and lowers the Go file and compares the complete derived representation
to that artifact. This is an executable translation regression, not a
compiler-correctness theorem. The Lean theorems are about this GoCore artifact.

## What is proved

| Module | Contract |
|---|---|
| `Heap` | Exact map projection of every dense `HeapCell`; lookup, in-bounds update and fresh append |
| `Ghost` | Iris `gen_heap` authoritative ownership of that projection; equality of all immutable context fields; a concrete resource bundle |
| `Lifting` | Actual `Step`/`stepFn` lifting: context-preserving steps, fractional reads, full-ownership writes and allocation |
| `Rules` | Variable load, normalized store, initialization, explicit-continuation recovery, interface-vs-nil comparison, frame and consequence |
| `Examples` | Normal and recovered named-result WP proofs; the helper and deferred-entry rules are specific to this program |
| `Adequacy` | Initialize Iris resources, give the initial heap to the client, and extract final-state facts through actual `execStmtLoop` |
| `Readout` | Instantiated adequacy, an arbitrary preserved frame cell, and transfer through the singleton pool driver with explicit premises |
| `Driver` | Actual setup, bounded termination, absence of registry boundary steps, named-result readout and whole-program controls |
| `Audit` | Post-import transitive axiom sweep, including A1, private/generated constants, the aggregate and trailing declarations |

`recovered_program` states:

```lean
runProgramPoolOutM 60 recoveryProgram "Recovered" #[] [] =
  .ok { values := #[.bool true], output := .empty }
```

The value claim passes through `wp_recovered`, the instantiated
`recovered_adequate`, and `adequate_program_result`. It is not merely a direct
computation of the final value. Separate kernel-checked computations provide
the finite successful execution witness, zero `seqOpCount`, and silence.
WP provides partial correctness and non-stuckness, not termination.

`normal_program_result` obtains the normal control's value through the same
Iris path. `uncaught_program` proves the explicit panic observation. The
latter is an executable theorem, not a successful `NotStuck` WP claim.
`framed_normal_adequate` starts with a concrete two-cell heap, updates the
result cell and proves the arbitrary second cell unchanged.

## Boundaries that remain visible

- A1's `Language` wraps the actual sequential configuration and state, with
  `Unit` as its terminal value and empty observations. Result values come
  from owned heap cells and actual named-result readout. There is no
  unconditional `EctxLanguage` or continuation-transport law.
- The generic lifting rules require a successful, choice-stream-preserving
  step for every stream under their resource/context premises. This fits the
  chosen program; it does not cover all nondeterministic Go operations.
- The whole-program examples use fuel 60, empty arguments and the empty
  initial choice stream. The generic pool transfer requires a successful
  sequential witness and zero registry boundary count at the same fuel.
  It retains the actual output; the recovered example proves silence
  separately. It does not establish general concurrent or labeled adequacy.
- Ownership is at whole root-cell granularity. Field/index paths live inside
  a cell; field splitting, slices, overlapping regions and concurrency need
  further design. There is no allocation/deallocation logic beyond append.
- `ContextEq` pins types, functions, methods, method sets and display metadata.
  It is satisfiable for the initialized model, but it is not Go typing.
  Heap address bounds and value normalization are not typing either.
- The customer still imports machine internals and unfolds some operations.
  These dependencies are recorded API work, not a stable facade promise.

## Validation and next phase

The gate builds the core and package, freshly elaborates every customer
module, requires named exports, audits transitive axioms against
`propext`/`Classical.choice`/`Quot.sound`, and requires three compiled poisoned
imports to be rejected. It also verifies tracked-clean exact dependency
revisions, source/artifact provenance and the three differential cases.
The intentionally poisoned scratch files are not live source modules.

See the [design and next-phase assessment](../../docs/2026-09-05_iris-customer-design.md)
and [sealed validation evidence](../../docs/evidence/2026-09-05_iris-customer/README.md).
The next semantic work should promote the semantics-owned A1 bridges through
an experimental facade, define a narrow admission contract, and rebuild this
customer across B7/C1. A full downstream logic and general call specifications
remain separate work.
