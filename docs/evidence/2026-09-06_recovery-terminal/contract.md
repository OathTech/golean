# Typed recovery terminal and output contract

[AGENT] Author draft, 2026-09-06. This increment closes the generic terminal
obligation above the unchanged `RecoveryAdmission` profile. Source-bound
independent review, dependency reconciliation and facade/customer integration
remain required. This is not complete O2 acceptance.

`RecoveryTerminal.Inv.run_classified` is named in Lean as
`GoLean.GoCore.RecoveryRuntime.Inv.run_classified`. For every fuel and every
original `Choices` list, an invariant state produces normal sequential
completion preserving that list, a panic whose text is `stringPanicHead` of
some actual boxed-string head, or fuel exhaustion. The proof inducts on the
supplied fuel and uses structural control progress, relational preservation
and the total string renderer. It does not assume a successful future run,
successful setup, a terminal record supplied by the caller, a renderability
predicate or an admissible subset of string bytes.

`runProgram_typed` obtains actual `runProgramSetupM` success and its invariant
from admission through `setup_inv`. On normal completion it reads the actual
external result roots using `loadMany`; `ParamsValues` gives the declared
result types and the theorem gives their arity. `runProgramPool_typed` carries
the classification to the shipped `runProgramPoolOutM` at the same fuel.
Normal, panic and exhaustion outcomes each have empty output. The sequential,
pool and observed-program `*_no_refusal` theorems exclude every `Refusal`
constructor, with no premise assuming the run succeeds.

`Inv.pool_observation_eq` relates the actual singleton pool observer to the
actual sequential observer at identical fuel, initial state, choice stream,
race state and output prefix. It proves completeness of computed metadata,
including the pool's abort-to-tombstone transition. `Inv.observer_classified`
and `runProgramPoolWithAbort_typed` put `some record` on every admitted panic
and `none` on normal completion and exhaustion. The record preserves complete
head bytes, recovered flag and every tail entry; the prior source-bound
`runProgramPoolWithAbort_witness` and `Inv.observed_abort` theorems identify
the actual reached transition and chain. `runProgramPoolWithAbort_panic_iff`
states the exact panic/record correspondence for the actual program driver.

The unconditional `stepAbortRecord?_member`, `PoolAbortWitness.string_member`
and `runProgramPoolWithAbort_member` apply even to broader, untyped subjects
when their actual observer emits a record. They prove equality with the
renderer member selected from the record's entire head bytes and recovered
flag. They make no typing or metadata-completeness claim for those broader
subjects. They preserve the observed output instead of asserting silence
outside the typed profile. `stringPanicHead` is R-1's selected text member;
these equalities do not turn it into a proved Go-source compiler theorem or
claim gc's allocation-dependent recovered/repanicked collapse.

## Claim and assumption ledger

The evidence `claims.json` lists all 32 advertised kernel theorems with their
full elaborated types and source modules: 22 reusable semantic contracts and
10 challenges. Constructor-style pretty printing retains default-valued
fields such as empty output. The following policies apply to each entry;
its recorded kernel type identifies which premises occur.

| Claim family | Profile and premises | Choices, resources and terminal/output policy |
|---|---|---|
| `Inv.*` | Explicit current structural `Inv`; `runProgram*` derives it from admission | Every supplied list; fuel is a visible arbitrary natural. Sequential success retains the original list. The singleton pool preserves its supplied byte prefix. Panic and fuel are distinct. |
| `runProgram_typed`, `runProgramPool_typed`, `runProgramPoolWithAbort_typed`, their refusal and panic/record corollaries | The independently checked whole-program `RecoveryAdmission`, with no added restriction | Actual existing default platform and fresh driver state; unbounded Lean heap arrays have no extra capacity premise. Empty output on every classified result. No generic sufficient-fuel or unbounded-termination claim. |
| Record member and witness theorems | An actual computed record or actual pool witness, sometimes an explicit current invariant | Fuel, state, choices and prefix remain those of the observed run. A run equation identifies the observation being analyzed; it is not the premise of the unconditional safety classification. |
| `Control.*`, `singleton_observer_string_abort`, `attachAbort_private`, `runConfigWithAbort_nonpanic` | Explicit local control, step, head value or nonpanic outcome premise in the recorded type | Supporting correspondence facts; they do not advertise whole-program admission, termination or Iris ownership. |
| `TerminalTests.*` | Fixture checker proofs, arbitrary byte/list parameters, explicit structural invariant, or concrete reached abort frontier as recorded | Kernel checks distinguish zero fuel, initialized false readout, full panic bytes/flags/tails, and unchanged prefixes. Full invalid-byte/multiline/repanic program runs are separately executable tests. |

All kernel entries are proved using only the classical foundational trio;
independent review is pending. Admission/setup/invariant and renderer
dependencies are already separate named contracts, pinned by source hash in
this draft. Their own reviews and integration status are not replaced by
this gate. Actual native translation and Go fidelity remain tested facts
owned by the shared-customer and R-1 evidence. Iris pointee ownership, WP
resources and fixture termination bounds remain with the customer; this
module manufactures none of them. General dispatch, concurrency, methods,
arbitrary interfaces and runtime-error inspection remain outside the
approved structural recovery profile.

## Validation and retained attempts

Run `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash scripts/check-recovery-terminal`.
The gate builds then freshly elaborates both semantic modules, the complete
test module and the post-import audit. It sweeps every declaration from every
imported local origin, including unused private helpers and declarations
after the audit definition. Five poisons must first compile, then fail that
same audit: each new semantic module, the test module, the audit module, and
a trailing test theorem using a forbidden proof escape. Their logs and all
exact theorem types are retained under the printed unique scratch directory.

`Tests/RecoveryTerminal.lean` also executes three whole-program challenges
through the actual pool observer: invalid UTF-8/control bytes, LF with bytes
after it, and equal repanic retaining the recovered head plus new tail entry.
Each checks exact member text, output, bytes, flags and chain tail. Those
checks are tests; the unconditional and frontier claims are kernel proofs.

[AGENT] The first whole-pool kernel challenge attempt exited 137 after 40
seconds under the unchanged 16 GiB cap. Its source and log are preserved in
the evidence. The final approach uses a generic, kernel-proved pool abort
frontier rule and explicit executable whole-program challenges. Earlier
ordinary elaboration failures are retained too. Failed attempts are never
counted as validation success.
