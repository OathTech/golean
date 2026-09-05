# Gate A1 — current-machine consumer contract spike

This separate Lake package tests a consumer interface against GoLean at
`79019a74c1e1c1418293d380d1fcfbd9ae489980`. It does not change the
interpreter, frontend, default build, or semantics gate. Its dependency on
GoLean is the enclosing checkout, not a frozen copy of an older machine.

Run from the repository root:

```sh
bash spikes/gate-a1/check
```

The command builds the normal project, builds the separate spike, freshly
elaborates its modules, checks their transitive axiom dependencies after
importing the complete package, runs evaluation probes and three negative
audit regressions, and prints a source/manifest fingerprint. It fails on
build errors, forbidden proof escapes, missing exports, or modified/mismatched
dependency checkouts. Dependency pins are checked before and after building;
module inventory changes require an explicit gate update. Run it after changes to the core, observations, driver,
toolchain, or this package. It does not run the differential corpus.

Lean is pinned to 4.32.2; Iris, Batteries and Qq are pinned in
`lake-manifest.json`. Iris uses the archived GoLean experiment's
`e7a0a43814c4f1154ca0c8049883ca56c2288b86` revision. A first build fetches
dependencies if they are absent. The A1 session used local copies at these
exact revisions because GitHub access through the session proxy returned 403;
it was not a clean-room dependency bootstrap. Dependency sources were not edited.

| Module | Claim |
|---|---|
| `Trace` | Counted, choice-threaded prefixes; exact successful sequential-run bridge; erasure to `Steps` |
| `Counterexamples` | Recovery/context refutation, real two-choice refutation, narrowness of `StateWf` |
| `PoolTrace` | Exact pool-driver trace, including fuel, exit choices, detector state and output; successful erasure to `StepM` closure |
| `ProgramTrace` | Entry/readout bridge to `runProgramPoolOutM`; observation projection excludes refusals and fuel exhaustion |
| `Language` | Bare sequential Iris `Language`; a continuation-sensitive recovery WP rule |
| `Examples` | Two outcomes of the real probe choice; print-before-panic program; seven-step recovery check with Iris WP and actual-driver non-vacuity |
| `Audit` | Post-import action checking required exports and all spike-module constants against the classical axiom trio; invoked by `gate_checks.py` |
| `Probes` | Compiled evaluations, separately labelled from proofs |

The Iris example proves a pure control rule with an abstract customer resource
interpretation. This package does not supply heap ownership, a frame theorem,
a generic bind rule, or general Iris-to-whole-program adequacy. Its bare
sequential adapter has no I/O observation channel and is not the pool driver.
The full output-bearing bridges are separate, proved in the semantics-facing
modules. Read the [decision note](../../docs/2026-09-05_gate-a1-contract.md)
before treating any of these as a release interface.

The [adversarial review and next-phase proposal](../../docs/2026-09-05_gate-a1-review-and-next-phase.md)
records the gate repair, its independent re-review, and proposed integration.
