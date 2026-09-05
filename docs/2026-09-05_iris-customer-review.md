# A2 adversarial review

[AGENT] independent reviewer `iris_customer_adversarial`, 2026-09-05;
recorded by the coordinator after the [USER] authorized both branch reviews.
Reviewed commit: `2f0a5a0386c23f8ecf0514bb2e6588df9ba3cada`.
Base: `8db2d6dad165393f4d3cdffee63b8e7d624f39e6`.

**Verdict: PASS for the bounded A2 spike. No blocking findings or required
code changes.** This supports retaining the customer after separate merge
sign-off; it does not close the remaining Gate A obligations.

## Scope and findings

The reviewer read every new customer proof module, package/gate
configuration, fixture, artifact checker, evidence record and material
documentation claim, plus the actual GoLean and pinned Iris definitions
supporting the proofs. The review did not edit live source.

| Adversarial question | Result and source |
|---|---|
| Is ownership initialized and nonvacuous? | `Ghost.lean` provides a concrete resource bundle; `Adequacy.lean` allocates the authoritative heap and initial points-to assertions. `Readout.lean` instantiates this construction and extracts actual array lookups. No abstract ghost-state assumption escapes into the program theorem. |
| Does the state interpretation describe this machine? | `Heap.lean` proves lookup, bounded update and fresh append correspondence. `ContextEq` pins every immutable `ExecState` field while allowing heap changes. Ownership is explicitly distinguished from Go typing. |
| Does lifting consider every relational successor? | `step_unique` uses existing `step_complete`; lifting premises require successful execution for every choice stream. Universal Iris step reasoning is not replaced by one favorable executable choice. |
| Is recovery checked against the real continuation? | `wp_recover_assignment` exposes assignment/sequence frames, the non-wrapper deferred frame and the suspended panic. The recovered WP follows closure capture, allocation, recovery, loads and store without assuming continuation transport. |
| Does the returned value actually depend on Iris? | `recovered_program_result` obtains the cell through `recovered_adequate`; `adequate_program_result` transfers the readout through `execProgLoop_single` and `execProgLoopOut_snd` to the real runner. Separate termination and silence checks do not supply the returned-value equality. |
| Are scope and provenance stated accurately? | Fuel, arguments and initial choices are explicit. Native artifact matching is an executable regression, not compiler correctness. The axiom sweep runs after complete imports and includes private, aggregate and trailing declarations. |

## Reproduced checks

The complete dedicated gate was independently rerun:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 \
  bash spikes/iris-customer/check
```

It exited **0**: core/package builds and fresh customer elaborations passed;
all **941 constants** passed the transitive axiom audit; all three compiled
poisoned imports were rejected; fresh native lowering matched the proof
artifact; and **3/3 differential cases passed**. The source fingerprint and
native-wire hash matched the sealed implementation evidence. All 16 original
evidence hashes and all 21 package-source hashes also verified.

The reviewer then changed the deferred handler's `boolLit true` to
`boolLit false` in an isolated copy of `Program.lean` and re-elaborated the
unchanged examples against it. The altered artifact compiled. The proof
failed at `Examples.lean:151` on exactly this obligation:

```lean
normalizeValueForTy state Ty.bool (GoValue.bool false) =
  Except.ok (GoValue.bool true)
```

This independently confirms that the recovered result proof is sensitive
to the actual handler store. The live proof sources were untouched.

The [review evidence](evidence/2026-09-05_iris-customer-review/README.md)
preserves the full gate log, mutation source and failure log, with hashes.
The original implementation evidence remains unchanged.

## Remaining limits and integration

The existing limits remain necessary: whole-root-cell ownership over a
concrete sequential example is not typed admission, general call/continuation
composition, concurrent adequacy or a verified frontend. Dependency pins and
tracked cleanliness were checked, but the entire upstream source was not
freshly elaborated and clean network bootstrap was not tested. These are
disclosed scope limits, not findings blocking this bounded customer.

[AGENT] coordinator checks independently verified source/evidence hashes and
the BUG-103 baseline delta. The two branches overlap only in `HANDOFF.md`.
No combined-tree execution was performed. Any later integration must resolve
that handoff, rebase the second branch, run applicable gates and obtain the
charter's required sign-off on the resulting candidate. Main remains clean
at the base above; no merge or push has been performed.
