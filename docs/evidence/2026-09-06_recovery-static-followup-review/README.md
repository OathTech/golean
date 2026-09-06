# Independent RS-1 follow-up review

[AGENT], root integrator, 2026-09-06. **Bounded verdict: PASS.** The diagnostic
finding in the [original independent review](../2026-09-06_recovery-static-independent/README.md)
is resolved by the source identified in `sources.sha256`. The author must
still finish ordinary CI and provide its final source-bound evidence before
integration. No O2 runtime or Iris acceptance is implied.

The reviewer read `RecoveryDiagnostics`, the updated checker/equivalence
proof, all new diagnostic controls, the expanded source-origin/compiled-poison
gate, the actual fresh native excluded fixture and its checker, and the full
dedicated gate log. The new checks distinguish structural profile exclusion,
malformed bare-initialization placement, and scoped binding/sort/call-vector
failure. They do not claim to classify every arbitrary Go source error.

The original `FunctionTyped`, `ProgramTyped`, and `RecoveryAdmission`
definitions are unchanged. `Statement.in_profile` and `Statement.placement`
prove that every admitted statement passes the added checks. Soundness
discards the redundant checks; completeness derives them from typing.

`Review.lean` freshly compiles all seven complete current core source bodies,
omitting only imports, with no author-built recovery oleans. It also compiles
the original checker's source under `LegacyChecker`: the original
`checkFunction`, `checkFunctions`, `checkRecovery` and equivalence proofs are
copied from the sealed prior independent review, using the unchanged
judgment and common error constructors. The new generic
`diagnostic_acceptance_unchanged` theorem proves acceptance equivalence
between the two separately compiled checkers for every program, entry and
argument array. This is stronger evidence than updating only expected error
labels in tests.

All thirteen prior independent probes remain; only the final reproducer's
expected outside-profile diagnostic changes to `statementProfile`, while
the malformed unbound write still gives `body`. The proof and post-import
audit passed without warnings:

```text
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean docs/evidence/2026-09-06_recovery-static-followup-review/Review.lean
```

`review.log` records 5,078 local/imported declarations checked with only
`propext`, `Classical.choice`, and `Quot.sound` allowed. The author's fresh
full dedicated gate additionally checks twelve modules, 46 exports, five
compiled forbidden declarations, unchanged whole A2 and second-fixture
native artifacts, the actual typechecked `panic(true)` exclusion, and 5/5
native differential/control results. The reviewer inspected those executions
without representing them as duplicate independent gate runs.

The original CHANGES REQUIRED report remains sealed and unchanged. This
follow-up closes RS-1 and supplies bounded implementation acceptance of the
static recovery foundation together with that report's otherwise-positive
analysis. Generic setup/preservation/progress/readout, the admitted arbitrary
byte and equal-string panic cases, and reusable customer rules remain the
separate required O2 work.
