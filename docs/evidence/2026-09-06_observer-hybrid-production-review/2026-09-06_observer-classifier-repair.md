# Oracle panic/fatal classification: production candidate

2026-09-06. [AGENT] typed-contract-review. **Candidate for independent
implementation review; full differential and final CI still owed.** No
baseline reconciliation or main merge has occurred.

The prior classifier accepted a fatal unwind as a panic, and an intermediate
system-trace classifier still read program-printed panic text as the actual
payload while discarding output. The minimal red regression was
`print("panic: forged\n\t"); panic("actual")`: it returned message
`forged` with empty output. The fresh kernel-free Go unit regression failed
with exactly that value before the replacement. Independent findings and
the stopped, incomplete full run remain in the evidence directory.

The replacement implements the independently reviewed
[crash-channel design](2026-09-06_observer-crash-channel-design.md):

- The oracle installs `runtime/debug.SetCrashOutput` before calling the
  subject, without a recover/defer wrapper. The runner resets owned report
  and acknowledgement files before every plain/race draw. Setup failure
  exits the child with 78, preserving `go run`'s exit and yielding a named
  setup refusal.
- `crashview.go` gives kind, first-line message and output a shared checked
  view. The complete report must be a byte-identical stderr suffix, before
  UTF-8 validation or JSON encoding. Its raw first runtime origin uses the
  pinned same-execution system traceback contract. Program output is the
  exact prefix before that suffix.
- Malformed/missing paired evidence, failed registration, unknown origins,
  additional report markers after the origin, corruption and suffix mismatch
  refuse. Successful observations require registration and an empty report.
- Fatal messages precede the runtime's crash-copy boundary. Their fallback,
  and init panics before registration, count all raw markers with no
  continuation exemption. Ambiguous payload/output is a named observation
  refusal; terminal kind is never guessed from the expected manifest status.
- `--copy-oracle` inserts the same hook into a fresh diagnostic oracle
  package copy. AST positions locate the real main opening brace; all other
  source bytes remain exact. It refuses missing/duplicate main, reserved
  helper collisions and reused output directories. Diagnostic runner wiring
  is a separate increment; its semantic frontend sources must stay intact.

No GoCore semantics, UTF-8 replacement policy, payload boxing identity,
Go toolchain pin or race observation policy changed. The owned file is a
trusted runtime transport, not cryptographic authentication of caller-forged
matching capture files. Runtime configuration, arbitrary file/fd manipulation
and resource-accounting effects remain outside the admitted source domain,
as explained and probed in the design. O2 admission retains arbitrary string
bytes and repeated panic; invalid-UTF-8 text membership is a separate R-1
obligation, not silently decoded here.

## Measured evidence at this checkpoint

`docs/evidence/2026-09-06_observer-classification/` retains source-bound logs,
raw counterexamples, prototype history and the following production results:

1. `minimal-red.log`: fresh Go test fails on the pre-repair source with
   message `forged`; the same test passes with the new strict fallback.
2. `hybrid-gate-final.log`: fresh helper build/unit tests, 47 extracted
   strict/sampling controls, 28 actual Go plain/race controls, two actual
   setup-IO failures, and 11 compiled corruption mutations rejected. The
   final run is under a verified 16 GiB cap and Lean threads 3; this matters
   because shell controls also invoke the existing Lean JSON comparator.
3. `focused-hybrid.tsv`: fresh Go/Lean run, 23 rows = 22 PASS and one
   FAIL/go-observation. All eleven marker rows include the minimal
   print/literal pair, glued output and a complete printed fake trace. The
   nine existing byte controls and two simple sync fatals also pass.

The exact changed existing row is
`sync/mutex-unlock-fatal/during-panic-unwind`: previous PASS/stage `-` →
FAIL/stage `go-observation`, cause `ambiguous fatal message/output before
m.dying`. This reveals a lost authenticated observation. Independent design
review `aafe225b`, explicit fidelity-boundary disposition `ab2ad4d5`, and the
root coordinator endorse that correction under K3/fail-closed. The refusal
is not conformance, not a GoCore terminal and not B7 equivalence drift.
The raw full differential must still measure every resulting row/stage
change before narrowly justified baseline reconciliation.

Relevant commands from this worktree:

```sh
env GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped \
  python3 scripts/check-observer-controls.py
env GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 \
  GOLEAN_COVERAGE_ARTIFACTS=artifacts/observer-classification/focused-hybrid \
  scripts/capped scripts/coverage run \
  --prefix panic-recover/panic-markers/ \
  --prefix panic-recover/panic-controls/ --prefix sync/mutex-unlock-fatal/
```

The first command exits 0. The focused differential exits 1 because its
explicitly reported refusal remains a failed observation. Neither that
result nor the earlier stopped full run is a green full baseline.
