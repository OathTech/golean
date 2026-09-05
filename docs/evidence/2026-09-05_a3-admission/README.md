# A3 bounded admission evidence

[AGENT], 2026-09-05. Worktree `gate-a3-admission`, base `700128f3`.
This folder seals the initial implementation's validation before integration
with the later BUG-103/semantic-interface train. It makes no combined-tip
claim; subsequent rebased gates belong in the coordinator's integration
record. The exact API/domain is in
[the design note](../../2026-09-05_a3-admission-design.md).

## Fresh checks

`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/check-admission` exited 0
(`gate.log`). The final script built the test library, freshly elaborated
all six admission/test/audit source modules, and checked 375 complete-module
constants with 14 required theorem exports, allowing only `propext`,
`Classical.choice`, and `Quot.sound` transitively. The regression module
contains 32 kernel-checked theorem declarations. Imported build caches were
reused; this was not a clean Lean/dependency bootstrap.

All three negative audit fixtures compiled before the external audit
rejected their exact named axiom: a trailing private axiom in the audit
module, a private axiom in core `Admission`, and a trailing private proof
using `sorry` in the tests. Their source copies, compile/audit logs and
external harness are retained as text. Empty compile logs are intentional:
the gate required successful exit 0 before invoking the rejecting audit.
The live source/cache trees were unchanged by these poisons; each fixture
used an independent copy of its compiled package root.

The capped default `lake build` passed (68 jobs). Fresh Go 1.26.5 native
emission and actual `NativeToIR` lowering matched the complete checked
Boolean program artifact. `native.json` has SHA256
`b72ed5518a3b3928455da2f0839c30b29c15f01d85a8922ba6d785225df259af`.
This executable artifact comparison is not a compiler-correctness theorem.
The opt-in one-case manifest then passed Go-vs-Lean conformance: 1/1,
with the harness's choice-stream depth/invariance checks. Its result and
metadata are preserved. This is a dirty-worktree run bound to the recorded
source hashes, not a clean-commit certification or full-corpus rerun.

## Ordinary CI and cached scope

`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci` exited 0
(`ci-initial.log`): 198 interpreter eval checks, warning-free core build,
the admission audit/poison step, frontend/diagnostic checks, cached full
3593-case baseline comparison and cached 394-case negative comparison with
no regression. The two cached records originated at `75dcb6d`, Go 1.26.5,
and were copied from the main checkout with their metadata. CI explicitly
printed that staleness. Their metadata and matrix hashes are preserved;
the two historical result matrices themselves are not duplicated here.
No new full-corpus or slow-tier certification is claimed.

This ordinary CI run preceded the final gate's extra habitual fresh-source
elaboration step. The final dedicated gate above reran the complete admission
check after that strengthening. No core/proof/fixture source changed between
these two successful runs. The rebased combined tree still needs its own CI.

During implementation, the initial lexical guard mistook the diagnostic
string "forbidden axiom" for a source declaration; stripping string literals
fixed that false rejection while retaining the dependency audit. An initial
poison overlay contained only one child module, so Lean failed to find its
sibling module under the selected package root. The gate failed correctly;
copying the complete compiled root repaired the fixture. Neither failure
was counted as a successful poison rejection.

## Binding and reproduction

`source-sha256.txt` binds 16 source/configuration/oracle-pin files at this
initial gate. It excludes later prose edits and merge-conflict resolutions.
Run from the repository root with `sha256sum -c` to compare a candidate
tree with that initial source set. `SHA256SUMS` seals the artifacts in this
folder and is checked from this directory.

The scripts use the worktree's Go cache, unique worktree-local scratch,
the pinned Lean toolchain and `scripts/capped`. Their scratch is retained.
Reproduce the complete check with `scripts/check-admission`; use
`scripts/check-admission --lean-only` for the CI proof/audit subset.
The independent reviewer record and its separate boundary probes are
identified by the dated handoff/review note after their final sealing.
