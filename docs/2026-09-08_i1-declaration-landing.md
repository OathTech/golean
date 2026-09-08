# I1 strict declaration boundary — implementation and review record

[AGENT] 2026-09-08, `land/i1-declarations`; implementation under the
[user-authorized charter](2026-09-08_i1-declaration-landing-charter.md).
The committed-source certification and audit disposition are recorded below.

[AGENT] Current disposition, 2026-09-08: the [second review](evidence/2026-09-08_i1-declarations/coordinator-review-update.md)
at `4eb2ab1c` is **MERGE-CLEAN**. Its sole required follow-up, N5, is fixed
by master-plan-v2 §2.2 R10, which queues the fixture re-pin authorization
guard; N1 is carried explicitly with R7's production boundary. [USER]
authorized this documentation fix and landing on main. This supersedes
the historical pauses below. Runtime source remains `061904f0`, independently
reviewed and gated at `4eb2ab1c`; no fixture or executable pin changes.

[AGENT] Final review-follow-up validation, 2026-09-08: `git diff --check`,
`scripts/check-evidence-size` and `scripts/check-agents-alias` pass; the
tracked second review compares byte-identically with the supplied file.
`tools/reconcile-records` reports the same two existing C13/C5 findings,
zero HIGH. Diff against `4eb2ab1c` outside `docs/` is empty. These are
fresh documentation checks; the full runtime `--diff` certification is
the clean second-review run at `4eb2ab1c`, whose log SHA256 is
`a608287bc37c7cdea3c6fb4d537b98d01c45fe050c99a74e7fa092cc25cf1090`
(`.tmp/review2/ci-diff.log`, PASS, captured `EXIT=0`). No fresh full runtime
run is claimed for this documentation-only follow-up. The whole branch
leaves both merge-protocol 5a paths unchanged, so no merged-tip `--slow`
re-certification is owed.

[AGENT] Review-status addendum, 2026-09-08: the coordinator supplied an
independent **FIX-FIRST** review at `8b4a1aec`. The user authorized corrections
and a pause for a second review. The [review response](2026-09-08_i1-review-response.md)
supersedes the pending first-audit disposition and the original readiness
statement below; previous gate results remain evidence only for their named
source commits.

[AGENT] Correction completion, 2026-09-08: fixes at `061904f0` passed both
the candidate and clean committed-source full `--diff` gates, with unchanged
3,654 executable / 394 negative baselines. The review response contains the
final evidence and handoff. The branch is **paused for the second review**;
the earlier readiness statement does not authorize a merge.

## Result and scope

The separate native declaration producer, strict raw-byte JSON parser and
Lean declaration decoder are assembled with a dedicated CI step. The boundary
describes closed declaration identities even when a corresponding executable
operation is unsupported. `Declaration.equality_exact` remains the unchanged
kernel theorem about equality of the representation. Agreement with Go type
identity is differential evidence over named tests, not a universal theorem
about arbitrary unchecked types or independently constructed package objects.
The nominal inventory's completeness and common checked-source provenance
remain the future package adapter's obligation.

The default executable build, `NativeToIR`, core runtime, executable wire and
supported-program profile are unchanged. Production I1 package integration,
query-preservation proofs, guard closure and marker removal remain outstanding.
The four imported September 6 notes are labeled historical; their old run
claims and evidence pointers concern the retained prototype branch.

## Source selection and fixes

Source selection: `typed-i1-json` at
`7ac3eb46bb3e2fe9c15b86b509569ef086327453`, fifteen selected source/doc blobs,
listed in [source-selection.tsv](evidence/2026-09-08_i1-declarations/source-selection.tsv).
The core declaration identity module and I1 spike already on main were reused.
No whole branch or dirty prototype tree was merged.

**A-R11, enforced fixture bytes.** `scripts/check-declarations` now compares
the freshly emitted JSON with `Tests/declaration-fixture/SHA256SUMS` before
running the Lean reader. The digest `26748fff476161bf0946095a26f6aaf01b191d40f98219a42faada33ceef3f3c`
was freshly reproduced at Go 1.26.5 and matches the retained prototype's
`fresh-go-fixture.json`. The same pin check rejects a copy with an extra
trailing space, which remains valid JSON. Fresh elaboration preserves Lake's
`--setup` metadata, following the landed recovery-terminal gate convention.

**A-R12, query isolation.** A declaration query constructs a private emitter
from checked source handles and copied active substitution inputs. Its mutable
identity/display/diagnostic registries and `types.Context` cache are fresh.
It does not shallow-copy the executable emitter or borrow its maps/slices.
Existing identity/substitution algorithms remain shared; no executable helper
was edited. Local identities, generic substitutions and stencil-local keys
retain their existing spelling and named refusals.

Red-first tests reproduced four state mutations, including two that poisoned
subsequent executable emission: an unknown local declaration and a foreign
package whose path contains a dot. Both success and refusal now preserve the
emitter state and byte-identical whole-program wire in those controls.
Additional controls cover active substitutions, private instantiation caches,
nested stencil keys and failure while rendering a stencil argument.

Missing-package controls formerly accepted a fabricated nominal named `error`
and unexported members with no defining package. The producer now refuses them
by name while retaining the actual universe object `error`. A package's empty
path is also refused where identity needs it. Exported member identity remains
package-independent. This strengthens the separate schema boundary, not the
production frontend's support boundary.

The lowerdiag inventory gains the eight prototype refusal formats and two
missing-package formats. Fresh vocabulary: 392 formats, 355 classified,
37 unclassified. These separate-channel diagnostics are recorded without
changing the classifier or its 90% gate threshold.

## Validation

**Author review finding I1-R1.** A scratch probe found that the prototype
refused anonymous constraint-only interfaces but accepted named ones, including
`comparable`. The named-type branch now applies the same method-set check;
regressions cover `comparable`, a named constraint, its alias, a nested pointer,
and positive `error`/named method-set/empty interfaces. This repairs the
documented closed-runtime-type boundary without changing executable lowering
or adding a new diagnostic format.

The initial `--diff` run was deliberately stopped for this source correction
at 1,010/3,654 published partial rows: process group 3373669, actual tool exit
143, original index tree `0b2290d4e981a0aed0d2a08d4edd738ca562f1c4`.
Its proof/unit/eval stages passed (207 eval cases), but it is NOT a full gate
success. Raw log and interruption record remain under `artifacts/i1-landing/`.
The rerun uses 32 GiB, three Lean threads and eight differential workers,
increasing throughput from the initial two workers while retaining the cap
and box-wide full-build lock. No run metadata is retroactively relabeled.

- Fresh frontend and lowerdiag package tests: PASS.
- Focused declaration gate: PASS; 24 fresh Go types and all 576 ordered
  identity comparisons; 17 malformed declaration controls; interface method
  order normalization; raw JSON/Unicode controls (12 positive, 16 named
  refusals, six malformed documents, five invalid UTF-8 inputs, two independently
  stated decoded scalars, one old-parser regression, and five actual declaration
  byte-boundary controls).
- Post-import audit: 1,712 declarations checked; all six private unused axiom
  poisons compiled and were rejected by name. No changes to the core equality
  theorem or the allowed foundational axioms.
- Fresh fixture equals the historical prototype artifact byte-for-byte;
  a corrupt-byte control is rejected by the actual pin check.
- Reconciler: the existing C13/C5 findings, two total, zero HIGH.

Eight additional author-run challenges went through the actual fixture byte
reader: duplicate and escaped-duplicate keys, invalid UTF-8, `uintptr` identity
collapse, generic argument collapse, raw tag byte collapse, a repeated matrix
pair and a missing nominal inventory. Every control was rejected for its
intended cause. These are author checks, not independent review.

The corrected `scripts/capped scripts/ci --diff` completed with **PASS, exit 0**
on frozen index tree `91c21fbbc0773ad375561adc478c9a7a5dbbe83f` over charter
commit `31ecd39d87c93d708dd62ba352f3c88ce011d42a`. The index tree was rechecked
after completion. This was a dirty candidate, not a certified commit.
Full scope: 3,654 executable rows (3,403 PASS / 251 expected FAIL), zero
baseline regressions; 394 negative PASS, zero baseline drift; 207 eval PASS.
Executable frontend pins and fresh derived artifacts match. The ordinary
`--diff` uses cached certified records for slow rows; fresh `--slow`
certification at the clean implementation commit is the next check.
All core build warnings are absent; the logged `sorry` warnings come from
deliberately poisoned temporary controls which the audits reject.

Compact records: [evidence index](evidence/2026-09-08_i1-declarations/README.md).
Full logs stay in ignored `artifacts/i1-landing/`.

## Committed-source certification and completion

[AGENT] 2026-09-08. `scripts/capped scripts/ci --slow` completed **PASS,
actual exit 0**, at clean implementation commit
`3e393be5d7f72d3be2dd57e45872e9fcc4a90518` (tree
`c55319ea2d19064fe5988666df2de952a2b2c273`). Both published metadata files
name that commit, `git_dirty=false`, Go 1.26.5 and no oracle drift. The
worktree stayed clean throughout the gate. Full scope: 3,654 executable rows
(3,403 PASS / 251 expected FAIL), 394 negative PASS, 207 eval PASS. Results
and stages match their baselines, respecting the existing `beside-loop`
stage alternation. Reconciler findings remain C13/C5, two total, zero HIGH.

Fresh `GOLEAN_SLOW=1` enumeration of `imported-goose/channel/google-search`
reproduced the exact six observations `{123,132,213,231,312,321}` and the
same wire SHA `2f1d639f2042466f50b61ab117db5b39629c425f733650b9be992c0b85beefcc`.
Graph: 6,193,933 nodes, 6,565,663 edges, 371,731 dedup hits,
`certified=checkCert`. The enumeration statistics were written at
2026-09-08 01:17:23 UTC. No baseline or certification-set re-pin was made.
The final declaration fixture also reproduces its enforced SHA exactly.
See the [committed gate tail](evidence/2026-09-08_i1-declarations/committed-slow-gate.txt)
and [measurements](evidence/2026-09-08_i1-declarations/committed-slow-measurements.json).
This completion record is a documentation-only follow-up; no runtime source
changed after that clean committed-source gate.

**Review disposition.** Author checks resolved A-R11, A-R12 and I1-R1;
missing-package regressions and the eight whole-reader challenges also pass.
The required adversarial audit ask was posed to the user against committed
`3e393be5`: run an independent agent audit of the declaration boundary,
query isolation, fixture pin and gate, or waive that independent review.
No answer or waiver has been received as of this record, and no independent
audit is claimed. This follows `CLAUDE.md`'s unconditional audit ask; its
scope/waiver and the explicit at-that-moment merge approval remain the user's.

The authorized L1b implementation arc is complete and ready for that review
and merge-sign-off process on `land/i1-declarations`. Production I1, B7 and
refusal-marker removal remain subsequent work. The primary checkout remains
on `main`; this lane has neither merged nor pushed.
