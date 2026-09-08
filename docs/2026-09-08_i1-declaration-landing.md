# I1 strict declaration boundary — implementation and review record

[AGENT] 2026-09-08, `land/i1-declarations`; implementation under the
[user-authorized charter](2026-09-08_i1-declaration-landing-charter.md).
The committed-source certification and audit disposition are recorded below.

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
Full logs stay in ignored `artifacts/i1-landing/`. Final committed-source
certification and the mandatory independent-audit ask remain pending at this
implementation commit. Merge and push have not been authorized.
