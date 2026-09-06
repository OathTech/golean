# Explicit string-member corpus contract

2026-09-06. [AGENT] typed-contract-review. Concrete apparatus proposal for
review before runner changes. The renderer implementation is separate work
in this tree; this document does not claim a functioning membership lane.

## Selection and authority

The optional corpus lane is `string-member`. It accepts only expected
`panic`, with a nonempty rationale and a sidecar at the fixed path
`baselines/string-members/<case-id>.json`. It is distinct from schedule
membership and ordinary exact observation equality. The fixed envelope id
is `golean-r1-explicit-string-v1`; no user-provided regular expression,
wildcard, arbitrary predicate or message-erasure flag is accepted. The
existing R-1 ruling authorizes this selected rendered-text member while
keeping occurrence, dynamic kind, recovery/repanic, defer order, output and
exit exact. A new envelope version requires a reviewed implementation.

## Sidecar and checked run records

The sidecar has exactly these keys (unknown and duplicate JSON object keys
are rejected):

```text
schema: golean-string-member-pin-v1
envelope: golean-r1-explicit-string-v1
case: exact corpus id
subject: { function, arguments }
binding: {
  go_sources: complete sorted relative-path -> SHA256 inventory,
  native_wire_sha256,
  go_toolchain, go_oracle_pin_sha256,
  apparatus_sources: fixed required path -> SHA256 inventory,
  control_package: separate source directory under Corpus/controls/string-members,
  control_sources: complete control package inventory,
  control_wire_sha256: freshly emitted complete control artifact hash
}
scope: typed-explicit-string | reviewed-broader-string-control
machine: exact golean-observation-v1 panic object, including output/message
matrix: golean-r1-string-controls-v1
controls: required role -> { function, arguments, expectation }
rationale: { path, section, sha256 } identifying the reviewed source argument
```

`arguments` preserves the ordinary typed argument representation; it is not
a lossy comma-joined reconstruction. Source inventories include every Go
file read by the harness/frontend, not only `main.go`. Subject/wire binding
is checked against the actual fresh files before any message pin is used.
The required apparatus inventory is fixed by checker code and includes the
crash observer, runner, native frontend, lowering, CLI and semantic renderer;
omitting a required file is an error. Fingerprints identify the checked
source, while the ordinary fresh-build/audit gate binds binaries to it.

The runner generates a fresh record directory. Every record preserves its
command/subject/arguments, exact process exit, source/wire binding, raw
stdout/stderr bytes, owned crash/registration bytes, checked output and
parsed observation. A certificate is a manifest of these checked records
and their hashes; it has no `forced_half_ok` Boolean. The checker validates
the mandatory role inventory, exact results and binding for every record.
The normal lane runner executes the controls afresh before declaring the
subject PASS. An imported cache is not accepted merely because it contains
positive status strings; any future cached mode would require its own
reviewed source/binary and freshness contract.

## Raw abort record

`--abort-record` reuses exactly the helper's existing checked crash view
from the same execution. It does not scan stderr independently. Its fixed
schema `golean-raw-panic-v1` contains actual `status: panic`, the child's
validated exit 2, and first-line `messageBytes` plus program `outputBytes`
as JSON integer arrays in [0,255]. The full raw report and both raw
descriptors remain separate evidence files; their hashes are included.
Actual outer `go run` exit 1 and setup/non-verdict refusal checks remain at
the runner boundary. No raw bytes pass through Bash command substitution,
String replacement decoding or a JSON string coercion.

Raw transport is not a dynamic-kind certificate. A line reading `42` does
not establish string versus integer, and the first line cannot reconstruct
the payload after LF. The checker never uses report text to fill these gaps.

## Forced-half matrix

The matrix is versioned in checker code and requires distinct records for:

| Role | Exact challenge |
| --- | --- |
| dynamic-kind-and-bytes | outer recovery checks string assertion and every byte against original |
| normal-control | matching nonpanic branch completes with its pinned result |
| direct-recovery | direct handler recovery cancels the active panic |
| indirect-recovery | ordinary nested call cannot recover the handler's panic |
| defer-order | two shared captures yield an order-sensitive pinned result |
| reversed-defer-control | reversed registrations produce the independently pinned different result |
| equal-repanic | equal literal values recover and repanic; actual abort remains a panic |
| unequal-repanic | unequal literal values preserve the same forced control structure |
| multiple-repanic | nested recovered/repanic sequence preserves exact occurrence/order |
| rethrow | panic of the actual recovered interface preserves string value/kind |
| computed-equal | runtime concatenation produces an equal string without assuming boxing identity |
| invalid-before-lf | ff/NUL/backslash before LF remain exact recovered bytes |
| invalid-after-lf | invalid bytes hidden by gc's first-line projection remain exact values |

The matrix is not satisfied by duplicating one run under different role
names. Each role binds its approved source function and arguments; roles
that must distinguish behavior must have distinct pinned results. Abort
controls must actually abort, while their outer-recovery companions check
kind/bytes/order. A companion alone never establishes the original abort.
Model and Go observations for non-rendering controls compare exactly through
the existing comparator; a timeout, unsupported result, fuel exhaustion,
fatal or ambiguous observer is not a successful control record.

Concrete schema refinement (2026-09-06, root design disposition):
`expectation` has exactly `kind`, `go`, and `machine`. For non-rendering
roles, `kind: exact` requires identical complete ordinary Go and machine
observation pins. For the five explicit abort roles, `kind: string-member`
uses the same fixed R-1 member predicate as the subject, an exact machine
pin, and exact Go `{status: panic, childExit: 2, outputBytes}` fields. The
actual raw Go message is retained in each fresh record; it is not required
to match a gc rendering pin. Pinning it inside these controls would
reintroduce the very rendering-latitude assumption R-1 removes. This is a
finite matrix: these abort controls cannot waive roles or recursively issue
certificates. Their dynamic-kind/complete-byte companions must pass exact
comparison, and the reviewed source argument must relate each companion to
its respective abort body. The implementation requires the complete actual
reached model chain to consist of boxed strings, including for the broader
historical evidence scope. A head-only label cannot discharge that check.
The rethrow and runtime-computed equality roles make the assessment's two
broader-core challenges mandatory; they do not extend O2's literal grammar.

The control package contains every original subject Go source byte-for-byte
plus separate control definitions. Only the original subject artifact is
submitted to O2 admission; type assertions and byte comparisons in the
control package are honest broader-core concrete evidence. Both complete
artifacts and source inventories are bound before consulting member pins.

For `typed-explicit-string`, a fresh checker result on the identical lowered
wire must establish the independent O2 profile. Its actual abort must be
connected to the typed preterminal chain through the reviewed generic
runtime invariant and real driver theorem. The certificate identifies that
theorem/audit/source inventory; the message string is never used as evidence
of the payload type. The certificate cannot be issued until this theorem
chain is implemented and audited.

For historical rethrow/computed-string examples outside that profile,
`reviewed-broader-string-control` explicitly records the weaker concrete
source/control argument. It cannot carry a fictitious O2-admission result
or be counted as generic O2 acceptance. Its recovery kind/byte checks and
actual abort are still mandatory. This distinction concerns evidence scope,
not the allowed string bytes or the R-1 rendering envelope.

## Acceptance and refusal

The actual machine observation must equal the sidecar's complete machine
pin. The checker then verifies the member constructor prescribed by the
fixed envelope and the source/payload evidence, rather than accepting any
arbitrary pinned text. The actual Go record must be panic/exit 2 with exact
program output equal to the machine output. Complete semantic payload bytes
and recovered status come from typed preterminal evidence or the explicitly
reviewed concrete control argument, never by parsing the first report line.

Any missing/stale source or wire, omitted/duplicate control, wrong kind,
wrong byte, changed output, suppressed abort, unrecognized member, invalid
record, refused observer or non-verdict exit fails. PASS is reported at
stage `string-member`, naming the envelope and machine pin, and means
rendered-text membership plus the stated exact forced-half evidence. It
does not mean gc printed that text. Existing exact and schedule-membership
rows continue using their existing comparisons.

Mutation tests must reach and reject replacement of one invalid byte,
dropping NUL, string/integer substitution, skipped/final-suppressed panic,
direct/indirect recovery confusion, reversed/duplicated defers, changed
output, fatal-as-panic, arbitrary member text, missing/duplicate/stale
controls and a claimed success after raw JSON refusal. Test mutations must
compile or be syntactically valid where relevant before rejection counts.

## Still to settle in implementation review

The wire/profile CLI and actual preterminal evidence plumbing need a precise
API implementation; a checked sidecar cannot substitute for them. The full
mandatory matrix must be instantiated by source-bound fixtures, and the
member-constructor check must consume actual payload evidence instead of a
second unverified text pin. These are engineering obligations within R-1,
not permission to weaken the profile or report partial acceptance.
