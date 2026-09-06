# Independent review: valid UTF-8 / newline panic rendering

[AGENT], 2026-09-06. Reviewer: primary integrator, independently of the
`typed_contract_review` agent who authored the `typed-panic-rendering`
implementation. **PASS for the narrow runtime repair.** Its required final
CI and exact ten-row baseline reconciliation have now passed. No
blocking implementation finding. This is not acceptance of O2 or the final
integrated sprint.

`provenance.json` binds the frozen target source and exact review commands.
The initial target was uncommitted over `5158589a`; the final reviewed
implementation is `ff7173dd`. Rechecking its source hashes found no change
to the runtime, tests or gates since the independent probes. The repair
note's final validation/bookkeeping additions were read separately. This
review read the actual Machine diff,
the reused `decodeRuneAt`, tests, audit integration and design note. It
compared the observer policy with the local pinned Go `runtime/panic.go`
(`printpanics`) and `runtime/error.go` (`printindented`), plus the existing
R-1 ruling. The author's 14-case focused green, eight kernel regressions and
full-corpus drift report are supporting evidence, not independent reruns.

## Why the implementation meets its stated boundary

The strict decoder distinguishes the invalid-byte sentinel (U+FFFD, width
one) from an encoded U+FFFD (width three), retains legal Unicode scalars,
and advances structurally. The existing core decoder enforces the legal
UTF-8 byte ranges, including the surrogate and maximum-code-point bounds.
The repair neither invents a replacement value for invalid bytes nor changes
the panic/recover control machinery.

Suffix formatting precedes first-line projection. This matters when a
recovered payload contains a newline: the suffix occurs on a later line
and must not be appended to the first line. ASCII newline is a UTF-8 boundary;
the strict second decode is explicit. Existing refusal checks for unsupported
payloads and equal-value recovered/repanic ambiguity still run before
projection, so a newline does not accidentally bypass them.

Both executable and relational abort paths continue to share `abortMsg`.
The coherence modules were rebuilt by the author's gate. No new relation
constructor, observation policy, nondeterministic choice, resource cap,
toolchain pin or trusted axiom was introduced.

## Independent executable challenges

`Review.lean` freshly compiled through the target's pinned build/import path,
under the 16 GiB cap and three Lean threads. Its five kernel theorems check:

- All 128 one-byte ASCII values round-trip, including NUL, control bytes,
  newline and DEL.
- Nine legal scalar boundary encodings round-trip, including the largest
  scalar and the legal noncharacters U+FFFE/U+FFFF.
- A carriage return preceding newline survives first-line projection.
- NUL and SOH survive rendering in the semantic model.
- An invalid truncated encoding after a newline remains a refusal.

`kernel-probes.log` records that all five depend only on `propext` and
`Quot.sound`. The reviewer requested no output olean and wrote no target
source or build-cache files.

Three independent Go programs also ran at go1.26.5. Raw stdout/stderr files
and `go-probes.json` preserve their exact results: carriage-return/newline
suffix placement, NUL/SOH payload bytes, and the maximum scalar. Parsing
used raw byte lines, avoiding shell string substitution. These are finite
checks and a source argument, not a generic UTF-8 correctness theorem.

## Mandatory follow-on work

The narrow repair does not complete the existing R-1 rendering quotient,
resolve invalid-UTF8 representation, or prove a generic decoder round trip.
Those remain obligations for O2's arbitrary explicit string payloads; the
profile must not silently become ASCII-only, control-free or no-repanic.

The separately exposed harness defect is real: the old shell observation
path drops NUL and can emit invalid JSON for other control bytes even though
the model preserves them. This is a separate red-first observer repair under
the existing valid-UTF8/JSON contract, not a defect introduced by this diff.
It must not be hidden by the new type checker. Invalid UTF-8 remains a
separate observation-representation investigation under existing R-1 authority.

The author retained the first full differential drift, reconciled only its
ten evidenced improvements, finished ordinary CI against that complete run,
and bound the final source/manifest/BUG004 changes in the
[repair evidence](../2026-09-06_panic-rendering/README.md). Those checks and
the sealed source manifest were independently inspected before acceptance.
The fresh full run is 3607 cases, 3363 PASS and 244 known FAIL; final ordinary
CI reuses that same runtime-bound full record. No main merge or push is
authorized by this bounded review. The later integrated interface audit must
retain both this lane's decoder/test checks and the Boolean contracts.
