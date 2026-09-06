# Diagnostic observer review: initial findings

[AGENT], `typed-preflight`, 2026-09-06 UTC. **Changes required; no diagnostic
PASS issued.** This seals the initial source-bound review and newly found
core classifier counterexample. A later classifier/diagnostic increment
requires a separate reviewed source checkpoint and green evidence.

The candidate diagnostic byte repairs use the frozen core file helpers in
`membership-sampling`, `gotest-triage` and `cedar-census`. Initial hashes are
in `provenance.json`; the copied scripts and source-extracted oracle blocks
are archived. No complete diagnostic tool was run: those commands perform
frontend/model/census work and can delete existing output. The review
executes only their exact oracle blocks in private scratch directories.

`review.py initial` ran under the 16 GiB cap with three Lean threads and the
reviewer's private Go cache. **149 checks: 146 PASS, 3 FAIL**, exit 1. All
three failures are the same real-Go fatal-during-unwind misclassification,
one per tool. Detailed records are in `initial-results.json`; raw inputs
and descriptor/result bytes are archived. Passed checks cover every JSON
control byte through each oracle, raw fd identity, alternating `-race`
forwarding in standalone sampling, exit 2/124/137/143/255 refusals,
stdout-only markers, malformed reports/UTF-8, raw nonempty success output,
and `.out` CRLF/NUL/trailing-LF comparisons. The checks are apparatus
evidence, not Go-versus-Lean conformance or a fresh full test-suite/Cedar
census. The existing independent harness binary from the preceding core
review is reused at its recorded hash; no new build is implied.

The `.out` comparison was inspected directly against pinned
`deps/go/src/cmd/internal/testdir/testdir_test.go`, `checkExpectedOutput`:
only actual CRLF is normalized, then compared to exact expected bytes;
missing expected output means empty. The candidate preserves the existing
stdout-then-stderr concatenation order, which cannot reconstruct
cross-descriptor write interleaving. Cedar's successful-driver silence check
uses raw file size; abort output is obtained from the shared stderr
splitter. These byte-transport changes passed the bounded checks.

[The separate fatal-classification finding](fatal-classification-finding.md)
records five real-Go false-panic acceptances: the three diagnostic tools,
core strict classification expecting panic, and core sampling allowing
panic. It also records a real multiline-payload collision that prevents
naive fatal-marker priority from resolving the problem. The author's
subsequent broad-substring draft has **not** received a PASS; the parent
requires a separate line/block-aware classifier repair and controls after
the ongoing frozen byte-transport full CI.

The historical core byte-transport PASS remains narrowly scoped to byte
transport under preserved splitting policy. It does not certify terminal
classifier completeness, and this newly found defect must not remain
deferred debt in the final sprint disposition. Invalid-UTF-8 representation,
R-1, and generic runtime-report parser correctness remain distinct claims.

`probes.tar.gz` contains exact initial scripts, extracted shells, generated
Go sources, and all raw probe inputs/results. `archive-members.sha256`
inventories every member and `archive-verification.json` records complete
verification after writing. `SHA256SUMS` seals all top-level evidence files
except itself. Scratch locations are historical; replay in a fresh private
directory, leaving sealed records intact. No parent/author runtime source,
baseline or dependency pin was edited; no main merge or push was performed.
