# R1 string member production record

[AGENT] `typed-string-members`, 2026-09-06. **R1 implementation and
baseline disposition are complete in this lane. Corrected ordinary CI
reports PASS after process completion**, with zero HIGH reconciliation
findings. Its build, semantic, proof, apparatus and exact cached baseline
checks all pass. `final-verification.json` binds the final hashes and
`ci-final-corrected.completion.json` records the terminal result. The first
ordinary final run's sole failure was the BUG-004 Cases line still naming
the newly passing rethrow. Independent follow-up `2094de72` accepted the
one-line correction; both original failure and corrective review are
preserved.

The renderer constructs the first-LF byte prefix for valid text and uses a
guarded exact byte round-trip or a reversible fixed-width all-byte escape
for explicit strings. The kernel proofs establish those statements, actual
string-head abort transitions and total readout. Escape injectivity is
proved; the whole renderer has an explicit collision regression and is not
claimed injective. Reviewed observer dependency `04109912`, integrated
through `414a2abe`, supplies exact full string-chain metadata from the actual
selected pool abort transition and erases to the shipped driver.

The fixed `golean-r1-explicit-string-v1` certificate binds the sources,
lowered artifact, arguments, toolchain, exact panic/exit/output fields and
actual AbortRecord chain. Its thirteen roles comprise eight exact controls
and five actual abort-member controls. Eight subjects have independent O2
admission artifacts on their actual wire; the historical same-value rethrow
has explicitly broader source/control evidence outside the O2 grammar.
This does not establish exact gc rendered-text equality, the remaining
non-string/Error/String-method cases, or the generic O2 terminal theorem.
The recovery terminal lane owns that theorem and final customer integration.

Validation includes nine focused member cases with thirteen controls, actual
plain/race Go and four model streams each; six raw native/driver cases; two
zero-fuel erasures; nine compiling Go semantic mutations; four nonverdict
capture refusals; six manifest-bypass refusals; and four compiled Go plus
eleven compiled Python apparatus mutation controls. The interface gate
checks 128 required exports and 15,113 local declarations, with 28 compiled
poison refusals. All these bounded gates passed.

The completed ordinary full `scripts/ci --diff` measured exactly 3,635
executable cases: 3,391 PASS and 244 existing FAIL. All 394 negative cases
passed. Exactly eight new member rows pass, and the historical rethrow
changes FAIL/lean-observation to PASS/string-member. There are no other
status/stage changes, omissions or PASS regressions. Its sole failed check
was that expected baseline drift, now independently disposed and applied.
The C4 bucket changes 25 + 1 to 24 + 1; all other failure buckets stay fixed.

The full run used the unchanged 16 GiB cap and actually used 32 workers
because the author missed the earlier two-worker coordination after restart.
Original metadata and `concurrency-attribution.json` preserve that deviation;
the root directed retaining the completed evidence without rerunning solely
to relabel it. Subsequent commands explicitly set two workers. The original
legacy `full_run=unknown` field is unchanged: the exact current manifest SHA
and equality of all 3,635 unique case identities independently establish
scope. Slow rows used the ordinary cached policy; this is not slow-tier
re-certification.

Independent apparatus review `d59b4ab1` covers exact v3, including six source
omissions discovered and fixed through review: both root Lean entrypoints,
three embedded frontend TSVs and the runtime-read stdlib pin. The initial
178-input and v2 180-input evidence are preserved; their interrupted CI runs
ended before the full corpus and do not establish complete source coverage.
Root implementation review `75da9338` accepts the exact 184-input v3 source,
with independent kernel/CLI/Go challenges. Root disposition `8e8bca46`
accepts the exact baseline, BUG-004 and language-ledger proposals;
`2094de72` corrects the earlier review of BUG-004's open failure Cases line.

`production-candidate-source-v3.json` fixes the 184 reviewed inputs.
`final-source-inventory.json` fixes 3,882 selected source/baseline inputs;
its adjacent scope file defines inclusion. `ci-final-corrected-provenance.json`
binds the final ordinary gate to the byte-identical preserved full
executable/negative TSVs and metadata. `ci-diff-v3-initial.log`,
`full-v3-initial-delta.json`, `full-v3-scope-verification.json` and the raw
nine-certificate archive preserve the complete full-run evidence.


Final CI explicitly used `GOLEAN_COVERAGE_JOBS=2 GOLEAN_MEM_MAX=16G
LEAN_NUM_THREADS=3 scripts/capped scripts/ci`. Its original supervisor exit
status was not recovered after the session identifier was omitted from the
forwarded tool result; the tracked process completed and the CI's own final
summary reports PASS. The separate completion monitor exited 0. No runtime
or cached result bytes changed to repair the Cases-line record. The three
remaining reconciliation findings are previously recorded unrelated
report-only medium findings.

`renderer-adoption.json` provides the exact four renderer/test fingerprints
for the recovery terminal lane. After later independently reviewed source
unions, the membership apparatus fingerprints must be refreshed against the
new complete source inventory and its focused/apparatus gates rerun. This
record seals the current source, not a future integrated source tree.
