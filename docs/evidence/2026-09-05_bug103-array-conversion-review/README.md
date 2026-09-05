# Independent BUG-103 review evidence

[AGENT] reviewer `bug103_adversarial`, 2026-09-05; preserved by the
coordinator. Reviewed source commit:
`7b7bc42c3f77154099ccbb3c6f6a302a8d1987d4`.
Verdict: **PASS for the bounded change; no introduced defect found**.
Full report: `docs/2026-09-05_bug103-array-conversion-review.md`.

`review-scratch/` is an unchanged copy of the reviewer's unique
`.tmp/bug103-review.KMnRI4/` directory. It contains the original report,
build/eval/proof logs, evidence/baseline checks, five additional supported
probe functions and manifest, and the tagged-struct frontier control.

`focused/`, `extra/` and `tagged/` preserve the fresh result/meta records,
native wires and available Go oracle streams from the corresponding
`artifacts/bug103-adversarial*` directories. Binaries and build caches are
excluded. The original implementation evidence is unchanged.

## Results and their meaning

- Core/eval builds passed; all **202 eval checks** passed.
- Five imported preservation/coherence theorem dependency checks contain
  only standard Lean axioms; exact output is in `proof-check.log`.
- Fresh focused differential: **22 PASS / 1 FAIL**, the unchanged FR-10
  refusal. The command's exit 1 is expected and preserved, not treated as
  universal conformance success. All six BUG-103 cases passed.
- Five extra supported differential probes: **5 PASS / 0 FAIL**, covering
  named/boxed array identity, interface elements and typed nils, shared
  map/function/channel references, recursive array pointers and empty
  function arrays. These are review evidence, not five additional entries
  in the recorded 3,598-case corpus baseline.
- The tagged anonymous-struct control remains **FAIL at frontend-export**
  under the existing FR-13 quarantine. No runtime regression is inferred.
- All 70 semantic-input hashes, their aggregate fingerprint and all 31
  changed-file/evidence hashes matched. Sealed full and negative baseline
  comparisons matched 3,598 and 394 records respectively. These expensive
  lanes were not re-executed by the reviewer; one slow-tier case retains
  its existing cached certification.
- The optional direct Go attempt in `tagged-go.log` failed at the nono OS
  sandbox's `/private` cache boundary. No fresh direct Go result is claimed
  for that optional frontier control. Supported differential probes used
  the harness's permitted cache and succeeded. No permission/profile change
  was needed or made for the completed review.

## Reproduction

The report records the capped build/eval/proof commands. The fresh focused
slice uses the 23 IDs in the original implementation's `focused.tsv`.
The two review manifests retain their original scratch paths. On a different
checkout, copy them to unique scratch and replace
`.tmp/bug103-review.KMnRI4/` in their directory column with
`docs/evidence/2026-09-05_bug103-array-conversion-review/review-scratch/`.
Then invoke the existing `scripts/diff-coverage` on each manifest, with
separate `GOLEAN_COVERAGE_ARTIFACTS` directories. The supported probe run
should succeed; the tagged frontier control should fail at frontend export.
Do not count that refusal as a conformance pass.

Use `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3` and `scripts/capped` for every
Lean/Lake invocation. `SHA256SUMS` seals all files in this evidence directory.
The review did not test a combined A2/BUG-103 tree or authorize merging.
