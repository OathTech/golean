# Narrow R1 baseline proposal

[AGENT] typed-string-members, 2026-09-06. **Proposed for independent
disposition; the tracked baseline is unchanged.** The full capped
`scripts/ci --diff` completed on the exact reviewed v3 source. Every required
check passed except the expected baseline drift: 3,635 executable cases,
3,391 PASS and 244 existing FAIL; all 394 compile-negative cases passed.
No refusal is counted as conformance.

The exact nine-row delta is in `full-v3-initial-delta.json`. Eight new
`panic-recover/string-members/*` rows pass at `string-member`. The existing
`panic-recover/repanic-same-value-abort` changes from `FAIL/lean-observation`
to `PASS/string-member`, explicitly under broader concrete source/control
evidence. It does not claim O2 admission. No other existing row changes
status or stage, no row disappears, and no PASS becomes a refusal/failure.
Every existing stage-alternation declaration remains intact.

`baseline-proposal.patch` and `baseline-proposed.tsv` make exactly those
row changes, retain existing row order, and add a measured provenance header.
The source/renderer/member contract has independent acceptance from
`d59b4ab1` and `75da9338`. PASS at this stage means the reviewed rendered-text
member with exact panic/exit/output and the finite thirteen-role controls;
it is not exact gc text equality or completion of the broader BUG-004 class.
The Error/String-method and non-string identity boundaries remain open.

Raw metadata records the actual 32-worker run under the unchanged 16 GiB
cap. The author missed the earlier two-worker lane setting after restart.
`concurrency-attribution.json` preserves that deviation and earlier focused
run metadata; all future conformance invocations explicitly use two workers.
Root directed preserving the completed run without rerunning merely to
relabel concurrency. The legacy direct `diff-smoke` path leaves its
`full_run` field unknown; `full-v3-scope-verification.json` independently
checks the exact current full-manifest hash and equality of all 3,635 unique
case identities. Original metadata is preserved unchanged.

After independent acceptance, apply the proposed baseline, record BUG-004's
bounded string-member progress and correct its historical value-equality
versus boxing-identity claim, integrate the sealed root review documents,
and run final CI against the preserved full source-bound records. Any
runtime change would invalidate reuse and require fresh affected conformance.

The exact coverage-ledger draft is `language-ledger-proposed.md`, with
`language-ledger-proposal.patch` and before/after hashes in
`language-ledger-proposal.json`. `language-ledger-derivation.json` compares the
actual failure sets and assigns the sole retired row to historical triage
L12 / (c) C4: 25 + 1 becomes 24 + 1, and 137 + 9 + 25 + 7 + 66 = 244.
It preserves historical counts and adds movement §8z immediately after §8y.
All three target files remain unchanged pending independent disposition.
