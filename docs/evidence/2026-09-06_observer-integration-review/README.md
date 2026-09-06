# Independent observer integration evidence review

[AGENT] typed_preflight, 2026-09-06. **PASS for the bounded integration,
CI-hook union and evidence/ledger increment.** This relies on the existing
independent apparatus implementation reviews; it does not replace them or
assert full observer correctness, R1 fidelity, O2 completion or sprint closure.

All three reviewed manifests were independently compared to the integrated
source. The sole difference is `scripts/ci`. Removing exactly its two added
observer gate blocks restores the complete `99e0225d` parent script, proving
that the existing build, proof, admission and recovery hooks were retained.
Both build configuration hashes also match that parent.

I read the raw terminal CI summary and replayed the evidence verifier
read-only: its final metadata write was replaced with an assertion that the
recomputed result equals the archived validation. All 3,844 source inputs,
3,627 executable rows, 394 negative rows, unique complete manifest inventories,
original manifest hashes and allowed baseline stages agree. The original
dirty-tree and unknown direct-runner metadata fields are preserved and
disclosed. The fresh full ordinary run is distinct from cached slow evidence.
No second full corpus run was performed by this review.

The exact movement is eleven new PASS cases and the previously reviewed
BUG-106 fatal-unwind case changing PASS to FAIL at `go-observation`. There
are no removals or other baseline changes. Arithmetic is therefore
3,616 + 11 = 3,627; 3,372 + 11 - 1 = 3,382 PASS; 244 + 1 = 245 FAIL.
The 65-to-66 post-vintage bucket change accounts for the named apparatus
refusal, and 137 + 9 + 26 + 7 + 66 = 245. The ledger distinguishes that
refusal from Go conformance or a semantic repair, retains historical totals,
and records the exact case, stage and cause. A missing closing parenthesis
in the historical BUG-103 clause was reported and corrected before sealing.

The raw CI retains its original report-only arithmetic findings. The final
reconciler report records their correction and keeps the remaining medium
historical-toolchain/frontier observations visible. No checker, baseline or
acceptance threshold was weakened by this bookkeeping change. Source hashes
and the exact bounded checks are attached; parent-reported process exit 0
is supported by the archived terminal `RESULT: PASS` summary.
