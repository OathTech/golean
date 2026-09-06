### 8z-uintptr. Movement at the uintptr identity repair (2026-09-06)

[AGENT] `typed-uintptr-identity`: the isolated full differential run moves
3,627 = 3,382 PASS / 245 FAIL to 3,635 = 3,390 PASS / 245 FAIL. Exactly eight
`ints/uintptr-identity/*` rows are born PASS; existing rows retain their
results and allowed stages. No existing red bucket changes: 137 + 9 + 26 +
7 + 66 = 245. This measurement predates integration with the independent R1
string-member work; their two 3,635-row manifests are different sets.

BUG-107 preserves a red-first type-identity mismatch and the readout observer
refusals. The fix retains distinct uintptr identity even at the same width
as uint64; it does not widen the supported platform claim. The full run used
two workers and the pinned Go toolchain. Its unfiltered regenerated manifest
matches the original metadata SHA exactly; original `full_run=unknown` is
preserved, not relabeled. The initial CI also failed its required goose guard
because that worktree lacked the pinned reference checkout. Restoring the
dependency and passing the remaining gate are separate from this measured
case delta. Slow certification and final integration remain owed.

Evidence: `docs/evidence/2026-09-06_uintptr-identity/full-delta.json`, complete
TSV/meta, manifest, initial CI log and independent implementation review.

