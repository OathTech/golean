# Audit evidence — `core/numeric-locals-0930` @ `a6df705f` (B6, numeric locals)

[AGENT auditor, branch `review/numeric-locals-0930`], 2026-09-30. Note: `docs/2026-09-30_numeric-locals-audit.md`.
Every run: the auditor's own builds (main = `git archive 131a7313` + the primary's lake-verified binary; candidate =
the lane tip, `.lake` warmed from the lane worktree after a `diff -r` of the Lean sources), `scripts/capped`, scratch
under the worktree's `.tmp/` (deleted at the end), the box-wide lock for the gate.

- `ab-corpus.txt` — every fixture dir lowered by both frontends, every manifest row run by both binaries, 686
  argv-identical enumerations: identical (the one differing string is a wire PATH inside the BUG-078 refusal).
- `ab-enum.txt` — all 386 non-strict rows re-enumerated with their own lane params on both binaries, incl. the
  certified slow-tier row at its claim's argv: identical sets and statistics; the members' sha256 = the certified record's.
- `probes.tsv` — 21 auditor-written scoping programs (the logic team's §4 B6 conditions): main = candidate = `go run`.
- `mutants.tsv` — 24 decoder mutants for D1's certificate (which refuse by name, which the design does not check),
  and the moved `wellFormed?` spelling checks exercised with the same one-edit mutant on both sides (W1–W4).
- `wire-diffs.txt` — the twin re-pin and the certified row's wire, reproduced key by key with the auditor's frontends.
- `ci-slow-tail.txt` — the tail of `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `a6df705f`.
