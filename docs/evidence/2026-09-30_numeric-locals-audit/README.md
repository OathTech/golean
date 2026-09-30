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

## Re-verification at `f11dad1f` (the fix round; D1–D6 ratified)

- `reverify-probes.tsv` — the 21 first-round probes re-run + 20 fix-round attack probes (F3: re-entered/adjacent
  sweeps through the real frontend; F1(b): every orphan-entry candidate) on `main` vs the fix-round tip, with `go run`.
- `reverify-mutants.tsv` — the 24 first-round mutants (the five F1 witnesses now refuse by name) + 13 new `pos`/`wire`/kind
  mutants on the fix-round binary; the residual unchecked bits named.
- `reverify-corpus.txt` — the corpus re-lowered and re-run on both sides; the 386 non-strict rows re-enumerated with
  their own params (the certified row's 6 members = the record's sha); the standing checks (core audit 158, BridgeSet
  rows 126/132 mutation fails the build).
- `reverify-ci-diff-tail.txt` — `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `f11dad1f`.
