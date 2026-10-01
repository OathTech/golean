# C4 (block-entry allocation) — evidence

[AGENT worker], lane `core/block-allocation-1001`, 2026-10-01. Fork base `main` @ `52eddf4c`; runtime commits
`59ac9431` (the decoder hoist) and `58fe18f9` (the core deletion, D3 (b), D8, RE-PIN 8), `ed423c72` (the inventory
rows). Handoff: `docs/2026-10-01_block-allocation-handoff.md`. Scratch under the worktree's `.tmp/` (deleted at the
end); every build/gate `scripts/capped`, full builds and gates under the box-wide lock (never taken over).

- `ci-diff-2a-drift.txt` / `ci-diff-2a-tail.txt` — `scripts/ci --diff` at `59ac9431` (hoist only): EXIT 1, 1047 s;
  red on the 5a pair + `sync/trylock/spin-until-trylock` (the posed budget row).
- `ci-diff-2b-drift.txt` / `ci-diff-2b-tail.txt` — the same gate at `58fe18f9`: EXIT 1, 909 s; the same two drift
  lines + the two stale `mem-callsites` rows (fixed at `ed423c72`).
- `spin-until-trylock.txt` — the posed row at a raised work cap on both binaries (identical observation set and
  leaves) and the per-branch-budget sensitivity that identifies the cause (channel 10, fuel).
- `choice-trace.txt` — the whole-corpus choice trace, lane vs main: byte-identical modulo the output path (26445 dump
  rows, sha256 `6bf9800841e8e5c4` on both sides).
- `google-search-recert.txt` — the certified slow-tier row re-enumerated on the lane: unchanged set; nodes/edges/wall
  moved (the handoff §2.4 has main's figures from the tracked record).
- `fuel-bisect.tsv` — minimal completing fuel by bisection, main vs lane, for the budget rows and three loop/closure
  rows (the per-declaration step saving, exactly).
- `elaboration-ab.tsv` — the sequential elaboration A/B (G-C3 stop rule): every hot module within 0.92–1.07×.
- `build-times-parallel.tsv` — the fresh parallel build's per-module times, for reference only.
