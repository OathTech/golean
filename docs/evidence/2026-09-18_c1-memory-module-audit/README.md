# Evidence — adversarial audit of C1 (S0–S2b), 2026-09-18

[AGENT] auditor (Fable), branch `review/c1-memory-module-0918` at candidate `a8ada3cc`.
Report: `docs/2026-09-18_c1-memory-module-audit.md`. Every file here is small (caps 256 KiB /
4 MiB); scratch lived under the worktree's `.tmp/` and `artifacts/` (gitignored).

- `core-audit.log` — `scripts/capped bash scripts/check-core-audit` at the tip (EXIT=0, classical trio only).
- `scratch-leaf-main.go` / `scratch-leaf-results.txt` — 13 leaf-write + len/cap subjects, main vs candidate (all SAME; go: `44 -128 18 6 7 9 42 -2 11 4 7755 3 12`).
- `scratch-nilchan-main.go` / `-results.txt` — 7 `alloc`-normalizes subjects (nil chan/func in composite literals, params, range vars); all SAME; go `7 6 1 3 9 6 1`.
- `scratch-retag-main.go` / `-results.txt` — 6 struct-tag-alias subjects; both binaries refuse the whole-struct copy through the alias (pre-existing, F9); go `1 1 1 8 3 5`.
- `scratch-deferrecv-main.go` / `-results.txt` — 4 deferred-receiver subjects for the fold's corner (e); all SAME; go `1 2 100 103`.
- `scratch-warm-results.txt` — the two reachable write-then-panic W arms (makeMap/makeChan into a nil target); all SAME; go `1 2 6`.
- `scratch-bug111-main.go` / `-machine-results.txt` / `-go-race.txt` — BUG-111 end to end: `go run -race` reports `aliasRace` and `plainRace` (2 reports, `aliasDisjointFields` clean); both binaries ACCEPT `aliasRace` (ok, 1) and refuse `plainRace` (race).
- `probe-IfaceCell.lean` / `.log` — the F3 witness: `HeapNormal` true on an interface-declared cell holding an array/struct; the candidate's `storeLoc` refuses a path write there.
- `choice-trace-subset-ids.tsv` — the 307 manifest ids (every 12th executable row minus the 2 standing exclusions).
- `choice-trace-subset-cmp.txt` — candidate vs main sorted consumption dumps: `cmp` EXIT=0, 2,690 records, one sha256.
- `trace-audit-s2a-subset.txt` / `choice-trace-s2a-cmp.txt` — the S2a binary (both accounts live) on the subset: `traceMismatches` = 0 on 1,818 (row, stream) results; dump byte-identical to main's.
- `bench-interleaved-clean.txt` — the load ≈ 1 interleaved re-timing (5 reps alternating main/cand per point).
- `bench-full-subset-{main,cand}-summary.md` — the lane's runner on both binaries (`--only` the target probes; the candidate pass ran under the auditor's own concurrent jobs — read the interleaved file for the ≤ 10 % targets).
- `detector-soundness-unpatched-summary.txt` — the tracked runner at the tip: every gc cell `gc-no-verdict` (EXIT 78 = the harness crash hook's setup failure, F2).
- `detector-soundness-patched-summary.txt` — the patched-COPY runner (crash files pre-created per run; the tracked script untouched) against the candidate binary.
