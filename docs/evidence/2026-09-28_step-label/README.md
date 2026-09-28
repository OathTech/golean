# The step-label reshape — gate tail and choice-trace identity (row 2a, 2026-09-28)

[AGENT worker, lane `core/step-label-0928`]. Consuming docs: `docs/2026-09-28_step-label.md` (design note),
`docs/2026-09-28_step-label-handoff.md` (§2 cites this dir). Tree: the lane's code commit `e61b4212` (the gate and
the lane binary ran on the working tree whose tracked content is that commit; the design note was present,
untracked). Base: `main` @ `84f0a9e4`. Host: linux/amd64, the shared 125 G box, under the box-wide build lock (no
concurrent lock holder). Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`); Lean
`leanprover/lean4:v4.32.2` (lean-toolchain).

| File | What | Producer (repo root) |
|---|---|---|
| `gate-tail.txt` | the `ci --diff` summary: EXIT=1, red on exactly the 5a pair (certificate provenance STALE; the one cached certified row `imported-goose/channel/google-search` judged stale), 3768 cases = 3531 / 237, eval tests 295 ok, core build warning-free, core audit / unseq scheduler / frontend pins (raft twin wire byte-identical) ok | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` (tail, ANSI stripped, worktree prefix removed) |
| `choice-trace-main-vs-lane.txt` | the whole-corpus choice trace, main's binary vs the lane's: consumption dumps BYTE-IDENTICAL (26 313 records), per-(row, stream) results identical but for one pre-existing ERROR row's artifact path, 0 alarms under the widened cross-check | `scripts/choice-trace-corpus --dump --jobs 6 --golean <bin> --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused --out .tmp/ct-<side>` per side; `sort`/`cmp` of `dump-*.tsv` and `results-*.tsv` |

Conclusion: ZERO behaviour change — no baseline row moved beyond the expected 5a line, the choice consumption of every
traced run is byte-identical, and the machine's own label records at EVERY step-level site (sequential and pool, now
compared in the init phase too) equal the tracer's independent account.
