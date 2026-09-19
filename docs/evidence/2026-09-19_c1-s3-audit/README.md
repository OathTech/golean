# Evidence — adversarial audit of C1 S3 (candidate `ee8d0ef0`, runtime `fd99b021`, over main `0f114df6`), 2026-09-19

Report: `docs/2026-09-19_c1-s3-audit.md`. Auditor worktree `.claude/worktrees/audit-c1-s3`, branch
`review/c1-memory-module-s3-0919`. Binaries: main's `da7bb8376164e23fdfb4933b81e406cd21efe6b63b6e9e5e5c08caad20bbc1d2`
(read-only copy `.tmp/golean-main`); the candidate's `ab355547ff2377e24604caabf69236b02e24b8875e50ae0f82069de42d87b051`
(rebuilt here from a plain `cp -a` of the candidate worktree's `.lake` at identical source; `scripts/capped lake build`
EXIT=0). Go `go1.26.5 linux/amd64` (= the pin). Small files only (`scripts/check-evidence-size`); bulk (the probe
directories with wires, the choice-trace artifacts, the detector-soundness artifacts, the benchmark jsons) stays under the
worktree's gitignored `.tmp/` and `artifacts/` and is described here. [AGENT] auditor throughout.

| file | what |
|---|---|
| `static-checks-and-statement-diffs.txt` | captured EXITs of the warm build, `check-core-audit`, `check-mem-callsites`, `gocore-eval-tests` (267 ok), `check-bugs.sh`, `check-evidence-size`, `check-agents-alias`; the escape-hatch scan; the declaration-name set diff over the nine modules; the three genuine theorem-statement changes (`stepFn_consumption_some`, `stepFn_stmtOp_oblivious`, `stepFn_stmtOp_spill`) |
| `probes-src.md` | every probe program (Go source) of the (a)/(b)/(d) batteries, one section per probe directory |
| `probes-a.log` | (a) reachability battery — 15 programs on main / candidate / gc |
| `probes-b.log` | (b) panic-path battery for the reordered W arms (first round with an `r.(error)` harness — two rows hit the pre-existing BUG-009/053 refusal identically on both binaries — and the second round with a plain `recover()`), plus the fixed (d) programs |
| `probes-d.log` | (d) the synchronization / conversion applies' write-then-panic battery (first round; the `import`-bearing programs re-run in `probes-b.log`'s second round) |
| `poolcmp-results.tsv` | (c) every schedule enumerated with `coverage-observations` under each row's manifest params on both binaries: 183 rows (49 concurrency membership + 41 racy + 93 confluent), 183 SAME (byte-identical stdout, equal exit) |
| `bench-runs.txt` | the two `run-probes.py --plan full` runs (BEFORE main's binary, AFTER the candidate's) with start/end/load, and the raw runner lines of the 5× `--only alloc_new,append_grow,empty` repeats |
| `bench-audit-compare.md` | `bench_compare.py` over this audit's BEFORE/AFTER jsons (AFTER-2 column = AFTER repeated, the script takes three) — the four charter §6 targets derived |
| `bench-repeats.txt` | net ratios of the five repeats + the full AFTER run against the 4.4 / 2.2 lines (0/18, 0/24 over) |
| `choice-trace-subset.txt` | the 306-row choice-trace comparison (sorted dumps, sha256, `cmp`), with the id list |
| `detector-soundness-audit.txt` | the official runner on the candidate binary: summary and the comparison with the tracked cell counts |

Reproduction (repo root of the audit worktree):

```sh
scripts/setup-deps --from /home/dev/projects/golean
cp -a /home/dev/projects/golean/.claude/worktrees/c1-s3/.lake .lake && scripts/capped lake build; echo EXIT=$?
cp /home/dev/projects/golean/.lake/build/bin/golean .tmp/golean-main && chmod a-w .tmp/golean-main
GO111MODULE=off GOCACHE=$PWD/.tmp/gocache go build -o .tmp/nativefrontend ./tools/nativefrontend
# probes: .tmp/probes/<name>/main.go (probes-src.md) → .tmp/nativefrontend --dir D --out D/program.json; BIN native-json-run --input D/program.json --function probe; (cd D && go run main.go)
E=docs/evidence/2026-09-11_bug090-rediagnosis
python3 $E/run-probes.py --golean .tmp/golean-main --frontend .tmp/nativefrontend --scratch .tmp/bench/before --plan full --out .tmp/bench/bench-before.json
python3 $E/run-probes.py --golean .lake/build/bin/golean --frontend .tmp/nativefrontend --scratch .tmp/bench/after --plan full --out .tmp/bench/bench-after.json
python3 docs/evidence/2026-09-19_c1-memory-module-s3/bench_compare.py .tmp/bench/bench-before.json .tmp/bench/bench-after.json .tmp/bench/bench-after.json
scripts/coverage-manifest | awk 'NR % 12 == 1 {print $1}' > .tmp/subset-ids.txt   # then choice-trace-corpus per side as in choice-trace-subset.txt
scripts/detector-soundness --select in-scope --jobs 6 --out artifacts/detector-soundness-audit
```
