# Evidence — C1 S3, the rollback (cost B: the validate/commit split, the pre-step store no longer held) (2026-09-19)

Lane `core/c1-memory-module-s3-0919`, base main `0f114df6` (the train r42 close over `3b99f42f`);
handoff `docs/2026-09-19_c1-memory-module-s3-handoff.md`; completion note
`docs/2026-09-19_c1-memory-module-completion.md`; charter `docs/2026-09-17_c1-memory-module-charter.md`
§2 B(b)/(c), §6 S3; predecessor evidence `docs/evidence/2026-09-18_c1-memory-module/` (S0–S2b) and
`docs/evidence/2026-09-18_c1-memory-module-s2c/` (S2c, BUG-111). Small files only
(`scripts/check-evidence-size`); bulk under `artifacts/` (gitignored) and `.tmp/` is described here.

Toolchain: `go version go1.26.5 linux/amd64` (the pin `baselines/go-oracle-pin`); Lean as
`lean-toolchain`; host linux/amd64, 32 cores, the shared build box (loads noted per run). Binaries:
main `0f114df6`'s `.lake/build/bin/golean` (the primary checkout, copied read-only to `.tmp/golean-main`
after train r42 released the box-wide lock) sha256
`da7bb8376164e23fdfb4933b81e406cd21efe6b63b6e9e5e5c08caad20bbc1d2`; the S3 tree's
`.lake/build/bin/golean` (copied to `.tmp/golean-s3`) sha256
`12ebb0e1202b8b43fec8ec131820cc323fd3500ce577692f609bd7839c244a52` — the tree at the benchmark was
the uncommitted S3 working tree over `0f114df6` (`runtime_tree_dirty: true` in `bench-after.json`'s
meta; the runtime commit that follows carries these bytes — its SHA is in the handoff §0). The committed
tree `fd99b021`'s gate-built binary (proof-only edits after the benchmark; the compiled code unchanged) is
sha256 `ab355547ff2377e24604caabf69236b02e24b8875e50ae0f82069de42d87b051` (copied read-only to
`.tmp/golean-s3-final`): it ran gate 2, the choice trace, detector-soundness and the AFTER-2 benchmark.

| file | what |
|---|---|
| `bench-before.json` / `bench-before-summary.md` | `run-probes.py --plan full` with main's binary: 67 points, 3 runs each, medians, net of the empty probe (0.0185 s); load1 3.9 → 2.2; 05:23–05:29Z |
| `bench-after.json` / `bench-after-summary.md` | the same plan with the S3 binary: empty 0.0191 s; load1 1.9 → 2.3; 06:37Z (the whole plan ran in 35 s — the 14 s and 18 s points are gone) |
| `bench-after2.json` / `bench-after2-summary.md` | the same plan, third run, with the committed tree's binary `ab355547…` on a quiet box: empty 0.0201 s; load1 0.97 → 0.99; 07:21:56–07:22:31Z (a confirmation run for the record) |
| `bench-compare.md` / `bench_compare.py` | every point BEFORE / AFTER / AFTER-2 / ratios / statuses, and the four charter §6 targets derived from them: all four MET on AFTER (including the `append_grow` ratio S1 owed); AFTER-2 repeats them except two single ratio steps over the line by the letter (`alloc_new` 4k→16k ×4.49 vs ≤ 4.4; `append_grow` 250→500 ×2.29 vs ≤ 2.2 at the noise floor) — reported as misses on those steps, not re-fitted (handoff §3); the producer script is the file beside it |
| `eval-tests-s3.txt` | `gocore-eval-tests` at the S3 tree: 267 ok, EXIT=0 — the 56 label-shape facts (`labelShapeFacts`) unchanged and passing |
| `mem-callsites-diff-s3.txt` | `scripts/check-mem-callsites` BEFORE the inventory edit: 3 NEW (the `alloc`/`allocCell` mentions now inside `applyStmtOpCore.plan`/`applyStmtOp.plan`), 5 STALE (the same three under the old declaration names + the two dead `storeMany` rows); after the edit: PASS, 70 rows |
| `gate-tail-s3-worktree.txt` | gate 1, the S3 WORKING TREE (binary `12ebb0e1…`): red on the 5a pair AND six proof-only `unusedSimpArgs` warnings (fixed before the commit) — handoff §2 |
| `gate-tail-s3.txt` | gate 2, THE DEFINITIVE GATE at the runtime commit `fd99b021` (clean tree, binary `ab355547…`): EXIT=1 red ONLY on the 5a pair; 3686 cases; DRIFT = exactly the one certified row; eval 267 ok (handoff §2) |
| `choice-trace-s3.txt` | the whole-corpus choice trace, the committed binary `ab355547…` vs main's `da7bb837…`: BYTE-IDENTICAL — 24,037 records per side, one sha256 `838d93e4…`, `cmp` EXIT=0; findings lines identical (handoff §2) |
| `detector-soundness-s3.txt` | the official `detector-soundness` runner (`--select in-scope --jobs 6 --out artifacts/detector-soundness-s3`) on the committed binary `ab355547…`: the summary and the cell-for-cell comparison with the prior official matrix (S2c audit fix round, 649 rows) (handoff §2) |

## Reproduction (repo root, the worktree at the S3 runtime commit)

```sh
mkdir -p .tmp/bug090-before .tmp/bug090-after .tmp/gocache
cp /home/dev/projects/golean/.lake/build/bin/golean .tmp/golean-main && chmod a-w .tmp/golean-main   # main 0f114df6, sha256 da7bb837…
GO111MODULE=off GOCACHE=$PWD/.tmp/gocache go build -o .tmp/nativefrontend ./tools/nativefrontend
scripts/capped lake build golean && cp .lake/build/bin/golean .tmp/golean-s3 && chmod a-w .tmp/golean-s3
E=docs/evidence/2026-09-11_bug090-rediagnosis
python3 $E/run-probes.py --golean .tmp/golean-main --frontend .tmp/nativefrontend --scratch .tmp/bug090-before --plan full --out .tmp/bench-before.json
python3 $E/run-probes.py --golean .tmp/golean-s3   --frontend .tmp/nativefrontend --scratch .tmp/bug090-after  --plan full --out .tmp/bench-after.json
python3 $E/summarize.py .tmp/bench-before.json $E/steps.json > bench-before-summary.md
python3 $E/summarize.py .tmp/bench-after.json  $E/steps.json > bench-after-summary.md
# AFTER-2 (the committed tree, after `scripts/capped scripts/ci --diff` rebuilt the binary; quiet box):
cp .lake/build/bin/golean .tmp/golean-s3-final && chmod a-w .tmp/golean-s3-final   # sha256 ab355547…
python3 $E/run-probes.py --golean .tmp/golean-s3-final --frontend .tmp/nativefrontend --scratch .tmp/bug090-after2 --plan full --out .tmp/bench-after2.json
python3 $E/summarize.py .tmp/bench-after2.json $E/steps.json > bench-after2-summary.md
python3 bench_compare.py .tmp/bench-before.json .tmp/bench-after.json .tmp/bench-after2.json > bench-compare.md   # (the script lives in this dir)
scripts/capped lake build gocore-eval-tests && .lake/build/bin/gocore-eval-tests > eval-tests-s3.txt
scripts/check-mem-callsites
# the gate, under the box-wide lock (docs/operational-lessons.md): scripts/capped scripts/ci --diff > .tmp/ci-1.log 2>&1; echo EXIT=$?
# the choice trace, both binaries, the two standing exclusions (as S2c did):
scripts/choice-trace-corpus --dump --jobs 6 --golean .tmp/golean-s3-final --out artifacts/choice-trace-s3   --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
scripts/choice-trace-corpus --dump --jobs 6 --golean .tmp/golean-main --out artifacts/choice-trace-main --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
for d in s3 main; do cat artifacts/choice-trace-$d/dump-*.tsv | LC_ALL=C sort > .tmp/dump-$d.sorted.tsv; done; cmp .tmp/dump-s3.sorted.tsv .tmp/dump-main.sorted.tsv; echo cmp EXIT=$?; sha256sum .tmp/dump-*.sorted.tsv; wc -l .tmp/dump-*.sorted.tsv
scripts/detector-soundness --select in-scope --jobs 6 --out artifacts/detector-soundness-s3   # then compare matrix.tsv cell-for-cell with the prior official run's (detector-soundness-s3.txt)
```
