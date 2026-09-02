# diff-coverage ARG_MAX fan-out defect — red-first record and post-fix refusal (2026-09-02)

[AGENT] Trusted-apparatus fix slice, branch `diffcov-argmax-hardening`
off main @ e7d07b26. The defect was found by the grossmith campaign
and verified by its auditor ([USER]-directed campaign; this dir is the
fix lane's own first-hand reproduction, not the campaign's transcript).
Consuming docs: `docs/operational-lessons.md` ("ARG_MAX is a cliff
whose height is set by TMPDIR length"), the fixture comment at
`scripts/test-lane-validation` G5, and the fan-out/assembler comments
in `scripts/diff-coverage`.

## The defect (pre-fix `scripts/diff-coverage`, main @ e7d07b26, line 1370)

```
ls "$ROWDIR"/*.in | xargs -P "$GOLEAN_COVERAGE_JOBS" -n 1 bash -c 'run_case "$1"' _ \
  || echo "WARNING …"
```

The glob expands inside bash but is handed to `ls` as ONE execve
argument vector, bounded by ARG_MAX (2,097,152 here). Past the bound
execve fails E2BIG (`ls: Argument list too long`) and three fail-open
behaviours compose:

- (i) GNU xargs without `-r` runs its command ONCE on empty stdin →
  `run_case ""` FABRICATES a manifest-error row for id "" and mv's a
  stray `.out` into the CWD (the repo root);
- (ii) `|| echo WARNING` absorbs the pool's nonzero exit;
- (iii) the assembler writes `FAIL <id> unknown harness "worker
  produced no result"` for EVERY row and `publish_results` PUBLISHES
  them (exit 1 = "results authoritative") — one global failure
  attributed per case, row-for-row indistinguishable from N
  independent worker deaths.

The serial path (`GOLEAN_COVERAGE_JOBS<=1`, a bash for-loop) never
execs the list and was immune. Main's 2,526 rows are safe today only
because the cliff is a function of TMPDIR length and nothing checked it.

## Conclusion (what the citing docs rely on)

Measured: at a 130-byte TMPDIR (168-byte per-file row paths) the
cliff is **11,817 rows** (bisection; predicted 11,848 from
ARG_MAX/(path+1+8) — the environment also counts). The pre-fix runner,
driven by a 19,999-row manifest under that TMPDIR, exhibited all three
sub-defects exactly as described: `Argument list too long`, a stray
`.out` in the repo root containing `FAIL<TAB><TAB>unknown<TAB>manifest
<TAB>expected 10 tab-separated fields`, and a PUBLISHED `latest.tsv`
with 19,999 `worker produced no result` rows, exit 1. The post-fix
runner on the SAME manifest/TMPDIR ran all 19,999 workers through the
`find -print0 | xargs -0 -r` fan-out (19,999 distinct, correctly
attributed per-row results; `fanout_find_exit 0`, `fanout_pool_exit 0`
in the meta; no stray file), and the empty-pool path (a fake `xargs`
reproducing "GNU xargs without -r on empty stdin") is refused with two
named causes, exit 2, nothing published, stale pair removed.

## Files

| file | producer | what it shows |
|---|---|---|
| `repro.sh` | (this dir) | the driver; every `*.log` below names its stage in its header |
| `mechanism.log` | `repro.sh mechanism` | no build needed: fake 19,999-file ROWDIR; `ls` E2BIG; `xargs` invoked once with `arg=<>`; `xargs -r` zero invocations; `find -print0 \| xargs -0 -r` all 19,999; the bisected cliff |
| `prefix.log` | `repro.sh prefix` | the PRE-fix runner (`git show e7d07b26:scripts/diff-coverage`) on the 19,999-row manifest: exit 1, stray `.out` + content, 19,999 published misattributed rows, meta |
| `postfix-scale.log` | `repro.sh postfix` | the fixed runner, same manifest/TMPDIR: 19,999 real per-row results, 0 `worker produced no result`, no stray file, `fanout_*` meta keys |
| `postfix-emptypool.log` | `repro.sh postfix` | the fixed runner with a PATH-shadowed no-`-r` `xargs` (the G5 fixture's shape): both refusals named, exit 2, nothing published |

Manifest construction (stated in `repro.sh`): every row carries an
11th field, so post-fix each row is a REAL, fast, per-row
manifest-stage FAIL (`too many tab-separated fields` — `run_case_rows`'
first check, no go/lean shell-out). The subject under test is the
fan-out, not the classification; the pre-fix runner never reads a
row at all. The pre-fix runner is materialised at
`scripts/.diff-coverage-prefix` because its `ROOT` derives from its
own location; the driver removes it (and the stray `.out`) afterwards.

## Reproduction (from the repo root; needs the built binary and go at the pin)

```
scripts/capped lake build
scripts/capped docs/evidence/2026-09-02_diffcov-argmax/repro.sh all
scripts/capped scripts/test-lane-validation --with-go      # G5 among the fixtures
```

Scratch lives in `artifacts/argmax-scratch/` (gitignored); the logs
have absolute worktree prefixes stripped to repo-relative paths.

## Toolchain, commit, host

- `go version go1.26.5 linux/amd64` — the pin in `baselines/go-oracle-pin`.
- Lean binary: `.lake/build/bin/golean` built from this tree
  (`scripts/capped lake build`, 58 jobs, exit 0).
- Commit: the logs record `e7d07b26 (dirty tree: M scripts/diff-coverage
  M scripts/test-lane-validation …)` — i.e. the fix's working tree
  before its commit; the PRE-fix runner is taken from git at exactly
  e7d07b26 regardless of tree state, and the post-fix runner is the
  content committed on `diffcov-argmax-hardening` immediately after.
- Host: linux/amd64, 32-core / 125 GB dev box; the runs were made with
  other lanes' processes present. Only the cliff count is a measured
  number and it is load-independent (an execve limit, not a timing).

## The fix (strengthens-only, [TRUST-ADJACENT]) — `scripts/diff-coverage`

1. `find "$ROWDIR" -maxdepth 1 -name '*.in' -print0 | xargs -0 -r -P N -n 1 bash -c 'run_case "$1"' _` —
   no argv bound, nothing runs on empty input.
2. `run_case` refuses an empty/non-file row path by name and returns 2
   (writes nothing).
3. Fan-out statuses captured via `PIPESTATUS` (serial path: any
   nonzero `run_case`), WARNED with the xargs code legend, and
   recorded in the meta (`fanout_find_exit`, `fanout_pool_exit`).
4. Assembler: `case_count > 0 && result_count == 0` ⇒ named refusal,
   `rm -rf ROWDIR`, exit 2 BEFORE `publish_results` (the existing
   "exit ≥ 2 ⇒ nothing published" invariant). Scattered deaths keep
   the per-row fail-closed rows.
5. Fixture: `scripts/test-lane-validation` G5 (Part B, `--with-go`,
   because it must get past the build/binary checks the fast-gate
   lane step precedes; asserts exit 2, no publish, both named causes
   on stderr, no stray `.out` — exit 2 alone would pass vacuously).
