# BUG-119 / BUG-120 zero-movement check — lane `fix/bug119-120-1008` (2026-10-08)

[AGENT] fix worker, 2026-10-08. Cited by `docs/BUGS.md` (BUG-119 and BUG-120 FIX paragraphs) and the draft row of
`docs/changelog/20d3946d-WINDOW.md`.

**Conclusion.** The lane routes the entry arguments of `coverage-observations` and `choice-trace` through
`entryArgValues` (BUG-119) and catches input-file read errors on every file-reading subcommand (BUG-120). Because
these subcommands drive the differential (`scripts/diff-coverage`, `scripts/detector-soundness`,
`scripts/membership-sampling`), every manifest row that passes `--arg-int` was run under MAIN's binary and the LANE's
binary on all three subcommands, comparing stdout, stderr and exit code byte for byte: **493 rows (491 strict, 2
membership), 0 differences** (`zero-movement.tsv`: per row the lane's exit codes and any `DIFF:` cell — none). One
row, `noodler/budget/loop-100k`, timed out (180 s) under BOTH binaries on the enumeration with the strict-enum
bound; re-run at `--work-cap 1000` it gives byte-identical output under both (`work cap exceeded after 1001
step(s)` — i.e. past the argument check). No lane output contains an argument-check or read refusal text.

**What ran** (`zero-movement-driver.sh.txt`, one row per call): the row's wire is emitted by the native frontend
built from the tree (`go build -o .tmp/nf ./tools/nativefrontend`); then, per binary,
`native-json-run` (row args), `choice-trace --stream default --stream 1,0,1` (row args), and
`coverage-observations` with the row's own params (membership rows: width/sites/cap/work/statuses as
`scripts/diff-coverage` derives them) or `scripts/detector-soundness`'s `--strict-enum` default
`width=4,sites=32,cap=512,work=4000000,backedge=1` (strict rows), `--expect-status` = the row's status.

**Reproduction** (from the lane worktree root, after `scripts/capped lake build GoLean golean`):

    cp <main checkout>/.lake/build/bin/golean .tmp/golean-main   # main's binary
    .tmp/golean-main --build-provenance   # must equal `python3 tools/certification.py build-identity` at main
    GO111MODULE=off go build -o .tmp/nf ./tools/nativefrontend
    scripts/coverage-manifest > .tmp/manifest.tsv
    awk -F'\t' '$1 !~ /^#/ && NF>0 && $4 != "-"' .tmp/manifest.tsv > .tmp/zm/rows.tsv
    cp docs/evidence/2026-10-08_bug119-120/zero-movement-driver.sh.txt .tmp/zm/one.sh && chmod +x .tmp/zm/one.sh
    tr '\n' '\0' < .tmp/zm/rows.tsv | xargs -0 -P 8 -n 1 .tmp/zm/one.sh | sort > zero-movement.tsv

**Provenance.** Main binary: `main` @ `6a90ba8d`, its `--build-provenance` identical to `tools/certification.py
build-identity` at `6a90ba8d`. Lane binary: the lane's source tree (CLI.lean / ChoiceTrace.lean as committed). Go
`go1.26.5 linux/amd64` (the oracle pin; only the frontend runs). Lean `v4.32.2`. Host: the shared linux/amd64 box
(32 cores), load average ~10 during the run, 8 rows in parallel — the timeout row is load-sensitive, the
byte-identity is not.
