# R13 evidence — sort.Slice instability (2026-08-15, dossier lane)

Probe for `docs/2026-08-15_dossier-r13.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; output verbatim.

## instability — 64 records, 4 key classes

    equal-key inversions after sort.Slice: 30
    stable? false
    SliceStable inversions: 0

gc's `sort.Slice` (pdqsort) reorders equal-key records (30
inversions at n=64) — the documented instability, realized.
`sort.SliceStable` preserves input order (0 inversions), the
contrast. For `[]int` sorts (the machine's supported kind today),
equal elements are bit-identical — no probe can observe which
"equal 5" came first, which is the declared-unobservable argument's
substance.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-r13/instability/main.go
