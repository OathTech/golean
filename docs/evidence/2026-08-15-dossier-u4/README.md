# U-4 evidence — overlapping copy/append aliasing (2026-08-15, dossier lane)

Probe for `docs/2026-08-15_dossier-u4.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; output verbatim.

## overlap-matrix — five aliasing shapes

    copied 4 | fwd  a[1:] <- a[:4]: 1 1 2 3 4
    copied 4 | bwd  b[:4] <- b[1:]: 2 3 4 5 5
    self c <- c        : 1 2 3
    append d[:1], d... : 1 1 2 3
    append f, f...     : 7 8 9 7 8 9

All five realize the spec's as-if-intermediate ("the result is
independent of whether the memory referenced by the arguments
overlaps"): forward-overlap copy does not cascade the first element
(1 1 2 3 4, not 1 1 1 1 1 — the naive left-to-right in-place loop's
answer), backward overlap shifts cleanly, self-copy is identity,
in-place aliasing append preserves the pre-append source values, and
the spill self-append duplicates the original.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-u4/overlap-matrix/main.go
