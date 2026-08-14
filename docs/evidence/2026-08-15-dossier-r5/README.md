# R5 evidence — float division by zero (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r5.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; outputs verbatim.

## float-div-zero — IEEE specials, no panic

    1.0/z   = +Inf
    -1.0/z  = -Inf
    1.0/nz  = -Inf
    z/z     = NaN
    f32/z32 = +Inf
    reached end: no panic

gc realizes IEEE ±Inf/NaN with NO run-time panic across signs, the
0/0 shape, and float32 — the machine's narrowed point
(Machine.lean:270–275: float arm dispatches before the integer zero
check).

## int-div-zero-contrast — the mandated integer panic (not latitude)

    recovered: runtime error: integer divide by zero

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-r5/float-div-zero/main.go
    go run docs/evidence/2026-08-15-dossier-r5/int-div-zero-contrast/main.go
