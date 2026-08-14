# E10 evidence — map key retention on overwrite (2026-08-15, dossier lane)

Probe for `docs/2026-08-15_dossier-e10.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; output verbatim.

## signed-zero-key — the in-language retention observable

+0.0 and -0.0 are `==` but distinguishable via `1/k`. Insert under one
sign, overwrite under the other, in both directions:

    insert +0, overwrite -0:  1/k = -Inf  v = 2
    insert -0, overwrite +0:  1/k = +Inf  v = 2

gc REPLACES the stored key with the overwriting key in both
directions (go1.26.5's realized `needkeyupdate` point for float64) —
matching the machine's always-replace pin
(`entries.set! i (key, value)`, Machine.lean:239–243).

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-e10/signed-zero-key/main.go
