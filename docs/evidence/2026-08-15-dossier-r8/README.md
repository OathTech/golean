# R8 evidence — WaitGroup counter representation (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r8.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; outputs verbatim. All probes are
single-goroutine (the latitude is representational arithmetic —
sequentially observable misuse).

## negative-basic — the documented misuse

    recovered (string? true ): sync: negative WaitGroup counter

Plain-string panic value (the BUG-054 box-class distinction: sync
package panics are plain strings, not runtime.Error).

## wrap-2p31 — a single Add(1<<31)

An unbounded-counter implementation would accept this (the doc only
forbids NEGATIVE counters). gc wraps the 32-bit counter before the
negative test:

    recovered: sync: negative WaitGroup counter

## wrap-incremental — 2^31 reached in two positive steps

    after Add(2^31-1): ok
    recovered: sync: negative WaitGroup counter

2^31−1 is representable (ok); +1 wraps negative and panics — the
wrap-before-test realization, matching the machine's BUG-055 formula
`counter' = ((counter + delta + 2^31) emod 2^32) − 2^31`.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in negative-basic wrap-2p31 wrap-incremental; do
      go run docs/evidence/2026-08-15-dossier-r8/$d/main.go
    done
