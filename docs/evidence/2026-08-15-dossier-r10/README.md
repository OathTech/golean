# R10 evidence — abort-line rendering (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r10.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local. `output.txt` per probe is the FULL
`go run` combined output (stack traces include file paths and frame
offsets that vary by checkout — the HEAD lines are the pinned
surface) plus the `go run` exit code; the in-binary exit status is
the `exit status 2` line.

## int-payload — `panic(42)`

    panic: 42

## error-payload — payload with an `Error() string` method

    panic: custom error text

gc's `preprintpanics` CALLS `Error()` at abort time and renders its
result — the machine's fail-closed edge (a method call at abort time
is unmodelable today; BUG-004 item class).

## recovered-chain — recover then re-panic from the deferred func

    panic: first [recovered]
    	panic: second

The first panic is rendered with ` [recovered]` and the re-panic
beneath — the chain shape whose eface-identity variant (re-panicking
the SAME value) is the machine's other fail-closed edge (needs
allocation identity, unmodeled; R10/BUG-004 item 1).

All three abort with in-binary exit status 2.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in int-payload error-payload recovered-chain; do
      go run docs/evidence/2026-08-15-dossier-r10/$d/main.go
    done
