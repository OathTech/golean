# R11 evidence — sync misuse fatal class (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r11.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local. `output.txt` per probe: full
combined output + `go run` exit; in-binary status is the
`exit status 2` line.

## unlock-unlocked — Mutex.Unlock without a lock, under a deferred recover

    fatal error: sync: unlock of unlocked mutex

In-binary exit status 2. The probe's deferred function (which would
print `deferred ran; ...`) produced NO output — a runtime throw does
not run deferred functions AT ALL (stronger than "recover does not
catch": the recover machinery is never reached; grep count for
"deferred ran" in output.txt: 0).

## rwmutex-runlock — RWMutex.RUnlock without a read lock

    fatal error: sync: RUnlock of unlocked RWMutex

Same class, exit status 2.

Contrast (probed under R8): WaitGroup misuse is a recoverable PLAIN
STRING panic — the sync package realizes BOTH classes, per API.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-r11/unlock-unlocked/main.go
    go run docs/evidence/2026-08-15-dossier-r11/rwmutex-runlock/main.go
