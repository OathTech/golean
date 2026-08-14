# R12 evidence — exit codes and terminal classification (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r12.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; `exit-codes.txt` verbatim.

## exit-codes.txt — the harness's terminal classes, realized

    exit-ok: exit 0
    exit-explicit: exit 7
    exit-panic: exit 2
    exit-race (-race): exit 66
    exit-deadlock: exit 2

- Normal completion: 0. `os.Exit(7)`: passthrough 7.
- Unrecovered panic: 2 (head line in R10's evidence).
- Deadlock: 2, head line `fatal error: all goroutines are asleep -
  deadlock!` (exit-deadlock/output.txt) — C9's pinned terminal; the
  probe here documents only the EXIT CLASS the harness keys on.
- `-race` report: 66 (the TSan default exit code the differential's
  race lane keys on).

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    B=docs/evidence/2026-08-15-dossier-r12
    for d in exit-ok exit-explicit exit-panic exit-deadlock; do
      go build -o .tmp/r12 $B/$d/main.go && ./.tmp/r12; echo "$d -> $?"
    done
    go build -race -o .tmp/r12race $B/exit-race/main.go && ./.tmp/r12race; echo "race -> $?"
