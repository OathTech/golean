# E5 evidence — early store across the phase boundary (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-e5.md` (inventory E5; BUG-032
final-check amendment). Toolchain: go1.26.5 linux/amd64; GOCACHE
repo-local; outputs verbatim.

## early-store-local — the recorded shape (`x` a LOCAL)

`x, a[i].f = 1, 7/z` with z = 0, x local, read by the deferred recover
closure. gc lands the x = 1 store BEFORE the phase-1 division panic —
the recorded early-store realization:

    recovered: runtime error: integer divide by zero | x = 1

`output-noopt.txt` (`-gcflags=all="-N -l"`) — identical:

    recovered: runtime error: integer divide by zero | x = 1

(The machine follows the spec's literal two-phase order: x stays 0.)

## early-store — the SAME shape with `x` a GLOBAL (new datum)

Identical statement, all variables package-level. gc does NOT land the
early store — it realizes the spec-literal point here:

    recovered: runtime error: integer divide by zero | x = 0

gc's early store is STORAGE-CLASS-DEPENDENT (locals early, globals
not) — the realization is compiler-internal (write-barrier/liveness
shaped), not a stable "stores land early" rule. Refines the BUG-032
final-check record, which exhibited only the local shape.

## swapped-order — `a[i].f, x = 7/z, 1`, globals

RHS positions swapped so the panicking operand precedes x's value
lexically; globals. Spec-literal result again:

    recovered: runtime error: integer divide by zero | x = 0

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in early-store early-store-local swapped-order; do
      go run docs/evidence/2026-08-15-dossier-e5/$d/main.go
    done
    go build -gcflags=all="-N -l" -o .tmp/e5-noopt \
      docs/evidence/2026-08-15-dossier-e5/early-store-local/main.go && ./.tmp/e5-noopt
