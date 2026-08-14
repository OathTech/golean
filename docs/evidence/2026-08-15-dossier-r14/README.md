# R14 evidence — constant arithmetic precision (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r14.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; outputs verbatim.

## precision-512 — 500-bit intermediates

    x = 1024

`(1<<500) / (1<<490)` folds exactly — gc exceeds the spec's 256-bit
minimum. A minimally-conforming 256-bit implementation MAY reject
this program ("give an error if unable to represent an integer
constant precisely").

## precision-boundary — gc's realized limit is exactly 512 bits

    == 1<<511 (in-program) ==
    1
    == 1<<512 / multiplication to 2000 bits (rejections, verbatim) ==
    .tmp/r14b/s.go:3:13: constant shift overflow
    .tmp/r14b/m.go:4:19: constant multiplication overflow

`1<<511` (a 512-bit value) accepted; `1<<512` rejected. gc is NOT
arbitrary-precision: an implementation with more precision would
ACCEPT programs gc rejects — the acceptance boundary cuts both ways.

## precision-5000 — shift-count cap (a separate, additional limit)

    invalid operation: invalid shift count 5000 (untyped int constant)

Shift counts themselves are capped (independent of value precision).

## float-rounding — RUNTIME-OBSERVABLE precision divergence

`const tiny = 1.0 + 1e-100` (needs ~333 fractional bits exactly):

    const tiny != 1.0 (exact): true
    float64(tiny) == 1.0: true

gc keeps the CONSTANT comparison exact (`true`). A conforming
256-bit-mantissa implementation must "round to the nearest
representable constant", making `tiny != 1.0` FALSE — a
runtime-observable output difference between conforming
implementations. This REFUTES the inventory's "no runtime
observable" note for R14.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in precision-512 precision-boundary float-rounding; do
      go run docs/evidence/2026-08-15-dossier-r14/$d/main.go
    done
    go run docs/evidence/2026-08-15-dossier-r14/precision-5000/main.go  # rejects
