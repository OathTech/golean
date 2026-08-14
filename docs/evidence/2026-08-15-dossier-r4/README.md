# R4 evidence — float fusion + extra intermediate precision (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r4.md`. Toolchain: go1.26.5
linux/amd64 at default GOAMD64 (=v1) — the oracle platform the
narrowing is scoped to. GOCACHE repo-local; outputs verbatim.

## fma-shape — the fusion discriminator

x = y = 1+2^-27, z = -(1+2^-26): per-op rounding gives x*y+z == 0;
a fused single rounding gives the exact residue 2^-54.

    x*y + z          = 0
    math.FMA(x,y,z)  = 5.551115123125783e-17
    2^-54            = 5.551115123125783e-17
    fused?           = false

The oracle platform does NOT fuse `x*y + z` (result 0 — double
rounding); `math.FMA` witnesses the fused value the narrowing
excludes (math library out of the machine's scope; shown for
contrast only).

## float32-precision — the extra-precision discriminator

a = 2^24 (ulp 2): per-op float32 rounding absorbs each +1;
extended-precision intermediates would carry a+2.

    a          = 1.6777216e+07
    a + 1 + 1  = 1.6777216e+07
    per-op rounding (b == a): true

The oracle platform rounds float32 per op — no extra intermediate
precision.

## NOT-OBTAINED

gc/arm64 and amd64 GOAMD64=v3 executions of the fma-shape (recorded
as OUTSIDE the envelope — the transfer-scope boundary): no
cross-platform runner in this lane. Cross-compilation cannot help
here (the datum is runtime output). What would obtain: an arm64
runner or a GOAMD64=v3-capable host.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-r4/fma-shape/main.go
    go run docs/evidence/2026-08-15-dossier-r4/float32-precision/main.go
