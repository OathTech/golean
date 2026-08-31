# E7 evidence — hidden-dependency initialization order (2026-08-15, dossier lane)

Probe for `docs/2026-08-15_dossier-e7.md` (inventory E7). Toolchain:
go1.26.5 linux/amd64; GOCACHE repo-local; output verbatim.

## hidden-dep — the spec's own example shape

`hiddenX = hiddenI(hiddenT{}).ab()` (method through an interface
conversion — the dependency on `hiddenA`/`hiddenB` is invisible to
per-package lexical dependency analysis), then `hiddenA = hiddenB`,
`hiddenB = 42`. Readout `hiddenX*10000 + hiddenA*100 + hiddenB`.

gc:

    4624242

i.e. gc initializes hiddenX AFTER hiddenA/hiddenB (ab() sees 42/42 →
hiddenX = 462). go/types' `InitOrder` — the frontend's realization,
driving `$pkginit` — puts hiddenX FIRST (ab() sees 0/0 → hiddenX = 0 →
readout 4242; the standing differential red on
`init/hidden-dep-order`, whose realized order is mechanically pinned
by a deviation-observation pin — check-golden then,
scripts/check-frontend-pins since the 2026-08-31 repo split). Both orders conform: the
spec text at the shape says the order "is not specified".

The probe program is a println-readout copy of the corpus case
`Corpus/coverage/exec/init/hidden-dep-order/main.go` (unchanged there;
this lane does not touch Corpus/).

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-e7/hidden-dep/main.go
