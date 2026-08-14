# E11 evidence — runtime check order inside one operation (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-e11.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; outputs verbatim.

## slice-both-invalid — `s[5:4]` on len/cap 3 (lo > hi AND hi > cap)

    recovered: runtime error: slice bounds out of range [:4] with capacity 3

The HIGH check fires first (hi vs cap), even though lo > hi also
holds — gc realizes high-then-low, the machine's pinned order
(`checkSliceBounds`, Ops.lean:173–218).

## slice3-both-invalid — `s[1:5:2]` (hi > cap AND hi > max)

    recovered: runtime error: slice bounds out of range [:5:2]

The hi-vs-max violation is the one rendered.

## iface-two-missing — assertion missing Alpha and Gamma (Beta present)

Interface declares Gamma, Beta, Alpha in that order; T implements only
Beta:

    recovered: interface conversion: main.T is not main.I: missing method Alpha

gc names ALPHA — the first missing method in NAME-SORTED order, not
declaration order (Alpha is declared LAST) — the machine's pinned
order (Ops.lean:716–747).

## mapkey-two-unhashable — `[2]interface{}{func(){}, map[int]int{}}` as key

    recovered: runtime error: hash of unhashable type func()

The FIRST offending component in hashing order (array element 0) is
named — the machine's pinned walk (Ops.lean:1564–1611).

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in slice-both-invalid slice3-both-invalid iface-two-missing mapkey-two-unhashable; do
      go run docs/evidence/2026-08-15-dossier-e11/$d/main.go
    done
