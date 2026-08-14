# R3 evidence — `[]byte(s)` conversion capacity (2026-08-15, dossier lane)

Probe for `docs/2026-08-15_dossier-r3.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; output verbatim.

## cap-matrix — escape regime × length

    local    len 5 cap 5
    escaping len 5 cap 5
    local    len 33 cap 33
    escaping len 33 cap 48
    local    len 100 cap 100
    escaping len 100 cap 112

- NON-ESCAPING conversions realize cap = len at every probed length —
  the machine's singleton point.
- ESCAPING conversions realize the size-class rounded capacity for
  len 33 (cap 48) and len 100 (cap 112) — OUTSIDE the cap = len
  singleton, reproducing the recorded transfer caveat
  (Machine.lean:313–333) first-hand.
- Escaping len 5 realizes cap 5 (not a visible rounding) — the
  escape+rounding exposure begins above the small-allocation regime
  on this toolchain; the envelope's lower end (cap = len) is realized
  by gc too.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-r3/cap-matrix/main.go
