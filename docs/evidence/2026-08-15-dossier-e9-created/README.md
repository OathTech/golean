# E9-created evidence — entries created during map iteration (2026-08-15, dossier lane)

Probe for `docs/2026-08-15_dossier-e9-created.md` (inventory E9's
created-entries sub-point; §9 flag 4). Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; `output.txt` verbatim (two
executions).

## created-entries — does gc ever PRODUCE a created entry?

200 independent iterations per execution; each ranges over a fresh
4-entry map and inserts 8 fresh keys (≥ 100) during the iteration;
counts runs producing at least one created entry.

    runs: 200 | runs producing >=1 created entry: 180 | total created entries produced: 542
    === second run (per-run variance) ===
    runs: 200 | runs producing >=1 created entry: 175 | total created entries produced: 563

gc PRODUCES created entries in ~90% of runs in this growth-regime
shape (4 → 12 entries forces bucket growth; produced counts vary per
run and per execution — the spec's "may vary for each entry created
and from one iteration to the next", realized).

KEY CONSEQUENCE: the machine's snapshot semantics resolves this
latitude to the singleton "never produced". gc's observations here
(created entries produced) are OUTSIDE that singleton — on any corpus
shape of this kind, `observed ∉ modeled`. The singleton is a
conforming implementation point (the spec permits skipping every
created entry) but fails the doctrine's lower bound for membership on
these shapes.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-e9-created/created-entries/main.go
