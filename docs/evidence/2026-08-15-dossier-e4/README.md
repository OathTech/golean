# E4 evidence — targets-vs-RHS unordered panic order (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-e4.md` (inventory E4; BUG-032
round-4 amendment (b)). Toolchain: go1.26.5 linux/amd64; GOCACHE
repo-local; `go run <dir>/main.go`; outputs verbatim.

## lhs-vs-rhs — `xs[ys[9]], b = zs[7], 2`

Panicking TARGET operand (`ys[9]`, len 3) vs panicking RHS operand
(`zs[7]`, len 3). gc reports the RHS's:

    recovered: runtime error: index out of range [7] with length 3

(The machine's phase-1 targets-then-RHS order — tgtOpK → rhsK,
StepFn.lean:459–500 — reports the target's `[9]`.)

## rhs-first-position — `b, xs[ys[9]] = zs[7], 2`

Same operands, the panicking target moved to the second target
position. gc's pick CHANGES — now the TARGET's panic:

    recovered: runtime error: index out of range [9] with length 3

New datum (beyond the BUG-032 record): gc's targets-vs-RHS pick is
POSITION-DEPENDENT, corroborating E3's finding that the realization is
compiler-internal and unpinnable — there is no simple "RHS first" rule
to pin even if pinning were wanted.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in lhs-vs-rhs rhs-first-position; do
      go run docs/evidence/2026-08-15-dossier-e4/$d/main.go
    done
