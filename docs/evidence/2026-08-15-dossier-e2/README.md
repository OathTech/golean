# E2 evidence — call vs. assignment-target operands (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-e2.md` (inventory E2: the
call-vs-operand order pin, BUG-052's latitude). These are CONFIRMATION
probes of the recorded pin — the record of authority is the BUG-052
S1-audit probe matrix and its five oracle-backed corpus pins
(`multi-assign/call-write-back-order/*`); this directory re-exhibits
the three observable directions first-hand for the dossier.

Toolchain: go1.26.5 linux/amd64 (the CI-pinned oracle family).
GOCACHE repo-local per the sandbox convention. Each probe is
`go run <dir>/main.go`; `output.txt` is the verbatim combined output.

## index-panic — the panic-direction discriminator

Callee sets the target's index operand out of range. Call-first (gc's
pin) reads it post-call → panic; operand-first reads 0 → no panic.

    panic: runtime error: index out of range [5] with length 3

gc realizes CALL-FIRST (the panic fires — operand read after the call).

## value-order — the value-direction discriminator

Callee moves the index operand within range (0 → 2). Call-first stores
at `xs[2]`; operand-first at `xs[0]`.

    10 11 42 7

gc stores at `xs[2]` — call-first.

## deref-target — the pointer-repoint discriminator

Callee repoints the deref target's pointer (`p = &b`). Call-first
stores through the NEW pointee.

    a 0 b 42 j 7

gc stores through `b` — call-first.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in index-panic value-order deref-target; do
      go run docs/evidence/2026-08-15-dossier-e2/$d/main.go
    done
