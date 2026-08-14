# R1 evidence — int/uint width (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-r1.md`. Toolchain: go1.26.5
linux/amd64 (+ GOARCH=386 cross-compilation of the SAME toolchain — no
install); GOCACHE repo-local; `output.txt` verbatim.

## width-witness — the oracle host's chosen width

    strconv.IntSize: 64
    unsafe.Sizeof(int(0)): 8
    unsafe.Sizeof(uint(0)): 8
    unsafe.Sizeof(uintptr(0)): 8
    bits in ^uint(0): 64

## overflow-acceptance — the acceptance entanglement, BOTH width points

`const big int = 1 << 62` compiles and runs on amd64
(`4611686018427387904`); under GOARCH=386 the SAME toolchain REJECTS
it at compile time:

    docs/evidence/2026-08-15-dossier-r1/overflow-acceptance/main.go:6:17: cannot use 1 << 62 (untyped int constant 4611686018427387904) as int value in constant declaration (overflows)

The width pin reaches the NEGATIVE lane (which programs compile), and
the other width point is realized by gc itself under GOARCH=386 — the
32-bit ACCEPTANCE datum is obtainable without any new toolchain.

## The 32-bit RUNTIME datum — NOT-OBTAINED

GOARCH=386 cross-compilation of width-witness succeeds (build exit 0)
but this host cannot execute linux/386 binaries (no output, exit 133 =
SIGTRAP). A 32-bit runtime oracle needs a host/emulation layer — out
of this lane's means.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    D=docs/evidence/2026-08-15-dossier-r1
    go run $D/width-witness/main.go
    go run $D/overflow-acceptance/main.go
    GOARCH=386 go build -o .tmp/r1-386 $D/overflow-acceptance/main.go  # rejects
