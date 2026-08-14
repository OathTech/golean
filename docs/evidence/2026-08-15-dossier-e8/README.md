# E8 evidence — multi-file declaration order (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-e8.md` (inventory E8). Toolchain:
go1.26.5 linux/amd64; GOCACHE repo-local; `output.txt` verbatim
(all runs appended in order).

## multi-file — three presentation modes of one package

`main.go` (defines `rec` + prints the sequence), `za.go`
(`var a = rec("a")`), `zb.go` (`var b = rec("b")`). Both vars are
dependency-free, so init order = declaration order = file presentation
order.

    == go run main.go za.go zb.go (sorted order) ==
    ab
    == go run zb.go za.go main.go (REVERSED argument order) ==
    ba
    == go run . in the probe dir (package mode, GO111MODULE=off) ==
    ab

(The first `go run ./<dir>` attempt from the repo root failed with
`go: cannot find main module` — module mode; the package-mode run uses
GO111MODULE=off per the sandbox convention. Kept in output.txt for
honesty.)

KEY DATUM: the go command sorts by file name in PACKAGE (directory)
mode, but with an EXPLICIT file-argument list it presents files in
ARGUMENT order — `go run zb.go za.go main.go` realizes `ba` with the
standard toolchain, no exotic build system needed. The narrowing's
transfer scope is therefore "directory/package-mode builds (and sorted
file lists)", not "the go command" simpliciter.

Appended datum: `go build -o .tmp/e8 zb.go za.go main.go` also
realizes `ba` — argument-order presentation holds for `go build` too.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache" GO111MODULE=off
    D=docs/evidence/2026-08-15-dossier-e8/multi-file
    go run $D/main.go $D/za.go $D/zb.go     # ab
    go run $D/zb.go $D/za.go $D/main.go     # ba
    (cd $D && go run .)                      # ab
