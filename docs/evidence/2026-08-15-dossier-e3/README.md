# E3 evidence — inter-target phase-1 operand order (2026-08-15, dossier lane)

Probes for `docs/2026-08-15_dossier-e3.md` (inventory E3; BUG-032
S1-delta amendment's third axis). First-hand reproduction of the
recorded facts: gc's panic pick among multiple panicking targets is
neither left-to-right nor right-to-left, flips on target swap, and is
stable under `-N -l` (compiler-internal, not an optimizer artifact).

Toolchain: go1.26.5 linux/amd64. GOCACHE repo-local. Each probe is
`go run <dir>/main.go`; `output.txt` verbatim.

## two-targets — `aa[5][0], b[*pn] = f6()`

Target 1 panics index-out-of-range (`aa[5]`, len 3); target 2 panics
nil-deref (`*pn`). gc reports the SECOND:

    recovered: runtime error: invalid memory address or nil pointer dereference

(The machine's left-to-right point reports the first — `[5] with
length 3`.)

## two-targets-swapped — `b[*pn], aa[5][0] = f6()`

Same two targets, swapped. gc's answer FLIPS — it is ordering, not
panic-kind priority:

    recovered: runtime error: index out of range [5] with length 3

## three-targets — `aa[5][0], cc[9][0], dd[7][0] = f8()`

gc picks the MIDDLE target's panic:

    recovered: runtime error: index out of range [9] with length 3

`output-noopt.txt` — same binary shape under
`-gcflags=all="-N -l"`, identical output (not an optimizer artifact):

    recovered: runtime error: index out of range [9] with length 3

## assign-many-twin — `aa[5][0], b[*pn] = 42, 7`

The call-free twin (E2's call pin not in play) realizes the same
second-target pick:

    recovered: runtime error: invalid memory address or nil pointer dereference

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    for d in two-targets two-targets-swapped three-targets assign-many-twin; do
      go run docs/evidence/2026-08-15-dossier-e3/$d/main.go
    done
    go build -gcflags=all="-N -l" -o .tmp/e3-noopt \
      docs/evidence/2026-08-15-dossier-e3/three-targets/main.go && ./.tmp/e3-noopt
