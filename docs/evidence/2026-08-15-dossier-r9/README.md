# R9 evidence — run-time panic values and message texts (2026-08-15, dossier lane)

Probe sheet for `docs/2026-08-15_dossier-r9.md`. Toolchain: go1.26.5
linux/amd64; GOCACHE repo-local; output verbatim.

## message-sheet — 13 classes, box class + exact text

    index-oob       | runtime.Error | runtime error: index out of range [5] with length 3
    slice-bounds    | runtime.Error | runtime error: slice bounds out of range [:9] with capacity 3
    nil-map-write   | runtime.Error | assignment to entry in nil map
    nil-deref       | runtime.Error | runtime error: invalid memory address or nil pointer dereference
    iface-conv      | runtime.Error | interface conversion: interface {} is int, not string
    div-zero        | runtime.Error | runtime error: integer divide by zero
    make-chan-neg   | runtime.Error | makechan: size out of range
    make-slice-neg  | runtime.Error | runtime error: makeslice: len out of range
    close-nil       | runtime.Error | close of nil channel
    close-closed    | runtime.Error | close of closed channel
    send-closed     | runtime.Error | send on closed channel
    panic-nil       | runtime.Error | panic called with nil argument
    sync-string-box | plain string  | sync: negative WaitGroup counter

Notes:

- All runtime-condition panics carry `runtime.Error` values
  (including `panic(nil)`'s `*runtime.PanicNilError` — the
  GODEBUG=panicnil=0 default the machine aligns with); the sync
  package's misuse panic is a PLAIN STRING — the BUG-054 box-class
  distinction, observable via `recover().(string)`.
- The `Error()` texts are non-uniform: some carry the
  `runtime error: ` prefix (index, slice, deref, div, makeslice) and
  some do not (nil map write, makechan, the channel trio) — the pin
  must (and does) track per-class strings, not a uniform prefix rule.

## Reproduction

    cd <worktree>
    export GOCACHE="$PWD/artifacts/go-build-cache"
    go run docs/evidence/2026-08-15-dossier-r9/message-sheet/main.go
