# gc probe matrix — the maxAlloc panic class (2026-09-02, t5-maxalloc)

[AGENT] Tier-5 slice for fidelity decision 5(b) ([USER] 2026-08-31:
"the deterministic maxAlloc panic class modeled"; the residual target
state is discrepancy D-001, `docs/discrepancy-backlog.md`). Consuming
records: latitude inventory R16 (`docs/2026-08-11_latitude-inventory.md`),
doctrine register #7 (`docs/2026-08-11_essence-of-go-doctrine.md`),
BUG-081 / BUG-082 (`docs/BUGS.md`), corpus package
`Corpus/coverage/exec/builtins/make-maxalloc/`.

## The question

gc panics DETERMINISTICALLY (a recoverable `runtime.Error`, not an OOM
abort) when one allocation request exceeds the runtime's maximum
allocatable size. Which requests, at which thresholds, with which
message — for `make` of slices / channels / maps, for `append` growth,
and is the panic recoverable?

## Spec truth at the pin (go1.26.5, `deps/go/doc/go_spec.html`)

The spec has NO "maximum allocatable size" sentence. §Making slices,
maps and channels: "A constant size argument must be non-negative and
representable by a value of type int … For slices and channels, if n is
negative or larger than m at run time, a run-time panic occurs." and,
for maps, "The precise behavior is implementation-dependent."
§Appending and copying slices: append "allocates a new, sufficiently
large underlying array". §Run-time panics: "The exact error values that
represent distinct run-time error conditions are unspecified." The size
limit, its value, and the panic-vs-clamp choice are therefore the
IMPLEMENTATION's — latitude, pinned to gc's realization (R16).

## gc's realization (runtime sources at the pin)

- `maxAlloc = (1 << heapAddrBits) - (1-_64bit)*1` (malloc.go:220);
  heapAddrBits = 48 on linux/amd64 → 2^48 bytes; 2^32-1 on 32-bit.
- `makeslice` (slice.go:102–115): `mem(cap) overflow || mem(cap) >
  maxAlloc || len < 0 || len > cap` → if `mem(len) overflow || mem(len)
  > maxAlloc || len < 0` then "makeslice: len out of range" else
  "makeslice: cap out of range" (issue 4085: blame len for
  `make([]T, huge)`). STRICT: `mem == maxAlloc` passes.
- `makechan` (chan.go:86–89): `overflow || mem > maxAlloc-hchanSize ||
  size < 0` → `plainError("makechan: size out of range")`;
  `hchanSize` = sizeof(hchan) rounded to 8 = 112 on amd64.
- `makemap` (map.go:60–67): an over-limit or negative hint is CLAMPED
  to 0 (`hint = 0`); `maps.NewMap` returns an empty map. No panic.
- `growslice` (slice.go:191–252): `newLen < 0` → "growslice: len out
  of range"; after `nextslicecap` + `roundupsize`, `overflow || capmem
  > maxAlloc` → the same message. The threshold is on the GROWN cap.
- `rawruneslice`/`rawstring`: `throw("out of memory")` — fatal, not a
  panic; unreachable without an already-huge value.

## Subject

`probe/main.go` — one probe per invocation (fatal errors kill the
process), selected by `os.Args[1]`; `report` recovers and prints the
`runtime.Error` check, message and dynamic type. `unsafe.Slice` is used
ONLY in the two append probes, to obtain a huge-length slice header
without materializing memory (gc-only subject; the frontend refuses
`unsafe`). Build: `go build -o <scratch>/probe probe/main.go`; run each
under `GOLEAN_MEM_MAX=4G scripts/capped <scratch>/probe <name>` (the
just-under probes attempt a 256 TiB allocation; the cap is the blast
radius).

## Results (go1.26.5 linux/amd64, 2026-09-02, overcommit_memory=0)

| probe | request | gc |
|---|---|---|
| slice-len-over-var | `make([]byte, 1<<48+1)` (var) | PANIC runtime.Error `runtime error: makeslice: len out of range` (runtime.errorString) |
| slice-len-over-const | `make([]byte, 1<<48+1)` (const) | same (compiles; the compiler checks only int representability) |
| slice-len-eq-maxalloc | `make([]byte, 1<<48)` | NO panic: `runtime: out of memory: cannot allocate 281474976710656-byte block` / `fatal error: out of memory` (exit 2) — behavior 1 |
| slice-int64-over | `make([]int64, 1<<45+1)` | PANIC `makeslice: len out of range` |
| slice-int64-eq | `make([]int64, 1<<45)` (= 2^48 bytes) | fatal out of memory — behavior 1 |
| slice-int32-over | `make([]int32, 1<<46+1)` | PANIC `makeslice: len out of range` |
| slice-3byte-over | `make([][3]byte, 1<<48/3+1)` | PANIC `makeslice: len out of range` |
| slice-3byte-eq | `make([][3]byte, 1<<48/3)` (= 2^48-1 bytes) | fatal out of memory — behavior 1 |
| slice-cap-over | `make([]byte, 0, 1<<48+1)` | PANIC `runtime error: makeslice: cap out of range` |
| slice-len-and-cap-over | `make([]byte, 1<<48+2, 1<<48+1)` | PANIC `makeslice: len out of range` (len blamed first) |
| slice-len-gt-cap | `make([]byte, 5, 1)` | PANIC `makeslice: cap out of range` |
| slice-len-neg | `make([]byte, -1)` | PANIC `makeslice: len out of range` |
| slice-cap-neg | `make([]byte, 0, -1)` | PANIC `makeslice: cap out of range` |
| slice-struct0-huge | `make([]struct{}, 1<<62)` | NO PANIC — len = cap = 4611686018427387904 (zero-size element: mem = 0) |
| chan-byte-over | `make(chan byte, 1<<48)` | PANIC runtime.Error `makechan: size out of range` (runtime.plainError — NO `runtime error:` prefix) |
| chan-byte-n 111 | `make(chan byte, 1<<48-111)` | PANIC `makechan: size out of range` |
| chan-byte-n 112 | `make(chan byte, 1<<48-112)` | fatal out of memory (the allocation is attempted) → hchanSize = 112 |
| chan-byte-n 113 | `make(chan byte, 1<<48-113)` | fatal out of memory |
| chan-int64-over | `make(chan int64, 1<<45)` | PANIC `makechan: size out of range` |
| chan-struct0-huge | `make(chan struct{}, 1<<62)` | NO PANIC — cap = 4611686018427387904 |
| chan-neg | `make(chan byte, -1)` | PANIC `makechan: size out of range` |
| map-hint-over | `make(map[int]int, 1<<48+1)`; insert | NO PANIC — len 1 (hint clamped) |
| map-hint-neg | `make(map[int]int, -1)` (var); insert | NO PANIC — len 1 (hint clamped) |
| append-growth-over-unsafe | `unsafe.Slice(&x, 1<<48-1)` ([]byte) then `append(s, 7)` | PANIC runtime.Error `runtime error: growslice: len out of range` |
| append-int64-over-unsafe | `unsafe.Slice(&x, 1<<45-1)` ([]int64) then `append(s, 7)` | PANIC `growslice: len out of range` |
| append-newlen-overflow | `s := make([]struct{}, 1<<62); s = append(s, s...)` twice | PANIC `growslice: len out of range` (newLen overflowed int) |
| recover-error-iface | recover the makeslice panic | `r.(error)` ok = true, `Error()` = `runtime error: makeslice: len out of range`; re-panic keeps the value |
| uncaught | `make([]byte, 1<<48+1)` in main | `panic: runtime error: makeslice: len out of range` + goroutine trace, exit 2 |
| sizes | `unsafe.Sizeof`/`Alignof` | sync.Mutex 8/4, RWMutex 24/4, WaitGroup 16/8, Once 12/4; string 16, slice 24, iface 16, map/chan/func/ptr 8; complex64 8/4, complex128 16/8; struct{int64,byte} 16, struct{byte,int64,byte} 24, struct{int64,struct{}} 16, struct{struct{}} 0, struct{[3]byte,int32} 8, struct{int32,[0]int64} 16 (align 8) |

## Findings

1. Two behaviors, one limit. Requests whose byte size EXCEEDS 2^48
   (channels: 2^48-112) panic deterministically (behavior 2 — modeled
   by this slice); requests AT or under the limit pass the check and
   fail to allocate on this host (behavior 1 — true OOM, an
   unrecoverable `fatal error`, which stays under the register #7
   rider / D-001). The boundary is exact and element-size-scaled.
2. Messages: slices/append are `runtime.errorString` and print with
   the `runtime error: ` prefix; `makechan` is `runtime.plainError`
   and prints bare. Both are `runtime.Error`, both recoverable.
3. Maps never panic on the hint — negative included. The machine's
   pre-slice arm panicked `makemap: size out of range` on a negative
   hint — but red-first showed that arm was DEAD end-to-end: the native
   frontend does not lower the hint, dropping its evaluation (BUG-082,
   open; red-first row `map-hint-eval-order`, gc 31 vs machine 11).
4. Zero-size elements never trip the limit (`mem = 0`); gc realizes
   `make([]struct{}, 1<<62)` and `make(chan struct{}, 1<<62)`. The
   channel form is a feasible corpus control (the machine's buffer is a
   capacity number); the slice form is not (the machine materializes
   backing arrays eagerly — BUG-078 residual (2)).
5. `append` growth past the limit needs an existing >2^47-byte slice
   (or `unsafe.Slice`, refused by the frontend): NOT expressible as a
   corpus row. The machine's check is decided on the new length's byte
   size (the stream-independence theorem `applyStmtOp_appendSlice_congr`
   forbids a cap-based decision); gc's threshold is on the grown cap
   (≈1.25×) — the band between is recorded on R16 as gc-panics/machine-
   allocates, an allocation-failure case of the rider.
6. Layout matters: the threshold divides by gc's element size WITH
   padding (`struct{int64; byte}` is 16 bytes, so `make([]T, 1<<44+1)`
   panics; a 9-byte count would put the threshold at 1<<44·16/9). The
   machine's `tySizeAlignFuel` transcribes go/types `gcSizes`; the
   `sizes` probe pins the sync-primitive and edge-case struct values.

## Red-first (machine side, 2026-09-02)

The new rows run through the PRE-slice golean binary (the primary
checkout's `.lake/build/bin/golean`, built 2026-09-01 05:12 at a tree
whose make/append arms are byte-identical to 0f3c05ff's — the one
later Machine.lean change, fa589f62, touched none of them) versus the
t5-maxalloc binary, on the frontend's wire for the fixture
(`native-json-run --input wire.json --function <subject>`):

| subject | pre-slice binary | t5-maxalloc binary | gc |
|---|---|---|---|
| makeMaxAllocChanSizeOverByte | `ok` (buffer = a capacity number) | panic `makechan: size out of range` | panic |
| makeMaxAllocChanSizeHeaderBoundary | `ok` | panic `makechan: size out of range` | panic |
| makeMaxAllocRecoverChanSize | 0 (nothing to recover) | 1 | 1 |
| makeMaxAllocSliceLenOverByte | KILLED (cgroup 4 GiB, 25 s — materializing 2^48+1 elements) | panic `runtime error: makeslice: len out of range` | panic |
| makeMaxAllocSliceLenOverInt64 | KILLED (same) | panic `makeslice: len out of range` | panic |
| makeMaxAllocMapHintNegative / Over | 1 (NO panic — the hint never reaches the arm) | 1 | 1 |
| makeMaxAllocChanZeroSizeElemHuge | 1 | 1 | 1 |

The map rows' pre-slice result is what exposed BUG-082's real shape:
the machine arm's negative-hint panic could not have fired, because
the frontend never lowers the hint. Raw log: this lane's scratch
`red-first.txt` (gitignored; the table is the record).
