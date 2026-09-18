# gc/amd64 NaN bit-pattern probe — evidence for `docs/2026-09-18_nan-latitude-memo.md` (2026-09-18)

[AGENT] records lane `records/nan-envelope-memo-0918`, tree at main `68b261e6` (clean; the
probe reads no repo state — a pure-gc oracle record). Host: linux/amd64, no concurrent load
relevant (bit patterns, not timing).

Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`), default
`GOAMD64=v1`, `GO111MODULE=off`, `GOCACHE` under the worktree's `.tmp/`.

## Files

- `main.go` — the probe. Every operand is a variable (a constant NaN is a compile error,
  spec#Constant_expressions); each arithmetic case is ALSO routed through a `//go:noinline`
  two-argument helper so that the SSA operand order at the call boundary is the source order.
- `out-opt.txt` — default optimization (what `go run` in the differential does).
- `out-Nl.txt` — `-gcflags=all='-N -l'` (optimizer and inliner off).

## Reproduction (from the repo root)

```sh
export GO111MODULE=off GOCACHE="$PWD/.tmp/gocache"
go run docs/evidence/2026-09-18_nan-latitude-memo/main.go                       > out-opt.txt
go run -gcflags=all='-N -l' docs/evidence/2026-09-18_nan-latitude-memo/main.go  > out-Nl.txt
diff out-opt.txt out-Nl.txt   # exactly one data line differs: `p+q  inline`
```

## The one finding that is not in the memo's table

`p+q inline` (both operands NaN, payloads 1 and 2) reports payload 2 under default optimization
and payload 1 under `-N -l`: SSE `ADDSD` returns the FIRST source operand's NaN, and gc is free
to commute `+`, so which payload survives a two-NaN operation is decided by register allocation,
not by the program. The noinline helpers (`add(p,q)` = …01, `add(q,p)` = …02) show the
first-operand rule at a fixed operand order.
