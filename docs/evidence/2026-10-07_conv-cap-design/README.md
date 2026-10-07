# Evidence — `[]byte(s)` / `[]rune(s)` capacity envelope at go1.26.5 (b6 design, 2026-10-07)

[AGENT] design worker, lane `design/b6-conv-cap-1007`. Record for `docs/2026-10-07_conv-cap-design.md`.
Oracle: `/usr/local/go/bin/go` = `go version go1.26.5 linux/amd64` (`baselines/go-oracle-pin`); gc source at
`deps/go` (tag go1.26.5). Bulk scratch lived in `.tmp/b6/` and was pruned; everything here regenerates from
the sources below.

| File | What |
|---|---|
| `gen-probe.py` | emits `probe_conv.go` (938 lines, not kept): per length × operand class × regime, one function printing `kind shape n cap(result)`. Lengths 0…100000 incl. every tmpBuf/size-class/page boundary of interest; literals up to 65537 (`MaxImplicitStackVarSize` = 64 KiB) |
| `summarize.py` | groups the probe output into member sets per (kind, operand class, n), checks them against the model and the spec floor, writes `envelope.tsv` |
| `envelope.tsv` | THE MEASURED ENVELOPE: 140 rows, `measured_members == model_members` on every row, every member ≥ len; `zero_copy_only` = members that vanish under `-gcflags=-d=zerocopy=0`; `per_regime` = the cap each regime realized |
| `roundup.go` / `roundup.txt` | a user-space transcription of `runtime.roundupsize` (noscan) over the pinned `internal/runtime/gc/sizeclasses.go` tables; `R n R(n) R(4n)/4` per probed n — the model's size-class member |
| `probe_inline.go` | the same source line (`conv(s)`, inlinable) realizing cap 5 / 32 (default build) and 8 / 8 (`-gcflags=-l`) |
| `probe_literal.go` | literal vs constant vs folded-concatenation vs variable operands, bytes and runes |
| `probe-outputs.txt` | the outputs of the two probes above, gc's `-m` lines (`zero-copy string->[]byte conversion`, `escapes to heap`, `does not escape`), and the wire operand the native frontend emits for each conversion in `probe_literal.go` |

Commands (from the repo root, GO111MODULE=off, GOCACHE under `.tmp/`): `python3 gen-probe.py probe_conv.go`;
`go run ./probe_conv.go 2> conv.default.txt` (`println` writes to fd 2); the same with `-gcflags=-l` (byte-identical
to the default run: the probe's regimes do not depend on the probe's own inlining) and with `-gcflags=-d=zerocopy=0`
(62 lines move: every non-literal `nomut` row); `go run ./roundup.go 2> roundup.txt`; `python3 summarize.py`.
The wire dump used `go run ./tools/nativefrontend --dir <dir> --out <wire.json>` at this branch's tip.

Regime legend (operand class / regime): `lit` = a string literal (or folded constant) operand; `var` = a runtime
string (`strings.Repeat` behind `//go:noinline`); `concat` = `var + "a"` (gc's `walkAddString` path); `ascii` =
a runtime ASCII string for runes (rune count = byte count); `nomut` = the result is only read (cap/len);
`mut` = one element written; `esc` = the result stored to a package variable.
