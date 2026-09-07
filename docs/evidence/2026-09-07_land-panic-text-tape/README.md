# gc witnesses, gc draws, enumeration stats, choice-trace comparison and gate tail — landing chunk L3 `land/panic-text-tape` (2026-09-07)

Consuming doc: `docs/2026-09-07_land-panic-text-tape.md` (§1 the gc reading,
§3–§4 the rows and the measurement). [AGENT] landing worker, lane
`land-panic-text`; every decision this dir records is the note's.

Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`),
`GODEBUG=panicnil=0` as `scripts/diff-coverage`'s oracle sets it,
`GOTRACEBACK=none` for the witness programs (the differential harness's
own setting is unchanged by this chunk); Lean per `lean-toolchain`, the
`golean` binary built by `scripts/capped lake build golean` at the landing
tip. Host: linux/amd64, 32 cores, 125 GiB; a sibling landing lane (L4) ran
concurrently — timing numbers here are not load-controlled and none is
load-bearing.

## Files (records only — no full-corpus tables, no archives, no source copies)

- `witness/w*.go` — the 38 gc witness programs of the note's §1 (w01–w37
  plus w06b; one `package main` each; run with `go build -o bin ./wNN &&
  ./bin`). [Count corrected at the audit fix round, L7: the note said 37.]
- `witness/table.tsv` — byte-exact first abort line per witness (escaped
  `\xHH` for non-printables), its hex, a sha256 prefix of the whole stderr,
  the stderr line count. Produced by the L3 worker's table script over the
  captured `stderr` files.
- `witness/table-Nl.tsv` — the layout-dependent witnesses re-run with
  `-gcflags='all=-N -l'` (`od -c` of the first line): the collapse of two
  literal constants does not depend on optimization.
- `gc-draws.tsv` — the 19 membership rows' gc draws at K=32 (plain/`-race`
  alternating) and the machine's two enumerated members per row, from
  `artifacts/coverage/membership/<id>/{samples,draws,observations}.txt`
  after `scripts/diff-one <ids>` at the landing tip.
- `enumeration-stats.txt` — the enumerator's per-row line for the 19
  membership rows (`observations=2 … sites=1 … width=2` on every row).
- `choice-trace-compare.txt` — the whole-corpus consumption-trace
  comparison, main's binary (`90bc3e06`) vs the landing binary, same corpus,
  same six streams (`scripts/choice-trace-corpus --dump`): per (row, stream)
  status/consumption/observation-hash differences, expected ONLY on the rows
  this chunk re-laned or added.
- `ci-diff-tail.txt` — the verbatim tail of `scripts/capped scripts/ci --diff`
  at the clean committed tip (the gate record), with the awk tally of the
  re-pinned baseline.
- `first-line-scope.txt` — the adversarial-audit fix round's MEASUREMENT
  (2026-09-07, R4e): `panic("head\nTAILA")` vs `panic("head\nTAILB")` —
  gc's full stderr differs, the harness's compared first line is identical
  (`head`), and the machine's `stringFirstLine?` agrees on both; the
  payload's tail is unmodelled and unobserved (unwinding-arc rule of
  2026-09-07; ledger FR-32).
- `controls-asymmetry.txt` — the fix round's R5 record: the retired
  string-member lane's `Controls` payload (`a\x00\x01\t\r\nZ`) — gc writes
  five first-line bytes, bash command substitution in the harness keeps
  four (the NUL is dropped), the machine renders all five; a red-by-accident
  if rowed strictly today, so DEFERRED to L4's byte view (ledger FR-33).
  Also carries the L4 (`.nil` arm fails closed) probe lines.
- `ci-diff-tail-fixround.txt` — the verbatim gate tail of `scripts/capped
  scripts/ci --diff` at the fix round's clean committed tip (zero drift
  expected: records, statement tightenings and one dead-arm fix only).
- `round24-rebase-slice.txt` — the merge-train round-24 rebase onto main
  dd636996 (L4 landed first): the focused 65-row slice's drift list vs the
  composed rows, the nine re-pinned rows' detail columns, and gc's first
  abort line (od -c) for the six L4 rows that flipped green under L3's
  renderer — lane note §7.2.

## Reproduction (repo root; `deps/` via `scripts/setup-deps`)

```sh
# gc witnesses (each program) — scratch stays repo-local (.tmp/ or artifacts/, never /tmp:
# docs/operational-lessons.md "Sandbox conventions"; corrected at the audit fix round, R8):
mkdir -p .tmp/witness && GOCACHE="$PWD/artifacts/go-build-cache" GOFLAGS= GODEBUG=panicnil=0 GOTRACEBACK=none \
  go build -o .tmp/witness/w ./docs/evidence/2026-09-07_land-panic-text-tape/witness/w01_panic_r.go ; .tmp/witness/w
# (the table's escaping: od -An -c on the first stderr line; sha256sum on the whole stderr)
# the rows:
scripts/diff-one panic-recover/repanic-same-value-abort $(awk -F'\t' '!/^#/{print "panic-recover/repanic-collapse/"$1}' Corpus/coverage/exec/panic-recover/repanic-collapse/cases.tsv) \
  $(awk -F'\t' '!/^#/{print "panic-recover/panic-text/"$1}' Corpus/coverage/exec/panic-recover/panic-text/cases.tsv)
# the choice-trace comparison (main's binary from a detached worktree at 90bc3e06):
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-before --golean <golean@90bc3e06> \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
scripts/choice-trace-corpus --dump --jobs 6 --out artifacts/choice-trace-after --golean .lake/build/bin/golean \
  --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused
# the gate:
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=4 GOLEAN_COVERAGE_JOBS=12 scripts/capped scripts/ci --diff
```

## Conclusion (one paragraph; the note's §1 and §4 carry the argument)

gc's `[recovered, repanicked]` marker is decided by eface identity
(`runtime/panic.go:715` at the pin) — a property of the interface BOX the
machine's value-level state does not carry: the same value-level chain is
rendered collapsed (`panic(r)`, two dedup'd literals, bools, two nil
faults) and two-line (a re-boxed value, a runtime-computed string, a package
var, two index faults) by gc at the pin, and two-line by every go ≤ 1.24.
Reified as `ChoiceSite.repanicCollapse`, both members are gc-certified on
the string, int, defined-int and `runtime.Error` families (`gc-draws.tsv`:
member 0 on 12 rows, member 1 on 7). gc writes string payloads' raw bytes,
a TAB after each LF and the suffix after the WHOLE payload, so the first
line of a multi-line payload has no suffix; invalid UTF-8 is written raw
and never escaped — the machine's escape-free strict decoder renders every
valid first line byte-exactly and REFUSES by name where the first line is
not valid UTF-8 (three red rows on BUG-004).
