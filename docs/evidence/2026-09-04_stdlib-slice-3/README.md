# Stdlib slice 3 evidence — print/println output observable + float-bits primitive (2026-09-04)

[AGENT] lane `stdlib-slice-3`; consuming doc `docs/2026-09-04_stdlib-slice-3-design.md`
(§2.3, §5, §6, §8), register `docs/stdlib-admission-register.md` (slice log
2026-09-04), latitude rows R7/R17/R18, BUGS.md BUG-093..096. Rules of
`docs/evidence/README.md` followed; every path repo-relative.

## Toolchain / host / commit

- `go version go1.26.5 linux/amd64` — the pin (`baselines/go-oracle-pin`);
  `deps/go` @ c19862e5f8 (the pinned checkout, unmodified).
- Lean: `leanprover/lean4:v4.32.2` (the repo toolchain), binary
  `.lake/build/bin/golean` built from the branch tree by `scripts/capped lake build`.
- Host: linux/amd64, shared build box (other lanes' gates running
  concurrently — the gotest wall-clock timeouts in `gotest-results.tsv`
  are load-sensitive and NOT verdicts).
- Tree: branch `stdlib-slice-3` off main ac45aedd (rebased onto main fc9bbef1
  at merge train round 14, 2026-09-05 [AGENT]; the records here are unchanged
  by the rebase — the tracked figure became 3479 = 3230 / 249 from the lane's
  own 3447 = 3210 / 237, see the baseline header); the slice's records
  were produced from the dirty working tree that became commit 450fca72
  (slice) / a4865e66 (slice tip); the audit-fix-round records
  (`rows-run-audit-fix-round.log`, `harness-split-tests.txt`, `c1-probe/`)
  from the tree that became the round's commit (SHA in the coordinator
  report). `gotest-results.tsv` is re-derivable at any later commit by the
  commands below (absolute worktree paths in the recorded outputs are
  elided as `<worktree>`).

## Artifacts and reproduction (from the repo root)

- `print-go-pin.txt` — the `deps/go/src/runtime/print.go` lines the machine's
  `renderPrint` transcribes (printlock/printunlock :60-87, printsp/printnl/
  printbool :112-126, printfloat64/32 + complex :128-158 (REFUSED this
  slice), printuint/printint :154-177, printstring/printslice/printeface/
  printiface :256-272 (address kinds, REFUSED)):
  `grep -n "" deps/go/src/runtime/print.go | sed -n '60,90p;112,178p;249,272p'`.
- `print-gc-oracle.txt` — gc's stdout (harness JSON) and stderr (program
  output, then any abort report) for every `builtins/print/*` row, from
  `artifacts/coverage/go-run/builtins__print__*/oracle.{stdout,stderr}` after
  `scripts/coverage run --prefix builtins/print`. The stderr bytes are the
  probe table for the R17 pin (60+ printed operands: every integer kind and
  the int64/uint64 extremes, bools, strings with embedded separators/newlines/
  multi-byte UTF-8, defined types, the panic/fatal prefix shapes).
- `float-bits-gc-oracle.txt` — gc's harness JSON for every `builtins/float-bits/*`
  row (the machine matched each green one; the three BUG-094 rows are the
  refused ones): `scripts/coverage run --prefix builtins/float-bits`. 27
  probes: the ten payload patterns of `roundtrip-payloads` (incl.
  0x7FF8000000000001, sNaN 0x7FF0000000000001, −qNaN 0xFFF8000000000000, ±0,
  ±Inf, subnormal min, finite max), NaN semantics + negation, literals
  (1.0, −2.5, 0.1, 1e300, runtime −0, folded −0.0, overflow +Inf), frombits
  arithmetic, the float32 pair (1.5f, quiet/signalling 32-bit payloads, −0f,
  0.1f, overflow), widening/narrowing.
- `rows-run.log` — `scripts/coverage run --prefix builtins/print --prefix
  builtins/float-bits`: 20 PASS, 14 FAIL by design (worktree path elided).
- `rows-run-audit-fix-round.log` — the A1/A2/D probe re-run: `scripts/coverage
  run --prefix builtins/float-bits --prefix builtins/print/refused --prefix
  spec-examples-stmt/min-max`: `min-max-payload{,/float32}` GREEN (gc's OR
  idiom bit-exact, both widths), `neg-canonical-refused{,/float32}`,
  `min-max-canonical-refused` and `roundtrip-payloads` REFUSED by the
  sign-insensitive guard (the last is the ruled PASS→FAIL flip), the
  spec-example min/max pins unchanged, `refused/unsafe-pointer` red,
  `refused/race-with-output` red at go-observation naming the split's cause.
- `c1-probe/` — the statement-granularity scheduling probe (README inside).
- `gotest-results.tsv` — `scripts/gotest-triage run --jobs 8 --only <each of
  the 195 files the 2026-09-01 triage recorded as print-refused>`; the id
  list is the `FRONTEND-REFUSED … builtin (print|println) in statement
  position` rows of that lane's `artifacts/gotest/results.tsv`. Tally:
  MATCH 120 / FRONTEND-REFUSED 62 / MACHINE-REFUSED 10 / MISMATCH 2 / INFRA 1
  (design note §6 diagnoses each MISMATCH/INFRA).
- `harness-split-tests.txt` — `go test -v -run TestSplit ./tools/coverageharness`
  (GO111MODULE=off): the fd-2 split's red-first tests, extended at the audit
  fix round A2 with the four understated shapes (`panic: fakepanic: real`,
  a printed `panic: fake` line, a printed `panic: hello` line beside a
  deadlock block, `fatal error: mine` glued to a deadlock block — all refuse
  by name now) beside the accepted ones (ok, panic, newline payload, repanic
  chain, fatal/deadlock incl. the unwinding shape, race, UTF-8, the literal).
- `register-render.tsv` — `GO111MODULE=off go run ./tools/nativefrontend
  --stdlib-register`: the machine block pasted into the register (primitive 2 / cap 2).

## Conclusion

gc's `print`/`println` bytes for bool/integer/string operands are
reproduced byte-exactly by the machine's `renderPrint` on every strict row
and on 120 real `$GOROOT/test` programs; the float-bits primitive
round-trips every probed payload bit-exactly and refuses only the
machine's canonical NaN (R7). The harness's stderr split recovers the
program prefix on every ok/panic/fatal/deadlock row here and refuses the
ambiguous shapes by name.
