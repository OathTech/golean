# stdlib source-through slice 1 (`stdlib-source-1`) — the landing evidence (2026-09-03)

[AGENT] Worker record for the `stdlib-source-1` lane (design memo
`docs/2026-09-03_stdlib-boundary-design.md` §6, the first implementation
slice). Consuming docs (rule 8): the memo §6 DONE marker,
`docs/discrepancy-backlog.md` D-002, `docs/stdlib-admission-register.md`
(slice log), `docs/language-coverage-ledger.md` FR-14/FR-21,
`docs/coverage-ledger.md` (Standard library semantics row),
`docs/2026-08-11_latitude-inventory.md` §3 (library realization note),
`docs/spec-sources.md` (the library-docs pin), `docs/BUGS.md` BUG-072,
the baseline re-pin header of `baselines/native-full.tsv`, and
`baselines/pins/twin-chdriver.wire.json` / `baselines/stdlib-pin.tsv`.

## Authorization (provenance, rule 7)

[USER] Mike, 2026-09-03, relayed to this worker by the [AGENT]
coordinator — NOT firsthand: «(3) agree, go ahead with the plan» —
ruling the memo's gates G1 (hybrid), G3 (library docs pinned; `godoc:`
anchors), G4 (library latitude as (b)-pins), G8 (admission register +
caps), G9 (first slice = `strings`+`strconv`) AS RECOMMENDED. The twin-
wire pin move below is authorized by G9's ruling (the raft subject's
`quorum`/`raftpb` call FormatUint/FormatInt/Split/TrimSpace, so the wire
must change when their shims are replaced by real source). Every other
decision here is [AGENT]; the two departures from §6 as written (the
retained ParseUint shim; the dropped-initializer rule) are argued in the
memo's DONE marker and the register.

**D-002 countersign ask (carried for the coordinator to pose):** the
re-bodied `strconv.ParseUint` shim is a BODY CHANGE under the D-002
freeze, forced by a fail-closed STOP (retiring it would have flipped the
green error-path rows red). It DELETES two hand-written pieces
(`goleanShimStrconvQuote`, the carrier type `goleanShimStrconvError`)
but ADDS `stdlibShimImports` (`tools/nativefrontend/stdlibshim.go`) — a
new coupling from an injected shim to a LIBRARY type (`&strconv.NumError{…}`
with the library's `ErrSyntax`/`ErrRange`). Validation: the 600k fuzz
below + `stdlib-source/strconv-parseuint/*`. The [USER] is asked to
countersign the coupling; the freeze itself permits a validated body
change.

## Toolchain, tree, host (rules 3–5)

- Oracle: `go version go1.26.5 linux/amd64` = `baselines/go-oracle-pin`;
  `deps/go` at `c19862e5f8` (= go1.26.5), VERSION `go1.26.5`.
- Machine: `.lake/build/bin/golean` built by `scripts/capped lake build
  golean gocore-eval-tests` on this worktree (Lean per `lean-toolchain`).
- Tree (rule 4): branch `stdlib-source-1` off main `345ef090`; every run
  below made on the worktree with the slice's changes UNCOMMITTED (the
  coverage metas say `git_dirty=true`) and committed unchanged as the
  commit that adds this directory (`git log -1 --format=%H -- docs/evidence/2026-09-03_stdlib-source-1/README.md`).
  The BEFORE measurements used the PRIMARY checkout's frontend at main
  `345ef090` (read-only; artifacts redirected via
  `GOLEAN_COVERAGE_ARTIFACTS` into this worktree).
- Host: linux/amd64, shared box with other lanes' builds running; the
  wall-time numbers are ±1 s noisy and are reported as such.

## What landed (the question this directory evidences)

Does the machine, executing the REAL `deps/go/src` bodies of
`strings.{Fields,TrimSpace,Split}` and `strconv.{FormatUint,FormatInt}`
(plus everything they reach: `unicode.IsSpace` and its `White_Space`
table, `unicode/utf8` decoding, `internal/stringslite.Index`,
`internal/bytealg`'s portable twins, `internal/strconv.formatBits`,
`math/bits.TrailingZeros`), agree with `go run` on every row that used
to exercise the hand-written shims, and on the documented edge cases?

Mechanisms (tools/nativefrontend): `stdlibsource.go` (allowed-library
list, oracle-context file selection, the substitution table
`stdlib-substitutions.tsv`, rev check, the library pin check, linkname
scan), `stdlibreach.go` (reachability pruning), `stdlibregister.go`
(the admission tables' dump), `load.go`/`emit.go`/`wire.go`/
`identity.go` (library units as source units: qualified calls, pruned
declaration passes, gc's node fact for init position, per-decl
quarantine of unsafe/body-less/linknamed sites), `stdlibshim.go`
(5 shim sources deleted; ParseUint re-bodied to the real `*NumError`).
Gates: `scripts/check-frontend-pins [stdlib-pin]`,
`scripts/check-spec-anchors` (godoc anchors via `tools/godocanchors`),
`scripts/check-stdlib-register` (new ci step).

## Results

### Differential — the shim suites stay green; the predicted flips flip

`scripts/coverage run --prefix <suite>` BEFORE (main frontend) and AFTER
(this lane), same golean binary: every row of `strings/fields-conformance`
(8), `strings/split-conformance` (8), `strings/trimspace-repeat` (10),
`strconv/format-parse` (8), `strings/shim-value-refused` (2),
`noodler/strings` (18), `noodler/strconv-formatint` (2),
`examples/wordfreq` (15) PASSes AFTER except the standing red-by-design
`repeat-bound-refused` (unchanged). FAIL→PASS flips (all free; listed in
the baseline re-pin header): `strings/split-conformance/empty-sep`
(predicted — the real `explode` runs), `strings/shim-value-refused/shimmed-value`
(predicted — `f := strings.Fields` is a real function value),
`strings/shim-value-refused/unmodeled-value` (UNPREDICTED — `strings.Contains`
lowers), `strconv/format-parse/unmodeled-member` (the memo's "ParseUint-
delta row" — flipped because `strconv.Atoi` lowers, not because of the
error type). PASS→non-PASS: none. Observation equality old-vs-new wire on
the same binary: `interpreter-cost.tsv` column `obs_equal` = yes for all
8 probed subjects.

New rows (`Corpus/coverage/exec/stdlib-source/`): `strings-fields` 9/9,
`strings-trimspace` 10/10, `strings-split` 11/11, `strconv-format` 8/8,
`strconv-parseuint` 6/6 PASS; `frontier` 0/2 (born red by design — see
FR-21); `fields-fuzz` 10/10 (below).

### The library-vs-oracle fuzz (memo §6) — 500 inputs, 0 mismatches

`tools/stdlibfuzz/fieldsgen` (seed 20260903, n 500, group 50) generates
`stdlib-source/fields-fuzz`: random strings over ASCII letters/digits,
every ASCII white-space byte, every non-ASCII White_Space rune at the
pin, the near-miss non-spaces (U+200B, U+2060, U+FEFF, U+0084, U+0086,
U+200C, U+200D) and multibyte letters; lengths 0..12; valid UTF-8 by
construction. The machine ran the LOWERED upstream `strings.Fields` on
all 500; `go run` ran the real one; all 10 subjects (50 inputs each)
PASS — the first fuzz that targets the machine's execution of library
text rather than a Go-vs-Go mock check.

### The retained ParseUint shim, Fields-standard validated

`parseuint-fuzz/gen.sh` extracts the shim SOURCE verbatim from
`stdlibshim.go` and runs it side by side with `strconv.ParseUint` under
the pinned toolchain — value, err-nil, `Error()` text, `*NumError`
fields, `errors.Is` against both sentinels — over random inputs (an
alphabet with digits, letters, `_-+ .xX"\`, a tab, invalid UTF-8 and a
multibyte rune, plus the extremes), bases 2..36 (5% base 0), bitSize
{0,8,16,32,64,3,7,63,65}. `transcript.txt`: seed 20260903 — 100,000
trials, 0 mismatches (3,464 ok-path, 81,157 error-path, 15,379 refused
at the recorded bounds base 0 / bitSize 65); seed 7 — 100,000 trials, 0
mismatches; and the Fields-standard run (memo §2.2.3 → g2.md's 600k
pattern): seed 20260903 — **600,000 trials, 0 mismatches** (20,654
ok-path, 486,325 error-path, 93,021 refused at the recorded bounds).
The standard is the [USER]'s to relax; it is met, not restated. Corpus rows `stdlib-source/strconv-parseuint/*` pin the type
assertion `err.(*strconv.NumError)` (true, as gc), the sentinel identity
through `Unwrap`, and the rendered texts incl. non-ASCII quoting.

### Interpreter cost (memo §6: a >2× slowdown is a finding, not a blocker)

`interpreter-cost.tsv` — golean `native-json-run` per subject, avg of 3,
old wire (main frontend) vs new wire, same binary; `suite-wall-times.tsv`
— whole-suite `scripts/coverage run` wall time BEFORE/AFTER (dominated by
fixed per-suite costs: go build of the oracle harness, frontend `go run`).

| subject | old wire | new wire | old ms | new ms |
|---|---|---|---|---|
| fields-conformance fcUnicodeSpace | 65 KB | 158 KB | 24 | 26 |
| split-conformance splitMultiByteSep | 77 KB | 406 KB | 23 | 28 |
| trimspace-repeat trimSpaceUnicode | 70 KB | 275 KB | 23 | 26 |
| format-parse formatUintBases | 190 KB | 1,081 KB | 24 | **360** |
| format-parse parseUintErrors | 190 KB | 1,081 KB | 38 | **376** |

FINDING (recorded, not re-budgeted): a program that reaches
`strconv.Quote` — every program whose `*strconv.NumError` is on the wire
(the retained ParseUint shim constructs it; `Atoi`'s error path too) —
pays ~340 ms of `$pkginit` for `strconv.isPrint16/isPrint32/isNotPrint16/
isNotPrint32/isGraphic` (~1,400 table elements as composite literals) on
EVERY subject run: 24 → 360 ms (15×) on `strconv/format-parse`, far
inside the 30 s row budget. The strings rows cost +2–5 ms. Suite wall
times moved within noise except `strconv/format-parse` 13.8 → 15.4 s.
The twin wire grew 9.32 MB → 10.20 MB for the same reason.

### The twin-wire pin move ([USER]-authorized by G9, relayed)

`baselines/pins/twin-chdriver.wire.json`:
`eef32142627a37ce04632c6ae8ab4d953a6ea620394acfe657d3d73ca9a0ac70` →
`b341dc3b74ff6d6452feb5c4a8b1de6de978ef9819026ff031318a83a1fed3ef`.
`twin-structural-diff.txt` (producer `twin-structural-diff.py`) shows the
delta after two semantically inert normalizations — WHAT IT CHECKS, stated
exactly: funcs/methods compared as canonicalized JSON per declaration
(gid shift + temporary renaming), types/globals/methodSets compared BY
NAME only (not content), `fileOrder` compared per package list (not per
file), `$pkginit` reported as changed without a statement-level diff — the 15 new library
globals initialize first, so every user `gid` shifts by +15; the
frontend's program-wide temporary counters (`$cN`, `$swiN`, …) renumber
— is EXACTLY: funcs removed = the 5 retired shim bodies (+ their lifted
literals and the deleted `goleanShimStrconvQuote`); funcs added = the 51
reached library functions (`twin-structural-diff.txt`); funcs changed = `$pkginit` (library inits),
`raftpb.ConfChangesFromString` (real Split/TrimSpace calls),
`raftpb.goleanShimStrconvParseUint` (real `*NumError`); methods changed =
`quorum.Index.String`, `quorum.VoteResult.String` (real FormatUint/
FormatInt calls); types/methodSets: `raftpb.goleanShimStrconvError` out,
`strconv.NumError`, `errors.errorString`, `unicode.{RangeTable,Range16,Range32}`,
`unicode/utf8.acceptRange` in; `fileOrder` gains the 9 library units
ahead of the subject packages. The deviation pin (`hidden-dep-order`)
did NOT move (`check-frontend-pins: ok [hidden-dep-order]`).

### The library pin (new, `baselines/stdlib-pin.tsv`)

48 rows (sha256 per lowered GOROOT file, 9 packages), file sha256
`05949f593242f08010bf1413abba8b19211034b4a047cfa655b3acaddae07135`.
Red-first: `TestStdlibPinMismatchRefusesByPath` mutates one hash byte
and a missing row — both refuse naming the path; `check-frontend-pins
[stdlib-pin]` regenerates and byte-compares. Also red-first at landing:
`scripts/check-stdlib-register` failed on a one-character mutation of the
register's `count overlay` line (diff shown, exit 1), then passed
restored; `tools/godocanchors` reported a `godoc:<strings>.<Nope>@go1.26.5` probe (a non-existent declaration)
and a wrong rev as UNRESOLVED (exit 1).

### The gotest standing lane (trigger: a frontend fragment widening)

`gotest-delta.txt` (+ `gotest-results.meta.tsv`): full 1,013-case run at
this lane vs the t4-gotest record at `670d3351`. Categories 331 MATCH /
641 FRONTEND-REFUSED / 15 MACHINE-REFUSED / 4 MISMATCH / 22 INFRA →
**344 / 637 / 11 / 0 / 21**. Of the 12 files whose old refusal named
`strings.`/`strconv.`/`utf8.`, 3 are now MATCH (`fixedbugs/issue77613.go`
strings.HasSuffix, `typeparam/stringable.go` strconv.Itoa in a String
method, `utf.go` utf8.DecodeRuneInString) and 9 moved to the NEXT
refusal cause (`fmt.*`, `println`, `io.ReadFull`, `reflect.DeepEqual`) —
the strings/strconv cause is retired everywhere. Honesty note: the base
commits differ (670d3351 vs 345ef090); the 4 MISMATCH→MATCH and the one
LOST MATCH (`fixedbugs/issue4353.go`, now refused by the BUG-078
materialization budget on a 100,000-element array; it imports no
`strings`/`strconv`) are other lanes' landings, not this slice's.

## Reproduction (rule 2; from the repo root, deps/go at the pin, golean built)

```
scripts/coverage run --prefix stdlib-source                       # the new suites
scripts/coverage run --prefix strings/fields-conformance          # (and the other 7 suites)
GO111MODULE=off go run ./tools/stdlibfuzz/fieldsgen -n 500 -seed 20260903 -group 50 -out Corpus/coverage/exec/stdlib-source/fields-fuzz
docs/evidence/2026-09-03_stdlib-source-1/parseuint-fuzz/gen.sh 100000 20260903
docs/evidence/2026-09-03_stdlib-source-1/parseuint-fuzz/gen.sh 100000 7
docs/evidence/2026-09-03_stdlib-source-1/parseuint-fuzz/gen.sh 600000 20260903   # the Fields-standard 600k run
GO111MODULE=off go run ./tools/nativefrontend --stdlib-pin-manifest | diff - baselines/stdlib-pin.tsv
GO111MODULE=off go run ./tools/nativefrontend --stdlib-register        # the register's machine block
scripts/check-frontend-pins ; scripts/check-stdlib-register ; scripts/check-spec-anchors
python3 docs/evidence/2026-09-03_stdlib-source-1/twin-structural-diff.py <(git show 345ef090:baselines/pins/twin-chdriver.wire.json) baselines/pins/twin-chdriver.wire.json
scripts/gotest-triage run --jobs 8 ; scripts/gotest-triage report
# gotest-delta.txt = the awk joins of this README's 'gotest standing lane' section over
#   <t4-gotest worktree>/artifacts/gotest/results.tsv (OLD, @670d3351) and artifacts/gotest/results.tsv (NEW):
#   category counts, the strings./strconv./utf8./unicode. refusal join, the MATCH-set delta; paths written <repo>-relative
# interpreter cost: emit each case with the main-@345ef090 frontend and this one, then
.lake/build/bin/golean native-json-run --input <wire> --function <subject>   # timed, avg of 3
scripts/capped scripts/ci --diff                                   # the gate (result below)
```

## Gate result (rule 6)

See the final section, appended after the gate run.

## Gate result (rule 6) — appended after the runs

- `scripts/capped scripts/ci --diff` on the slice tree (before the
  baseline re-pin): every step ok except the expected `differential
  baseline diff (DRIFT)` — exactly the 6 FAIL→PASS flips and the 56 new
  `stdlib-source/` rows listed in the re-pin header; 3251 rows run, 3061
  PASS / 190 FAIL; `gate-tail.txt` is that run's tail. Re-pin guard: 0
  PASS→non-PASS.
- `baselines/native-full.tsv` re-pinned from that run with the written
  reason (its header), `# cases: 3251 (3061 PASS / 190 FAIL)` re-derived
  from the rows; `scripts/coverage-baseline-diff --full`: no regression.
- `scripts/capped scripts/ci` on the re-pinned tree (judging the
  recorded full run): **RESULT: PASS** — check-frontend-pins ok on all
  three pins (deviation unmoved, twin re-pinned, stdlib-pin 48 files),
  check-spec-anchors ok (705 spec# + 235 mem# + 6 godoc:), check-bugs ok
  (87 bugs, 0 wrong-answer backlog), check-stdlib-register ok,
  frontend `go test` ok (incl. the 8 new stdlib-source tests), reconciler
  3 findings / **0 HIGH** (the three MEDIUMs — C13 historical version
  sites, C5 FR-7's `=` citation, C9 wire-schema commits since the
  certified set — predate this lane). `gate-final-summary.txt` is that
  run's step summary. The ONE tool change outside the slice:
  `tools/reconcile-records`' frontier-row regex accepts `FR-1…FR-N`
  (the table gained FR-21), and the reconciler's C1H/C4 checks were
  satisfied by re-deriving the baseline header and ledger §8 from the
  rows.
- Conclusion (one paragraph): the machine executing the pinned GOROOT
  bodies of `strings.{Fields,TrimSpace,Split}` and `strconv.{FormatUint,
  FormatInt}` agrees with `go run` on every prior shim row, on 44 new
  documented-edge rows and on 500 fuzzed Fields inputs; six shim-surface
  refusals are moot and flipped green; two library sites the slice
  cannot lower refuse by name (FR-21) with the overlay as the recorded
  remedy; the twin wire's delta is exactly the shim→source replacement
  plus the library units; interpreter cost is +2–5 ms on the strings rows
  and +340 ms per subject wherever `strconv.Quote`'s tables reach the
  wire (a recorded finding, inside budget).
