# Adversarial audit — branch `fix/review-boundary-0911` (BUG-108/109/110), candidate tip `ef9eb4d9`

**VERDICT: FIX-FIRST (records-only fixes; no code change is required to merge).**
No wrong answer found; no fail-open with an observable effect found. Two tracked
records make claims that do not hold as written (a decode-time SPEED-UP that
measures as a slow-down; an "oracle default" that the runner does not pin), and
one BUG-110 claim is stronger than the code ("validated" = arity only). Correct
those three texts, then merge; the code fixes themselves stand.

[AGENT] auditor, 2026-09-15. Ordered by [USER] Mike 2026-09-15, verbatim, relayed
by the [AGENT] coordinator — cite as relayed: «Go ahead and launch the autit».
Worktree `.claude/worktrees/audit-review-boundary`, branch
`review/review-boundary-0911` at `ef9eb4d9` (five commits over main `a461ed8b`).
Toolchains: `go1.26.5 linux/amd64` (= oracle pin), Lean `v4.32.2`; post-fix
`golean` sha256 `44c8ed60…` (a plain copy of the candidate worktree's build dir,
re-verified by `scripts/capped lake build` under the box-wide lock, EXIT=0, 202
jobs, binary unchanged); pre-fix `golean` = the primary's certified binary at main,
sha256 `18beb979…`; candidate frontend built from `ef9eb4d9`. Every command judged
by captured exit code. Evidence (probe logs, matrices, timing):
`docs/evidence/2026-09-15_review-boundary-audit/`. Nothing here was merged,
pushed, or written to `main` / `fix/review-boundary-0911`.

## Findings

### F1 — FAIL-OPEN (low; no observable shown): `resultTypes` entry TYPES are trusted, not validated; only the arity is checked

- What I did: lowered a fixture with `_ = one()`, `_, _ = two()`, `a, _ := two()`,
  expression-statement calls and `b, _ = two()` (`i-fixture-main.go.txt`), mutated
  the `resultTypes` vectors byte-wise, drove each through the post-fix CLI
  (`i-resulttypes-matrix.txt`).
- What happened: `_ = one()` with `resultTypes:[string]` (i08), `b, _ = two()` with
  `[string,string]` (i10) and `_, _ = two()` with `[string,string]` (i13) all RAN
  and answered 42, exit 0 — an int is written into a `string`-typed discard temp and
  the machine does not object. Arity mutations refuse by name (i01/i02/i03/i09:
  `resultTypes arity N does not match the M target(s)`), a non-array (i11) and a
  non-type entry (i12) refuse, a vector on a non-call node refuses (`unknown key`,
  i07). Expression-statement vectors (i04/i05/i06) have no target count to check
  against and are caught only at RUN time by the machine (`extra GoCore assignment
  value` → status `stuck`; `storeK value/target arity mismatch` → status `error`) —
  fail-closed, but not a by-name refusal at the boundary.
- Why it matters: BUG-110 is precisely "unvalidated semantic metadata on the trusted
  boundary"; the record says «the vector is validated, never reconstructed»
  (`docs/BUGS.md` BUG-110 FIXED paragraph; `GoLean/NativeToIR.lean:740-754`
  «checked against the arity the consumer expects»). The types are accepted
  unchecked although the decoder holds the callee's declared results (`funcs`/
  `methods` tables) for `call` nodes and the callee expression's `type` for
  `call-value`. The observable is unaffected today (a discard temp is never read).
- Where: `GoLean/NativeToIR.lean:748-754` (`decodeResultTypes`), `:983-989`
  (expression-statement `discardTemps`), `:1521-1531`, `:1597-1609`.
- Proposed disposition: fix round — either (a) cross-check each entry against the
  callee signature (post-decode pass; refuses by name; makes i04–i06 boundary
  refusals too), or at minimum (b) narrow the BUG-110 record to «arity-validated;
  entry types trusted» and row the cross-check as owed. [AGENT] recommends (b) now
  + (a) owed. Side observation for the state-cleanup arc (out of lane): the machine
  stores an int into a `string`-typed cell without complaint.

### F2 — RECORDS-CLAIM: the twin decode-time «2.3× FASTER» does not reproduce; on the committed binary the twin decodes 1.6× SLOWER

- What I did: interleaved A/B, 9 runs each after a warm-up, `native-json-run
  --function nonexistent_fn` (read + parse + decode + lookup; both binaries reach
  `GoCore function not found`), pre-fix binary on the wire WITHOUT `buildContext`
  (the old twin pin `13d8b659…` byte-for-byte), post-fix binary on the emitted wire
  (`n-decode-timing.txt`). Three separate passes.
- What happened: twin 11.4 MB — PRE median 0.132 s, POST 0.214 s (+62%; passes 2/3:
  0.129→0.210, 0.123→0.212). Largest corpus wire 3.5 MB — 0.049 → 0.081 s (+65%).
  Fixture 1.5 KB — 0.020 → 0.020 s.
- Why it matters: «Honest measurement … numbers derivation-anchored» (charter).
  The record states twin «0.124 s → 0.055 s (FASTER … a hypothesis, not
  isolated)» in three tracked places: `docs/BUGS.md` BUG-110 FIXED paragraph,
  `docs/evidence/2026-09-11_review-boundary/README.md` (S3 "Timing verdict" +
  `s3-decode-timing.txt`), `HANDOFF.md` owed item 6. The largest-wire direction
  and magnitude DO reproduce (+65% vs recorded +44%). The recorded timing binary
  (`dae23a5c…`) is not the committed one (`44c8ed60…`, = the certified record's
  receipt); the audit did not rebuild it.
- Where: the three texts above; `GoLean/StrictJsonParse.lean` (the strict parser's
  cost is real and expected).
- Proposed disposition: fix round (records only) — replace the speed-up sentence
  and the `readFile` hypothesis with the measured slow-down; keep the (correct)
  «far inside the 30 s per-case budget» conclusion. Performance itself: no action.

### F3 — RECORDS-CLAIM + SCOPE (consistency): «cgo ENABLED, as the oracle's `CGO_ENABLED=1` default» is an unpinned host assumption, and the frontend already carries a SECOND build context that pins cgo the other way

- What I did: `grep CGO_ENABLED scripts/diff-coverage` (0 mentions; `go_run_oracle`
  at `scripts/diff-coverage:1315` scrubs GOFLAGS and pins GO111MODULE/GODEBUG/
  GOTRACEBACK only); ran the oracle side under `CGO_ENABLED=0` on the cgo probes;
  compared `go list -f '{{.GoFiles}}'` for every `stdlibSourceAllowed` package
  under `CGO_ENABLED=1` vs `0`.
- What happened: with `CGO_ENABLED=0` the oracle SELECTS DIFFERENTLY — f47
  (`import "C"` sibling) drops the file silently and prints 1; f50 (`//go:build
  !cgo`) includes it and prints 2 — while the frontend refuses both shapes by name
  under either host state (`CgoFiles … cgo is outside the modeled fragment`;
  `reserved tag "cgo"`). So: a red, never a silent wrong answer — the pin's
  direction is safe. Separately, `tools/nativefrontend/stdlibsource.go:554-563`
  `libraryBuildContext()` pins `CgoEnabled = false` and documents itself as «the
  ORACLE's build context», contradicting `fileselect.go:20-27`; the wire's single
  `buildContext.cgoEnabled=true` therefore describes the user units only. No
  allowed stdlib package's file set differs between the two cgo states (checked:
  `strings strconv internal/strconv internal/stringslite internal/bytealg unicode
  unicode/utf8 math/bits errors bytes slices cmp encoding/binary`), so there is no
  concrete effect today.
- Why it matters: «three spellings of ONE pin» (`fileselect.go:60-63`) is four,
  and two disagree; a record on trusted surface #1 asserts a property of trusted
  surface #2 that surface #2 does not enforce (Go auto-disables cgo on a host with
  no C compiler).
- Where: `tools/nativefrontend/fileselect.go:20-27,60-70`; `stdlibsource.go:552-563`;
  `docs/BUGS.md` BUG-108 FIXED paragraph; `scripts/diff-coverage:1309-1317`.
- Proposed disposition: (i) records fix round — reword «the oracle's CGO_ENABLED=1
  default» to «the frontend's pin; the runner inherits the host's cgo state»; (ii)
  record as owed: pin `CGO_ENABLED=1` in `go_run_oracle` or assert it in the oracle
  pin guard — a trusted-surface-#2 change, PENDING [USER] (the candidate already
  flags harness changes so); (iii) owed: one `build.Context` for user and library
  units (the stdlib pin manifest would not move — selection is identical).

### F4 — RECORDS-CLAIM (minor): the twelve gate lines are prose, not tails

- What I did: read `docs/evidence/2026-09-11_review-boundary/` (9 files) against the
  README's gate table; compared with the repo convention (`docs/architecture-
  rules.md:123` «gate tails, transcripts», e.g. `docs/evidence/2026-09-08_typed-
  test-gates/committed-gate.txt`).
- What happened: no `ci` tail is tracked for any of the 12 `ci`/`ci --diff`/
  `ci --slow` runs; exit codes, wall times and red sets are asserted in the README
  only. What the audit could re-run is green: `check-wire-boundary` (11 controls,
  EXIT=0), `check-bugs.sh` (0), `check-evidence-size` (0), `certification.py
  check-records` (PASS — the installed record's inventory matches the tip),
  `check-frontend-pins` (0: twin `e1a87725…` fresh emit = pin; stdlib pin 61 files),
  `go test ./tools/{nativefrontend,coverageharness,lowerdiag}` (0), warm `lake
  build` (0), and the 11 `source-selection/` rows through the real runner (11/11
  PASS, `l-focused-source-selection-run.txt`). The full `--diff`/`--slow` exits
  rest on the candidate's word. The installed certified record's receipt reads
  `source_commit 07bc55cb, git_dirty true` (minted on the S3 tree before commit) —
  permitted by the provenance design (the receipt records dirty state) and
  superseded by the merge train's step 5a re-certification.
- Proposed disposition: no fix round; the 5a run at the merged tip yields fresh
  tails — track its `RESULT:` tail with the 5a records commit.

### F5 — SCOPE: checked, nothing outside the remit

Every hunk of the 57-file diff maps to BUG-108 (`fileselect.go` new, `main.go`/
`load.go` selection sites, `emit.go` `buildContext`, `langversion.go` = pure
factor-out of `judgeBuildConstraintLine` with byte-identical refusal texts,
`stdlibsource_test.go` following the production selection path, `Tests/*`
envelopes gaining the required key, twin re-pin, lowerdiag cause rows), BUG-109
(`modfile.go`/`modfile_test.go`, the two call sites, one cause row) or BUG-110
(`CLI.lean`/`ChoiceTrace.lean`/`StrictJsonParse.lean`/`NativeToIR.lean`,
`check-wire-boundary` + its `ci` step, `TODO.md` F5 discharge). `load.go`'s old
«expected exactly one package» refusal becomes go/build's `MultiplePackageError`
behind the same `unsup` — a wording change, same outcome (f13).

### F6 — PERFORMANCE: the strict parser costs +62–65% decode time on the two largest wires

0.08 s on the 11.4 MB twin, 0.03 s on the 3.5 MB largest corpus wire, nil on a
1.5 KB fixture (F2's table). Against the 30 s per-case budget: no action; the
records (F2) are what need correcting.

### N1–N8 — NITs

- N1 `godebug default=go1.21` in `go.mod` (g12) is accepted silently and is absent
  from BUG-109's owed list (only `//go:debug` LINES are named); inert under the
  oracle's `GO111MODULE=off`. Add to the owed list.
- N2 The over-depth refusal prints BOTH bounds («declaration envelope 64,
  production wire 1024», `StrictJsonParse.lean:130`) instead of the one in force.
  Cosmetic; name the effective bound.
- N3 `scripts/check-wire-boundary`'s surrogate controls say they mutate «the
  UNREAD `package` field»; `"package":"main"` first occurs inside `fileOrder[0]`
  (alphabetical key order), so that is where they land (h41 reproduces the gate's
  mutation; refused `offset 152`). Both fields are unread — the control is valid;
  fix the comment.
- N4 The header scan judges legacy `// +build` lines where go/build would not
  (go/build ignores `+build` when a `//go:build` line exists and requires a
  following blank line) — over-refusal only (f22 refuses `// +build cgo` in an
  excluded file). Fail-closed; record.
- N5 Item (b) is clean: every excluded-and-constrained file refuses NAMING the
  file and the constraint (f10, f17, f22, f45, f46, f50); every silent drop is a
  file gc also never opens (f07, f08, f16, f26 block-comment "constraint", f27
  constraint after `package`, f44 empty `_windows`, f48 `import "C"` in a
  `_windows` file). PENDING [USER] on the constraint policy stands as the
  candidate recorded.
- N6 Owed item 1 reproduced with the real harness binary: `_bad.go` («expected
  'package', found this») and `bad_windows.go` («expected ')', found 'EOF'») make
  `coverageharness` refuse before `go run` — a red at the harness stage where gc
  and GoLean both answer 1; never silent. Trusted surface #2: PENDING [USER].
- N7 The pre-fix binary's behaviour the candidate removed, for the record: it
  silently ACCEPTED a duplicate key at every depth (h01, h02, h25), lone/mispaired
  surrogates (h03, h04, h31, h32, h41) — all ran and answered 42 — and died with
  `uncaught exception: Tried to read file … containing non UTF-8 data` on invalid
  UTF-8 (h05, h06, h21, h22): a crash-shaped exit, now a named refusal. Neither
  binary crashes at 100 000-deep nesting.
- N8 A case file named `zz_golean_harness.go` would be overwritten in the oracle
  copy (no collision check, unlike `zz_golean_crash.go`); pre-existing, not this
  lane's; contrived.

## Item-by-item

- (a) cgo pin — F3. Both host states refuse on the GoLean side; direction safe.
- (b) excluded + constrained — N5, N4: named refusals; no silent include/drop that
  gc does not also make.
- (c) depth — 1024 parses (h15a, then the schema refusal names `buildTags[0]`),
  1025 refuses by name (h15b), 100 000 refuses without a crash (h15c); twin 73 and
  deepest corpus wire 120 (`init/library-var-type-*`) reproduced with a bracket-
  depth count outside strings; 8.5× headroom. The frontend has no matching bound:
  a deeper legitimate program exports and then refuses at the decoder — a named
  `FAIL/lean-observation`, not silent. N2 on the message.
- (d) BUG-109 not a row — the argument HOLDS: the differential oracle is
  `GO111MODULE=off go run .` (`scripts/diff-coverage:1315`) inside a copy that the
  harness assembles from `*.go` only (`tools/coverageharness/main.go:317-333`,
  `:226-251`), and the negative lane requires gc to REJECT the program
  (`scripts/coverage-negative:204` «program unexpectedly compiled») — a `go 1.21`
  module compiles. No lane can host the row without an apparatus change. Not a
  finding; the pins (13 unit shapes, walk-up, nested module; transcripts) are the
  right instrument today.
- (e) oracle view vs GoLean — the harness copies EVERY `*.go` (incl. `.hidden.go`
  and `_ignored.go`; Go's `filepath.Glob` matches leading dots) by basename into a
  fresh dir plus `zz_golean_harness.go`/`zz_golean_crash.go`, and gc re-selects
  there (verified in the copy of `excluded-init`: `GoFiles=[main.go zz_golean_
  crash.go zz_golean_harness.go] ign=[extra_arm64.go extra_linux_arm64.go
  extra_windows.go]`, the `_`/`.` files not even listed). Divergence shapes: an
  excluded file with invalid syntax or a second `main`/subject (harness refuses —
  red); an excluded file carrying a constraint (GoLean refuses — red); nothing
  silent found (`f-file-selection-matrix.txt`, 45 shapes).
- (f) matrix — table below; every include/exclude decision agrees with `go list`
  (the frontend IS go/build); divergences are named over-refusals. Note
  `x_amd64_linux.go` IS included by go/build (the last `_linux` element names the
  OS when the pair does not match) — both sides agree.
- (g) matrix — table below; the [USER] ruling is implemented as stated, including
  «no `go` directive → refuse» (Go assumes 1.16: the oracle prints 9 there).
- (h) matrix — table below; 40 mutants, every rejection a named refusal with an
  offset/path, no crash, no silent default; lenient acceptances are value-preserving
  (`\u0000`, U+10FFFF, trailing whitespace).
- (i) matrix — table below; F1.
- (j) `buildContext` requirement — the 51 tracked wires lacking the key are all
  historical `docs/evidence/**` wires; the only reader is `fr25_test.go:252` via
  `encoding/json` (passes). `spikes/`, `raftsubject/`, `Tests/` carry no other
  wire; the nine hand-built envelopes gained the key. Twin re-pin: added keys
  `['buildContext']`, removed none, all shared keys identical (independent python
  diff of the two pins); `check-frontend-pins` header change = the reason only.
- (k) scope — F5.
- (l) the 11 rows — S1a baseline `6264f152` carries `FAIL … differential` ×5 and
  `FAIL … frontend-export` ×2 as claimed (`baselines/native-full.tsv:4385-4395`
  there); the S1 transcript shows Go=1 / GoLean=2; at the tip 11/11 PASS through
  the real runner (`l-focused-source-selection-run.txt`, EXIT=0).
- (m) records — `check-bugs.sh` ok (110 bugs; symmetric rule holds for 108's seven
  Cases); `check-evidence-size` PASS; `check-records` PASS; certified diff = claim
  `wire_sha256` + inputs inventory + receipt, the six observation lines untouched;
  baseline body 3428 PASS / 248 FAIL = header. F4 on tails.
- (n) performance — F2/F6.
- (o) F1, F3, N1–N8.

## Matrices

### (f) file selection — `go list` under linux/amd64 vs the candidate frontend (`f-file-selection-matrix.txt`)

| # | shape | go list GoFiles / Ignored | go run | frontend | golean | agree? |
|---|---|---|---|---|---|---|
| f01 | `x_linux.go` | in | 2 | lowered | 2 | yes |
| f02 | `x_amd64.go` | in | 2 | lowered | 2 | yes |
| f03 | `x_linux_amd64.go` | in | 2 | lowered | 2 | yes |
| f04 | `x_amd64_linux.go` | in (last elem `linux` = GOOS) | 2 | lowered | 2 | yes |
| f05 | `x_linux_arm64.go` | ignored | 1 | lowered w/o | 1 | yes |
| f06 | `linux.go` | in | 2 | lowered | 2 | yes |
| f07 | `_x.go` | not listed | 1 | dropped | 1 | yes |
| f08 | `.x.go` | not listed | 1 | dropped | 1 | yes |
| f09 | imported `lib/{x_test.go,y_windows.go,_z.go}` | main only (GOPATH unset → go run cannot find lib) | — | lib.go only | 1 | yes (harness gopath copy re-selects) |
| f10 | `//go:build ignore` | ignored | 1 | REFUSE «EXCLUDED by build constraint» | — | over-refusal, named |
| f11 | `testdata/t.go` | in (main only) | 1 | lowered | 1 | yes |
| f12 | `package main` only | in | 1 | lowered | 1 | yes |
| f13 | two package clauses | error «found packages main and other» | error | REFUSE, gc's text quoted | — | yes |
| f14 | `asm_amd64.s` | SFiles | 1 | REFUSE «non-Go sources» | — | over-refusal, named |
| f15 | `_bad.go` invalid | not listed | 1 | dropped | 1 | yes (harness would refuse: N6) |
| f16 | `bad_windows.go` invalid | ignored (never read) | 1 | dropped | 1 | yes (harness would refuse: N6) |
| f17 | `x_windows.go` + `//go:build cgo` | ignored | 1 | REFUSE «reserved tag "cgo"» | — | over-refusal, named |
| f18 | `x_windows_amd64.go` | ignored | 1 | dropped | 1 | yes |
| f20 | `X_WINDOWS.go` | in (case-sensitive) | 2 | lowered | 2 | yes |
| f21 | `x_Linux.go` | in | 2 | lowered | 2 | yes |
| f22 | `x_windows.go` + `// +build cgo` | ignored | 1 | REFUSE «reserved tag "cgo"» | — | over-refusal (N4) |
| f23 | `//go:build unix` | in | 2 | REFUSE «reserved tag "unix"» | — | over-refusal (standing policy) |
| f24 | `//go:build !windows` | in | 2 | REFUSE «reserved tag "windows"» | — | over-refusal (standing) |
| f25 | `//go:build gc` | in | 2 | REFUSE «reserved tag "gc"» | — | over-refusal (standing) |
| f26 | `x_windows.go`, constraint inside `/* */` | ignored | 1 | dropped | 1 | yes |
| f27 | `x_windows.go`, constraint after `package` | ignored | 1 | dropped | 1 | yes |
| f29 | `c.c` | error «C source files not allowed» | error | REFUSE «non-Go sources» | — | yes |
| f30 | `h.h` | in (main only) | 1 | lowered | 1 | yes |
| f31 | `x.syso` | in; link error | error | REFUSE «non-Go sources» | — | yes |
| f33 | `x_linux.go` + `//go:build linux` | in | 2 | REFUSE «reserved tag "linux"» | — | over-refusal (standing) |
| f34 | `windows.go` | in | 2 | lowered | 2 | yes |
| f35 | `x_android.go` | ignored | 1 | dropped | 1 | yes |
| f37 | `x_386.go` | ignored | 1 | dropped | 1 | yes |
| f43 | empty selected `empty.go` | InvalidGoFiles | error | REFUSE, gc's text quoted | — | yes |
| f44 | empty `empty_windows.go` | ignored | 1 | dropped | 1 | yes |
| f45 | `x_windows.go` + `//go:build !windows` | ignored | 1 | REFUSE «reserved tag» | — | over-refusal, named |
| f46 | `//go:build purego` | ignored | 1 | REFUSE «EXCLUDED by build constraint» | — | over-refusal, named |
| f47 | `import "C"` | CgoFiles | 2 | REFUSE «CgoFiles … cgo» | — | over-refusal, named (F3) |
| f48 | `x_windows.go` with `import "C"` | ignored | 1 | dropped | 1 | yes |
| f49 | `x_linux_amd64_test.go` | test file | 1 | dropped | 1 | yes |
| f50 | `//go:build !cgo` | ignored | 1 | REFUSE «reserved tag "cgo"» | — | over-refusal (F3) |
| f51 | `x_test.go` in main | test file | 1 | dropped | 1 | yes |

### (g) `go.mod` — the loopvar probe (`g-gomod-matrix.txt`); oracle columns are `GO111MODULE=on` (directive honoured) and `=off` (the harness's mode)

| # | go.mod | go run on | go run off | frontend | golean |
|---|---|---|---|---|---|
| g01 | `go 1.26` | 3 | 3 | accept | 3 |
| g02 | `go 1.26.5` | 3 | 3 | accept (Lang go1.26) | 3 |
| g03 | `go 1.26rc1` | 3 | 3 | accept | 3 |
| g04 | `go 1.27` | error (requires ≥1.27; GOTOOLCHAIN=local) | 3 | REFUSE «declares go 1.27» | — |
| g05 | `go 1.25` | 3 | 3 | REFUSE «declares go 1.25» | — |
| g06 | no `go` directive | **9** (Go assumes 1.16) | 3 | REFUSE «has no go directive … assumes go 1.16» | — |
| g07 | `toolchain go1.26.5` | 3 | 3 | accept | 3 |
| g08 | `toolchain go1.27.0` (GOTOOLCHAIN=local) | 3 (line inert) | 3 | accept | 3 |
| g09 | `go.work` (`go 1.21`) + `go 1.26` | error (go.work lists 1.21) | 3 | accept (go.work ignored) | 3 |
| g10 | nested `lib/go.mod` `go 1.21` | error (no main module) | error (no GOPATH) | REFUSE naming `lib/go.mod` | — |
| g11 | parent-dir `go.mod` `go 1.21`, row in `sub/` | 9 | 3 | REFUSE naming the parent go.mod | — |
| g11b | parent-dir `go 1.26` | 3 | 3 | accept | 3 |
| g12 | `godebug default=go1.21` | 3 | 3 | accept (N1) | 3 |
| g13 | `go 1.26 // pinned` | 3 | 3 | accept | 3 |
| g15 | CRLF line endings | 3 | 3 | accept | 3 |
| g16 | empty `go.mod` | error (missing module) | 3 | REFUSE «has no go directive» | — |
| g17 | `go 1` | error (invalid go version) | 3 | REFUSE «declares go 1» | — |
| g18 | `go v1.26` | error | 3 | REFUSE «go/version cannot parse» | — |
| g20 | `GO 1.21` | error (unknown directive) | 3 | REFUSE «has no go directive» | — |
| g21 | `go 1.21` (the review's F2) | **9** | 3 | REFUSE «declares go 1.21; GoLean implements the Go 1.26 language only» | — |
| g22 | no `go.mod` | error (no main module) | 3 | accept (the pin) | 3 |

### (h) strict parser — 40 byte-level mutants of the `Tests/wire-boundary` wire through the real CLI (`h-strict-parser-matrix.txt`); PRE = main's binary on the same bytes minus `buildContext`

| # | mutant | POST (44c8ed60) | PRE (18beb979) |
|---|---|---|---|
| h00 | control | ok 42 | ok 42 |
| h01 | duplicate `stmt` key inside a statement | REFUSE `$["funcs"][0]["body"]["body"][0]: duplicate JSON object key` | **ran, 42** |
| h02 | duplicate key in an object inside an array (`funcs[0]`) | REFUSE `duplicate JSON object key` | **ran, 42** |
| h03/h04 | lone `\ud800` / `\udc00` | REFUSE `unpaired high/low surrogate in JSON string` | **ran, 42** |
| h05/h06 | raw 0xFF inside / outside a string | REFUSE `JSON input is not valid UTF-8` | `uncaught exception … non UTF-8 data` |
| h07 | UTF-8 BOM | REFUSE `offset 0: $: expected JSON value` | REFUSE `unexpected input` |
| h08 | trailing `x` | REFUSE `expected end of input` | same |
| h09 | trailing newline + spaces | ok 42 | ok 42 |
| h10/h11 | `NaN` / `Infinity` | REFUSE `invalid JSON number` (path named) | REFUSE `unexpected input` |
| h12 | `01` | REFUSE `leading zero` (path named) | REFUSE `unexpected character in array` |
| h13 | `1e400` | parses; schema refusal `buildTags[0]: String expected` | parses; schema refusal |
| h13b | `1e1025` | REFUSE `JSON number exponent …` (bound named) | parses; schema refusal |
| h14 | `-0` | parses; schema refusal | same |
| h15a | nesting exactly 1024 | parses; schema refusal | parses |
| h15b | nesting 1025 | REFUSE `JSON nesting deeper than the bound …` (path named) | parses |
| h15c | nesting 100 000 | REFUSE (no crash) | parses (no crash) |
| h16 | empty file | REFUSE `unexpected end of input` | same |
| h17/h35 | raw 0x01 / raw TAB in a string | REFUSE `unescaped control character in JSON string` | REFUSE `unexpected character in string` |
| h18 | `\u0000` escape | ok 42 (value-preserving) | ok 42 |
| h19 | 257-digit number | REFUSE (number-length bound named) | parses; schema refusal |
| h21 | overlong `C0 80` | REFUSE `not valid UTF-8` | `uncaught exception` |
| h22 | UTF-8-encoded surrogate `ED A0 80` | REFUSE `not valid UTF-8` | `uncaught exception` |
| h24 | top-level array | parses; `program: object expected` | same |
| h25 | duplicate `schema` with identical values | REFUSE `duplicate JSON object key "schema"` | **ran, 42** |
| h28 | unterminated | REFUSE `unexpected end of input` | same |
| h29 | NUL byte between tokens | REFUSE `expected object key` | REFUSE `expected "` |
| h31/h32 | `\ud800A` / `\ud800\ud800` | REFUSE `unpaired high surrogate` | **ran, 42** |
| h33 | valid pair (U+1F600) | ok 42 | ok 42 |
| h34 | `\x41` | REFUSE `illegal \ escape` | same |
| h36 | raw U+10FFFF | ok 42 (valid scalar) | ok 42 |
| h37/h38 | unquoted key / single quotes | REFUSE `expected object key` | REFUSE `expected "` |
| h39 | trailing comma | REFUSE `expected JSON value` (path named) | REFUSE `unexpected input` |
| h40 | big mantissa, negative exponent | parses; schema refusal | same |
| h41 | the gate's own first-occurrence surrogate (lands in `fileOrder[0].package`) | REFUSE `offset 152: unpaired high surrogate` | **ran, 42** |

### (i) `resultTypes` — mutants of the multi-call fixture (`i-resulttypes-matrix.txt`)

| # | site / mutation | result |
|---|---|---|
| i00 | control | ok 42 |
| i01 | `_, _ = two()` → 1 entry | REFUSE `arity 1 does not match the 2 target(s)` |
| i02 | `_, _ = two()` → 3 entries | REFUSE `arity 3 …` |
| i03 | `_ = one()` → `[]` | REFUSE `arity 0 does not match the 1 target(s)` |
| i04 | expr-stmt `one()` → `[]` | decodes; RUN-time `stuck`: `extra GoCore assignment value` |
| i05 | expr-stmt `one()` → 3 entries | decodes; RUN-time `error`: `storeK value/target arity mismatch` |
| i06 | expr-stmt `two()` → 1 entry | decodes; RUN-time `error` (same) |
| i06b | expr-stmt `none()` → 1 entry | decodes; RUN-time `error` (same) |
| i07 | vector on an `ident` node | REFUSE `unknown key 'resultTypes' …` |
| i08 | `_ = one()` → `[string]` | **ok 42** (F1) |
| i09 | `a, _ := two()` → 1 entry | REFUSE `arity 1 does not match the 2 target(s)` |
| i10 | `b, _ = two()` → `[string,string]` | **ok 42** (F1) |
| i11 | `resultTypes: 5` | REFUSE `call.resultTypes: array expected` |
| i12 | `resultTypes: [5]` | REFUSE `…resultTypes[0]: object expected` |
| i13 | `_, _ = two()` → `[string,string]` | **ok 42** (F1) |

## What I did NOT check

- No full `scripts/ci --diff` / `--slow` at the tip (not required; the box-wide
  lock was taken only for the warm build and the 11-row focused run). The full-run
  exit codes and the "no other movement" claim rest on the candidate's records (F4).
- The candidate's timing binary `dae23a5c…` was not rebuilt; the A/B is main's
  binary vs the tip's (F2 names this).
- `sync-op`/`atomic-op` `resultTypes` mutations (the `bool` check at
  `NativeToIR.lean:1580`) — not exercised through the CLI (needs a `sync.Mutex`
  fixture); read only.
- go/build's `//go:build` vs `// +build` blank-line semantics were reasoned from
  the go/build source, not probed beyond f22/f26/f27.
- `tools/lowerdiag/static.go`'s `parser.ParseDir` census (report-only, recorded by
  the candidate) — not probed.
- The five `docs/evidence/2026-09-11_review-boundary/` transcripts were read, not
  re-executed at the cut `a461ed8b` (their content is consistent with the S1a
  baseline commit and with my pre-fix binary's behaviour in (h)).
