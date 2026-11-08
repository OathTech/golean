# Apparatus defects — the record of defects of the runners, instruments, harnesses and checks

This record holds the known defects of the APPARATUS — the corpus runners, the
instruments, the harnesses and the checks that drive the machine and the
oracle and judge their output — as distinct from the defects of the modelled
surface, which `docs/BUGS.md` indexes. The class boundary ([USER] Mike,
2026-10-27, paraphrased, relayed by the [AGENT] coordinator): a fidelity bug
is a defect of the modelled surface — the interpreter, the lowering, the
observation the machine produces — with an observable semantic effect, a wrong
value or a wrongly-stuck run; that is the serious class, and the fidelity index
is for it only. An apparatus fail-open — a runner or instrument that could have
reported a false green — is a different, lesser class and does not belong in
the index; the coordinator's interim rule of the same day that admitted
apparatus false greens to the index is withdrawn. Opened 2026-10-27 by the
[AGENT] lane `records/apparatus-record-1027` with the nine entries the ruling
names (the five older ones, BUG-110/117/119/120/122, and the four from the
deep-clean review of 2026-10-26, BUG-166/167/168/169 ← DC02/DC08/DC09/DC07),
moved here from the index with their numbers; each carries a `- Moved:` line
and the index keeps a tombstone under the number.

Conventions ([AGENT] 2026-10-27, the owner may overrule):

- **Entry format** is the index's: `## BUG-NNN — <title>`, `- Status: open|fixed`,
  `- Pinned-by: none (<the controls, harness modes or probes that pin it>)`,
  then prose. The numbers are ONE sequence shared with the index (a moved entry
  keeps its number; a new apparatus entry takes the next free number of the
  shared `BUG-NNN` sequence), so a citation of a number anywhere in the repo
  resolves to exactly one entry; a number is never reused.
  `scripts/check-bugs.sh` checks that every tombstone in the index resolves to a
  heading here, that no number is live in both records and that no heading is
  duplicated.
- **Pins here are controls, not baseline rows.** An apparatus entry's
  `Pinned-by:` names its `scripts/check-wire-boundary` controls, its harness
  modes or its probe matrix. It carries no `- Cases:` or `- Expect:` line:
  the index's machinery (the baseline cross-check, the untriaged ratchet, the
  re-pin guard of `scripts/ci`) reads the index alone, so a baseline-row pin
  placed here would be a dead pin — check-bugs refuses one by name; an
  apparatus entry that needs a baseline row stays in the index until that
  machinery is extended.
- **Not in the campaign's sweep.** The defect-neighbourhood campaign
  (`docs/defect-shapes.md`) sweeps the fidelity index; the tool-boundary shape
  S24 left its sweep order with these entries. A `- Neighbourhood:` line here is
  historical.

What stayed in the index, and why ([AGENT] 2026-10-27, raised for the owner at
the ask): BUG-091 (the frontend's refusal text named a label by map iteration
order — its site is the lowering, trusted surface #1, not a runner or
instrument, and its `Expect: FAIL` pin is a corpus row the index's check holds;
it has no semantic effect, so it is the borderline case the owner may move);
the oracle-observer family BUG-105/106/107/114 (`tools/coverageharness`,
`scripts/diff-coverage`: the terminal classification's refusals and the
transport's lost bytes — defects of a harness by site, but honest reds, not
fail-opens, three of them `Pinned-by: differential` with rows the gate's
re-pin guard reads from the index and BUG-107 a [USER]-ruled release limit
cited by `docs/release.md` §4 — moving them needs that machinery extended, so
they wait for the owner's word); BUG-065 (the pool enumerator's budget — a
driver of the machine, trusted surface #1). Not entered here either: the
apparatus candidates `docs/defect-shapes.md` §5 lists as
«apparatus-not-a-verdict» (DC03, DC10, DC18 and the others) — this record is
not claimed complete; an entry is made when someone decides to make it.

---

## BUG-110 — the production wire decoder is fail-open at two points: `Lean.Json.parse` collapses DUPLICATE object keys before the schema validators see them (a forged leading `schema` field vanished behind the genuine one and the wire ran), and a call assigned to `_` with its `resultTypes` vector removed is reconstructed as `int` by `resultTypes[i]?.getD .int` [decoder; trusted surface #1 boundary; review 2026-09-11 F3 = 2026-09-05 gate audit F9, ACCEPTED (master plan §7.2), unfixed at filing — FIXED 2026-09-12, stage S3]

- Status: fixed ([AGENT] lane `fix/review-boundary-0911` stage S3, 2026-09-12 — filed open by the coordinator 2026-09-11 from `docs/2026-09-11_project-review.md` §4 F3; the F9 disposition of 2026-09-05 named the same `.getD .int` sites)
- Pinned-by: none (not a baseline row — the pin is `scripts/check-wire-boundary`, a `scripts/ci` step ("wire boundary (production byte decoder through the real CLI)"): the fixture `Tests/wire-boundary/main.go` (the review's discard-call probe) is lowered fresh by the frontend, its wire BYTES are mutated, and every mutant is driven through the real `golean native-json-run` — a forged leading duplicate `schema`, a duplicate key inside a call node, an absent `resultTypes` vector, a mis-sized one, a missing `buildContext`, an unpaired high / low surrogate escape in an UNREAD field, a raw invalid UTF-8 byte (all must refuse naming their cause), plus the untouched wire and a valid surrogate pair (must run and answer 42))
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

FIXED ([AGENT] S3, 2026-09-12). (1) The production wire is parsed from its
BYTES by `GoLean.StrictJson.parseBytes` (`GoLean/StrictJsonParse.lean`) at
every production entry — `GoLean/CLI.lean` `native-json-run` and
`coverage-observations`, `GoLean/ChoiceTrace.lean` `loadProgram` — via
`IO.FS.readBinFile`: a duplicate object key (at any depth), an unpaired
surrogate escape and invalid UTF-8 refuse BEFORE any schema validator sees a
collapsed object (`Lean.Json.parse` kept one value per key and substituted
U+FFFD). (2) `resultTypes` is REQUIRED on every call-shaped node (`call`,
`call-value`, `atomic-op`, `sync-op` — presence and array shape at
recognition, `requireResultTypes`) and arity-checked where it is consumed
(`decodeResultTypes`: the assignment consumers against the target count, the
sync-op result against `bool`); the two `resultTypes[i]?.getD .int` sites
(the `$cr`/`$cv` discard temps) and the expression-statement site's "absent →
targetless" fallback are gone — an absent or mis-sized vector refuses by
name, never reconstructed. This also discharges TODO.md's F5 item (the
`sync-op`/`atomic-op` nodes accepted an absent key).

[narrowed by audit F1 — `docs/2026-09-15_review-boundary-audit.md`, [AGENT]
2026-09-15] What (2) validates is the ARITY, not the entry TYPES; the reading
this paragraph invited as landed — «the vector is validated, never
reconstructed» — is stronger than the code and is narrowed here. Measured
(audit matrix (i), through the real CLI): arity mutations refuse BY NAME
(`resultTypes arity N does not match the M target(s)`; i01, i02, i03, i09), a
non-array (i11) and a non-type entry (i12) refuse, and a vector on a non-call
node refuses (`unknown key 'resultTypes' …`, i07) — but the entry TYPES are
TRUSTED: `_ = one()` with `resultTypes:[string]` (i08), `b, _ = two()` with
`[string,string]` (i10) and `_, _ = two()` with `[string,string]` (i13) all RUN
and answer 42 on `int`-returning callees, although the decoder holds the
callee's declared results (the `funcs`/`methods` tables) and the callee
expression's `type`. Expression-statement vectors (i04–i06) have no target
count to check against and are caught only at RUN time by the machine (`extra
GoCore assignment value` → status `stuck`; `storeK value/target arity
mismatch` → status `error`) — fail-closed, but NOT a by-name refusal at the
boundary. No observable is affected today (a discard temp is never read).
OWED (audit F1 disposition (a)): a callee-signature cross-check of every
`resultTypes` entry — a post-decode pass, refusing by name, which would also
make the expression-statement vectors boundary refusals. Side observation,
OUT OF LANE, for the state-cleanup arc: the machine stores an int into a
`string`-typed discard cell without objection — a typing/normalization
contract question, not a BUG-110 residual. The parser's nesting
bound is a PARAMETER now: the declaration envelope keeps 64, the production
wire uses `wireNestingDepth = 1024` — the 64 refused 105 real corpus wires at
the stage's first gate (program ASTs reach depth 120 today; the finding and
the histogram are in the evidence README). Movement: none — the
frontend emits the vector on every call-shaped node (`emitResultTypes`), and
every corpus wire is valid JSON without duplicate keys; the raft twin wire is
byte-identical. Decode-time cost of the strict parser [corrected by audit F2 —
`docs/2026-09-15_review-boundary-audit.md`, [AGENT] 2026-09-15. The superseded
sentence, as landed, read: «A/B interleaved, 7 runs each, medians — the raft
twin wire (11.4 MB) 0.124 s → 0.055 s (faster: the byte read replaces
`IO.FS.readFile`'s `String` build — a hypothesis, not isolated), the largest
corpus wire (3.5 MB, `stdlib-source/frontier/*`) 0.052 s → 0.075 s (+0.023 s,
the strict parser's own cost), a 1.5 KB wire 0.021 → 0.020 s». The claimed
SPEED-UP does not reproduce and is WITHDRAWN, together with the `readFile`/
`String`-build hypothesis; the lane's timing binary (`dae23a5c…`) was NOT the
committed one (`44c8ed60…`, the certified record's receipt), which is why the
lane's number is not reproducible — the audit did not rebuild it]: re-measured
A/B interleaved, THREE separate passes, NINE runs each, medians — the raft twin
wire (11.4 MB) 0.132 s PRE → 0.214 s POST, +62% (passes 2 and 3: 0.129 →
0.210, 0.123 → 0.212); the largest corpus wire (3.5 MB,
`stdlib-source/frontier/*`) 0.049 s → 0.081 s, +65%; a 1.5 KB fixture wire
0.020 s → 0.020 s, unchanged. The strict parser COSTS decode time on the large
wires; it does not save it. What stands unchanged: against the runner's 30 s
per-case budget the cost is far inside budget, and the parser is not weakened.
The original fix sketch follows.

Cause: `GoLean/CLI.lean:470` parses production wires with `Lean.Json.parse`,
whose object representation keeps one value per key, so a duplicate key is
gone before any validator runs. `GoLean/NativeToIR.lean:1508` and `:1585`
type the discard temporary as `int` when the `resultTypes` entry is absent
instead of refusing. `GoLean/StrictJsonParse.lean` already rejects duplicate
keys and malformed surrogates for the declaration path and states (line 15)
that it is not wired into production NativeToIR.

Scope of the demonstration: the absent-vector mutation still returned the
right value (42) because the callee returned an int; the defect is
unvalidated reconstruction of semantic metadata (a fail-open default on the
trusted boundary), not a shown wrong value. The duplicate-key acceptance is
a validator bypass.

Fix (dispositions §4 step 1): wire `StrictJsonParse` into the CLI's
production entry; delete the `.getD .int` default — require the vector or
refuse by name (or derive it from the validated callee signature); add
production-byte-input mutation tests (duplicate keys, absent vectors,
malformed surrogates) driven through the CLI, not through an already-parsed
`Json` value.

## BUG-117 — `scripts/gen-inittask-table` is FAIL-OPEN: a build or `nm` failure for a std package is recorded as the silent `?`/unknown row instead of dying [apparatus; derived oracle artifact `tools/nativefrontend/inittask-std.tsv` (the gate's inittask re-derivation, `scripts/ci`); trusted surface #2; found by the FR-37 lane's gate run 1 and its adversarial audit (apparatus finding), 2026-10-07; FIXED 2026-10-07, lane `lane/field-offsets-inittask-1007`]

- Status: fixed ([AGENT] build worker, lane `lane/field-offsets-inittask-1007`, 2026-10-07, under [USER] Mike
  2026-10-07 (items 1-4 approved as proposed), item 4, relayed; rowed open by the [AGENT] train worker r71 the same day —
  every detected gap is rowed, [USER] Mike 2026-09-03, relayed. The fix lands with the lane's merge.)
- Pinned-by: none (a transient tool failure under gate load, not a row state: seen ONCE — the FR-37 lane's gate run 1,
  `ci --slow` at `10270c5a`, the `crypto/hmac` row read `unknown`; NOT reproduced in 3+4 re-runs (four hand
  re-derivations at the same tree byte-identical; gate run 2 ok) — `docs/evidence/2026-10-07_fr37/ci-slow-run1.tail.txt`, removed from main by the 2026-10-12 evidence triage; in
  history as `git show 63c9ea65:docs/evidence/2026-10-07_fr37/ci-slow-run1.tail.txt`)
- Discovered: 2026-10-07, FR-37 lane gate run 1; classified fail-open by the lane's Fable adversarial audit (apparatus
  finding, as relayed by the [AGENT] coordinator)
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: `row_for` maps BOTH an empty `Export` from `go list -export -e` (any build failure, transient included — the
script never reads `{{.Error}}`) AND a non-zero `go tool nm` (`inittask_symbols` returns `(None, None)`) to the silent
`?`/unknown row. A transient failure under gate load is therefore RECORDED as "unknown" instead of dying with its
cause; only the downstream byte-exact comparison against the tracked table (`scripts/ci`, «derived oracle artifacts
re-derived») caught it. Run directly (`-o` to regenerate the tracked table), the script would have written the wrong
row silently. Effect direction: not a wrong answer at the frontend (an `?` package refuses on import), but a
fail-open record of the oracle's own facts — the doctrine's «unclassified case → explicit refusal naming its cause»
violated in the apparatus.

WHERE: `scripts/gen-inittask-table` — `inittask_symbols` (`if r.returncode != 0: return None, None`), `row_for` (the
`not export_file` arm and the `defined is None` arm), and the `go list -export -e -f
'{{.ImportPath}}\t{{.Export}}' std` format (no `.Error` field read).

FIX PLAN (queued, [USER] approved 2026-10-07 (items 1-4 approved as proposed), item 4, relayed; batched with the field-offsets
lane): die on `nm` non-zero, naming the package and `nm`'s stderr; add `{{if .Error}}{{.Error.Err}}{{end}}` to the
`go list` format and die unless the error is of the known no-Go-files / build-constraints class (the legitimate
no-archive directories the `?` arm documents). Fix criterion: a forced `nm` failure and a forced build error both
make the script exit non-zero naming the package; the tracked table re-derives byte-identical.

FIX (2026-10-07, lane `lane/field-offsets-inittask-1007`): `inittask_symbols` returns the failed run and `row_for`
dies on it, naming the package, the archive and `nm`'s stderr. The `go list` step now reads JSON
(`-json=ImportPath,Export,GoFiles,CgoFiles,Error,DepsErrors` — an error text may hold any byte, which a tab-separated
`-f` format would split) and `row_for` dies on (i) any package `Error` unless it is of the no-Go-files class («no
non-test Go files» / «build constraints exclude all Go files») on a package with no `GoFiles`/`CgoFiles`, (ii) any
`DepsErrors`, (iii) an empty `Export` on a package that HAS Go files and reported no error (the transient
`crypto/hmac` shape) — `unsafe` stays the documented `0`. A finding the plan did not anticipate: under go1.26.5 the
six tracked `?` rows (`crypto/internal/fips140test`, `embed/internal/embedtest`, `internal/copyright`,
`internal/coverage/test`, `internal/runtime/wasitest`, `net/internal/cgotest`) carry NO `go list` error at all — they
are test-only directories (`GoFiles` = `CgoFiles` = 0) — so the `?` arm keys on "no non-test source files", and the
no-Go-files error class is accepted only on that same condition. Fix criterion met: the regenerated table is
byte-identical to the tracked one modulo the `# generated:` date line (the line `scripts/ci`'s re-derivation also
excludes); `scripts/test-gen-inittask-table` (new, a fake `go` under `.tmp/`; wired into `scripts/ci`) forces an `nm`
failure, a package error, a no-Go-files error on a buildable package, a dependency error, a missing archive, a failed
`go list` and a malformed listing — each exits 1 naming its cause — plus two positive controls. Evidence
`docs/evidence/2026-10-07_field-offsets/inittask-regen.txt`.

## BUG-119 — `golean coverage-observations --arg-int` is UNCHECKED against the entry parameters: an out-of-range literal wraps SILENTLY at its parameter's kind, and an `--arg-int` at a `bool`/`string`/interface parameter reaches the machine unchecked — `native-json-run` refuses both by name since train r73 [CLI; tool interface; PREDATES lane `lane/argbool-layout-1007` (the lane left `coverage-observations` unchanged by design); found by the lane's Opus adversarial audit (note), 2026-10-07; FIXED 2026-10-08, lane `fix/bug119-120-1008`]

- Status: fixed ([AGENT] fix worker, lane `fix/bug119-120-1008`, 2026-10-08, under [USER] Mike 2026-10-08 (asked for bug fixes while things were calm), relayed by the [AGENT] coordinator. The fix lands with the lane's merge.)
- Pinned-by: none (a CLI-interface gap; no corpus row passes an out-of-range or ill-typed `--arg-int` to
  `coverage-observations`; the fix's controls are in `scripts/check-wire-boundary`)
- Discovered: 2026-10-07, the argbool-layout lane's Opus adversarial audit (a note, not a blocking finding), as relayed
  by the [AGENT] coordinator; rowed by the [AGENT] train worker r73 — every detected gap is rowed, [USER] Mike
  2026-09-03, relayed.
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: train r73 added `entryArgValues` (`GoLean/CLI.lean`), which type- and range-checks every entry argument against
its parameter BEFORE any step and refuses by name (`status:error`). Only `native-json-run` calls it.
`coverage-observations` parses `--arg-int` (`parseEnumArgs`) and hands `cfg.args.map GoValue.int` straight to
`enumSetup`, so `--arg-int 300` at a `uint8` parameter is silently the value 44, and an `--arg-int` at a non-integer
parameter is unchecked — the two drivers disagree on the same command line. Fail-open in the tool interface; not a
wrong answer on any tracked row.

WHERE: `GoLean/CLI.lean` — `parseEnumArgs`' `--arg-int` arm and the `enumSetup program functionName (cfg.args.map
GoValue.int)` call site.

FIX PLAN (queued, [AGENT]; PENDING [USER] scheduling): route `coverage-observations`' arguments through
`entryArgValues` (the same refusals, by name, `status:error`); add the out-of-range and ill-typed controls to
`scripts/check-wire-boundary` for that subcommand. Fix criterion: the two subcommands refuse the same command lines
with the same causes.

FIX (2026-10-08, lane `fix/bug119-120-1008`): `coverage-observations` AND `choice-trace` (the same unchecked
`--arg-int` → `enumSetup` path, in `GoLean/ChoiceTrace.lean`: single-case mode and `--batch`) now pass their entry
arguments through `entryArgValues` BEFORE `enumSetup` — the same refusals with the same texts (the flag, argument
position, parameter name and type; out-of-range literal; arity; unknown entry function), exit 1. The refusal CHANNEL
is each subcommand's own ([AGENT] decision): `native-json-run` prints a `status:error` JSON on stdout;
`coverage-observations` and `choice-trace` print their `<subcommand>: <wire>: <cause>` line on STDERR, as every other
refusal of theirs does — their stdout is the observation set / the trace table, which the harness reads line by line
(a `status:error` JSON there would be one more «member» line to a consumer that ignored the exit code); `--batch`
records a case's refusal as its named `ERROR` line, as for any other case failure. Both enumerators also gain
`--arg-bool <true|false>` (parity: the same literal parser `parseBoolLiteral`, positional interleaving with
`--arg-int`); the apparatus does not emit it (the manifest's args column is ints, and `tools/certification.py`'s flag
whitelist refuses it by name — fail closed, left unchanged: [AGENT], no apparatus change in a CLI fix).
`choice-trace`'s real-engine cross-check runs `runProgramPoolOutM` on the checked values (was
`runProgramPoolOutIntsM` on the raw ints — the same function after `map GoValue.int`). Zero movement: every one of
the 493 manifest rows with an `--arg-int` (491 strict, 2 membership) was run through `native-json-run`,
`choice-trace` (two streams) and `coverage-observations` (the row's own params; strict rows under
`detector-soundness`'s `--strict-enum` default) with main's binary (`6a90ba8d`, provenance-identical) and the lane's:
stdout, stderr and exit code byte-identical on all 493 × 3 (one row, `noodler/budget/loop-100k`, timed out at 180 s
under both binaries; re-run at `--work-cap 1000`, byte-identical, past the argument check) —
`docs/evidence/2026-10-08_bug119-120/`. Controls: 12 enumerator entry-argument controls in
`scripts/check-wire-boundary` (per subcommand: the mixed `--arg-int`/`--arg-bool` call answers; out-of-range,
int-at-bool, int-at-declared-bool, bool-at-int and arity refuse by name, exit 1).

## BUG-120 — a MISSING `--input` file makes `golean native-json-run` die with an UNCAUGHT IO exception instead of a named refusal [CLI; tool interface; PREDATES lane `lane/argbool-layout-1007`; found by the lane's Opus adversarial audit (note), 2026-10-07; FIXED 2026-10-08, lane `fix/bug119-120-1008`]

- Status: fixed ([AGENT] fix worker, lane `fix/bug119-120-1008`, 2026-10-08, under [USER] Mike 2026-10-08 (asked for bug fixes while things were calm), relayed by the [AGENT] coordinator. The fix lands with the lane's merge.)
- Pinned-by: none (no corpus row runs a missing wire; the harness always writes the wire before running; the fix's
  controls are in `scripts/check-wire-boundary`)
- Discovered: 2026-10-07, the argbool-layout lane's Opus adversarial audit (a note, not a blocking finding), as relayed
  by the [AGENT] coordinator; rowed by the [AGENT] train worker r73 — every detected gap is rowed, [USER] Mike
  2026-09-03, relayed.
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: `native-json-run` reads the wire with `IO.FS.readBinFile input` outside any `try`; a missing or unreadable file
raises an IO error that escapes `main` as the runtime's uncaught-exception message, not the CLI's `cliErrorJson`
refusal (`status:error` naming the file and the cause) that every other input failure (JSON parse, decode, entry
arguments) produces. It still fails (non-zero exit), so not a wrong answer — but the refusal is not in the CLI's own
named shape. The same unguarded read pattern may exist in other subcommands; the fix round should check them.

WHERE: `GoLean/CLI.lean`, the `native-json-run` handler (`let bytes ← IO.FS.readBinFile input`).

FIX PLAN (queued, [AGENT]; PENDING [USER] scheduling): catch the read's IO error and emit `cliErrorJson
s!"{input}: cannot read input: {err}"` (exit 1); a missing-file control in `scripts/check-wire-boundary`. Fix
criterion: a missing `--input` prints a `status:error` JSON naming the path.

FIX (2026-10-08, lane `fix/bug119-120-1008`): the check the entry asked for found the same unguarded read in EVERY
file-reading subcommand — `native-json-run`, `coverage-observations`, and `choice-trace` (its wire, its `--batch`
manifest and the prior results file it resumes from); `observation-eq` reads no file. All now read through
`readInputBytes` / `readInputText` (`GoLean/CLI.lean`), which catch the OS error and refuse naming the path and the
cause on one line (`<path>: cannot read input: <OS error>`), exit 1: `native-json-run` as a `status:error` JSON,
the enumerators on their stderr line, a `--batch` case with a missing wire as that case's named `ERROR` line (the
batch continuing, as for any case failure), a missing `--batch` manifest before any results file is created.
Before: `uncaught exception: no such file or directory …` from the runtime, exit 1, on all three (reproduced on
main's binary). Controls: 5 missing-input controls in `scripts/check-wire-boundary`. Train r75 tidy: the refusal names the path
ONCE (`oneLine` drops Lean's own `file: <path>` line). Out of scope, open: the batch loop's WRITES — BUG-122.

## BUG-122 — a failed WRITE of `golean choice-trace --batch`'s results file or its `--dump` file escapes as the runtime's UNCAUGHT IO exception instead of the subcommand's named refusal [CLI; tool interface; PREDATES lane `fix/bug119-120-1008` (outside BUG-120's read-side scope); found by the lane's Opus adversarial audit (informational note), 2026-10-08; FIXED 2026-10-12, lane `fix/release-runtime-1012` (release-readiness item 9)]

- Status: fixed (2026-10-12, lane `fix/release-runtime-1012`, the commit «CLI + machine: two "fail-closed" stops that
  were crashes» — release-readiness punch list item 9; [USER] Mike 2026-10-12 (starting with the items that need no input from the user), relayed by the [AGENT] coordinator)
- Pinned-by: none (no corpus row runs `choice-trace --batch` against an unwritable output; the repro is in
  `docs/evidence/2026-10-08_train-r75/repros.txt`, item 2; the standing controls are the two `unwritable-output`
  controls of `scripts/check-wire-boundary` — the results path and the dump path under a missing directory, each
  refused `choice-trace: <path>: cannot write output: <OS error>`, exit 1, no `uncaught`)
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

- Discovered: 2026-10-08, the bug119-120 lane's Opus adversarial audit (verdict MERGE-CLEAN; an informational note,
  not a blocking finding), as relayed by the [AGENT] coordinator; rowed by the [AGENT] train worker r75 — every detected gap is rowed, [USER] Mike 2026-09-03, relayed.

FIXED [AGENT] 2026-10-12: exactly the fix plan below — `CLI.writeOutputText` / `CLI.appendOutputLines`
(`GoLean/CLI.lean`, beside `readInputText`) catch the OS error and refuse `<path>: cannot write output: <OS error>`
(the path named once, Lean's `file:` line dropped by the same `oneLine`); `runBatch` routes the two headers and every
per-case append through them, a per-case failure attributed `case <id>: …` (an unparsable manifest line's ERROR record
`manifest line <n> (unparsable): …`), returned as the subcommand's `.error` → `choice-trace: …`, exit 1. Fix criterion
met: both repro commands print the named refusal, exit 1, no `uncaught exception` (the two controls above run them).

WHAT: BUG-120's fix made every input READ refuse by name; the batch loop's WRITES are still unguarded — the results
header (`IO.FS.writeFile outPath`), the `--dump` header (`IO.FS.writeFile dp`) and the per-case appends
(`IO.FS.withFile outPath .append`, `IO.FS.withFile dp .append`). An unwritable path (a missing directory, a
permission failure, a full disk) raises an IO error that escapes `main` as `uncaught exception: <OS error>` with Lean's
`file: <path>` line, exit 1 (reproduced for the two headers at train r75). It FAILS CLOSED (non-zero exit, no false
result), and Lean's rendering happens to carry the path — but the refusal is not in the subcommand's own
`choice-trace: <path>: <cause>` shape, and a per-case append failure mid-batch is not attributed to its case.

WHERE: `GoLean/ChoiceTrace.lean` `runBatch` (the header writes and the batch loop's appends, ~1089–1106).

FIX PLAN (NOT scheduled; [AGENT]): route the writes through a catching helper beside `CLI.readInputBytes` /
`readInputText` that refuses `<path>: cannot write output: <OS error>` (exit 1, the path named once), and a control in
`scripts/check-wire-boundary` (`--out` / `--dump` under a missing directory). Fix criterion: both repro commands print
the subcommand's named refusal, exit 1, no `uncaught exception`.

## BUG-166 — the NEGATIVE corpus runner discarded `go build`'s EXIT STATUS before matching the expected diagnostic: an oracle that timed out (124) or was killed (137) after emitting the text read as a rejection, and the frontend leg then published PASS — a false green on a negative semantic verdict [apparatus; fail-open; deep-clean review 2026-10-26 DC02 / validation V1; FIXED 2026-10-26 (commit 348a7a78, lane `apparatus/dc-false-greens-1026` — the status is classified first: 1 is gc's rejection, 0 `go-compile`, every other status the new stage `go-crash` named by `undecided_cause`); late entry 2026-10-27 under the campaign's apparatus rule (the review's F5)]

- Status: fixed (2026-10-27, late entry — the fix landed 2026-10-26 with no entry; entered under the rule the [AGENT] coordinator set for this campaign on 2026-10-27, the owner may overrule at the ask: an apparatus fail-open that could have produced a false green on a semantic verdict is entered, one that could not is not; [AGENT] lane `records/defect-shapes-1027`)
- Pinned-by: none (apparatus: `scripts/coverage-negative`; the pins are the review's V1 harness modes re-run by the lane — the real fixture `arrays/array-compare-different-length` with the oracle subprocess controlled: exit 1 PASSes, 2/124/137/143 and a SIGKILL are FAIL `go-crash` with the cause named, runner exit 1 — and `scripts/run-with-timeout.sh`'s shared `undecided_cause`/`signal_cause`)
- Discovered: `docs/2026-10-26_deep-clean-release-pass.md` DC02 (validation V1), 2026-10-26.
- Neighbourhood: none — outside the campaign's step-2 sweep since the move (2026-10-27; was «to be swept in step 2, shape S24», the shape that left the sweep order); the entry's own pins stand
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: `if output="$(…)"` dropped the compiler's status; a non-verdict (timeout, kill, usage error) with the diagnostic text in its output counted as the deliberate rejection the row expects. SITE: `scripts/coverage-negative` (the oracle leg); the status vocabulary now shared with `scripts/diff-coverage` through `scripts/run-with-timeout.sh`. ROUTE: the negative lane's oracle leg under load or a kill; the lane's survey found every other subprocess status in the apparatus already sound (the commit's local-space table).

## BUG-167 — the raft harness printed «all green» after running NOTHING: an unknown `-scenario` matched no table entry and a non-positive `-iters` entered no iteration, and the driver judged only its failure counter — a false green on the subject's verdict [apparatus (an instrument outside `scripts/ci`); fail-open; deep-clean review 2026-10-26 DC08 / validation V2; FIXED 2026-10-26 (commit d4bc0442 — the selection is validated before anything runs, the loop counts its runs and the green line names them); late entry 2026-10-27 under the campaign's apparatus rule]

- Status: fixed (2026-10-27, late entry — the fix landed 2026-10-26 with no entry; entered under the coordinator's apparatus rule of 2026-10-27 (a false green on a verdict), [AGENT] lane `records/defect-shapes-1027`)
- Pinned-by: none (an instrument outside the gate: `raftharness/main.go`; the pins are the review's V2 harness — the tracked `main.go` compiled with a fixture table of one failing and one green scenario: a typo, 0, −1 and a stray argument exit 2 by name; `basic×1` exits 1 «1 FAILURE(S) in 1 run(s)»; `green×2` exits 0 naming `2 run(s): 1 scenario(s) x 2 iteration(s)`. The dependency-backed full harness could not run offline.)
- Discovered: `docs/2026-10-26_deep-clean-release-pass.md` DC08 (validation V2), 2026-10-26.
- Neighbourhood: none — outside the campaign's step-2 sweep since the move (2026-10-27; was «to be swept in step 2, shape S24», the shape that left the sweep order); the entry's own pins stand
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: a verdict derived from a counter that nothing incremented. SITE: `raftharness/main.go` (scenario selection, the iteration loop, the summary line). ROUTE: every invocation whose selection is empty or malformed.

## BUG-168 — the raft instruments parsed the machine's observation WITHOUT its exit status: a machine that flushed a matching `ok` observation and then died by SIGKILL was «both oracles agree», and a negative mode accepted any non-zero `go run` (a compile error or a missing dependency included) as the expected stop — false greens on the subject's verdicts [apparatus (instruments outside `scripts/ci`); fail-open; deep-clean review 2026-10-26 DC09 / validation V3; FIXED 2026-10-26 (commit d4bc0442 — `ownedout.machine_exit_agrees` applied first on every machine leg per `docs/cli.md` §2.1's exit contract; `--expect-stop` requires the program's own stop, `--expect-panic-member` a runtime panic's `exit status 2`; `tracereplay.py` records `returncode` and refuses status-less resumed records); late entry 2026-10-27 under the campaign's apparatus rule]

- Status: fixed (2026-10-27, late entry — the fix landed 2026-10-26 with no entry; entered under the coordinator's apparatus rule of 2026-10-27, [AGENT] lane `records/defect-shapes-1027`)
- Pinned-by: none (instruments outside the gate: `tools/raftsubject/runprobe.py`, `codeccheck.py`, `tracereplay.py`; the pins are the review's V3 harness re-run by the lane — a machine printing the matching observation then SIGKILLing itself → exit 1 «died on signal 9 (no verdict)»; an `ok` observation with exit 1 → «exit status 1 and observation status 'ok' disagree»; the ok/ok control passes; a `--resume` of a record without `returncode` refuses naming the record)
- Discovered: `docs/2026-10-26_deep-clean-release-pass.md` DC09 (validation V3), 2026-10-26.
- Neighbourhood: none — outside the campaign's step-2 sweep since the move (2026-10-27; was «to be swept in step 2, shape S24», the shape that left the sweep order); the entry's own pins stand
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: the CLI's contract is exit 0 iff status `ok`, 1 for any other status, nothing else a verdict; an instrument reading the observation alone cannot tell a completed machine from a killed one that flushed early. SITE: the three instruments' machine legs and `runprobe`'s negative modes. ROUTE: every machine and oracle leg of the raft probes.

## BUG-169 — the observation COMPARATOR (`golean observation-eq`) accepts AMBIGUOUS or MALFORMED JSON and IMPOSSIBLE byte values: duplicate `status`/`output` keys collapse to one (`Lean.Json.parse` keeps the last), an unpaired surrogate escape is normalized to U+FFFD and compared equal, and a string observation accepts `bytes:[256]` — the exposed comparison protocol is less strict than it advertises, so a lossy or forged observation can compare equal [apparatus; byte transparency at the readout; OPEN; deep-clean review 2026-10-26 DC07 / frontend FE-02 and robustness, punch list P08 (route the observation text through the strict parser and validate the value domains); late entry 2026-10-27, the review's F6]

- Status: open (late entry 2026-10-27 — a known apparatus fail-open with no entry, assigned to no lane; entered so the byte-transparency shape holds its open instance beside BUG-105 and BUG-138, [AGENT] lane `records/defect-shapes-1027`)
- Pinned-by: none (apparatus; no corpus row — neither reviewer claims the Go observer produces these values today; the finding is the protocol's advertised strictness. The pins when fixed: duplicate-key, unpaired-surrogate and `bytes:[256]` inputs refuse by name through `observation-eq` and the harness's comparison path — the BUG-110 mutant style, in `scripts/check-wire-boundary`.)
- Discovered: `docs/2026-10-26_deep-clean-release-pass.md` DC06–DC07 («admission and observation decoding are too permissive»), 2026-10-26; punch list P08.
- Neighbourhood: none — outside the campaign's step-2 sweep since the move (2026-10-27; was «to be swept in step 2, shape S27», whose remaining members are the wire's and the readout's own channels); the pins named above stand
- Moved: 2026-10-27 from `docs/BUGS.md` (the fidelity index), under the [USER] ruling of 2026-10-27 relayed by the [AGENT] coordinator (an apparatus defect, not a fidelity bug); the number is kept and the index holds a tombstone; text as it stood there, except the `- Neighbourhood:` line where one existed (amended in place to say the entry is outside the campaign's sweep).

WHAT: the production wire is parsed strictly since BUG-110 (`GoLean.StrictJson.parseBytes`), but the observation comparison still reads both sides with `Lean.Json.parse`, so the same duplicate-key and surrogate collapse BUG-110 closed at the wire is open at the readout, and the byte-array decoder does not check `0 ≤ b ≤ 255`. SITE: `GoLean/CLI.lean` `observation-eq` and the observation decoder it shares with `scripts/diff-coverage`'s comparison. ROUTE: every differential comparison of a string-carrying observation (values, `output`, panic messages).

## BUG-296 — the ORACLE HARNESS REPRINTS each source through go/printer, which rewrites what it prints: a lone legacy `// +build` line gains a synthesized `//go:build` twin, so a row whose meaning depends on the file AS WRITTEN reaches gc as a different program

- Status: open (2026-10-27; entered at the train-25 stage by the [AGENT] coordinator from the admission fix lane's report, `frontend/fix-admission-1027`)
- Pinned-by: none (apparatus: `tools/coverageharness` — the harness assembles the oracle program by printing the parsed files; the two rows that showed it, `source-selection/sweep-s20-plusbuild-no-blank` and `…-after-block`, were RETIRED with `# removed:` lines rather than pinned to a reprinted program)
- Discovered: 2026-10-27, lane `frontend/fix-admission-1027` while fixing BUG-216 — gc on the file as written prints 2 (go/build ignores the legacy line), the oracle harness's reprint carries a `//go:build ignore` twin (gofmt's synchronization rule), so the oracle excluded the file and printed 1.
- Neighbourhood: none — an apparatus defect outside the campaign's sweep; the class is «the oracle does not see the file as written»: any construct go/printer normalizes (build-constraint twins, comment placement, import grouping, trailing commas, a BOM) is invisible to the differential on the oracle side. A row whose source depends on exact bytes cannot be oracle-tested until the harness builds from the original files (a fix shape: copy the files verbatim into the oracle's tree and inject the harness code as a separate file).

## BUG-297 — the ORACLE HARNESS REFUSES an ok run whose own program output ends with a line `exit status N`, reading it as the go command's trailer

- Status: open (2026-10-27; entered at the train-27 stage by the [AGENT] coordinator from the S27 sweep lane's report, `sweep/s27-bytes`)
- Pinned-by: none (apparatus: `tools/coverageharness` `split.go` — the probe `exit-status-trailer`: gc stderr `first\nexit status 1\n` with exit 0; the machine `output:"first\nexit status 1\n"`; the harness: «an `exit status N` trailer on an ok run (the child did not exit 0)»)
- Discovered: 2026-10-27, the S27 sweep (byte transparency), probing the output channel.
- Neighbourhood: none — an apparatus defect outside the campaign's sweep. A FALSE RED, never a false green: a program that prints such a line cannot be oracle-tested until the splitter distinguishes the go command's trailer (the last line, after the child's exit, only when the child exited non-zero) from the program's own bytes.

## BUG-298 — the CORPUS MANIFEST admits ASCII subject identifiers only, so a non-ASCII function name cannot be a row

- Status: open (2026-10-27; entered at the train-27 stage by the [AGENT] coordinator from the S27 sweep lane's report)
- Pinned-by: none (apparatus: `scripts/coverage-manifest` — «invalid subject identifier: größe»; the cell was probed by hand: `--function größe` → the machine `3, [195,188,255]`, gc `3 true 3`, agreement)
- Discovered: 2026-10-27, the S27 sweep.
- Neighbourhood: none — an apparatus limit, not a verdict: a legal Go identifier outside ASCII is a construct the corpus cannot hold a row for; the frontend, the wire and the machine carry it (the hand probe).

## BUG-431 — the ORACLE OBSERVER's fatal split attributes the RUNTIME's own diagnostic lines, printed before `fatal error: …` by the throwing code path, to the program's `output`: a stack overflow's `runtime: goroutine stack exceeds 1000000000-byte limit` / `runtime: sp=… stack=[…]` lines come back as the subject's print bytes [apparatus; `tools/coverageharness/crashview.go` `checkedAbortView`'s fatal rule; a hand probe of the S22 sweep, 2026-11-07]

- Status: open (2026-11-07; entered by the [AGENT] lane `sweep/s22-readout` from its hand probe `.tmp/probes/hand/c6-recursion`)
- Pinned-by: none (apparatus: no corpus row can reach it — the machine's stop on unbounded recursion is `fuel-out`, so a `fatal` row with reason `stack overflow` is red at lean-observation before any output compares; the probe: `func rec(n int) int { return rec(n+1) + 1 }` — gc `fatal error: stack overflow` preceded by two `runtime: …` lines, exit status 2, the observer `--abort-status fatal`, `--abort-message "stack overflow"`, `--split-stderr … --expected-status fatal` → `"runtime: goroutine stack exceeds 1000000000-byte limit\nruntime: sp=0x… stack=[0x…, 0x…]\n"`)
- Discovered: 2026-11-07, the S22 sweep (matrix group C6, implementation limits).
- Neighbourhood: none — an apparatus defect outside the campaign's sweep. The same shape for every runtime throw that `print`s diagnostics before `throw`/`fatal`: `runtime: out of memory` (`runtime: out of memory: cannot allocate …` lines; S23's class on the oracle side), `runtime: unexpected return pc`, `runtime: g N: unexpected return pc`, the `runtime: sp=…` lines of `morestack` — each would be read as program bytes. A FALSE RED at worst (the machine prints nothing there), never a false green: a compared `output` holding runtime text cannot equal the machine's. The fix is the fatal rule's: the bytes between the program's last authenticated output and the `fatal error:` marker are program output only if the runtime wrote nothing there, and the runtime's pre-marker prints are a closed set (`runtime: ` at a line start on the throwing path) the observer can name and strip — or refuse by name, as it does for a second marker.

## BUG-361 — the DEDUP ENGINE (`coverage-observations --engine dedup`) on a goroutine that POLLS through a registry op — a `select` with `default` in a loop, a mutex-protected flag read in a loop — is KILLED at the memory cap instead of refusing by name: at `--work-cap 800000` and above it reaches 8.4 GB within 4.2 s under `capped -m 8G` (exit 137, nothing printed) where at `--work-cap 200000` it refuses by name after 97 k nodes at 670 MB — the work cap, its only budget, does not bound its memory; the registry-free spinner `for {}` and the `len(ch)` poller close in 0.07 s at 75 MB [apparatus (the enumerator's dedup engine); a kill in place of a named refusal, never a false green; found by the S15 sweep 2026-11-07]

- Status: open (2026-11-07; entered by the [AGENT] lane `sweep/s15-scheduling` under the campaign's index boundary — an apparatus defect goes to this record; the number is from the sweep's reserved block)
- Pinned-by: none (apparatus: `coverage-observations --engine dedup --expect-status ok --work-cap <W>` on the subjects `mutexPoll` and `selectDefaultPoll` of `Corpus/coverage/exec/goroutines/sweep-s15-backedges/main.go`, exported alone with `--subject`; measured under `capped -m 8G` with `/usr/bin/time`: `mutexPoll` W = 20 M / 6 M / 2 M / 800 k → exit 137 at 8.43 GB in 4.2 s, W = 200 k → «dedup engine: dedup work budget exceeded (97102 nodes, 102900 edges, 5799 hits, 61203 hashes, maxBucket 7) — raise the row's work cap» at 670 MB in 0.6 s; `selectDefaultPoll` W = 2 M → exit 137 at 8.43 GB in 4.6 s, W = 200 k → the same refusal at 649 MB; `spinningChild` (`for {}`) and `lenPoll` W = 2 M → the certified singletons {1} and {7} in 0.07 s at 75 MB. The DFS engine on `mutexPoll` exceeds a 4 M work cap by name (2.88 M steps + 1.12 M probes, 2 m 41 s); `selectDefaultPoll` and `lenPoll` are rowed under DFS with `iters=5`)
- Discovered: 2026-11-07 by the S15 sweep (cell B16, the mutex poller, on BUG-152's Neighbourhood line) while trying to certify the cell's set: the lane's second session had started a dedup retry at 20 M work units that the box's stop cut; the third measured the kill at every cap from 800 k up and the named refusal at 200 k.
- Neighbourhood: none — an apparatus defect outside the campaign's sweep. The class: a loop whose every iteration completes a registry op (the select entry's default take; `Lock`/`Unlock`) gives a state graph the engine does not close within its budget (97 k nodes and growing at 200 k work units, where the registry-free `for {}` and the `len(ch)` poll fold back onto a few nodes), and the engine holds a copy of every node: about 6.9 KB per node at 200 k units and 8.4 GB before 800 k. A cap above a few hundred thousand units on such a cell is therefore a kill under `capped` and a runaway without one — a non-verdict, never a false certificate (the checker-accepted certificate is produced only on a closed graph). The row's alternative is the DFS engine with `iters=` (the pollers' rows), which the dedup engine refuses by design (`--allow-nonterm-iters`). FIX SHAPE (not this lane's): a node or memory budget the engine refuses on by name before the cap, sized against the box's limit, and the stats line printed on the way out.
