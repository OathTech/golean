# Valid UTF-8 control bytes at the observation boundary

> **Landing preface ([AGENT] landing worker, chunk L4 `land/observer-terminal`,
> 2026-09-07).** This file is the sprint's design record, landed VERBATIM below
> this block from branch `typed-consumer-sprint` (archive tip `7edc298f`,
> `docs/ARCHIVE.md`); the landing note is
> `docs/2026-09-07_land-observer-terminal.md`. Where this record and the landed
> code differ, the landed code is: (1) the same-run crash channel is MANDATORY
> on every stderr-classifying query (landing review finding A-R6) — the "strict
> raw fallback" for an empty acknowledgement that this record describes did
> NOT land; a pre-`main` abort (package initializer or `init()` aborting before
> `main`'s first statement) refuses by name and its rows are red on BUG-107's
> `Cases:` line; (2) a runtime chain-shape pin (inside a channel copy every LF
> before the trace header is TAB-followed, the runtime's single `[signal …]`
> line excepted). The `docs/evidence/2026-09-06_observer-*` directories this
> record cites stay on the archive branch (they do not land — [USER] ruling of
> 2026-09-07, relayed, `AGENTS.md` "Evidence on main"). The two gate scripts it
> names (`scripts/check-observer-controls.py`, `scripts/check-observer-tools.py`)
> did not land in this chunk (landing note, "What did NOT land"); the harness's
> Go tests run under `scripts/ci` instead.

[AGENT], 2026-09-06 UTC. Branch `typed-observer-controls`, based on
`ff7173dd959435ede346c77318c29f13e16ed5f3`. This is the separate K3 apparatus
repair identified during the panic-renderer review. The semantic model is
unchanged. Independent byte-transport review passed, and the full differential
run completed with only the nine expected new PASS rows. Final ordinary CI
after that exact baseline reconciliation passed (exit 0); no main merge or
push is authorized.

## Defect and exact boundary

Go strings and the Go runtime's panic output retain NUL and SOH. The previous
`scripts/diff-coverage` captured raw panic output in Bash command substitution,
which drops NUL, then escaped quotes, backslashes, LF, CR and TAB manually.
SOH and other unescaped JSON controls survived that helper and made invalid
JSON. The same defect affected strict panic/fatal extraction and panic
sampling for membership/confluent rows. The Lean model already preserved the
bytes: `panic("a\x00b")` produced the correct modeled message but the oracle
observation incorrectly contained `ab`.

The existing observer retains the first line following `panic: `; fatal
unwinding permits a single TAB before `fatal error: `. LF ends that line,
and CR remains a payload byte. This repair retains these rules and the
existing `splitStderr` ambiguity, trace-header, trailer, and UTF-8-prefix
checks. A multiline payload's recovered/repanicked suffix remains after
the first observed line. The manifest reason remains a gate; it never
substitutes for the actual observed message.

The wrapper's stdout is its observation JSON channel. The program's
`print`/`println` bytes are stderr, followed on abort by the runtime report.
These descriptors stay in separate raw files. An abort marker or expected
reason found only on stdout cannot justify a panic/fatal classification.
Aborted stdout remains available in byte-preserving diagnostics; this
change does not add stdout to the modeled `output` field.

## Implementation and paths inspected

`go_run_oracle` now returns only its exit status and leaves raw stdout and
stderr in their existing files. Strict and sampling paths classify the raw
stderr file. `coverageharness --abort-message` validates the existing split,
extracts the actual first panic/fatal line, and emits a JSON string literal
using Go's JSON encoder. `--split-stderr` continues to encode the program
output separately. Both use `outputLiteral`, which explicitly rejects
invalid UTF-8 before encoding. `--read-observation` checks untouched stdout
for valid UTF-8 and one complete JSON value before shell transport; the
Lean comparator still validates the observation schema and values. Thus an
illegal raw NUL in stdout cannot disappear before validity checking.

Diagnostics use `--quote-file`, a separate ASCII Go-quoted byte rendering,
with each descriptor labeled. This diagnostic text is never an observation
or a source of classification. It retains invalid bytes as diagnostic
escapes without choosing an invalid-UTF-8 observation representation.

The generated wrapper's success/error JSON already uses `encoding/json`;
its returned Go string values use byte arrays. No change was needed there.
The other output path, `splitStderr`/`outputLiteral`, already encoded valid
controls correctly. This audit covered strict panic/fatal/deadlock/race,
membership/confluent samples, successful stdout, and the wrapper encoder.

A repo-wide follow-up search found duplicated observer code in the diagnostic
tools `membership-sampling`, `gotest-triage`, and `cedar-census`. Their repair
is a separate reviewed increment. Those scripts are outside the core full
corpus's execution path, and this core commit does not claim to fix them.

Invalid-UTF-8 panic/output observation and BUG-004/R-1 membership remain
separate obligations. The repair does not choose replacement characters or
escaped representatives for invalid payload bytes, change boxing identity,
or discharge the existing rendering-quotient ruling. UTF-8 validation of
the observed message concerns its selected first line; this is not a new
claim about the unobserved remainder of a panic report. Generic UTF-8 decoder
correctness and O2 terminal contracts remain owed independently.

## Red-first and focused results

The first eight new native rows ran before editing the observer. All reached
the differential stage: NUL produced a decoded mismatch; SOH and the three
mixed-control panic cases produced comparator exit 2 (invalid oracle JSON,
not a decided equality mismatch). TAB, CR, and ordinary control-byte stderr
output passed as pre-existing behavior controls. The ninth, child-confluent
row was added after that red run to exercise the actual sampling path.

| Case under `panic-recover/panic-controls/` | Initial result | Fixed focused result |
| --- | --- | --- |
| `nul` | FAIL / differential / NUL lost | PASS |
| `soh` | FAIL / differential / invalid JSON | PASS |
| `tab` | PASS | PASS |
| `cr` | PASS | PASS |
| `newline` | FAIL / differential / invalid JSON | PASS |
| `recovered-newline` | FAIL / differential / invalid JSON | PASS |
| `output-prefix` | FAIL / differential / invalid JSON | PASS |
| `output-ok` | PASS | PASS |
| `child-confluent` | Not in initial red run | PASS / confluent / one enumerated observation |

`ControlBytes.lean` separately kernel-checks NUL/SOH preservation and the
mixed-control first-line result in the unchanged model. Both declarations
use only `propext` and `Quot.sound`; these are concrete controls, not a
generic UTF-8 theorem.

## Durable gate and evidence

The ordinary CI now runs `scripts/check-observer-controls.py`. It records
source hashes, freshly builds the Go harness, and runs its complete unit
tests. Coverage includes all 32 JSON control bytes, UTF-8 text, fatal
continuations, first-line selection, empty first line, ambiguous/glued
reports, absent trace/trailer, invalid UTF-8, and raw stdout controls.

The gate extracts the actual strict classification block and exported
sampling functions from `scripts/diff-coverage`. Twenty-six fake-oracle
probes exercise raw descriptor capture, decoded byte identity, named
refusals, and strict failure stages. They include stdout-only markers or
reasons, NUL inside an expected-reason candidate, malformed stdout, invalid
UTF-8, an ambiguous report, fatal exit status, and a killed oracle. These
are apparatus tests, not Go conformance evidence. Four separately compiled
mutants must then fail targeted behavioral tests: NUL deletion, raw SOH in
JSON, whitespace/CR trimming, and NUL deletion before stdout validation.

Evidence is in [the evidence directory](evidence/2026-09-06_observer-controls/).
`sources.sha256` binds the candidate model, harness, runner, gate and native
fixtures; `base-*` files preserve the base observer sources. Initial red
log/TSV/meta are preserved verbatim. The first run's raw descriptor files
were overwritten by the focused green rerun, so
`green-native-raw-streams.json` explicitly records the later green run only.
This is a source-bound dirty-worktree run, not a clean-commit certification
or a stable dependency pin.

Commands run from this worktree (Lean/Lake and CI capped at 16 GiB,
`LEAN_NUM_THREADS=3`, coverage workers 2):

```sh
scripts/capped scripts/coverage run --prefix panic-recover/panic-controls
scripts/capped python3 scripts/check-observer-controls.py
scripts/capped lake env lean docs/evidence/2026-09-06_observer-controls/ControlBytes.lean
scripts/capped scripts/ci --diff
```

The fresh full run completed: **3,616 cases = 3,372 PASS / 244 known FAIL**.
Compared to the previous 3,607-row baseline, the only drift was the nine new
PASS rows above; no existing result/stage changed outside an already-approved
stage alternation, and no case disappeared. The full raw result has SHA256
`9707b7cb100c886fc0b50cbdecd6beae906b462ff87e71a19b15eebb91ecb4c3`.
The initial `scripts/ci --diff` exited 1 solely for expected baseline drift;
all build, observer, interface/admission audits, 202 evals, lane controls,
394 compile-negative cases, and derived-oracle checks passed. Its raw log,
comparison and full result/meta are preserved. The baseline was then updated
only by adding those nine rows and their reason; historical rows and stage
alternation declarations are unchanged. Final ordinary CI passed (exit 0)
against that same complete source-bound run, without an unchanged full rerun.
Its report-only ledger count finding was then corrected as a records-only
edit; the targeted reconciler retained only the two unrelated pre-existing
MEDIUM findings (historical Go-version references and a frontier citation).

Independent byte-transport review is commit
`83c177c25dfa55d081afe0c75b90d028aeabef1b` (324 independent probes, bounded
PASS at the frozen source hashes). The later finding commit
`0e3f7e20276cbac6d45e409a151d179f6f3ef280` records an inherited, separately
discovered classifier error: fatal during panic unwind can be observed as
panic. That finding does not invalidate the byte-preservation result, but it
does block claiming the whole observer correct. A separate classification
increment, independent review and fresh full differential run are required;
the finding is not deferred as acceptable debt. Diagnostic-tool completion
is likewise separate. No O2 acceptance or universal observer correctness is
claimed here.
