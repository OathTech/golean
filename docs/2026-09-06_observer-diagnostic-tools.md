# Diagnostic observer copies: byte-preserving transport

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

[AGENT], 2026-09-06 UTC. This is a separate increment following the core
[observer repair](2026-09-06_observer-controls-repair.md), which remains
independently source-bound and reviewed. The three scripts here are lane
diagnostic tools, not executable-corpus gates. No semantic model, oracle pin,
baseline, or invalid-UTF-8 observation policy changes.

## Determined repairs

The repository-wide search found the same raw Bash capture/manual JSON
encoding in `membership-sampling`, `gotest-triage`, and `cedar-census`.
Each now retains raw descriptors separately and uses the core harness's
file-reading message encoder. JSON travels into shell variables only after
encoding; diagnostics are separately quoted. Invalid UTF-8 messages refuse
explicitly. An oracle exit outside 0/1 cannot turn partial panic text into
a verdict. Stdout cannot supply a stderr panic marker.

The standalone sampling tool validates raw success stdout through the
shared helper before reading JSON. The Go test-suite triage tool compares
actual byte strings to `.out`, using the pinned rule from
`deps/go/src/cmd/internal/testdir/testdir_test.go`, `checkExpectedOutput`,
lines 1137–1158: replace CRLF with LF in actual output, then compare exactly
to the expected file (or empty when absent). Previously both sides passed
through Bash capture, removing NUL and trailing LF. Consequently a newline
could falsely match empty output, while correct CRLF output could be rejected.
The existing concatenation order, stdout then stderr, is retained; this is
not a new claim to reconstruct cross-descriptor write interleaving.

The Cedar census's documented success rule requires silent drivers.
It now checks file sizes, so NUL-only or LF-only output is visibly nonempty.
On abort it obtains the actual stderr output prefix through the shared
splitter instead of fabricating an empty `output` value. Raw `go.out` is
retained for diagnostics alongside the separate descriptor files. Its new
harness build is in `preflight_machine`; helper build failures refuse.

## Bounded evidence and remaining gate

`scripts/check-observer-tools.py` extracts the actual three oracle functions
or blocks and probes them before frontend/model comparison. Its first 21
probes ran before these script edits; the raw red log records lost NUL,
invalid JSON, invalid-UTF-8 acceptance, false silence, and `.out` byte
comparison defects. Existing positive controls remain visible. The fixed
21 probes pass. Nine additional real-Go probes also pass, exercising each
tool's actual panic report with NUL/SOH/TAB/CR/newline and program output,
invalid-UTF-8 refusal, and NUL-only success-output rejection.

These are transport tests, not a fresh full Go test-suite/Cedar census or
Go-versus-model conformance run. The core observer's nine native corpus
cases and full gate are recorded separately. Source hashes and raw
red/green logs belong in `docs/evidence/2026-09-06_observer-diagnostic-tools/`.
This section records the earlier transport-only checkpoint. Current hybrid
review and validation are reported below; the older logs remain intact.

## Shared classifier follow-up history

The intermediate scripts set scoped `GOTRACEBACK=system` and asked the shared helper
for the actual terminal kind, removing the rejected substring-priority
draft. Sampling refuses actual fatal/deadlock; triage supports the shared
panic/fatal/deadlock kinds; Cedar retains explicit fatal refusal. Provenance
records the traceback setting. The new ordinary CI step invokes the durable
diagnostic gate, which then passed 75 checks (48 synthetic and 27
actual Go cases) including marker literals/prefixes, glued prefixes, plain
and race forwarding and exact descriptor preservation.

This does **not** approve the diagnostic increment. Its copied helper is
source-bound to the classifier candidate in `artifacts/observer-diagnostics/
borrowed-classifier.json`; exact source-commit integration remains required.
Independent review `80bf1251` found a shared message/output boundary flaw:
`print("panic: forged\n\t"); panic("actual")` produces an authentic runtime
origin but the current helper selects the printed payload and loses output.
That helper and diagnostic checkpoint were **CHANGES REQUIRED**. No full
diagnostic census or Go-versus-Lean conformance claim follows from those
75 apparatus checks.

## Crash-channel production candidate

The replacement uses the independently reviewed same-execution owned
`SetCrashOutput` channel and the core's one checked byte view. Standalone
sampling consumes the generated oracle wrapper and resets report/ack files
before every plain or race draw. Triage and Cedar each create a fresh sibling
oracle source directory, copy and instrument only its main entry through
`--copy-oracle`, and preserve their original semantic frontend inputs.
Triage runs the copied package, including the helper, instead of a single
file. Cedar retains the original case GOPATH for imported packages. The
oracle directory is recorded beside raw stdout/stderr, and provenance records
the crash-channel version. No source copy contains a recovery wrapper.

All abort-kind, message and output calls pass the paired report and
registration files. Successful observations also validate registration and
an empty report; setup/reset failures are named apparatus failures. Raw
init/fatal fallback has no continuation exemption. A real fatal during panic
unwind now refuses when its message/output boundary cannot be authenticated:
it cannot pass as a panic in any of the three tools. Their existing status
domains remain explicit: sampling accepts ok/panic, triage also fatal/deadlock,
and Cedar refuses fatal while accepting panic/deadlock. None counts a refusal
as conformance.

The final focused diagnostic gate passes **105 checks**: 66 synthetic raw
descriptor/exit/byte controls and 39 actual Go executions, exercising each
tool's minimal printed-prefix/literal pair, glued output, repanic, controls,
wrong-kind fatal, invalid-UTF-8 refusal and positive cases. Source hashes and
exact source preservation checks are emitted. Five syntactically valid
mutations expose false acceptance under the existing negative controls:
omitting channel evidence in each tool, lossy `.out` byte handling, and
Cedar's false silence. These are apparatus checks, not a full diagnostic
census or a new Go/model conformance claim.

Evidence is in `docs/evidence/2026-09-06_observer-diagnostic-tools/`.
Independent diagnostic implementation review is bounded PASS (`c5b83045`,
additive packaging correction `0333f0a1`): fifteen fresh independent probes
exercise each actual tool, source-copy byte preservation, init panic,
initializer exit-zero without registration, and valid captures attached to
non-verdict exits 124/137. The new verdict lives in `PRODUCTION-REVIEW.md`;
the historical CHANGES REQUIRED report remains at its original path.

Temporary borrowed helpers were replaced by a fast-forward to reviewed core
commit `b5dd407624741d4df78252f14f72650a07b06caa`, and the exact diagnostic
delta was restored from preserved stash `7582978ceaec6a84d88a515f1dd24faef0d239df`.
All sixteen frozen diagnostic/helper hashes still match the independent
review. The core's complete 3,627-case result is reused only after checking
the identical source and manifest dependencies; these diagnostic tools do
not participate in that executable-corpus run. Final ordinary CI exits 0,
including the fresh 105-control/five-mutation diagnostic gate, source/audit
checks, 202 eval tests and retained complete 394/3,627-case baselines.
The log openly labels the older dirty-worktree coverage provenance; the
separate `reviewed-dependency-integration.json` binds that actual run to
the identical reviewed dependency. No new full corpus or diagnostic census
is claimed. All sixteen reviewed source hashes were rechecked after CI.
