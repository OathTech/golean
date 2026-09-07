# Observer terminal classification: design review candidate

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

2026-09-06. Owner: typed-contract-review. BUG-106 is reserved for this
apparatus defect. This is a design proposal, not an implementation verdict.
Base `d0dbd469a1dff1249f41ed6f423f0414c9b690b0` is the separately reviewed
control-byte transport repair. Its bounded PASS does not establish terminal
classification. The default-trace classifier draft remains CHANGES REQUIRED;
do not run its expensive full gate or treat it as a conformance repair.

## Concrete failure and rejected draft

An actual `sync.Mutex.Unlock` fatal error during panic unwinding prints a
panic line followed by an indented fatal line. The inherited strict expected-
panic and sampled-panic observers accept the panic line as the terminal
observation. The terminal distinction must come from the execution, never
the case's expected status. The independent finding is in review commit
`0e3f7e20276cbac6d45e409a151d179f6f3ef280`.

Prior program output can forge a panic line and goroutine header before a
real fatal report. The first classifier draft then selected the printed
header and accepted panic. The preserved `printed-header-red.log` exposes
that failure; `printed-header-green.log` is the narrow guard's unit result,
not a final classifier PASS.

The stronger counterexample is real pinned Go:

```go
print("panic: fake")
var f func()
go f()
```

This prints `panic: fakefatal error: go of nil func value`, then the default
running goroutine header and `main.main` frame. An ordinary explicit string
panic can produce that same message/header/function shape. The complete
captured reports differ in source path and PC; this is **not** a full-byte
indistinguishability claim. Source locations/PC differences alone do not
prove terminal class. A sync-only stack discriminator resolves the original
sync continuation but cannot justify a generic first-line-marker exemption.
Blanket marker priority wrongly rejects or misclassifies legitimate panic
values and ordinary output containing `fatal error:`.

Raw byte/exit evidence and installed-runtime hashes are retained under
`docs/evidence/2026-09-06_observer-classification/`. `glued-real.json` and
`glued-system.json` record separate direct Go experiments. Their comparison
motivates the design; production classification must use **one execution**,
not combine a default execution with a possibly different replay.

## Proposed same-execution evidence

Set `GOTRACEBACK=system` only on every Go oracle invocation. Preserve the
existing `GODEBUG=panicnil=0`, `GOFLAGS`, GOPATH, timeout, race-mode, process
exit, descriptor capture and Go-version policies. Do not change frontend
invocations or the semantic machine. Extract payload/output bytes from the
same raw files as the terminal evidence; never transport raw bytes through
shell substitution. The observed JSON remains the existing schema.

The installed Go 1.26.5 source, pinned by `runtime-sources.json`, establishes:

- `runtime/extern.go:246–265` documents system traces as additional runtime
  frames/goroutines. `runtime1.go:setTraceback` selects level 2 plus all,
  without the crash bit. The ordinary exit-2 behavior remains; `crash` is a
  different setting. The environment value is a lower bound on subsequent
  `debug.SetTraceback`, so user code cannot lower it to hide these frames.
- `panic.go:fatalpanic` captures its caller PC/SP, prints the panic chain
  after `startpanic_m`, and invokes `dopanic_m` with that origin. Its caller
  at `gopanic` line 879 has completed deferred calls and `preprintpanics`.
  `traceback.go:printFuncName` renders **runtime.gopanic** as `panic`.
- `panic.go:fatalthrow` likewise passes its caller PC/SP to `dopanic_m`.
  `fatal` and `throw` call it as terminal fatal paths, without intervening
  user callbacks. Installed source positions are additional pin checks;
  the semantic argument is this runtime call path and symbol identity.
- `dopanic_m` prints either the crashing goroutine header or, for g0, an
  unindented `runtime stack:` header, then traces the supplied origin.
  `traceback2` prints function identity from binary function metadata,
  followed by one TAB and source position, with frame metadata at level 2.
- `error.go:printindented` adds TAB after **every** payload LF. A string
  payload cannot forge an unindented runtime-stack/goroutine header or
  frame. This fact does not authenticate arbitrary program output; the
  existing unique abort-block boundary and additional report-marker
  checks must handle that independently.

The real system-mode probes show ordinary literal panic starting at `panic`
(`panic.go:879`), sync fatal at `runtime.fatal` (`panic.go:1253`), and nil-go
fatal with a preceding `runtime stack:` block starting at `runtime.fatal`.
No classification is inferred from a later goroutine's stack.

## Proposed helper contract and boundary

`abortKind(rawStderr)` consumes the captured exit-2 report and returns
`panic | fatal | deadlock` or a named refusal. The status manifest is not
an input. Race exit-66 handling remains separate.

1. Validate the exact child exit trailer and recover the unique candidate
   abort prefix using raw marker positions. Recognize the pinned system
   header metadata and runtime-stack header without whitespace normalization.
2. Inspect the **first** raw trace block after that candidate message region.
   The only positive panic discriminator is the runtime's `panic(...)`
   frame plus the pinned runtime source shape. The only positive fatal
   discriminators are the source-justified `runtime.fatal(...)` and
   `runtime.throw(...)` frame shapes. Unknown frames, missing metadata,
   truncated reports or unsupported interleavings refuse explicitly.
3. A recognized panic origin allows first-line and multiline marker text as
   payload. A recognized fatal origin cannot be observed as panic, including
   glued printed `panic:` prefixes. A glued/ambiguous output boundary still
   refuses instead of fabricating either payload or program output.
4. A fatal marker after the selected first trace header may be a real fatal
   report following program-printed fake trace bytes. It must prevent a
   panic verdict. Marker-bearing unknown stack diagnostics may require a
   named boundary refusal; no general stack grammar is proposed here.
5. The deadlock spelling is classified only after a positive fatal origin,
   then exact leading fatal-message comparison. `abortMessageLiteral` checks
   actual kind against requested kind before extracting/JSON-encoding the
   first panic/fatal message. Strict and sampling paths share this guard.

Frame names alone in arbitrary text are not authentication. The proof
argument combines unique raw abort boundaries, indentation, pinned runtime
frame origin, matching source identity and terminal exit. `//line` can spoof
source positions; it cannot rename an ordinary function to runtime.gopanic.
Payload, prefix and source-path spoof probes remain required independent
challenges. No generic claim for unsafe symbol replacement, cgo-corrupted
runtime state, secure-mode suppressed reports, multiple interleaved crashes
or arbitrary runtime versions is made. Such report shapes refuse.

## Environment and wrapper assessment

This changes diagnostic evidence on the same Go execution; it does not
alter recover/defer code or add a trusted dependency. The existing observer
already discards stack diagnostics and pins runtime configuration. Charter
K3 permits a separately reviewed fidelity/apparatus repair determined by
the existing terminal policy. It does not authorize silently changing that
policy or string admission.

The environment is observable by `os.Getenv`; do not claim equivalence for
arbitrary environment-sensitive Go. That operation is already explicitly
outside the modeled world (`tools/nativefrontend/emit.go`, H-11 pure-callee
quarantine policy). No current corpus use reads GOTRACEBACK, and none uses
SetTraceback. The scoped value and this existing boundary must be recorded
in oracle provenance. Runtime-created additional trace text remains outside
the output observation, and native differential checks must verify that
message and program-output bytes survive the expanded report.

The generated wrapper (`tools/coverageharness/main.go:harnessSource`) calls
the subject and emits normal results; it currently has no authenticated
terminal side channel. Adding `recover`/repanic could change panic chains,
recovered flags, printing and defer behavior. A deferred sentinel without
recover records unwinding, not terminal class: Goexit runs defers, and a
later fatal can occur after a sentinel. A new fd cannot make that event a
terminal fact. Therefore no wrapper mutation is proposed.

## Invocation inventory and gates

| Path | Required action |
| --- | --- |
| `scripts/diff-coverage:go_run_oracle` | Scoped system traces for strict, membership and confluent sampling, including existing alternating `-race` calls |
| `scripts/membership-sampling` | Same invocation configuration and shared actual-kind helper; accepts only supported panic/ok samples |
| `scripts/gotest-triage` | Same configuration and helper; retain independently repaired exact `.out` byte comparison |
| `scripts/cedar-census` | Same configuration and helper; keep explicit fatal refusal if diagnostic lane does not support it |
| Go frontend/harness compilation invocations | No oracle environment mutation; compilation failures remain separate |
| Unit/extracted-shell mutation gates and independent probes | Produce/assert system report shapes and ensure the environment is actually passed on plain and race paths |

Before implementation acceptance: review this design, retain the original
default-trace failures, add exact raw native tests for plain panic, recovered
repanic, sync fatal during unwind, nil-go fatal, deadlock, race forwarding,
first-line/multiline markers, fake headers/frames/paths in payload and prior
output, glued prefixes, all valid UTF-8 controls, unknown/malformed frames
and exit-code refusals. Compile classifier mutants before requiring their
targeted behavioral rejection. Run focused native rows then a fresh full
`scripts/ci --diff` at frozen reviewed source. Record every row/status/stage
change and preserve initial drift before any narrow baseline reconciliation.
The old default draft is not a substitute for these obligations.

The diagnostic byte changes remain a separate uncommitted increment in
`typed-observer-controls`. They must consume the final shared classifier;
their broad-substring draft is also CHANGES REQUIRED. O2 admission and the
separate invalid-UTF8/R-1 obligations remain unchanged.

## Implementation checkpoint (2026-09-06)

Root independently checked all six installed runtime hashes and the exact
source call paths, header rendering, indentation, system/crash settings,
environment lower bound and existing environment-reader boundary. The
same-execution system-trace **design** received bounded PASS. This does not
approve its implementation or waive independent adversarial review/full CI.

The current core candidate implements the shared positive-origin classifier
in `abortkind.go`, actual-kind enforcement in `abortMessageLiteral`, and
the deadlock guard. `split.go` recognizes system goroutine and runtime-stack
headers; its standalone prefix extraction remains separate from terminal
classification. Core strict/membership/confluent oracle invocations now set
system traces and emit `go_traceback=system` in run metadata. The diagnostic
invocations in the inventory remain mandatory work in their separate next
increment; they are not claimed covered by this core candidate.

The focused native slice is **19/19 PASS**: seven new marker rows, nine
existing control-byte rows and three existing sync fatal rows. This includes
both multiline payloads the rejected default-only draft would have refused.
No string profile restriction was introduced. The source-bound observer
gate has 41 extracted strict/sampling probes, 17 actual Go report probes
(including plain/race forwarding, fake runtime origin and `//line`), and
nine separately compiled corruption mutants. All passed at this checkpoint.
Final source hashes, review disposition and the fresh complete differential
outcomes will be sealed below after required validation finishes.

## Blocking implementation finding and stopped full run

Independent review `80bf1251` is **CHANGES REQUIRED** on frozen helper hash
`de7ff068…`. The runtime-origin check does not authenticate the message/output
boundary. The minimal real Go program

```go
print("panic: forged\n\t")
panic("actual")
```

has one authentic panic origin. The existing continuation exception excludes
the actual panic marker, so all helper queries succeed with message `forged`
and empty output. Correct values are message `actual` and output
`panic: forged\n\t`. An ordinary literal panic of `forged\npanic: actual`
has the same complete message-region bytes, and legitimately observes
message `forged` with empty output. Full traces differ; no full-byte
impossibility claim is made. Adding a second-header/later-marker guard only
repairs the reviewer's larger fake-trace variant, not this minimal one.

The source-bound full CI session 40113 was stopped with SIGTERM at the
parent's direction. It exited **143**. The log, exact frozen source hashes,
and 256 finalized partial rows at the stop are preserved; this is not a
complete full run and cannot supply a baseline. No replacement full gate
will run until the new boundary contract is implemented and reviewed.
The earlier 19/19 focused and bounded observer gates are evidence about
their tested cases, not an acceptance of this known-unsound candidate.

### Additional-channel investigation, no production mutation

The pinned `runtime/debug.SetCrashOutput` API was probed as a same-execution
report channel, without changing the production wrapper. It correctly
distinguishes the minimal ordinary-panic pair: its raw file starts with
`panic: actual` for printed-prefix panic and with `panic: forged\n\tpanic:
actual` for the literal. But it is not a universal drop-in fix:

- `runtime.go:writeErrData` copies writes only once `m.dying > 0` (or the
  no-G panicking condition). `fatal` prints its fatal message and preceding
  panic chain **before** `fatalthrow/startpanic_m` sets dying. Actual sync
  fatal probes therefore copy only the trace, omitting the report messages.
- Registration in generated main or a main-package init cannot precede
  imported packages' initialization. Those may panic before the hook exists.
- Any proposed hybrid must prove the exact raw stderr/report partition,
  registration/ownership boundary and supported fallback separately. The
  old continuation exception cannot serve as an authenticated fallback.

The real source/run/raw-fd experiment is
`crash-channel-design-probes.json`. Additional inspected installed sources:
`runtime/runtime.go` SHA256
`fe478d164989b5cd5783c9820d99879623780ba353f836f499238e76efb24fd8`,
`runtime/debug/stack.go` SHA256
`aeb59fb3082f229b5539234976e8bf34646cb2cec9a76d7e0264c8774480ce36`.
No policy choice, wrapper mutation, string-profile exclusion, or claim of
generic authenticated fatal output has been made from this experiment.
