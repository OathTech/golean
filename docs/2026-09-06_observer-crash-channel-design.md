# Same-execution crash channel: bounded design and decision ledger

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

2026-09-06. [AGENT] typed-contract-review. **Prototype/design only.** The
production classifier remains CHANGES REQUIRED under independent review
`80bf1251`. The interrupted full CI is not reused. This proposal follows
the concrete minimal printed-prefix failure in
[the terminal-classification design](2026-09-06_observer-terminal-classification-design.md).

## Proposed contract

The observer consumes the same execution's process exit, raw stdout, raw
stderr, an owned crash-report file, and a hook-registration acknowledgement.
Expected status/payload is not an input to report authentication.

The Go harness installs `runtime/debug.SetCrashOutput` immediately before
calling its subject, without adding recover/defer behavior. The runner
truncates both owned files before **every** plain or race execution. The
wrapper opens the report file for write/truncate, registers it with the
runtime, closes the original `*os.File`, and writes the acknowledgement.
SetCrashOutput duplicates the descriptor with close-on-exec; the runtime
owns that duplicate until child-process exit. A setup/open/dup/acknowledgement
failure exits with a distinct nonverdict code (prototype: child 78), and
must become a named oracle-setup/go-run refusal. It must never be counted
as the subject's panic, success or Go conformance.

After an ordinary panic, validate all of:

1. The oracle process returned a runtime verdict and the exact child-exit-2
   trailer exists. Strip only that trailer from raw stderr.
2. The registration acknowledgement is present and the report is nonempty.
3. The remaining stderr ends in the **entire, byte-identical** report file.
   No decoding, whitespace normalization or shell capture precedes this.
4. The report starts at its panic marker and its first crashing runtime
   origin is the pinned gopanic/fatalpanic origin. Reject unsupported later
   terminal-report blocks, unknown origins, corruption or truncation.

Then the bytes before that exact suffix are program output; the first raw
panic line in the report determines the observed payload. A string can
contain any marker text or fake headers: it no longer supplies the output
boundary. The existing valid-UTF8 JSON transport remains exact. Arbitrary
invalid-UTF8 **representation** remains the separate R-1/string obligation;
this channel preserves those raw bytes rather than replacing them silently.

The concrete production API should take paired crash-file and registration
file arguments for actual-kind, message and output queries; all three must
use one shared checked report view. File/shape failures are explicit refusals.
Successful runs retain the existing stdout-validation and stderr-output
contract; a nonempty crash channel on success must refuse. Missing one of
the paired arguments must not silently disable checks. Direct legacy queries
without channel evidence use only the strict raw fallback below.

## Missing/partial report coverage and strict fallback

The wrapper cannot register before dependency/main-package initialization.
An init panic therefore has no hook acknowledgement. Fatal messages and
their preceding panic chain are also not copied: installed
`runtime/runtime.go:writeErrData` begins duplication after `m.dying > 0`,
whereas `panic.go:fatal` emits its messages before `fatalthrow/startpanic_m`.
The real probes confirm both limits.

The only proposed raw fallback counts **every** marker, including those
preceded by LF TAB. It has no repanic/unwind continuation exemption:

- A raw panic candidate requires exactly one `panic: ` marker, a valid
  output boundary and positive panic origin. Full remaining-report checks
  reject later actual reports after a printed origin.
- A raw fatal/deadlock candidate requires exactly one `fatal error: `
  marker and zero `panic: ` markers, a valid output boundary and positive
  fatal origin. Exact fatal-message comparison selects deadlock only after
  this terminal evidence.
- Otherwise payload/output authentication is missing, and the observer
  emits a named `go-observation` refusal. It does not guess empty output or
  turn Go's terminal kind into a GoCore refusal. Static O2 admission remains
  unchanged, including arbitrary strings and unrestricted repeated panic.

The required O2 profile excludes package initialization and printing, and
the ordinary-panic channel nevertheless handles arbitrary preceding print
bytes in its supported source domain. This is not a claim that every Go
subject can register the hook early enough or that all fatal reporting has
been authenticated.

## Ownership and configuration boundary

Suffix equality authenticates a partition **given an owned runtime report
channel**; it is not cryptographic authentication of caller-supplied files.
As with existing raw stdout/stderr capture, the runner must own isolated
per-case files and serialize draws for each case. Stale or forged files,
missing acknowledgement, failed reset/setup, and suffix mismatches refuse.
A caller able to replace captured files can fabricate matching evidence;
do not claim the byte validator detects every chosen matching suffix.

Accepted subjects must not replace the files, close the private runtime fd,
or reconfigure crash output. This is an existing supported-source boundary,
not a new Go language invalidity: fresh native/model probes of `os.WriteFile`,
`debug.SetCrashOutput` and `debug.SetTraceback` all produce
`unsupported/frontend-quarantined`. The O2 static grammar also has no such
operations. These three probes are evidence, not a general theorem about
all unsupported Go or a hostile filesystem. Frontend/model comparison must
still reject those programs; no apparatus-only forged-file test is Go
conformance evidence.

The scoped system traceback value remains on the **same** plain/race run.
`debug.SetTraceback("none")` cannot lower its environment minimum; a real
probe confirms that. Explicitly disabling SetCrashOutput yields either an
unambiguous strict fallback or a named refusal. Hook setup adds no recovery
handler and closes its original fd before the subject; fd lifetime is
covered by the successful real panic probes. Program-visible environment,
file IO, runtime/debug configuration, unsafe fd/symbol manipulation and
resource-accounting observations remain outside the accepted model boundary;
do not generalize this into observational equivalence for arbitrary Go.

## Actual bounded evidence

Evidence directory: `docs/evidence/2026-09-06_observer-classification/`.

- `hybrid-prototype.py` generates instrumented wrappers in unique scratch
  and implements the proposed byte view independently as a **design** tool.
  It leaves production sources unchanged.
- `hybrid-current-rows.json`: actual pinned-Go executions for every current
  nine fatal, 27 deadlock and four init-tagged panic rows. Thirty-nine yield
  strict single-marker observations. Exactly one refuses: the existing
  `sync/mutex-unlock-fatal/during-panic-unwind` PASS would become a
  `go-observation` refusal because its pre-dying panic/fatal output boundary
  is unauthenticated. The four init panics visibly lack registration and use
  the strict fallback. This is an oracle-only experiment, not fresh Go/Lean
  conformance and not promotion of any old baseline failure.
- `hybrid-challenges.json`: 15 actual Go tests (plain and race) cover the
  minimal printed-prefix/literal pair, every ASCII output byte plus Unicode,
  first-line markers, repanic, child panic, traceback lowering, hook disabling,
  init fallback/refusal, fatal unwind and setup/ack IO failures. Three
  corrupted/missing-channel controls refuse. Three compiled prototype
  mutations expose discarded output, choosing payload from raw stderr, and
  skipping suffix equality. These are prototype tests, not production-gate
  acceptance.
- `hook-source-boundary.json` preserves the three fresh frontend/model
  quarantine probes. `crash-channel-design-probes.json` preserves the actual
  missing fatal-message behavior and exact source hashes.

The source search found no public pre-dying output-separation mechanism in
this installed runtime: SetCrashOutput is gated on dying; `printBacklog` is
a private, lossy 512-byte circular buffer for core dumps; goroutine writebuf
diversion is private/test infrastructure. Patching runtime writes, reading
private Go runtime state, adding a tracer, or rewriting program print calls
would require separate designs/trust or fidelity arguments. This bounded
search is not an impossibility theorem.

## Decision ledger

| Alternative | Result and remaining obligations | Authority/disposition |
| --- | --- | --- |
| Keep the rejected raw/system classifier | Known forged payload and lost output pass | Rejected by independent review; cannot ship |
| Strict raw-only observer | Closes marker ambiguity but refuses ordinary repanic/multiline-marker payloads | Insufficient for the required O2 consumer; not proposed as completion |
| Same-run ordinary-panic channel plus strict fallback | Preserves required ordinary-panic strings; exposes the one measured sync-unwind apparatus limitation and unsupported init shapes | Recommended bounded K3 repair, pending independent design/implementation review and exact row disposition |
| Additional pre-dying tracing/runtime instrumentation | Could address broader fatal reporting; no faithful implementation established | Separate investigation; no new dependency/private-runtime assumption approved |

The selected diagnostic organization, directed by the parent after reading
this design, is a **separate oracle source copy** containing the same hook.
Their semantic frontend inputs remain the exact original sources. Triage
and Cedar currently reuse a directory for oracle and semantic inputs; their
runner must separate those directories before instrumentation. Standalone
membership sampling already consumes generated oracle wrappers. A shared
helper should parse the oracle copy, locate exactly one package-main entry,
insert the hook call at its opening brace, and add a separate helper file.
Missing/duplicate main, identifier collision or copy/setup failure is a named
apparatus failure. Preserve original source bytes except the explicit oracle
insertion, and preserve local-package resolution. The native differential
harness already separates oracle wrapper sources from semantic frontend
inputs. No blanket diagnostic-domain claim is made by this prototype.

Production acknowledgement handling must distinguish an empty file (a
possible init abort before registration) from malformed nonempty content
or an unreadable/missing file. The latter refuse rather than silently
selecting fallback. A paired successful observation requires successful
registration and an empty report; an init panic may explicitly use the
empty-ack/empty-report fallback. The runner resets both files before every
draw, and a failed reset cannot execute the subject with stale evidence.

Before any next full gate: independent review against the actual minimal
forgeries; production implementation with meaningful compiled mutations;
fresh focused Go/Lean observations and exact stage/cause record for the
sync-unwind limitation; runtime/statement audit updates as applicable. Any
later baseline reconciliation preserves the raw initial delta and cannot
turn a refused observation into conformance. The broad charter and B7/I1
can continue independently; this is a fidelity repair, not B7 zero-drift.
