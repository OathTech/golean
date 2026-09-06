# Independent production observer repair review

2026-09-06, typed-preflight. **Bounded implementation PASS.** No blocking finding
in the frozen helper, native differential runner wiring, or diagnostic-copy API.
This supersedes the earlier CHANGES REQUIRED finding for these new source bytes;
it does not retroactively approve the rejected classifier or its interrupted CI.
Full differential/CI reconciliation and diagnostic runner wiring remain owed.

The candidate is the author's uncommitted delta over `d0dbd469`. The supplied
16-file manifest is copied as `candidate-sources.json`; `complete-helper-sources.json`
and `helper-source.tar.gz` bind every helper Go file used in my fresh private build.
The candidate hashes matched before and after independent probes. Source review
also covered the current design/repair ledger, extracted strict/sampling test
logic, negative controls, and the native source/input separation.

The shared checked abort view validates paired acknowledgement/report evidence,
the entire byte-identical stderr suffix, and the first pinned runtime origin.
The panic payload comes from the owned report; output comes from the preceding
raw bytes. Strict fallback counts every marker, with no LF-TAB exemption. Expected
metadata can reject an observation but cannot authenticate its kind or payload.
Unknown or additional reports refuse. UTF8 validation precedes JSON encoding;
the raw actual-kind query is not a promise that a message can be represented.

I checked setup failure routing specifically. Reset failure returns a nonverdict
code before execution; both strict and sampling callers run `undecided_cause`
before reading any old capture as an observation. Runtime hook failure exits the
child with 78, which is named separately from panic/fatal results. Successful and
race output queries require valid registration and an empty report. No recovery
handler was added. Source input to nativefrontend remains the original corpus
directory; the crash helper only enters the Go oracle package.

The diagnostic-copy API locates main's actual opening brace using unadjusted AST
offsets, preserves all other copied Go source bytes, and refuses ambiguous main,
reserved-name collisions, or reuse of an output directory. It is a supported Go
package copier, not a general build-system/resource-file equivalence theorem.
The frozen source does not yet wire the diagnostic scripts to that API.

## Independent executable evidence

`python3 docs/evidence/2026-09-06_observer-hybrid-production-review/probe.py`
exited 0 (`probe.log`) using Go 1.26.5, own worktree Go cache, and unique scratch.
The helper was freshly built from the archived source copy; author sources were
read-only. Nine actual Go programs use the production `--copy-oracle` hook,
including two race-instrumented executions:

- Six byte-exact observations: minimal printed-prefix/literal pair, control-byte
  and Unicode output, a printed positive runtime frame, glued output, and marker
  payloads with CR. All three production kind/message/output queries agree.
- A forged init report and fatal during panic unwind refuse all abort queries.
- Invalid UTF8 cannot become a JSON message; the raw kind query may still identify
  panic. This is an explicitly unfinished representation obligation, not R-1
  completion or a conformance pass.

Ten additional protocol controls pass: unpaired and missing files, absent or
malformed acknowledgement, changed suffix/content, exact success output, missing
success acknowledgement, stale crash evidence on success, and reused copy output.
For every native case, original semantic source stayed byte-identical and removing
exactly the one hook insertion restored the original oracle main source. Raw
stdout, stderr, crash and acknowledgement bytes and CLI results are retained in
`results.json`. The three success controls use constructed descriptor files and
are protocol tests, not additional actual native successful executions.

The author's source-bound gate records 47 extracted controls, 28 native controls,
two setup failures, and 11 compiled mutation failures, ending PASS. I inspected
the controls and final log without rerunning that complete gate. The focused
Go/Lean TSV records 23 rows: 22 PASS and the one explicit refusal below. These
author results are copied/hash-bound as supporting evidence, not labeled as my
fresh full conformance run.

## Exact justified refusal and remaining scope

`sync/mutex-unlock-fatal/during-panic-unwind` moves from PASS/stage `-` to
FAIL/`go-observation`: `ambiguous fatal message/output before m.dying`. My actual
native control confirms the cause. The prior apparatus's terminal/output
ambiguity and the runtime crash-copy activation point justify exposing this lost
authenticated observation under K3. The disposition remains the reviewed one in
`ab2ad4d5`: no GoCore semantic or O2 admission narrowing, no observation-policy
change, and no counting refusal as conformance. This repair is separate from B7
representation equivalence. Fresh full evidence must report every resulting
status/stage change before narrowly justified baseline reconciliation.

The runner-owned file/configuration assumption remains explicit: matching
caller-forged files are not cryptographically authenticated. This review makes no
claim for unsupported file/fd manipulation, hook overrides, arbitrary runtime
versions, resource observations, or every possible fatal report. Unknown report
shapes remain named refusals. Production diagnostic wiring and its corresponding
source-preservation/observation probes require their own review.
