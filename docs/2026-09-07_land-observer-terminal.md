# Landing chunk L4 `land/observer-terminal` — the same-run crash-channel observer, the pinned terminal classifier, and the harness rework, on main (2026-09-07)

[AGENT] landing worker, lane `land-observer`, under the coordinator's brief
for decomposing `typed-consumer-sprint` (archive tip `7edc298f`, 96 commits
over main `47195683`) into reviewable chunks; plan of record
`docs/2026-09-07_typed-sprint-landing-plan.md` (§2.4 L4, §2.1 L2, §4 D4).
Inputs read in full: `CLAUDE.md`, `AGENTS.md`, the L2 note
`docs/2026-09-07_land-gate-tooling.md` (§3 the fixes, §6 the measurement that
moved this work out of L2), the prep branch's evidence
(`docs/evidence/2026-09-07_observer-terminal-prep/` ON THE PREP BRANCH — not
landed), auditor A's R6/R8/R9/R10 and §1, auditor B's R14 and landability row
5, the sprint's five observer design notes (landed, §1.4), and BUG-105/106 as
the sprint wrote them.

[USER] ruling (Mike, 2026-09-07, relayed by the [AGENT] coordinator — cite as
relayed): «The evidence blob should not land, and generally we should not
dump big evidence bundles on main (they can't be easily hosted on GH for
one). … We'll want to decompose and land in sane chunks that can be reviewed.
And where appropriate fix some of the issues, eg. the choice tape stuff».
[USER] direction for this chunk (relayed, same day): land in reviewable
chunks; fix where appropriate; DEFAULT for the open pre-`main` question is
"stay RED, fail-closed, each on a `Cases:` line with the cause written", the
named-exception option written into the BUG entry as the plan;
`sync/mutex-unlock-fatal/during-panic-unwind` PASS→FAIL on BUG-106's line.

Method: path selection — `git checkout prep/observer-terminal-harness --
<paths>` for the code (prep tip `b1407cc5`, parent main `47195683`; main
`90bc3e06` differs from `47195683` on these paths in NOTHING, verified
`git diff --stat 47195683 main -- <paths>` = `scripts/ci` only), `git checkout
typed-consumer-sprint -- <paths>` for the corpus rows and the design notes;
every hunk read; never a merge. Branch `land/observer-terminal` off main
`90bc3e06`, worktree `.claude/worktrees/land-observer`, ONE squashed landing
commit (sprint authorship credited in §8).

## 1. What landed

### 1.1 The harness (`tools/coverageharness/`, from the prep branch, byte-identical to `b1407cc5`)

| file | what |
|---|---|
| `crashhook.go` (new) | `copyOraclePackage` (`--copy-oracle`: a FRESH copy of a diagnostic tool's package with `_goleanSetupCrash();` spliced at `main`'s opening brace by byte offset — every other source byte preserved) and `crashHelperSource` (`zz_golean_crash.go`: opens `oracle.crash`, `debug.SetCrashOutput`, closes the fd, writes `oracle.registered`; any failure exits 78 BEFORE the subject) |
| `crashview.go` (new) | the one checked view every abort query shares: the channel is MANDATORY (A-R6); the report must be the byte-identical stderr suffix; the runtime chain-shape pin; the strict fatal rule (one `fatal error: ` at a line start, no `panic: ` before the authenticated trace); ok/race require a registered channel and an EMPTY report |
| `abortkind.go` (new) | the pinned first-frame classifier under `GOTRACEBACK=system` on go1.26.5 (`panic`@`panic.go:879` / `runtime.fatal`@`:1253` / `runtime.throw`@`:1229`; `runtime stack:` or the `gp=… m=… mp=…` header; unknown shapes refuse) |
| `observe.go` (new) | `--abort-message` (Go's JSON encoder on the actual first line), `--read-observation` (stdout validated: UTF-8 + one JSON value, returned UNCHANGED), `--abort-record` (`golean-raw-panic-v1`, byte arrays — landed UNWIRED, §1.6) |
| `main.go` | the modes above, `--crash-report`/`--crash-registered` (paired, required by every stderr-classifying query — a bare query is a usage error, exit 2), `--quote-file` (diagnostics only), the reserved-identifier/filename collision refusals, the hook as the generated wrapper's first statement |
| `split.go` | abort splitting moved into `crashview.go`; `splitNonAbortStderr` keeps ok/race; `outputLiteral` refuses invalid UTF-8; `abortTraceHeaderRe` accepts the default and the system header shapes |
| tests: `abortkind_test`, `abortrecord_test`, `crashhook_test`, `crashview_test`, `evidence_test`, `observe_test`, `split_test` | the sprint's fixtures, every one naming its runtime-written report; A-R6's `TestMissingRegistrationRefusedByName` / `TestNoEvidenceRefused` / `TestAbortWithoutCrashReportRefused`; the chain-shape pin's `TestSignalLineShape` |
| `hookinert_test.go` (NEW here, §4) | A-R9: the hook is inert on the OBSERVATION, on real pinned Go |

### 1.2 The runners (from the prep branch; one cosmetic edit here)

`scripts/diff-coverage`: `go_run_oracle` resets the two owned files before
EVERY plain/race draw (a failed reset is exit 78, never a run on stale
evidence), sets `GOTRACEBACK=system` (A-R10, provenanced: manifest lines
`go_traceback system`, `go_crash_channel same-run-setcrashoutput-v1` — the
latter's TAB indentation, auditor A's cosmetic, fixed here to two spaces), and
no longer prints the oracle's bytes: the strict, membership and confluent
paths classify the stderr FILE (`grep -aqF`), ask the harness for the kind
(`--abort-status`), the message (`--abort-message`) and the output
(`--split-stderr`), and read a green run's stdout through `--read-observation`;
`go_diagnostics` quotes each descriptor separately for the detail column.
A-R8: an `expected_reason` that is empty or contains LF/CR is a manifest
refusal, so the `grep -F` match is exact by construction. `scripts/
gotest-triage`, `scripts/membership-sampling`, `scripts/cedar-census`: the
three diagnostic oracle copies moved onto the same checked view (fresh
`--copy-oracle` package for triage/cedar; the semantic frontend input is never
the instrumented copy); triage's `.out` comparison now follows the pinned
`testdir_test.go:checkExpectedOutput` rule on raw bytes. `scripts/
test-lane-validation`: the synthetic successful draw writes the paired
evidence a registered real subject would.

### 1.3 The corpus rows (from the sprint tip)

`Corpus/coverage/exec/panic-recover/panic-controls/{cases.tsv,main.go}` (9
rows: NUL, SOH, TAB, CR, newline, recovered-newline, output-prefix,
output-ok, child-confluent) and `…/panic-markers/{cases.tsv,main.go}` (11
rows: forged `fatal error:` prefixes, fake traces, glued output, the
printed/literal continuation pair). Measured on main: 14 PASS, 6 red at the
MACHINE (§5) — not the "20 born PASS" the plan expected, because the plan
counted them at the sprint tip, where L3's renderer repair was already in.

### 1.4 Records

- The five sprint design notes, VERBATIM below a marked landing preface
  ([AGENT], dated, naming exactly where the landed code differs from the
  record — the mandatory channel, the chain-shape pin, the not-landed gate
  scripts, the archive-branch evidence): `docs/2026-09-06_observer-{crash-channel-design,
  terminal-classification-design,classifier-repair,controls-repair,diagnostic-tools}.md`.
- `docs/BUGS.md`: BUG-105 (fixed — transport), BUG-106 (open — the fatal-unwind
  boundary), BUG-107 (open — the pre-`main` abort; the named-exception plan
  written in), BUG-004's `Cases:` line +6 (§5); each new entry carries a
  MERGE-TRAIN NOTE on numbering.
- `docs/language-coverage-ledger.md`: the §8 head paragraph and movement §8x
  (lettered to leave §8w to L3's renderer movement; the train re-letters).
- `baselines/native-full.tsv`: the re-pin (§5).
- `docs/evidence/2026-09-07_land-observer-terminal/`: README, `moved-rows.tsv`
  (the six-row table), `ci-diff-tail.txt` (§7). Nothing else.

### 1.5 One additive gate step (NEW here, [AGENT])

`scripts/ci` gains `coverage-harness unit tests (go test -count=1
./tools/coverageharness)` between the lowerdiag step and the eval tests — the
same `step`/`ok`/`bad` shape as the frontend unit-test step, so it can only
add a red. Reason: this chunk lands 900 lines of observer code whose tests
`scripts/ci` otherwise never ran (the sprint's two Python gate scripts did,
and they do not land — §1.6); an untested trusted-surface-#2 component was
the worse outcome. `-count=1` because the inertness test execs the pinned
`go run`, whose effects the test cache cannot key.

### 1.6 What did NOT land, and why

| path(s) | disposition |
|---|---|
| `scripts/check-observer-controls.py`, `scripts/check-observer-tools.py` and their two `scripts/ci` steps (the L2 note assigned them here) | NOT landed. Both were written against the sprint's harness, whose empty-ack/empty-report state fell through to a raw fallback. Under the mandatory channel (A-R6, the prep branch) they fail by construction, not by a bug they would catch: in `check-observer-controls.py` the shell probes `ambiguous`, `invalid-utf8-panic`, `fatal-continuation`, `sync-fatal`, `fatal-not-panic`, `mixed-unknown` (synthetic `crash` empty → the landed harness answers `runtime wrote no crash report`, not the expected text), the native probes `init-simple`/`init-forgery`/`init-literal` (expect a classified init panic / `ambiguous`; landed: `no hook registration acknowledgement`) and `disabled-hook-simple`/`disabled-hook-forgery` (expect a fallback verdict), and the mutation anchors `missing-ack` and `missing-success-ack` name lines that no longer exist in `crashview.go`; in `check-observer-tools.py` the string-expected probes with an empty synthetic report (`invalid-utf8`, `glued-prefix`, `printed-origin`, `unknown-origin`, `fatal-unwind`) hit the same `no crash report` refusal first. Re-cutting them is authoring new probe expectations for the R6-uniform contract — a follow-up chunk (`land/observer-gate-scripts`), not a hunk review. Until then the harness's Go tests are the gate (§1.5); the shell-level probes those scripts add (fake oracle through the REAL exported `diff-coverage` functions; compiled mutants) are owed. |
| the `string-member` vocabulary of `scripts/diff-coverage` (lane line, manifest block, `tools/string_member_runner.py` dispatch, the `expected_reason == "-"` exemption), `scripts/coverage-manifest`/`coverage-baseline-diff` hunks | L3's; the prep branch already carried none of it (`grep -i string.member` over the landed code paths hits only the `observe.go` comment naming `--abort-record`'s consumer) |
| `Corpus/controls/` | the brief said "minus `string-members`"; on the sprint tip `Corpus/controls/` contains ONLY `string-members/` and main has no `Corpus/controls/` at all — the set is empty |
| `docs/evidence/2026-09-06_observer-*`, `docs/evidence/2026-09-07_observer-terminal-prep/` | archive branch / prep branch; the design notes' links to them dangle (stated in each preface) |
| `--abort-record` (`observe.go`, `abortrecord_test.go`) | LANDED but UNWIRED: no landed script calls it; its only consumer is L3's `string_member_runner.py`. Unit-tested (`TestRawPanicRecordEveryByte`), refuses without the channel, emits `golean-raw-panic-v1`, never a `golean-observation-v1` value. Disclosed so L3 does not re-land it. |

## 2. Observation-schema compatibility (REQUIRED)

**What the observation carries now vs main.** The observation schema is
UNCHANGED: `golean-observation-v1`, fields `schema`, `status`, `message`,
`output`, `values`, in the same key order (the runner still assembles the
abort observation by string splice, `{"message":<lit>,"schema":…,"status":…}`
+ `attach_output`). What changed is HOW two strings are produced: (a) the
panic/fatal `message` literal is Go's `encoding/json` on the actual first
report line instead of a Bash hand-escape — for every payload the old path
encoded correctly (printable, `\`, `"`, LF, CR, TAB) the bytes are identical,
and for NUL/SOH/other controls the old path produced a wrong or invalid
literal (BUG-105); (b) the program-output `output` literal is split at the
AUTHENTICATED report boundary instead of at a marker search. A green run's
`go_observation` is the stdout file's bytes (`--read-observation` validates
and returns them unchanged; previously `cat` through the same `$(…)`). The
run META (`latest.meta.tsv`) gains two additive lines, `go_traceback system`
and `go_crash_channel same-run-setcrashoutput-v1`; `scripts/ci` and
`coverage-baseline-diff` read named keys, so nothing that consumed the meta
changes meaning. The baseline TSV's columns (`result id stage`) are
unchanged; the two born families are the only new ids.

**Cached certified sets (`baselines/certified/*`).** Byte-compatible. Shown
two ways: (i) every data row of the one certified record on main
(`imported-goose__channel__google-search.certified.tsv`, 6 observations)
piped through `coverageharness --read-observation` and `cmp`-ed against its
input — `rows=6 byte-changed-or-refused=0`; (ii) the full gate's
CERTIFIED-CACHED path (§7) verifies the tier=slow row against its record
unchanged. `--read-observation` is NEW in this chunk (main had no such
mode); its contract is "validate, then return the bytes", so cached
observations compare byte-for-byte and an invalid stdout is a named refusal
instead of a comparator exit 2.

**The K=32/80 sampling rule and stage alternation.** Untouched:
`MEMBERSHIP_DRAWS=80`/`=32` and their selection are not in the diff (`git
diff main -- scripts/diff-coverage | grep MEMBERSHIP_DRAWS` hits only the
unchanged `export` context line); `membership_go_observation` changes only
HOW a draw is read (stderr file via `grep -aqF` + the harness; stdout via
`--read-observation`), not how many draws or which statuses are accepted —
its refusals are the classifier's, enumerated in §5. The baseline's one
alternation row (`channels/select-select/beside-loop
lean-observation|differential`) and its `# reason:` block survive the
re-pin: `scripts/check-alternation-survival git:HEAD:baselines/native-full.tsv
baselines/native-full.tsv` → 0.

**`GOTRACEBACK=system` changes the oracle's stderr for every aborting case —
only in the trace.** One before/after pair (`print("out\n"); panic("boom")`,
addresses elided):

```
default:  out⏎ panic: boom⏎ ⏎ goroutine 1 [running]:⏎ main.main()⏎ \t…/main.go:5 +0x…⏎ exit status 2
system:   out⏎ panic: boom⏎ ⏎ goroutine 1 gp=0x… m=0 mp=0x… [running]:⏎ panic({0x…?, 0x…?})⏎ \t/usr/local/go/src/runtime/panic.go:879 +0x… fp=0x… sp=0x… pc=0x…⏎ main.main()⏎ …
```

Every byte before the trace header — program output, the panic/fatal
message region — is identical; the split happens at the authenticated
report boundary, so the `output` field is unaffected. `hookinert_test.go`
(§4) pins the same fact for the HOOK across ok/panic/fatal/deadlock/unwind.

**Abort classification changed exactly as measured.** Six rows (the five
PASS→FAIL flips the brief names, plus one FAIL→FAIL stage change the brief
also names) — `docs/evidence/2026-09-07_land-observer-terminal/moved-rows.tsv`:

| row | main | now | cause | entry |
|---|---|---|---|---|
| `sync/mutex-unlock-fatal/during-panic-unwind` | PASS/- | FAIL/go-observation | `ambiguous fatal message/output before m.dying (1 panic/1 fatal markers precede the authenticated trace), refused` | BUG-106 |
| `init/init-panic` | PASS/- | FAIL/go-observation | `crash evidence: no hook registration acknowledgement — the oracle's _goleanSetupCrash never ran (the subject aborted before main's first statement, or the hook was not installed); an unauthenticated run is refused` | BUG-107 |
| `noodler/initpanic/panic` | PASS/- | FAIL/go-observation | same | BUG-107 |
| `noodler/initpanic/var-panic` | PASS/- | FAIL/go-observation | same | BUG-107 |
| `noodler/initpanic/deadlock` | PASS/- | FAIL/go-observation | same (`could not classify Go deadlock report: …`) | BUG-107 |
| `init/quarantined-var-panicking/sibling` | FAIL/frontend-export | FAIL/go-observation | same; the oracle side now refuses before frontend export is reached | BUG-107 |

Nothing else moved: the focused slice (76 rows) showed exactly these six
plus the 20 born ids; the full gate (§7) is the whole-corpus statement. The
prep branch had measured the same six over all 410 non-ok rows of main's
corpus (L2 note §6). The brief's hard stop ("any sixth moved row") was read
as "any moved row beyond these six named rows"; none appeared.

## 3. D4 — the observation policy this chunk asks the [USER] to ratify

Auditor B (R14) is right that this is a change to how trusted surface #2
classifies aborts, not a K3 apparatus repair adjudicable by the implementer.
Stated precisely, the policy the [USER] ratifies by signing off this chunk:

> **Authenticated crash observation.** An oracle abort is observed only from
> evidence the Go runtime itself wrote in the SAME execution: a
> `runtime/debug.SetCrashOutput` report installed as `main`'s first
> statement, acknowledged by a registration file, whose bytes are the exact
> suffix of the captured stderr and whose first runtime frame is the pinned
> `gopanic`/`fatal`/`throw` origin under `GOTRACEBACK=system` on go1.26.5.
> (a) For a runtime panic the report IS the panic chain, so message and
> program output are an exact partition — program output may contain any
> bytes, including `panic:`/`fatal error:` text and fake traces. (b) For a
> fatal/deadlock the runtime prints the message BEFORE `m.dying`, so the
> report holds only the trace; the message is admitted from the raw bytes
> under one strict rule — exactly one `fatal error: ` marker at a line
> start and no `panic: ` marker before the trace — and every other shape
> REFUSES (BUG-106). (c) An abort with no acknowledgement (pre-`main`) or no
> report (`os.Exit(2)`, a printed report) REFUSES (BUG-107). (d) A green or
> race run requires a registered channel and an EMPTY report. (e) A refusal
> is stage `go-observation`, never conformance, never a machine verdict.
> The oracle's environment adds `GOTRACEBACK=system` and the oracle program
> is rewritten before compilation by exactly the hook insertion, both
> recorded in every run's meta; the hook is inert on the observation (§4).

What the policy changes for existing PASS rows: exactly the five in §2 — every
one a classification main made from bytes the runtime did not authenticate.
No PASS row's MEANING changes otherwise: 3348 rows keep result and stage with
observations produced by the new path (the full gate is the check), the 6
red-first born rows are the machine's (§5). If the [USER] refuses the policy,
the re-cut is the byte-transport half alone (`d0dbd469`'s scope: file-based
descriptor reading + Go's JSON encoder, main's marker-search classifier
kept) and the five rows stay green — that re-cut was NOT built, because the
byte transport's own tests depend on the checked view and the direction of
the policy is the doctrine's (a visible red beats a classification from
unauthenticated bytes).

The [USER] may later rule the **named pre-`main` exception** (BUG-107's plan
paragraph): an empty acknowledgement + empty report + exit-2 trailer + a
pinned runtime trace positively identifies "aborted before `main`", and a
distinct, tested, self-naming path may then classify under the strict raw
rule. That flips the four `init`/`noodler` rows to PASS and `sibling` back
to its frontend-export red, with no other movement. Not built here: the
default the brief set is red, fail-closed.

## 4. A-R9 disposition — the oracle program is rewritten before compilation: KEPT, with an observation-level proof

The existing test `TestOracleCopyPreservesSemanticSources` proves the SOURCE
side only (the semantic input is untouched; the copy's edit is exactly the
insertion) — the L2 note said so plainly. The brief's condition for keeping
the splice was a test proving byte-inertness ON THE OBSERVATION, so one was
added: `tools/coverageharness/hookinert_test.go`.

- `TestCrashHookInertOnObservation`: five subjects (ok with control-byte
  output; panic with output and a multi-line payload; `sync` fatal; deadlock;
  BUG-106's fatal-during-unwind) go through the REAL harness generator
  (`run(config…)`); a second copy of each generated package replaces
  `zz_golean_crash.go` with `func _goleanSetupCrash() {}` — identical source
  layout, so even trace line numbers agree; both run under the pinned `go
  run` with the oracle's exact environment. Required byte-equal: exit
  status, stdout, and stderr up to the first trace header plus the `exit
  status 2` trailer (every byte the observer reads; the excluded trace
  frames carry per-run addresses and are never observed). Required
  DIFFERENT: the instrumented side's `oracle.registered` is `registered\n`
  and its `oracle.crash` is non-empty on every abort (empty on ok); the
  no-op side's files stay empty — so the two variants differ in the live
  hook alone. The hooked run's bytes also classify to the expected kind.
- `TestOracleCopyInertOnObservation`: the diagnostic tools' `--copy-oracle`
  splice against the PRISTINE package (no insertion at all): same
  byte-equalities, and the hooked run partitions `print("glued");
  panic("actual\x00\nsecond")` into output `glued` / message `actual\x00`.

Both pass on go1.26.5 (1.3 s warm). So: the splice is inert on the
observation by test, not only by construction, and it stays. Exit 78 remains
a setup sentinel (a subject legitimately exiting 78 is a red, not a wrong
answer). The splice's residual, stated plainly: it is NOT byte-inert on the
oracle BINARY (two extra source files, one extra call), only on what the
observer reads.

## 5. The re-pin, the `Cases:` lines and the ledger

Tally (awk over the data rows, the header's derivation line):
`3598 = 3353 PASS / 245 FAIL → 3618 = 3362 PASS / 256 FAIL`; 3353 − 5 + 14 =
3362; 245 + 5 + 6 = 256; 3598 + 20 = 3618. Twenty born rows inserted after
`panic-recover/panic-bool-abort` in manifest order (0 reorders, 0 removals);
six rows rewritten in place; the alternation row and its reason block
untouched. Re-pin done positionally from the focused measurement (a
regeneration from `latest.tsv` would have dropped the alternation) and
verified by `scripts/coverage-baseline-diff` (the 76 run rows match the new
baseline), `scripts/check-alternation-survival` (0), and the full gate (§7).

Every PASS→non-PASS flip is on a `Cases:` line: `during-panic-unwind` on
BUG-106; the four `init`/`noodler` rows (and the stage-changed `sibling`) on
BUG-107. The six red-first born rows are the MACHINE's, not the observer's:
`panic-controls/{newline,recovered-newline}` and `panic-markers/{mixed-line,
fake-trace,literal-continuation}` at lean-observation and
`panic-controls/child-confluent` at confluent, all with `panic abort rendering
for payload … (dynamic type string)` / `unsupported` — main's `asciiString?`
refuses an embedded LF (BUG-004 item 3, exactly `panic-newline-abort`'s red).
They are on BUG-004's `Cases:` line with a dated paragraph; L3's renderer
repair flips them and removes them. Their ORACLE side is decided by the new
observer (message `original`/`forged`/the control-byte first line; output
exact), which is what this chunk claims for them. BUG-105 (fixed) therefore
lists the six single-line transport controls, and says why the other three
are not on its line. `scripts/check-bugs.sh` → `ok (107 bug(s); pinned cases
behave as claimed)`; the untriaged ratchet is unchanged (coverage 10, latitude
4, wrong-answer 0 — `go-observation` is outside the fidelity filter, and the
six machine reds are declared on BUG-004).

Ledger: §8 head paragraph re-derived (frontier 137, design questions 9,
profound-reason pins 26 unchanged; (a)-queued 8 → 14 — six more item-3
witnesses; post-vintage 65 → 70 — the five apparatus refusals; `sibling` stays
in its bucket, its stage moved, its red did not: 137 + 9 + 26 + 14 + 70 =
256); movement §8x.

Numbering: BUG-105/106 are the sprint's numbers for the same two entries;
BUG-107 is new. Main tops at BUG-104; L3's worktree (`land-panic-text`) had
no BUGS.md edit when this chunk was cut, and the plan's D1 only SUGGESTED
107 for the held L5 — numbers are allocated at landing. Each entry carries a
MERGE-TRAIN NOTE; the train renumbers whichever chunk lands second.

## 6. Deviations from the plan, stated

- The plan's L4 expected "20 born rows, 0 flips" and "BUG-106 landed in L2";
  measured: 14/6 born and six moves here, because L2 measured the harness
  out (L2 note §6) and the plan counted the rows at the sprint tip.
- The plan's L4 compatibility point (2) said `--read-observation` "returns
  the harness JSON bytes unchanged (no re-encoding)" as if pre-existing; it is
  new in this chunk, with that contract.
- The two Python gate scripts the L2 note routed here did not land (§1.6);
  one Go-test ci step was added instead (§1.5). [AGENT] call, disclosed for
  the audit.
- `Corpus/controls` is empty for this chunk (§1.6).
- BUG-107 exists (the brief spoke of "the BUG entry" for the pre-`main`
  rows); a separate entry was chosen because the cause, the fix plan and the
  ruling it awaits differ from BUG-106's.

## 7. Gate

`GOLEAN_COVERAGE_JOBS=16 scripts/capped scripts/ci --diff` at the CLEAN
committed tip `8a71caf6` (kept reachable as
`refs/snapshots/land-observer-terminal-gated`): **RESULT: PASS**. Verbatim
lines (the whole block: `docs/evidence/2026-09-07_land-observer-terminal/ci-diff-tail.txt`):

```
  ok   bug-index cross-check
  ok   evidence-on-main size gate
  ok   coverage-harness unit tests
  ok   differential run completed (exit 1; failing-set judged by baseline diff)
  ok   lane-validation fixtures incl. harness half (F4/F6/B3-B5/G5/T1-T8/D1-D6)
  ok   negative baseline diff (no regression)
  ok   baseline diff FULL (3618/3618, no regression)
  ok   re-pin guard (5 PASS→non-PASS flip(s), all listed in BUGS.md Cases)
  note reconciler: 4 finding(s), 2 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
```

Run meta (`artifacts/coverage/latest.meta.tsv`, copied into the tail):
`git_commit 8a71caf62a7b5d75b32daf71673b704c5a0e0108`, `git_dirty false`,
`go_toolchain go1.26.5`, `go_drift_actual false`, `go_traceback system`,
`go_crash_channel same-run-setcrashoutput-v1`, `jobs 16`. Full-corpus tally
3362 PASS / 256 FAIL = the pin. The whole-corpus movement statement:
`scripts/coverage-baseline-diff --full --baseline <main 90bc3e06's pin>
artifacts/coverage/latest.tsv` lists EXACTLY the six rows of §2 and 20 NEW
ids — no other row moved (the brief's hard stop did not fire). Certified set:
`imported-goose/channel/google-search` PASS/membership, detail
`CERTIFIED-CACHED (certified 2026-09-05T17:57:01+00:00 …)`;
`baselines/certified/` byte-identical to main.

The reconciler's two HIGH findings at the tested tip were THIS chunk's own:
the §8 reds TABLE (frontier / design questions / (c) pins / (a)-queued /
post-vintage / total — the rows `tools/reconcile-records` parses) still
summed to 245; the §8 head paragraph and §8x had been updated, the table had
not. Fixed in the amend: (a)-queued 8 → 14, post-vintage 65 → 70, total 245
→ 256, each cell naming its rows. `tools/reconcile-records` at the amended
tip reports the two pre-existing MEDIUMs only (C13, historical Go-version
sites across nine docs; C5, FR-7's `=` citation) and 0 HIGH — both MEDIUMs
were on main before this chunk (the sprint's controls-repair note records the
same two as "unrelated pre-existing").

The amend (this commit) differs from the tested commit by exactly three
documentation files: the tail file, this note (§7, plus a §1.4 cross-reference
corrected §6 → §5), and the ledger table fix
(verify: `git diff refs/snapshots/land-observer-terminal-gated HEAD --stat`).
The gate was not re-run whole at the amended tip; the steps that read those
files were re-run there — `scripts/check-evidence-size` (PASS, 0 new),
`go test ./tools/lowerdiag` (it reads the ledger's FR/Q rows; ok), and
`tools/reconcile-records` (above).

Also run at the tip: `go test ./tools/coverageharness/... ./tools/nativefrontend/...
./tools/lowerdiag/...`, `go vet ./tools/coverageharness`, `gofmt -l` (clean),
`scripts/test-lane-validation` (fast half; the `--with-go` half runs inside
`ci --diff`), `scripts/check-bugs.sh`, `scripts/check-alternation-survival`.
No 5a: `tools/nativefrontend/wire.go` and `GoLean/NativeToIR.lean` are
byte-identical to main (`git diff --stat main -- …` empty); `GoLean/` is
untouched entirely.

## 8. Provenance

Squashed from `typed-consumer-sprint` (archive; `docs/ARCHIVE.md`) via
`prep/observer-terminal-harness` `b1407cc5` (the L2 worker's fixed cut:
A-R6 uniform, A-R8, the chain-shape pin). Sprint commits carried (authorship
theirs): `d0dbd469` Preserve valid control bytes in oracle observations;
`b5dd4076` Authenticate oracle panic observations with a same-run crash
channel; `2b679404` Use checked crash observations in diagnostic oracle
tools; `819182b5` (harness parts only — `--abort-record`). Sprint reviews
cited by the landed notes: `83c177c2` (byte transport), `0e3f7e20` (the
fatal-unwind finding), `80bf1251` (CHANGES REQUIRED on the system-only
candidate), `aafe225b`/`ab2ad4d5` (crash-channel design + row disposition),
`1bd2022b` (production review), `198aee9f` (lane self-test mocks),
`c5b83045`/`0333f0a1` (diagnostic tools). This chunk's own edits ([AGENT],
2026-09-07): `hookinert_test.go`; the `scripts/ci` step; the `diff-coverage`
TAB cosmetic; the five design-note prefaces; BUG-004's line and paragraph;
BUG-105/106/107; the ledger head + §8x + the §8 reds table (the amend); the
baseline header; this note and the evidence directory. Not merged, not pushed.
