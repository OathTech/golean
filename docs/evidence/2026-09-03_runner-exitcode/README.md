# diff-coverage read comparator/oracle exit 2, 137, 143 as verdicts — red-first record (2026-09-03)

[AGENT] Lane-tooling fix slice, branch `runner-exitcode` off main @
784c313e (the `timeout-cause` landing). Discharges the residual that
slice's audit F1 recorded as OWED in `docs/operational-lessons.md`
("A killed command has decided nothing"). Consuming docs: that entry,
the fixture comment at `scripts/test-lane-validation` T5-T8, the
`undecided_cause` / `signal_cause` / `obs_eq` / `obs_eq_cause` comments
in `scripts/diff-coverage`, and the reporting convention in
`docs/coverage-suite-structure.md` (Reports).

## The defect (pre-fix `scripts/diff-coverage`, main @ 784c313e)

`run_with_timeout` maps a signal death to `128 + signal`;
`runObservationEq` (GoLean/CLI.lean) exits 2, decode message on
stderr, when it cannot decode an observation. Only 124 was named.
Every path was fail-CLOSED (none of these ever passed), but each read
a non-verdict code as a verdict:

| path | read exit 2 / 137 / 143 as | reported |
|---|---|---|
| every `obs_eq` caller (6 sites: Go-observation validity, confluent member, nondet invariance, Go-sample validity, coupling pin, sample loop) | "not equal" | `Go output is not a valid observation`, `enumerator/driver drift`, `varies with iteration order`, `copied-driver drift`, the too-narrow soundness alarm — and `>/dev/null 2>&1` discarded exit 2's decode message |
| the differential-stage `lean observation-eq` | "not equal" | `Lean=… Go=…` — a MISMATCH of two identical observations (T7 red row) |
| the strict Lean run (`native-json-run`) | an observation | `expected status ok, got ` (empty) |
| `go_run_oracle`, both consumers | a red program | `expected Go panic, got: ` (empty) / `status outside the declared set` |
| lake build, harness generation, both native exports, the three enumerators | a failure with an exit code | cause-blind detail (`enumerator failed (exit 137; …)`, an empty harness output) |

## The fix (cause-naming only)

No budget value, pass criterion, stage word, or baseline expectation
changes; `GoLean/` untouched (runObservationEq's codes are documented,
not changed). Three helpers classify the code BEFORE the capture is
read: `undecided_cause` (0/1 = verdict, the caller interprets; 124 =
`TIMED OUT after Ns (KNOB)`; 137/143/any 128+n = `KILLED (exit N — …;
did not decide)`; else `failed with exit N (did not decide)`),
`signal_cause` (the 128+n subset, n in 1..64, for the `go run
./tools/…` sites — `go run` collapses every child exit to 1, so 2..128
there is a tool refusal, not a kill — and the enumerator, which names
its code), and `obs_eq_cause` (adds exit 2 = `could not decode the
observation (exit 2 — did not decide; comparator said: <message>)`).
Exception (audit F1): at the two SELF-comparison sites exit 2 IS the
decision, so `Go output is not a valid observation` stays, now with
`(comparator said: <message>)`; T5 asserts that text (red on main,
which had the verdict without the message).
`obs_eq` now keeps the comparator's stderr in `OBS_EQ_STDERR` and the
differential stage goes through it. Every did-not-decide stays
`report_fail` at the same stage as before — never a pass, never a skip.

## Files changed

- `scripts/diff-coverage` — the helpers + every consumer.
- `scripts/test-lane-validation` — fixtures T5-T8 (Part B, `--with-go`);
  the shim's mode variable renamed `FAKE_GOLEAN_SLOW` → `FAKE_GOLEAN_MODE`.
- `scripts/ci:501-504` — the `--with-go` lane step's label names T5-T8
  (display only).
- `docs/operational-lessons.md` (residual discharged, second lesson),
  `docs/coverage-suite-structure.md` (Reports convention), this directory.

## Red-first fixtures

`scripts/test-lane-validation --with-go` T5-T8 reuse T1-T4's fake root
and `golean` shim: T5 forwards the comparator call to the REAL binary
with an undecodable status (a genuine exit 2 with its genuine decode
message, `left.status: unknown observation status "weird"`, asserted
with the accurate validity wording); T6
`kill -9`s the shim on the strict default-stream run (137); T7
`kill -TERM`s it on the differential-stage comparison (143); T8 adds a
fake `go` that `kill -9`s itself on the oracle's `go run … .` shape
only, on a baseline-PASS panic subject. The runner gains no override
knob.

- `red-main-runner.log` — the suite with main's runner (784c313e):
  T5-T8 FAIL with exactly the four wrong-cause texts above; exit 1.
  (T1-T4 green there: main already names 124.)
- `green-fixed-runner.log` — the suite with this branch's runner:
  T1-T8 ok (rows printed), every pre-existing fixture ok; exit 0.
  The FIRST post-fix run had T7 red: `obs_eq_cause` ended in
  `[[ -n "$stderr" ]] && printf`, so an empty capture (a SIGTERM leaves
  none) made the namer return 1 and the kill read as a verdict once
  more. Fixed with an explicit `return 0`; recorded as the second
  lesson in the operational-lessons entry.

Re-run: `scripts/test-lane-validation --with-go` (needs go on PATH and
the built `.lake/build/bin/golean`).
