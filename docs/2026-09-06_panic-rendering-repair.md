# Valid UTF-8 and first-line panic rendering

Date: 2026-09-06 UTC. Lane: `typed-panic-rendering`, based on
`5158589a83df9e54f5763f684286d35acb6b5afa`. This is a separate K3 fidelity
repair under the [approved sprint charter](2026-09-05_typed-consumer-sprint-charter.md),
not completion of O2 or a new observation policy. Main is unchanged.

## Determined behavior and repair

The existing observer retains the first line after `panic: `
(`scripts/diff-coverage`, `panic_message`). The pinned Go 1.26.5 runtime
prints a payload before its recovered/repanicked suffix (`runtime/panic.go`,
`printpanics`, lines 734–757). String payloads use `printindented`
(`runtime/error.go`, lines 305–319), which inserts a tab after each newline.
Consequently a multiline payload's first line ends before the suffix. For
example, recovering `"first\nsecond"` and then panicking with `"other"`
observes `first`, not `first [recovered]`.

Local oracle source hashes (Go 1.26.5, linux/amd64):

- `runtime/panic.go`: `4951c11983710ee957881d230290aa8cb130a873d83c55c86a0e4c7ecd35d190`
- `runtime/error.go`: `138957e6d2a126af0d6b2d032466fbe2bc3c95bb57b058a00987e814b2385e1f`

`Machine.utf8StringAux?` reuses the total `decodeRuneAt` already used by
Go string range and conversion. U+FFFD with width one is its invalid-byte
sentinel; a valid encoding of U+FFFD has width three and is retained. The
offset strictly advances, with termination measured by remaining bytes.
The helper preserves newlines and refuses any invalid encoding.
`renderPanicHead` performs the existing payload/refusal and recovered-chain
checks, formats the suffix, then projects to the first line. Byte-prefix
projection is safe at the ASCII newline boundary; strict decoding remains
explicit rather than silently substituting a fallback value.

This keeps the new helpers constructive. The interface audit checks all
constants originating in `Machine` and the new test module, and separately
checks that the three decoder/projection helpers use at most `propext` and
`Quot.sound`. Compiled private-core and trailing-test poison controls were
added alongside the existing controls. The public correspondence layer's
existing classical-trio allowance is unchanged.

No transition constructor changed. Sequential and pool abort paths already
share `abortMsg`; their executable/relation correspondence rebuilds against
the same total helper. The executable driver still reports a visible refusal
when rendering is unavailable, and fuel and terminal checking keep their
existing order.

## Red-first regressions

All ten cases below ran against the unchanged base renderer before editing
runtime source. Every one reached Lean and failed at `lean-observation` with
`status=unsupported`, instead of the Go panic below. This is semantic red
evidence, not an emission/lowering failure. The `output-prefix` case retained
`before\n` even in its refused observation.

| Case (under `panic-recover/`) | Expected panic message | Before | After |
|---|---|---|---|
| `panic-newline-abort` | `first line` | FAIL / unsupported | PASS, strict |
| `panic-text/unicode-two` | `é` | FAIL / unsupported | PASS, strict |
| `panic-text/unicode-three` | `界` | FAIL / unsupported | PASS, strict |
| `panic-text/unicode-four` | `😀` | FAIL / unsupported | PASS, strict |
| `panic-text/unicode-mixed` | `aé界😀z` | FAIL / unsupported | PASS, strict |
| `panic-text/unicode-newline` | `é` | FAIL / unsupported | PASS, strict |
| `panic-text/trailing-newline` | `first` | FAIL / unsupported | PASS, strict |
| `panic-text/recovered-newline` | `first` | FAIL / unsupported | PASS, strict |
| `panic-text/recovered-unicode` | `é [recovered]` | FAIL / unsupported | PASS, strict |
| `panic-text/output-prefix` | `é`, with output `before\n` | FAIL / unsupported | PASS, strict |

`Tests/PanicRendering.lean` was also run before the runtime edit: its six
positive declarations were rejected by kernel computation as false. The
invalid-encoding and equal-repanic refusal controls passed on that base.
After the repair all eight declarations pass kernel checking, including
valid U+FFFD, empty/leading/trailing newline boundaries, runtime-error
strings, recovered suffix placement, and nine invalid-byte patterns.
Invalid bytes after a newline remain refused; no invalid-byte observer is
chosen by this repair.

The focused red run used `scripts/diff-one` on exactly the ten listed IDs;
the focused green run adds existing plain-defined-payload and recovered
forced-half controls. Commands use `GOLEAN_MEM_MAX=16G`,
`LEAN_NUM_THREADS=3`, `GOLEAN_COVERAGE_JOBS=2`, and `scripts/capped`.
The copied build cache belongs exclusively to this worktree.

## Scope correction and remaining O2 work

The earlier [design review](2026-09-05_typed-contract-design-review.md)
correctly identified equal-value repanic and invalid-byte rendering as gaps,
but overstated the need for a new user decision about boxing identity.
The existing [R-1 ruling](2026-08-20_w32-re-envelope-charter.md), lines 28–54,
already authorizes the rendering quotient: forced payload kind and control
flow remain exact, and the rendering requires a conforming member, a pinned
text, and case-level membership evidence. This is an existing ruling to
implement with an explicit observer/member contract, not automatically a
new semantic-policy request. See also `docs/raft-w43-log.md`, item 5.

This repair deliberately leaves that separate R-1 work unchanged: equal
repanic still refuses before projection, and Error/String-method rewrites
still refuse before projection. Invalid UTF-8 still cannot be represented
raw in the existing String-valued terminal message. Whether a conforming
escaped representation implements the existing ruling must be assessed in
that separate lane; this note does not assume that the ruling is absent.
None of these boundaries can be hidden by narrowing the O2 minimum profile.

The new concrete regressions are not a generic decoding theorem or an O2
safety proof. O2 still needs its declared admission/setup, preservation,
progress, readout and consumer contracts, including the remaining renderer
boundary. In particular, an arbitrary-string decoding round-trip lemma is
not supplied by these finite kernel examples.

An additional, separate observer defect was reproduced during this review:
valid UTF-8 control bytes are mishandled by the shell oracle path.
`panic("a\x00b\x01c")` emits first-line payload bytes `61 00 62 01 63` in
Go, and a kernel check confirms that the machine renderer preserves them.
Using the actual `json_string_literal` and `panic_message` functions from
`scripts/diff-coverage` with its command-substitution path drops NUL (Bash
prints an explicit warning) and leaves byte `01` unescaped, making invalid
JSON. The old ASCII renderer already accepted these bytes: this is an
existing harness defect, not introduced by UTF-8 decoding. Evidence is in
`control-bytes.go`, `ControlBytes.lean`, and `control-bytes-observer.json`
under the evidence directory. These are valid UTF-8, so the invalid-UTF-8
boundary does not cover this obligation. The shell-to-JSON transport needs
its own determined repair; this lane does not change the harness or weaken
the required O2 string profile.

## Validation and handoff

The full `scripts/capped scripts/ci --diff` run completed all **3607 cases:
3363 PASS / 244 FAIL**, at Go 1.26.5. Its raw baseline comparison contains
exactly the ten improvements above, with no other result/stage change or
missing case. The full table and metadata are retained in
[the evidence directory](evidence/2026-09-06_panic-rendering/README.md).
Full table SHA256:
`c06abc481699499275ddb1e6b2a4e720249499e59ac267c2fe81c27357f0fb32`.

The initial CI attempt also recorded missing gitignored `deps/go` and
`deps/goose` setup, before the differential started. The existing
`scripts/setup-deps --from /home/dev/projects/golean --only go,goose`
restored isolated checkouts at their unchanged pins; setup completed before
the corpus ran. Initial CI exited 1 for those early setup-dependent checks
and the expected baseline drift. Its full log is preserved rather than
relabeled as a green run. All 202 evaluation tests, the fresh full negative
corpus (394 rows), coherence build, dependency/poison audits and differential
harness self-tests passed in that run.

Only the ten established rows were reconciled in `baselines/native-full.tsv`.
The existing row order, stage-alternation declarations, corpus expectations,
toolchain and observation policy are unchanged. BUG-004 keeps its three
remaining R-1 failures open and records the multiline partial fix. The
baseline comparison now passes for all 3607 rows; the bug-index check also
passes, retaining its 14-entry unexplained-failure backlog.

As in the preceding BUG-103 repair, final ordinary `scripts/capped scripts/ci`
rechecks all standing gates against the same complete differential record.
The runtime, tests and fixture sources remain unchanged since the fresh
full run, verified by `source.SHA256SUMS`; no cached result is attributed to
changed runtime source. The record is explicitly a **dirty-worktree** record,
bound to those source hashes, not a clean commit certification or stable pin.
`--diff` retains the standing `tier=slow` cached-certificate policy; no fresh
`--slow` enumeration is claimed.

Final ordinary CI **passed, exit 0**, including the restored setup-dependent
checks, all 202 evaluation tests, the 394-row negative comparison and the
3607-row full differential comparison. Its report-only reconciliation found
two coverage-ledger arithmetic warnings introduced by the ten-row movement;
the ledger was then updated by exactly A7's retirement (queued reds 8→7),
and a fresh `tools/reconcile-records` run removed both warnings. Two unrelated
MEDIUM record findings remain: historical/off-pin Go-version citations and
the frontier table's pre-existing `=` case citation. No runtime, fixture or
test source changed in this record-only follow-up.

The independent implementation review **passed for this narrow repair**.
The primary integrator independently read the source and pinned Go printing
functions, then freshly kernel-checked five additional properties: all 128
ASCII byte decodes, nine Unicode boundary encodings, CR before newline,
NUL/SOH rendering, and invalid UTF-8 after newline. Three independent Go
byte probes cover CRLF/recovered suffix placement, control bytes and the
maximum scalar. The review/provenance is retained on the integration branch
under `docs/evidence/2026-09-06_panic-rendering-review/`; it is separate from
this author's evidence. No blocking finding remains in the narrow delta.

This lane is ready for internal feature integration. Generic decoder
correctness, the control-byte observer repair, and R-1/invalid-UTF-8 work
remain distinct O2 obligations. Main merge and push remain unauthorized.
