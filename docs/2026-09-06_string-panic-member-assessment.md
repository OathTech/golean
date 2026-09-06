# String panic members under the existing R-1 ruling

2026-09-06. [AGENT] typed-contract-review. Design assessment, not an
implementation or an O2 completion claim. Prepared while the separate
crash-channel observer design undergoes independent review.

## Authority and exact remaining problem

[R-1](2026-08-20_w32-re-envelope-charter.md), lines 28–58 and 328–370,
already authorizes conforming rendered-text members while retaining exact
panic occurrence, payload kind, recovery/repanic/abort control, deferred-call
order and exit. This ruling is to be implemented, not requested again.
The pinned Go specification's `Handling_panics` requires termination and an
error report including the panic argument's value, and specifies recovery's
returned value and control effects. It does not prescribe gc's textual
collapse or byte encoding. The proposal below is an application of that
existing rendering ruling to the required explicit-string domain; it does
not make recovered Go string bytes unspecified.

The current `renderPanicHead` returns `none` when a recovered first entry and
the following entry have structurally equal payloads. `renderPanicPayload`
also returns `none` for a boxed string whose byte array is not valid UTF-8.
Both prevent total readout over O2's required string domain. Merely excluding
equal strings, repeat panic, or invalid UTF-8 from admission would leave the
charter obligation unmet.

The historical `repanic-same-value-abort/forced-half` fixture is useful
evidence of recovery and Go value equality. Its comment and old log claim
that `r == orig` establishes the eface identity responsible for gc collapse;
that is incorrect. Go interface equality here compares the string values,
not the runtime data pointers. R-1 removes the need to reproduce that pointer
identity solely to choose the rendered text. The fixture should be described
accurately rather than credited with a stronger guarantee.

## A concrete total string member

A small, defensible choice is to preserve current valid-UTF-8 payload text
and always use ` [recovered]` for a recovered entry, independent of equality
with the next entry. Equal and unequal strings then follow the same total
rendering rule. This represents a recovered entry followed by another panic
without claiming gc's allocation-dependent collapse. Format the suffix
before the existing first-line projection, preserving the reviewed newline
behavior.

For a string that is not valid UTF-8, render a quoted sequence containing
one fixed-width `\xHH` escape for **every** byte. For example, bytes
`[0xff, 0x00, 0x5c, 0x0a]` have the member `"\xff\x00\x5c\x0a"`.
Escaping every byte in that branch avoids ambiguity between a literal
backslash and an encoded byte and preserves the entire value, including
newlines. The member consists of valid ASCII; a simple decoder has a
machine-checked round trip. This is a rendering choice under R-1, not UTF-8
replacement or a change to `GoString`, equality, recovery, storage or calls.
Its line projection can differ from gc for invalid strings; the row must be
marked as text membership rather than exact gc observation.

Minimum helper contracts, with names illustrative rather than promised API:

```lean
renderStringMember : GoString → String
decodeEscapedBytes : String → Option GoString
decodeEscapedBytes (escapeAllBytes s) = some s
renderStringMember_of_utf8 : utf8String? s.bytes = some t →
  renderStringMember s = t
renderStringHead_total : every chain payload is a boxed string →
  ∃ text, renderPanicHead state first rest = some text
```

The final theorem must use the actual string invariant and real terminal
readout. It must not introduce a premise that the renderer succeeds. The
recovered flag is still supplied by the semantics; the member rule must not
modify chain construction, which entry `recover` returns, or whether the
execution aborts.

There is one additional concrete Option seam: `firstPanicLine?` re-encodes
a Lean `String`, takes its byte prefix before LF, and runs `utf8String?`
again. Generic total readout therefore also needs a theorem that this
operation succeeds for every Lean string, or a reviewed total String-level
first-line projection with the required correspondence. Totalizing the
initial boxed-string renderer alone is insufficient. Likewise the final
`Terminal.panic` carries text, not a payload-kind tag: the forced-kind
argument must come from the actual preceding `Config.abort?` chain and its
typed invariant, not from guessing a type after reading terminal text.

## Raw oracle transport and a separate membership check

The repaired crash observer is a prerequisite: it supplies the same
execution's actual terminal kind, authenticated raw report and exact output
prefix. Its byte boundary must be established before any text decoding.
For invalid UTF-8, a dedicated raw panic record can encode the first report
line as an array of integers in `[0,255]`. The existing successful string
value observation already uses such arrays. Do not cast invalid bytes to a
Go string and pass them through `encoding/json`, which replaces them, and do
not put raw bytes through Bash substitution.

That record is transport evidence, not an inferred payload-kind certificate.
The text `panic: 42` alone cannot establish whether its payload was a string
or an integer. Nor does the first report line reconstruct a complete
multiline payload. Keep the complete raw report as evidence and compare the
forced half using the independent source/profile and semantic controls below.

Current `observation-eq` and finite `coverage-observations` compare concrete
JSON observations. A rendering envelope is not automatically the set of
oracle strings sampled from gc, and replacing every message by `"panic"`
inside those paths would hide both type and control mistakes. Implement an
explicit, opt-in string-rendering member check with these separate inputs:

1. The source-bound subject/profile and its forced-half evidence inventory.
2. Actual oracle terminal/exit evidence and exact program output from the
   checked byte view; raw message bytes are retained separately.
3. The machine's actual panic member and the exact pinned member string for
   this row. The pin is never substituted for the machine result.
4. The stated string-rendering envelope and its spec/R-1 rationale.

Acceptance requires all four checks. A changed machine pin is visible drift;
an actual fatal, successful return, unsupported state, fuel exhaustion,
missing terminal evidence, wrong payload kind, changed output or failed
control probe remains red. Ordinary rows retain their exact observer.
Membership means the pinned machine text is a conforming rendering; it does
not claim that gc emitted it or that every runtime trace was observed.

## Forced-half controls and proof obligations

Use complete native artifacts and direct kernel traces from the same
subject family. At minimum cover equal literal re-panic, rethrow of the
recovered string, separately computed equal strings, unequal strings,
multiple nested recover/repanic steps, recovery outside a handler, direct
versus indirect recovery, and invalid-byte literals both before and after
an embedded LF. Add an outer recovery variant that checks the dynamic
string kind and **every recovered byte**, together with an order-sensitive
result encoding which distinguishes skipped, duplicated or reordered defers.
The abort variant must independently reach a real panic terminal; an outer
recovery variant alone does not prove the original program aborts.
Rethrow and computed-string controls are broader existing-core/corpus
checks for BUG-004; they do not require extending O2's current explicit
string-literal panic grammar. Equal-literal recovered/repanic sequences
already expose the rendering gap within that grammar.

For generic O2, connect the admitted explicit-string panic grammar and the
proved runtime invariant to the actual terminal payload kind and recovery
readout. Runtime errors cannot be dismissed merely because explicit panic
syntax is string-valued: the invariant/progress proof must exclude them or
classify them correctly. The concrete controls are evidence for the frontend
and Go/model bridge, not a substitute for that generic theorem.

Mutation controls must fail for: replacing one byte by U+FFFD; dropping a
NUL; exchanging string and integer panic kinds; suppressing the final panic;
incorrect direct/indirect recover; reversing deferred calls; changing output;
accepting fatal as panic; accepting an arbitrary machine string without its
member pin; and treating refused raw JSON decoding as a membership success.

## Scope, decisions and provenance

Six standalone pinned-Go probes are retained in
`docs/evidence/2026-09-06_observer-classification/string-member-probes.json`,
with complete source, source hashes and raw descriptor hex. Equal literals
and rethrow of `recover()` print `orig [recovered, repanicked]`; a noinline
runtime concatenation producing the equal string prints `orig [recovered]`.
The invalid-byte report preserves raw `ff 00 5c` before its first LF, and
an invalid byte after LF does not appear on the first line. An outer recovery
after rethrow yields dynamic string kind and exact bytes
`[255, 0, 92, 10, 90]`, equal to the original value. These are native
source/report evidence, not fresh model conformance or checked-observer
acceptance. They demonstrate why complete semantic bytes and projected
rendered text need separate contracts.

No new user ruling appears necessary for the two string rendering choices:
they are concrete members of the already approved R-1 text envelope. The
implementation and forced-half checking contract still require independent
review. Error/String-method payloads are a different BUG-004 slice and are
outside O2's explicit-string profile; this proposal does not call those
methods at abort time or implicitly resolve their effects.

The crash-channel classifier's current known-unsound source must be repaired
and reviewed before this design consumes its output. The measured fatal
unwind limitation remains an apparatus refusal, not a string-profile
restriction. No code, baseline or observation policy changed in this note.

Read against worktree base `d0dbd469a1dff1249f41ed6f423f0414c9b690b0`:

| Reference | Exact revision or SHA-256 |
| --- | --- |
| Local Go reference repository | `c19862e5f8415b4f24b189d065ed739517c548ba` |
| `deps/go/doc/go_spec.html` | `e5806989624c1e9dd32bddaedd2f70a1dd208295cb6d0ff72b02625b2cd6f592` |
| R-1 charter | `55de04802059c063c0e0a6bb948f35129295bfe68c6ae3b4fe8db7b16f432270` |
| `docs/raft-w43-log.md` | `c29f6dcbb5818a8593c3232dc97d1735243ca07b3759a9fbbe0cdd8535988fb5` |
| `GoLean/GoCore/Machine.lean` | `4bafe367252e73068ec60b8933bbe49f383215643d6468015610afa66a5cb957` |
| `GoLean/GoCore/Value.lean` | `aeded44416b5f286fc12033922cfab35d43d46c7d45fb7c6e8ea106e9eab6f8e` |
| `GoLean/CLI.lean` | `5df0ac7c6b6902d23b997c3292d1d656e97fa9c12c424951d947dd1d4101825a` |
| Existing re-panic fixture `main.go` | `e12b6491142d3f694dcd8560c8356e707d1a855f5d85059210c81a9d976f16ab` |
| Installed Go 1.26.5 `runtime/panic.go` | `4951c11983710ee957881d230290aa8cb130a873d83c55c86a0e4c7ecd35d190` |
