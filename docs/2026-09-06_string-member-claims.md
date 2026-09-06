# R-1 string member claim ledger

[AGENT] typed-string-members, 2026-09-06. Candidate source and acceptance
obligations are fixed in the production review request. “Proved” below means
kernel-checked about the model. Independent production reviews `d59b4ab1`
and `75da9338` accept the exact 184-input v3 candidate; disposition `8e8bca46`
accepts the exact full-run baseline and ledger movement. Final gate status
is recorded in the evidence directory's `FINAL.md`. These claims do not
assert frontend correctness, exact gc
text equality, arbitrary-program safety, or a stable customer interface.

| Definition or theorem | Source | Domain, choices and resources | Claim and status |
| --- | --- | --- | --- |
| `PanicText.lfPrefix_valid`, `firstLine_bytes` | `GoLean/GoCore/PanicText.lean` | Any valid Lean UTF-8 String; no execution choices or fuel | The constructed text is exactly the byte prefix before LF. Proved constructively. |
| `decodeEscapedBytes_escapeAllBytes` | same | Every `GoString`, including invalid UTF-8 and NUL | Parsing the quoted fixed-width all-byte escape returns the complete original byte string. Proved. |
| `escapeAllBytes_injective` | same | Escape constructor only | Equal escape encodings identify the input bytes. Proved. This does not concern both renderer branches together. |
| `renderStringMember_bytes_or_escape` | `GoLean/GoCore/StringPanic.lean` | Every `GoString`; no soundness/completeness premise for the custom decoder | The selected member either byte-round-trips exactly or equals the reversible all-byte escape. Proved. |
| `renderPanicHead_string`, `abortMsg_string`, `abortMsg_string_total` | same | Actual boxed-string head; arbitrary bytes, recovered flag, state and tail | Explicit recovered suffix before first-LF projection; total string readout. Proved. No tail-equality or boxing-identity premise. |
| `stepFn_string_abort` | same | The actual `Config.abort?` identifies the supplied head/tail; head is a boxed string; every choice stream | The real selected transition returns the specified panic terminal. Proved. |
| `runConfig_string_abort` | same | Same actual abort premises; every choice stream; fuel `n + 1` | The real sequential driver consumes the abort step and returns that panic terminal. Proved. Zero fuel remains exhaustion. |
| `runProgramPoolWithAbortInts_erasure` and observer witnesses | Reviewed `GoLean/GoCore/AbortObservation.lean`, `RecoveryPoolObservation.lean`, `RecoveryProgramObservation.lean` | All actual driver inputs, fuel and choices; witness only when computed record exists | Instrumentation erases to the shipped pool/program/Ints driver; a record comes from the reached selected abort transition, with output/detector/choice facts and full boxed-string chain. Proved in independently reviewed dependency `04109912`, integrated through `414a2abe`. |
| `native-json-string-run` | `GoLean/CLI.lean` | Fresh lowered artifact and CLI arguments; optional independent O2 profile requirement | Reports only actual-driver chain data, admission result, supplied fuel/choices and ordinary observation. Source reviewed through the production request; six raw native cases and two zero-fuel erasures tested. The CLI itself is outside the total semantic core. |
| Fixed `golean-r1-explicit-string-v1` membership | `tools/string_member.py`, `tools/string_member_runner.py` | Exact source/wire/argument/toolchain binding; actual panic/exit/output; nonempty all-string actual chain; thirteen fresh controls | Eight complete exact comparisons and five real-abort member comparisons retain kind/bytes/recovery/order controls. Tested by nine fresh corpus rows and compiling mutation/refusal controls; independently accepted at exact v3. Pins cannot supply chain data or cached verdicts. |
| Typed versus broader evidence scope | Fixture and historical source arguments | Eight subjects independently O2-admitted on the identical lowered artifact; historical rethrow explicitly broader | Concrete tested admission/source/control distinction. The generic O2 admission-to-terminal theorem is the recovery terminal lane's pending integration obligation. No O2 theorem is inferred from a text pin. |

The facade exports the new string theorems. Its post-import audit checks
private, unused, generated and trailing declarations, enforces the existing
classical trio for the interface, and retains the stricter constructive
renderer boundary. The post-observer candidate gate passed with 128 required
exports, 15,113 local constants, and 28 compiled poison refusals. The
`rendered_text_does_not_identify_bytes` regression explicitly proves a
collision between valid direct text and an invalid-byte escape member.

The differential lower-bound evidence is concrete: all nine selected rows
passed with the thirteen controls, actual plain/race Go aborts, and the
default plus three strict model choice tapes. This does not exhaust Go
behaviors. The upper-bound argument is the independently reviewed R-1
rendering policy plus the two source arguments, preserving the exact forced
fields. Their production reviews are accepted. The generic typed terminal
integration remains necessary before advertising the completed typed chain.
