# Total explicit-string panic members: implementation checkpoint

2026-09-06. [AGENT] typed-contract-review. Isolated branch
`typed-string-members`, base `4158368f5ab873bd9ed7785e98b9c9ecee94eb01`.
This is a core implementation and proof checkpoint. Independent review,
final full differential/CI, the explicit membership apparatus and the O2
whole-driver witness remain acceptance obligations. Main is unchanged.

The reviewed R-1 design authorizes two string-only changes: preserve decoded
UTF-8 text after an exact byte roundtrip check, otherwise render quoted fixed-width escapes for every byte; and
always append ` [recovered]` for a recovered boxed-string head before taking
the first line. Non-string equal-payload refusal remains unchanged. Payload
construction, Go string storage, recover, panic propagation and defer order
are untouched. Error/String-method rendering remains outside this slice.

The separately reviewed byte roundtrip guard removes reliance on an
unproved postcondition of the existing custom UTF-8 decoder. The generic
`renderStringMember_bytes_or_escape` theorem proves that every result is
either byte-exact text or the reversible escape member. A decoder defect
cannot silently replace or drop payload bytes. Pre-guard source hashes and
the passing 91-export/18-poison interface gate remain separate evidence.

`PanicText.lean` proves an LF prefix of valid UTF-8 is valid, using the
string's existing encoding witness. `firstLine` then constructs that exact
byte prefix as a String; its byte correspondence is definitional. The proof
does not use a fallback decoding assumption. The escape parser only accepts
the ASCII grammar and has a generic round trip for every `GoString`; its
encoding is injective within that escape grammar.

The first attempted character-based projection exposed a hidden
`Classical.choice` dependency through Lean's library UTF-8 decoder. The
post-import constructive-helper audit rejected it. Both that failed log
and the intermediate getD attempt are retained. The replacement constructs
the proven-valid byte prefix directly and parses escaped text via raw ASCII
bytes, keeping the established constructive machine-helper boundary.

`StringPanic.lean` gives exact `renderPanicHead_string` and `abortMsg_string`
equations, plus existential totality, from the actual head's boxed-string
value. The bytes, recovered flag, tail and choice stream are arbitrary.
`stepFn_string_abort` connects an actual `Config.abort?` result to the real
panic step; `runConfig_string_abort` gives the real driver outcome with
positive fuel. Zero fuel still exhausts. The runtime lane must connect its
reachable typed abort witness to these equations, retaining complete head
bytes and recovered flag in addition to kind. Neither a text pin nor a
caller-provided payload certificate can replace that witness.

The total renderer itself is intentionally **not** injective: a valid
literal can spell the quoted escape member of an invalid-byte string.
`rendered_text_does_not_identify_bytes` pins this concrete collision. The
round-trip theorem concerns `escapeAllBytes`, not every branch of the panic
renderer. This is another reason membership must retain actual preterminal
bytes and must not infer semantic payload identity from terminal text.

The source-bound red experiment freshly elaborates the base Machine in a
private copied cache and kernel-proves its three old refusals: invalid byte
before LF, invalid byte after LF, and recovered equal-string repanic. The
new tests prove the corresponding explicit members, generic byte round trip,
malformed escape rejection, non-string boundary, actual positive-fuel abort
and zero-fuel exhaustion. Full payload bytes after LF remain significant even
when gc's first report line would hide them.

The public facade and interface gate import the new helpers/proofs/tests,
require their theorem inventory and audit all imported local declarations.
New private helper/proof axioms and a trailing test sorry are compilation
controls that must be rejected by the post-import audit. Semantic coherence
modules are rebuilt against the changed shared renderer. These checks do
not substitute for full conformance under the explicit R-1 membership lane.

The apparatus schema is proposed separately in
`2026-09-06_string-member-certificate-design.md`. Ordinary observation
equality remains untouched at this checkpoint. No baseline has been repinned
for the string change, and no incomplete O2 acceptance is claimed.
