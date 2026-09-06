# Total explicit-string panic members: implementation checkpoint

2026-09-06. [AGENT] typed-contract-review. Isolated branch
`typed-string-members`, base `4158368f5ab873bd9ed7785e98b9c9ecee94eb01`.
This is a working implementation checkpoint. Independent R-1 production
review, final full differential/CI and tracked integration of the reviewed
observer dependency remain acceptance obligations. Main is unchanged.

Dependency integration checkpoint after the client restart: the committed
root tip `414a2abe` was merged as `620489c9`. Before the merge, snapshot ref
`snapshot/typed-string-members-before-observer-414a2abe`, stash
`63593b8b4866fbadb4bf2882d6b3e5fee5be9964`, and a complete hashed archive
preserved all 77 working files. All 71 non-union files remained byte-identical,
including the three observer copies now supplied by their reviewed committed
dependency. Six interface/build/CI files retain both branches' requirements;
three text conflicts were resolved by that union. The source manifest and
draft-pin fingerprint changes are recorded separately. Production review
and final gates remain owed on this restored source; the generic typed
terminal bridge remains the recovery terminal lane's integration obligation.

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
positive fuel. Zero fuel still exhausts. The separately developed
actual-driver observer now retains the complete reached boxed-string chain,
including every entry's bytes and recovered flag. It proves all-input
erasure to the shipped pool/program/Ints driver and ties a computed record
to the actual abort query, selected transition, detector/output/choice
facts and final panic. Its frozen sources have independent bounded review
(ad961e41) and author commit 04109912. The local development copies are
byte-identical; tracked dependency integration is still owed. The generic
typed normal/panic/fuel bridge remains the runtime lane's integration
obligation. Neither a text pin nor a caller-provided payload certificate
can replace the actual witness.

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

The implemented apparatus is specified separately in
`2026-09-06_string-member-certificate-design.md`. It uses the same checked
crash view as ordinary observations, transporting the authenticated Go first
line as raw byte arrays. It preserves exact output and actual exit/kind,
checks all source/wire/pin bindings, and executes a finite thirteen-role
matrix afresh. Eight controls compare exactly; five real abort controls use
the same fixed R-1 member predicate and their exact kind/value companions.
The typed subject package and the broader control package are separate;
every original subject Go file is copied byte-for-byte into the latter.
The CLI obtains metadata only from the actual driver. Integer arguments are
not silently converted to Boolean, and the historical rethrow scope does
not claim O2 admission.

The first actual corpus-lane run passed all eight new typed subjects. Each
case emitted both whole native artifacts freshly, ran all thirteen controls,
captured plain and race-enabled Go executions and checked four actual
pool-driver witnesses (the default and the existing three strict tapes).
Raw records, the initial pins/source hashes, results and metadata are
retained in the dated evidence directory. This is bounded current-source
evidence, not full-corpus or final independent acceptance. The historical
rethrow draft pin has separately prepared fresh source/control evidence.

The next source-bound gates passed: the combined public interface checks
98 required exports and 13,924 imported local constants, with all 21
compiled private/trailing poison controls rejected. The apparatus gate
checks six raw-native/actual-driver cases, two zero-fuel CLI erasures, nine
compiling Go semantic mutations, four otherwise-valid capture/non-verdict
exit refusals, four compiling Go-helper mutations and five compiling Python
checker mutations. Earlier narrower and failed logs remain separate.
Ordinary observation equality is unchanged. The native-full conformance
baseline has not been repinned for this string change; the new member pins
remain draft acceptance inputs until review and the full gate.

Independent production review found an apparatus binding defect in the
first 178-input candidate: `Main.lean` and the `GoLean.lean` aggregator were
absent from the fixed inventory. Changing either executable entrypoint
therefore did not stale a member pin. That candidate and its unfinished
CI source-audit run are preserved; the run was terminated before changing
source and is not a full-corpus result. The narrow repair adds both fixed
paths, tests missing and changed bytes independently of the implementation's
inventory list, and compiles two omission mutants that must reach failing
source-binding assertions. The corrected inventory and draft fingerprint
refresh are a separate candidate, pending the independent reviewer's check.
