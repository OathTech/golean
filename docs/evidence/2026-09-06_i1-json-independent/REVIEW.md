# Independent I1 raw-JSON boundary review

[AGENT] `string_members`, 2026-09-06. **Bounded PASS; no implementation
blocker found** in the exact fourteen inputs of `candidate-source.json`
(SHA256 `9ddabb224392a84b5c64edcfb190e22c979464e7bf452460310c2e609ac08337`).
The writer and isolated reviewer copies still match every hash. Candidate
source bytes are copied under `source/`; the writer worktree was read-only.

The parser checks a decoded key against its current object before insertion.
Each nested object starts with a separate empty map, while its enclosing
object retains earlier keys. Surrogate escape handling admits the complete
valid pair range and refuses lone/reversed/malformed pairs. `parseBytes`
calls checked UTF-8 construction before parsing. The pinned Parsec `ws`
implementation admits exactly TAB, LF, CR and SPACE. Numeric values use the
pinned Lean JSON primitives; this review does not establish an unbounded
number, depth, input-size or resource guarantee for the recursive adapter.

Independent validation passed:

- 107 targeted inputs: 21 exact JSON tree/value comparisons (including long
  integer/decimal values, Unicode scalar limits, surrogate pairs, NUL and
  control escapes, separate object scopes and distinct normalization forms),
  13 decoded duplicate-key refusals, ten malformed UTF-8 refusals, and the
  remaining grammar/control/surrogate/whitespace refusals. Explicit VT, FF,
  NBSP, NEL, em-space, U+2028/U+2029 and U+3000 outside strings refuse;
  valid literal Unicode separators inside strings remain exact.
- The actual whole-document fixture reader accepts its freshly emitted
  24 Go types and 576 identity pairs, and refuses duplicate `schema`, escaped
  duplicate `schema`, and duplicate `types` documents before projection.
  The duplicated values are otherwise unchanged, so these controls exercise
  raw duplicate identity rather than a downstream type mismatch.
- The full focused declaration gate freshly elaborates its named modules,
  passes the original 47 checks and Go fixture, audits 1,712 declarations,
  and rejects all six compiled unused-axiom controls. An additional compiled
  private axiom in the imported `GoLean.StrictJson` helper is also rejected,
  checking a dependency outside the six original injection targets.

The API limits are directly demonstrated. An old parser can collapse the
duplicate basic-type object before `decode` sees it; it can also replace an
unpaired surrogate in a nominal ID and then satisfy a supplied U+FFFD
inventory entry. `decodeBytes` rejects those original inputs. Explicit
U+FFFD remains valid. Deliberately replacing invalid UTF-8 outside the
candidate likewise creates valid Strings that textual `parse` accepts;
the raw-byte API rejects the original bytes. These are the documented
boundaries of already-parsed values and already-created Strings, not a
claim that those APIs can recover lost provenance.

The independent harness initially used `String.fromUTF8!` for that last
control; this Lean API panics on invalid bytes. Its source and diagnostics
are preserved separately. The corrected harness uses explicitly generated
lossy companion files outside the candidate, and its final stderr is empty.
JSONL records are separated only at LF, preserving literal U+2028/U+2029.
Neither harness correction changed candidate source.

Source/gate closure is recorded in `source-closure.json`, including local
imports, the actual fixture driver and pinned Lean parser/UTF-8 primitives.
The post-import audit covers local parser/declaration/test constants,
including private and unused declarations. The small external fixture
wrapper is an exact reviewed alias to the tested reader. This is not a
general proof of JSON parser or compiler correctness.

Production CLI, NativeToIR and executable GoCore are unchanged. The new
byte decoder and strict whole-fixture reader are preparatory I1 plumbing;
they supply no source typing, executable-demand permission, body/layout,
runtime reflection or production marker-removal result. Full ordinary CI
and eventual production envelope/admission integration remain separately
owned gates. The root reported ordinary CI PASS; this review independently
ran only the bounded declaration and adversarial checks described above.

All Lean/Lake invocations used the 16 GiB cap and three threads; commands
also explicitly set two coverage workers. Unchanged dependency build
artifacts were copied into the isolated checkout before fresh named-module
elaboration. Binary poison artifacts remain in the recorded unique scratch;
their source, logs and hashes are retained here without committing binaries.
