> Historical prototype record, selected from `7ac3eb46bb3e2fe9c15b86b509569ef086327453`
> by [AGENT] 2026-09-08. Its validation describes that prototype only.
> Current scope, changes and fresh evidence: [I1 landing charter](2026-09-08_i1-declaration-landing-charter.md).
> Evidence paths below refer to the retained prototype branch; they are not
> copied into this landing. Production I1 integration remains outstanding.

# I1: preserve JSON identity before declaration decoding

[AGENT] root, 2026-09-06. Bounded companion to the positive declaration
foundation, based on integration `b34cee67`. Implementation and independent
review are in progress; this is not production I1 admission or marker removal.

The positive decoder consumes `Lean.Json`, whose object map has already
collapsed duplicate keys. Exact-key schema checking alone cannot reject
`{"kind":"basic","basic":"int","\u0062asic":"bool"}` before the last
value replaces the first. The pinned Lean string parser also replaces an
unpaired surrogate escape with U+FFFD. Identity-bearing input must not gain
an unrecorded replacement or silently discarded field at that boundary.

`GoLean.StrictJsonParse` checks decoded object keys before inserting them,
retains valid scalar/escape spellings, and refuses unpaired surrogate escapes.
`parseBytes` first checks UTF-8, so invalid input bytes cannot be replaced
before textual parsing. Explicit U+FFFD and valid surrogate pairs remain
accepted. Keys in different objects are independent, and Unicode normalization
is not performed: distinct decoded scalar sequences remain distinct keys.
Numbers and ordinary escapes use the pinned Lean parser primitives. The
container grammar and its upstream provenance are documented in the source.

The new `NativeDeclaration.decodeBytes` composes this input boundary with the
existing exact positive schema and nominal inventory checks. An enclosing
package decoder must validate the entire raw input before projecting fields;
strictly decoding a reserialized subobject would be too late. The fresh
Go declaration fixture reader now uses that same byte parser for its entire
document. Production `NativeToIR`/CLI is unchanged and does not yet call it.

The focused gate checks 12 valid JSON inputs, 16 named refusals, six malformed
documents, five invalid UTF-8 encodings, two independently stated decoded
scalars, the original duplicate-collapse witness, and the actual declaration
byte decoder's one positive/four negative controls. It also rechecks all
24 freshly emitted Go types and 576 go/types identity pairs. The declaration
audit covers the new parser and tests, including unused/private declarations;
six compiled injected axioms must be rejected. Recursive parsing is an
adapter implementation outside the total GoCore model, not a proved compiler
correctness or unbounded resource guarantee.

Next: independent review and ordinary CI, then integration into the full
function/method declaration envelope. Metadata-query preservation, checked
executable demand/guard closure, reserved runtime-error context and actual
refusal-marker removal remain mandatory I1 work. This boundary alone does
not discharge any of those obligations.
