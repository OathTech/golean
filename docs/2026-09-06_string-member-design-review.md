# Independent string panic member design review

[AGENT] root integrator, 2026-09-06. **Bounded design PASS** for the
assessment hash `d9c97bb87b0308c67aa37baaa452616a1b037893740588dcfff3e7495d309a99`.
This is authority/design review; implementation, forced-half validation and
integration acceptance remain separate obligations.

I read the existing R-1 ruling and its per-row requirements, the pinned Go
specification's handling-panics text, and the actual `renderPanicPayload`,
`renderPanicHead`, `firstPanicLine?` and abort boundary. R-1 explicitly
permits conforming rendered-text members, while retaining exact panic
occurrence, payload kind, recover/repanic/abort control, defer order and
exit status. Applying it to boxed string payloads does not require a new
user decision. It does not change Go string value bytes or recovery values.

A uniform recovered suffix for the reviewed string domain avoids pretending
that Go value equality determines gc boxing identity. Keeping valid UTF-8
text and rendering every byte of an invalid-UTF8 value as fixed-width hex
escapes is a concrete text member, subject to the required decoder round
trip and byte-preserving source/observer evidence. It must not silently
change the policy for unrelated payload families.

The totality argument must reach the real driver. Closing the payload
renderer alone leaves the separate first-line UTF-8 projection seam.
Require either success of that actual operation or a proved correspondence
for a total replacement, then boxed-string chain to actual `abortMsg`
success. Kind evidence must come from the typed preterminal chain, not
the rendered string. The independent control review's generic
`abort_query_preserves_string_kind` supplies that structural seam; it is
not itself a completed rendering theorem.

The oracle must transport raw bytes before JSON/string decoding. Member
acceptance must separately check the source-bound forced-half inventory,
actual terminal/exit and exact program output, actual machine text against
its visible per-row pin, and the applicable envelope argument. A refused
or corrupted observation, changed kind/control/output, fatal, successful
return or fuel exhaustion cannot become a membership pass. Recovered
controls alone cannot establish that the corresponding abort variant
actually aborts. The invalid-byte-after-LF case needs an explicit delta:
its new fully escaped member may differ even where gc's old first line was
valid UTF-8.

I independently verified all six retained native source hashes and decoded
their raw reports. Equal literal and recovered-value rethrow have the gc
collapse suffix; a separately computed equal string does not. Invalid
bytes before LF remain `ff 00 5c`; bytes after LF are absent from the first
line. The outer recovery probe returns dynamic string kind and exact bytes
`[255,0,92,10,90]`. These are checks of retained native evidence, not new
model conformance runs. The historical claim that interface value equality
proves eface identity must be corrected in the eventual implementation.

Exact design, native evidence and source hashes are retained in
`docs/evidence/2026-09-06_string-member-design-review/`. The current
classifier's separately reviewed bounded source and its complete terminal
CI result remain prerequisites. The known fatal-unwind observation refusal
is neither an O2 profile restriction nor a string rendering member. No
baseline, semantic source or observation policy changes in this review.
