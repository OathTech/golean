# Strict declaration input checkpoint

[AGENT], 2026-09-06. The fourteen inputs in `candidate-source.json` are
accepted after independent bounded review `8051028b`, imported here only
for its I1 packet. The earlier design note records the proposal state;
this checkpoint records its completed validation. No candidate source
changed during validation or review.

Ordinary CI job 85137 returned numerical exit 0. It includes a warning-free
default build, fresh declaration elaboration, 47 input checks, fresh Go
emission with 24 types/576 identity comparisons and 17 malformed declaration
controls, and a 1,712-declaration audit with six compiled poison rejections.
The independent review additionally checks 107 raw/text inputs, actual
whole-fixture duplicate fields, exact decoded values and another imported
helper poison. Its bounded PASS and failed harness attempt are preserved in
the adjacent `2026-09-06_i1-json-independent` packet.

The full 3,627 executable/394 negative records in ordinary CI are cached
and hash-bound in `ci-provenance.json`; this is not fresh full conformance.
`ci-completion.json` records the exact candidate revalidation and a
post-run 3,899-input reconstruction from the accepted parent inventory.
That reconstruction is not described as a pre-run full-input freeze.

Production CLI, NativeToIR and GoCore execution are unchanged. This provides
an input boundary for subsequent positive package declarations. It does not
complete executable admission, query preservation or refusal-marker removal.
No policy, source-typing or universal descriptor claim follows from parsing.
