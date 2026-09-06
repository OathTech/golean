# Source argument for the historical recovered-string rethrow

2026-09-06. Bounded broader-core source argument for independent review.
The subject is `panic-recover/repanic-same-value-abort`, whose original
`main.go` is copied byte-for-byte into
`Corpus/controls/string-members/historical/main.go`. The subject inventory
and freshly emitted whole artifact are bound separately from the complete
control package and its fresh artifact.

## Historical rethrow

`repanicSameValueAbort` starts with the explicit string value `orig` and
directly defers a closure whose `panic(recover())` recovers that value and
rethrows the same interface value. It has no imports, globals, initializers,
methods, concurrency or output operations. This source is outside the O2
literal-only panic grammar: its rethrow operand is a recovered interface.
The certificate therefore uses `reviewed-broader-string-control` and makes
no O2-admission claim. Its computed metadata must still come from the
actual shipped pool driver and identify the entire reached chain as boxed
strings. No arbitrary tail, Error/String-method effect or caller payload
sidecar is accepted on the strength of the head's type.

The exact `catchHistorical` companion calls the original function, recovers
in the outer handler, checks the dynamic string kind with a comma-ok
assertion and checks the entire byte value `orig`. A normal return leaves
its result false. `ControlDynamic` requires this check along with all
thirteen-role matrix companions in the explicit family. The original
`repanicSameValueForcedHalf` source remains an ordinary exact corpus row;
its Go `==` comparison checks value equality, not eface data identity.

The added `subjects.go` and `controls.go` provide the same explicit
equal/unequal/multiple panic, rethrow, computed-equal, direct/indirect
recovery, complete invalid-byte and defer-order challenges described in
`docs/2026-09-06_string-member-fixture-argument.md`. They are source-bound
broader-core controls. They do not replace the historical entry's original
definition or pretend that its whole original artifact is O2-admitted.
The five abort controls retain real panic/exit and actual whole-chain
evidence, exact model member pins and output, with exact kind/value/order
companions; the eight non-rendering controls compare exactly.

The model selects `orig [recovered]` as its conforming R-1 member from the
actual head bytes and recovered flag. gc may instead print its collapsed
`orig [recovered, repanicked]` member. The owned same-run crash channel
authenticates raw Go panic/report bytes and output without equating those
texts, inferring kind from text or weakening actual terminal/exit checks.
An ambiguous report, non-string actual chain, failed companion, changed
output or stale source/artifact remains a failed certificate. This is
concrete source/control evidence for this historical artifact, not a
generic safety theorem for the broader core.
