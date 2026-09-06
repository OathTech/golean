# Source argument for the explicit string-member fixtures

2026-09-06. Implementation argument for independent review. This document
does not itself certify a run. Each issued certificate binds its exact hash,
the full subject and control source inventories, both complete fresh native
artifacts, the actual driver/witness sources and the executed control records.

## Explicit subject

The original package at
`Corpus/coverage/exec/panic-recover/string-members` contains only nullary
entries and the explicit-string recovery profile's constructs. All bodies,
including unused entries, go through the independent O2 checker. The copied
`main.go` in `Corpus/controls/string-members/explicit` is byte-identical.
The separate `controls.go` is broader-core concrete evidence: its type
assertions, string equality and integer order encoding are not advertised
as O2-admitted code.

`Equal`, `Unequal` and `Multiple` begin with the same `"orig"` string panic.
Their ordinary named deferred handlers each recover directly and raise an
explicit replacement string. Registration order determines the handler
order; the first/head panic bytes remain `orig`, with its recovered flag
true, while the tail records the actual replacement values and flags.
The computed pool witness identifies that entire reached chain and the
actual panic transition. Exact `catchEqual`, `catchUnequal` and
`catchMultiple` controls call these same entry definitions, then verify
the final active recovered value is a string with value `orig`, `next`, or
`third`, respectively. They return false if the subject returns normally.
`ControlDynamic` requires all three checks to succeed.

`InvalidBefore` and `InvalidAfter` raise respectively bytes
`ff 00 5c 0a 5a` and `61 0a ff`. Their companion controls call these actual
functions and use a comma-ok string assertion followed by Go string
equality with the complete literal. Go string equality compares the
complete byte value, including the NUL and bytes after LF. The controls
therefore cannot pass after UTF-8 replacement, NUL removal or first-line
truncation of the semantic value. `InvalidRecovered` combines the first
literal with `equalHandler`. Its paired `controlRecoveredBytes` checks
the first direct recovery's entire value before the same `orig` replacement,
then checks that the replacement remains an active string panic in the
outer handler. This paired control is an explicit source argument, not a
claim that its instrumented handler is byte-identical to `equalHandler`.

`Unicode` and `Controls` have direct companions calling the actual entries
and checking respectively the full Unicode literal and the NUL/SOH/TAB/CR/LF
literal. `ControlDynamic` also requires these checks and the recovered-byte
control. Thus an unrelated positive kind assertion cannot discharge the
matrix for an untested subject payload. The emitted whole-chain witness
is still needed to identify which actual payload/flag the model rendered;
the first line of Go's report supplies neither kind nor the bytes after LF.

## Finite forced-half matrix

The version-one matrix has thirteen distinct invocations. Eight are exact
Go/model observation comparisons. `ControlNormal` returns the same
nonpanic `Normal` entry result. `ControlDirect` can return true only after
a direct handler recovers an active panic. `ControlIndirect` first calls
`recover` through an ordinary nested function, then relies on the outer
direct handler to recover the still-active panic; turning the indirect
call into effective recovery changes its result. `ControlOrder` and
`ControlReversed` encode the two deferred operations as 21 and 12, so order,
skipping and duplication change the result. `ControlInvalidBefore` and
`ControlInvalidAfter` check the complete recovered byte sequences described
above. `ControlDynamic` combines the explicit kind/byte and replacement
checks; all must be true.

The other five invocations really abort: `Equal`, `Unequal`, `Multiple`,
`ControlRethrow` and `ControlComputed`. `ControlRethrow` panics with the
actual recovered interface. `ControlComputed` creates the equal string
through a noinline runtime concatenation before replacement panic. Their
outer companions `catchRethrow` and `catchComputed` check the exact string
value and are required by `ControlDynamic`. String value equality does
not establish interface data-pointer identity; that unavailable identity
is the C4 rendering latitude addressed by R-1.

Each abort control uses the same fixed R-1 member predicate as the subject:
actual panic and exit, exact program output, a complete actual boxed-string
chain, and the exact model text pin with its byte-preserving direct-or-escape
construction. Its raw Go report is retained without requiring gc to print
the selected model text. These five checks do not issue nested certificates
or waive the eight exact controls. None permits non-string tails or
Error/String-method effects based only on a string-valued head.

## Observation limit and claim

The same-execution owned crash report determines the Go message/output
partition. A refused report, fatal terminal, missing registration,
non-verdict process exit, unsupported model result, changed output or
stale source/artifact remains a failed certificate. Invalid payload bytes
travel in a raw integer-array record; they are never UTF-8-replaced.
Ordinary output remains under the existing UTF-8 output observation policy.

The selected model member formats a recovered suffix before taking the
first LF line. Direct text must round-trip to the entire semantic payload;
otherwise the all-byte quoted escape is reversible. Invalid bytes after LF
therefore remain represented by the escape even when gc's first line is
decodable. A successful certificate means this fixed R-1 rendering
membership plus the specified exact forced-half evidence. It is not a
claim of exact gc rendered-text equality or a proof that the differential
apparatus establishes all Go behaviors.
