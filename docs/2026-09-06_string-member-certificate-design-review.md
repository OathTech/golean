# Independent review: string member evidence and byte guard

[AGENT] root integrator, 2026-09-06. **Bounded design PASS**, following
the existing [R-1 ruling](2026-08-20_w32-re-envelope-charter.md) and the
[initial string design review](2026-09-06_string-member-design-review.md).
This approves implementation, not its completion or conformance acceptance.
The reviewed proposal is retained in the evidence directory below.

The proposed `string-member` lane distinguishes exact forced observations
from a particular rendered-text member. The fixed schema/envelope and exact
machine observation pin make the chosen member visible. Complete source and
wire inventories, fresh checked control records, and a code-defined role
matrix are appropriate prerequisites. Neither a success Boolean nor a
rendered first line establishes dynamic payload kind or the bytes after LF.
In particular, a valid literal can spell the escaped rendering of different
invalid bytes; the renderer is not injective.

Acceptance must consume full payload bytes and recovered status tied to the
actual model driver and its preterminal abort query. Naming a theorem in a
JSON document is insufficient: the extraction function needs a proved
connection to that actual execution. The runtime lane owns this connection;
the renderer lane owns abort-point equations and checked record transport.
The ordinary comparator still owns exact non-rendering control observations.
Missing, stale, duplicate or malformed records and refused/fatal/fuel outcomes
must fail, including when a source or role is re-labelled to look complete.
Historical broader-core rows require their explicitly weaker reviewed
source/control argument and cannot be advertised as generic O2 admission.

The proposed decoder guard is also within R-1: accept decoded text only when
its UTF-8 encoding equals the original Go bytes, otherwise use the proved
fixed-width all-byte escape member. Prove the generic disjunction that the
result is byte-exact text or that exact reversible escape. This removes
dependence on an unproved decoder postcondition from the rendering argument.
It neither repairs nor changes Go string storage or recovery values. Record
the pre-guard source and passed gate separately, and preserve known valid
UTF-8 behavior in the focused controls. Non-string policy is unchanged.

The concrete schema, mutation tests, actual driver witness, forced-half
fixtures, source fingerprints and fresh integration gates still require
implementation review. This design verdict does not waive any of them.

Review inputs and hashes:
`docs/evidence/2026-09-06_string-member-certificate-design-review/`.
