# I1 declaration/admission design evidence

[AGENT], `typed-preflight`, 2026-09-06 UTC. See the
[bounded design assessment](../../2026-09-06_i1-admission-design.md).

The independent checker exactly reproduces all 696 entries in the parent's
census from the sealed preflight coverage archive, including complete wire
hashes and recursive marker paths/reasons. Counts: 522 recorded PASS cases
across 80 unique wire byte strings, and 174 FAIL cases. Every observed
marker is at a declaration boundary; none is a nested executable wire node.
This is not a claim that lowered GoCore contains no markers.

`syntactic-closure.json` additionally records an exploratory closure for
each of those 522 PASS entry points, including `$pkginit`. The scan follows
wire `func` references and expands interface anchors by method name, as
the existing initializer-quarantine checker does. Seventy cases reach
quarantined declarations syntactically; there are no missing referenced
IDs. This is not a verified dynamic call-target analysis, an admission
verdict or proof of unreachable code.

`check.py` re-reads the original sealed archive and asserts equality of all
marker and closure records. Its fresh run exited zero (`check.log`,
`check.exit`). It runs only Python data processing; no Lean/model build or
fresh differential run was needed or is claimed for this design review.

The archive retains 12 representative wire artifacts/case records and the
inspected lowering, semantic, emitter, shim, substitution and pinned-Go
reference sources. `provenance.json` binds them to exact source hashes and
records the parent source revision separately from the historical corpus
revision. The full census is from `10fefeb3`, never live CI scratch files.
`archive-members.sha256` and `archive-verification.json` record complete
member verification; `SHA256SUMS` seals the evidence files. The design note
hash is included in provenance.

No semantic source, baseline or dependency pin was edited. No constructor
removal, closure proof, accepted-program theorem or descriptor policy has
been implemented by this bounded assessment. Its conclusions do not waive
the no-PASS-regression requirement, the outstanding B7 capture gap, or any
separate descriptor gate.
