# Consumer-contract integration handoff

[AGENT], 2026-09-05. The user authorized landing the reviewed A2 customer,
integrating BUG-103, and continuing with the semantic interface and A3 lanes.
A2 landed on main at `700128f3`. BUG-103 is rebased and re-gated on that
tip and landed at `8ad8cfc8`. The experimental semantic interface subsequently
landed at `4919b05a`, after independent review and combined-tree gates.

The rebase's sole source conflict was two added lane handoffs. Both original
texts are preserved byte-for-byte as dated documents:

- A2: `docs/2026-09-05_iris-customer-handoff.md`.
- BUG-103: `docs/2026-09-05_bug103-array-conversion-handoff.md`.

Those documents describe their original lane state. Their pending-review and
pending-authorization statements are historical: both adversarial reviews
passed, and the user subsequently authorized this integration. Original
sealed evidence remains unchanged; its HANDOFF.md hash denotes the original
BUG-103 handoff, now preserved at the dated path above.

Integration disposition and fresh combined-tree gate evidence are recorded in
`docs/2026-09-05_bug103-integration.md`. Full differential: 3,598 cases,
3,353 PASS / 245 known FAIL, no result/stage drift; 394 negative oracle
checks and 202 eval checks pass. One slow-tier certificate remains cached.
The source-reviewed runtime/proof/customer bytes are unchanged by integration.
No push is authorized.

The current next-phase work adds the independently reviewed A3a checker,
exposed explicitly through `GoLean/Interface.lean`. It proves exactly index
structure, Boolean entry/argument validity and a whole-program syntax policy.
It is opt-in, does not restrict the interpreter/frontend, and does not prove
typing or refusal freedom. An admitted unbound-variable program is proved
to refuse; the test is a permanent record of that limitation. See
`docs/2026-09-05_a3-admission-handoff.md` and the master plan §7.4.1.

The first admission extension should add scoped variable/result typing and
a driver setup theorem, then cover A2's calls/captures/initialization/recovery.
B7/C1 and generic composition retain their separate contracts and gates.
The full Gate A and a stable consumer pin remain open.

Final combined-tree validation is complete: ordinary CI, the full admission
gate and both customer gates PASS. An independent integration review finds
no defect, and all four audits reject an isolated unused Admission axiom.
Exact source bindings, commands, fresh 1/1 + 3/3 differential results and
the cached full-corpus comparison scope are recorded in
`docs/evidence/2026-09-05_a3-integration/README.md`.
