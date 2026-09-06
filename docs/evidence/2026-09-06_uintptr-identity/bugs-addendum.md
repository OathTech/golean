
## BUG-107 — uintptr is lowered as uint64, merging distinct Go type identities [fidelity; integer identity]

- Status: fixed in the isolated candidate; final integration and slow certification pending ([AGENT], 2026-09-06)
- Pinned-by: differential
- Cases: ints/uintptr-identity/assertions, ints/uintptr-identity/method-parameters, ints/uintptr-identity/method-results, ints/uintptr-identity/aggregate-identity, ints/uintptr-identity/map-keys, ints/uintptr-identity/direct-readout, ints/uintptr-identity/boxed-readout, ints/uintptr-identity/wrap

`NativeToIR.intKindOfName` mapped `uintptr` to `.uint64`. Equal widths do
not imply equal Go types: a fresh Go/native/model probe returned 8 in Go
and 15 in the model because cross-type assertions and method satisfaction
incorrectly succeeded. Five regression rows failed differentially; two
direct/boxed readout rows were refused by the old Go observer. The unsigned
wrapping control already passed. Raw red evidence precedes the repair.

The pinned specification's Numeric_types, Type_identity, Method_sets and
Type_assertions rules determine the repair: a distinct `IntKind.uintptr`,
whose unsigned width is `8 * Platform.wordBytes`. The pinned platform remains
64-bit. Atomic classification and both observation encodings preserve this
identity. Generic integer operations and the shared relational atomic plan
cover the new constructor; no evaluator-only semantic rule is introduced.

The focused native run passes all 48 identity/atomic rows. Independent review
adds eight Go/native/model checks, observation range/identity challenges and
ten kernel probes. The full differential run is 3,635 = 3,390 PASS / 245 FAIL:
exactly eight new PASS rows, no existing result or unapproved stage changes,
and no removals. All 3,851 source inputs and the 12 reviewed candidate inputs
were unchanged. The initial CI also refused a missing pinned `deps/goose`
checkout; that dependency has been restored, with a clean gate still owed.

This is a separate K3 fidelity repair, not B7 representation equivalence.
B7 must explicitly adopt the accepted repaired reference before comparison.
Source-bound records: `docs/2026-09-06_uintptr-identity-repair.md` and
`docs/evidence/2026-09-06_uintptr-identity/`.
