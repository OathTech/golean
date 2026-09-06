# Recovery contract consumed through the semantic facade

[AGENT] Reconciled integration candidate, 2026-09-06. The shared customer was accepted at
`bd31dd5d` (implementation `10cd6e8f`, independent review `163d44ea`, attached
as `bd31dd5d`). The terminal worktree integrated that checkpoint at
`658fe3eb`, preserving the original shared 35-source author/review packet.
This increment adds the generic terminal contract and facade consumption.
The accepted renderer `819182b5898f565f2488d706ef160319453e2f1d` is merged at
`ccf826cbfefde651f1c75eee34579f43701b562d`; all four former temporary
renderer/test imports equal those committed bytes. Final author gates passed;
independent union acceptance remains pending. The original draft packet remains historical
evidence; the reconciled candidate is recorded in
`evidence/2026-09-06_recovery-facade-final/`.

`GoLean/Interface.lean` exposes the actual recovery setup and frame layout,
same-fuel singleton-pool and unchanged-choice bridges, and the generic typed
terminal/metadata contracts. The facade documents each contract's profile,
fuel, output and terminal boundary. It remains experimental and brings no
Iris or native frontend dependency into the semantic build.

Both customers now obtain admission, call layout, unwind and readout
contracts through that facade. The existing shared setup, allocation,
seven-form call rule, single-pointee ownership, functional WP proofs and
Iris adequacy arguments are unchanged. Five direct core imports were
replaced; the complete native artifacts retain their exact GoCore values.
An import change does not hide representation dependence: the adapter and
artifact constructor inventory remains in
`2026-09-06_recovery-facade-migration.md` and must migrate through B7.

The new customer module `GoLeanIris/Terminal.lean` has seven named theorems:

| Theorem | Evidence and guarantee |
|---|---|
| `observed_normal_of_program` | Combines the generic typed observer classification with the actual normal program result to derive `none` metadata. Its run premise analyzes a result; it does not supply the unconditional safety theorem. |
| `recovered_observed_all_choices` | Existing Iris-derived A2 result true at fuel 60, empty output and no abort metadata, for every supplied choice list. |
| `normal_observed_all_choices` | Same statement for A2's normal entry, using its existing independent Iris argument. |
| `shared_observed_all_choices` | Existing shared functional result `!b` at fuel 200, empty output and no metadata, for every Boolean input and choice list. |
| `uncaught_has_actual_record` | The semantic uncaught control at fuel 60 and empty initial choices has computed actual-pool metadata. Its selected member equals `customer panic`; actual source/transition provenance comes from the observer witness theorem. |
| `a2_entries_no_refusal` | All three admitted A2 entries exclude every model refusal at every fuel and choice list, including the legitimate uncaught-panic entry. |
| `shared_no_refusal` | The shared fixture excludes every model refusal for every Boolean input, fuel and choice list. |

No uncaught-panic Iris NotStuck theorem is introduced. The normal/recovered
results continue to require their existing functional proof and separately
checked fuel bound; admission supplies refusal freedom and classification,
not those functional results or a generic termination bound.

The customer gate inventories 24 customer modules, six local semantic
helpers and the aggregate, and its required theorem set grows from 136 to
143. The complete post-import origin audit and compiled poisons are retained
and extended for the new modules. The semantic interface gate adds the
terminal theorem/test inventory and poisons for the six promoted helpers;
ordinary CI also invokes the dedicated terminal gate. Final reported counts
come from the completed, dependency-reconciled runs: 143 customer exports and
15,605 audited declarations with 26 compiled poisons; 160 facade exports and
15,448 declarations with 35 compiled poisons. The dedicated terminal gate
checks 32 claims and five compiled poisons. Ordinary CI, all nine renderer
member rows, both complete native artifact comparisons and the eight
A2/shared native rows passed on the final 239-input manifest. Full corpus
records in ordinary CI are the explicitly reused accepted R1 3,635/394
records, with their original stale/dirty metadata retained.

The first draft customer build could not clone Iris because the network
proxy denied the connection. Exact clean pinned Iris, Batteries and Qq
trees were copied locally from the accepted shared worktree for both spike
packages; no revisions or source were changed. An initial copy dereferenced
two tracked Iris symlinks; those destination paths were restored from their
pinned Git objects before clean revision checks passed. All later copies
preserved symlinks. The copied dependency hashes/revisions and failed build
logs are retained in `artifacts/terminal/` for the final packet.

The former rendering test asserted invalid UTF-8 refusal and necessarily
fails against the new renderer. For draft compilation the renderer owner's
exact updated `Tests/PanicRendering.lean` was imported as a fourth temporary
renderer source with its hash and old source preserved. The renderer owner
confirmed this intentional regression update. All four imported files now
match the accepted renderer commit exactly; there is no remaining temporary
semantic source dependency.

The first facade customer gate exposed a build-artifact bug in the new
terminal gate: refreshing Lake's actual `.olean` without its `--setup` file
dropped package metadata. The later CLI C build consequently referred to an
initializer name that did not match the packaged object. The gate now passes
the actual per-module Lake setup file while freshly elaborating and replacing
the artifact. The affected interface artifact was preserved, then rebuilt.
The terminal gate and default CLI link passed after this repair. Semantic
theorem sources and all source-level claim statements were unchanged.
