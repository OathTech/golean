# Independent final integration review: A3 admission and semantic interface

[AGENT], 2026-09-05. **PASS: no introduced integration defects found; no required changes.**

Reviewed `.claude/worktrees/gate-a3-admission` at `7c5e297185724e38cba4734fcd37346174ce060a` plus the integration edits to the facade and three audits. Landed integration base: `4919b05a`. This is a bounded integration review, building on the separate independent A3 semantic review, not a replacement whole-project audit. The reviewer changed no live source, Git state, dependency source, or main checkout.

## Source and contract preservation

- All A3 checker, predicate, test, fixture and gate-tool files match the independent A3 review's source bindings exactly. Of that broader 123-file inventory, 118 match. The other five differences are fully accounted for: `Ops.lean`, `StateWf.lean` and `GoLean.lean` equal landed-main bytes; `lakefile.toml` and `scripts/ci` preserve all landed-main content plus precisely the AdmissionTests library and admission gate additions. Both InterfaceTests/AdmissionTests targets and both CI steps survive the rebase. The comparison is reproducible with `check-integration-bindings.py`.
- `GoLean/Interface.lean` imports Admission and accurately states its exact guarantee: `IndexStructure ∧ Entry ∧ BooleanSyntax`. Opt-in use, unchecked lexical/return/name/metadata/runtime-state properties, the admitted-unbound-variable refusal, and the fact that A2 is outside the Boolean profile are explicit. No interpreter/frontend admission enforcement was silently introduced.
- The facade's transitive local source import graph contains 20 modules with no Iris, GateA1, GoLeanIris or NativeToIR dependency. The core interface audit and its external harness include all three Admission origins; the A1 and A2 audits select those same origins. Their existing bridge/customer obligations remain required. The core interface audit also requires `checkBoolean_iff`, `admitted_index_bound` and `admitted_all_bodies`.
- The exact current integration inputs are bound in `integrated-source-bindings.json` (81 GoLean/proof/configuration/gate files). All hashes still match after validation. Documentation was finalized separately by the coordinator; this report binds the implementation and its stated limited contract.

## Fresh independent validation

All three gates ran sequentially after the coordinator released shared build ownership, with `GOLEAN_MEM_MAX=16G`, `LEAN_NUM_THREADS=3`, and every Lean invocation through `scripts/capped`.

| Gate | Result |
|---|---|
| `bash scripts/check-admission` | Exit 0, PASS. Six fresh elaborations; 14 required theorems, 375 constants, classical trio only; all three compiled poison controls rejected; fresh native artifact matches; one differential fixture passes |
| `bash spikes/gate-a1/check` | Exit 0, PASS. Every A1 module and aggregate freshly elaborated; 12 required exports, 862 constants, classical trio only; all three compiled poison controls rejected |
| `bash spikes/iris-customer/check` | Exit 0, PASS. Every customer module and aggregate freshly elaborated; 18 required exports, 1274 constants, classical trio only; all three compiled poison controls rejected; fresh native artifact matches; all three differential fixtures pass |

A1 source/dependency fingerprint: `b1ec2c92eeb7c122b491ef30257e3120ab726c4eb4282ae6104fe1dcd943b6d9`.
A2 source/dependency fingerprint: `c560db8217173ad3537ec17e6f358802502adfddf14bf5c36af4a0b308a2c564`.
Fresh A3 native wire SHA256: `b72ed5518a3b3928455da2f0839c30b29c15f01d85a8922ba6d785225df259af`.
Fresh A2 native wire SHA256: `5a421bbd5aba27476017ad766a9fab6a1e43dff2de58c1043647428eb62eb197`.

An additional isolated replacement of `GoLean/GoCore/Admission.lean` appended an unused private axiom named `reviewedIntegratedAdmissionHole`. The replacement compiled successfully (exit 0). The **Admission, semantic-interface, A1 and A2** external post-import audits each rejected that exact axiom by name (exit 1). This tests the newly integrated origin selection directly; fixture compilation failure is not counted as rejection. Reproducer and five individual logs are retained.

The coordinator's separately executed `.tmp/a3-integrated-ci.log` was inspected: ordinary CI PASS, semantic interface 19 exports / 526 constants and three compiled poison controls, admission 14 / 375, and 202 eval checks. The executable 3598-case and negative baseline comparisons are explicitly cached at `8d8f548`; they are not fresh full-corpus recertification. The reviewer did not repeat ordinary CI or the full corpus. The fresh independent differential measurements in this review are the A3 one-case and A2 three-case fixtures.

## Limits and disposition

Builds used existing worktree caches and exact pinned dependency checkouts; this is not a clean upstream/bootstrap elaboration claim. No new broad Go-verification, full typing, refusal-freedom, concurrent-adequacy or stable-pin guarantee follows from this integration. The semantic bridges and A2 proof chain continue to pass with the limited admission API present. A3b's stronger scoped typing/setup boundary and later support for A2 remain explicit next work.

Preserve the report, binding JSON/check logs, integration diff, import graph, gate logs, fixture result/metadata files and mutation reproducer/logs. The `integrated-admission-private/` subtree contains copied build artifacts and should not be tracked wholesale.
