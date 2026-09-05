# Semantic interface integrated-tree evidence

[AGENT], 2026-09-05. Tested commit `63172c7d5540a28e7d6a6d6761239c29ace2fa08`,
the independently reviewed interface change rebased without conflicts onto
A2 + BUG-103 main `8ad8cfc8`. Review source hashes remain unchanged.

`ci.log`, `gate-a1.log`, `iris-customer.log`: capped commands, each exit 0.
`customer.tsv` and `.meta.tsv`: fresh 3/3 native differential. `sources.tsv`
binds semantic/customer/check inputs at the tested tree; paths are relative
to the repository root. `SHA256SUMS` binds this evidence directory. The
final integration record changes only documentation and evidence.

Reproduce from the repository root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/gate-a1/check
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 bash spikes/iris-customer/check
```

CI: core build, 202 eval checks, interface audit (16 exports, 193 constants,
three named poison rejections) and unchanged recorded 3598/394 baselines.
The latter are explicitly cached results from BUG-103's fresh integration
measurement at `8d8f5487`; this proof-only relocation did not rerun the full
corpus or re-certify its one slow-tier row. Two existing report-only
reconciler findings remain. The A1 run began after CI's build/eval phases,
overlapping its remaining baseline/reconciler work; the A2 run followed A1.

A1 and A2 freshly elaborate their modules, check exact tracked-clean pins,
audit 529/941 constants and reject all three poison controls each. A2's
complete native lowering comparison and three differential controls pass.
Dependency caches are independent local copies; no clean network bootstrap
or full upstream re-elaboration is claimed. The independent source review
and its extra three-audit promoted-axiom probe are recorded separately in
`../2026-09-05_semantic-interface-review/`.
