# Independent A2 review evidence

[AGENT] reviewer `iris_customer_adversarial`, 2026-09-05; preserved by the
coordinator. Reviewed source commit:
`2f0a5a0386c23f8ecf0514bb2e6588df9ba3cada`.
Verdict: **PASS for the bounded spike; no required code changes**.
Full report: `docs/2026-09-05_iris-customer-review.md`.

- `gate.log`: independent complete customer gate, exit 0. This reproduces
  the source fingerprint, 941-constant audit, three poison rejections, fresh
  native artifact match and all three differential cases.
- `Program.lean.txt`: isolated mutated artifact; the deferred store is
  `false`, while the normal-return control is unchanged.
- `Examples.lean.txt`: unchanged proof source used against the mutation.
- `mutated-program.log`: empty output from successful mutation compilation,
  exit 0.
- `mutated-examples.log`: expected exit 1 on the store's impossible
  false-to-true normalization obligation, at `Examples.lean:151`.
- `coordinator.log`: independent cross-branch baseline/provenance check and
  integration limits. No combined-tree execution is claimed.
- `mutate-handler.py`: the reviewer's reproducible equivalent of the isolated
  mutation setup. The recorded outputs above came from the original review
  invocation, not a second execution of this packaged script.

After the ordinary customer gate, reproduce the mutation from
`spikes/iris-customer`:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 ../../scripts/capped lake env python3 \
  ../../docs/evidence/2026-09-05_iris-customer-review/mutate-handler.py
```

It copies the compiled customer tree into unique scratch, overwrites only
the scratch `Program.olean`, then re-elaborates the unchanged examples with
that scratch directory first in `LEAN_PATH`. It checks that the mutation
compiles and the proof rejects it for the intended reason. Live source and
build outputs remain unchanged, and scratch is retained.

`SHA256SUMS` seals every artifact in this directory. The original implementation
evidence is preserved separately, without changing its historical hashes.
No fresh upstream dependency rebuild, clean network bootstrap, full Go
corpus run or concurrent adequacy claim is part of this review.
