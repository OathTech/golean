# BUG-103 combined-tree integration evidence

[AGENT], 2026-09-05. Tested clean commit:
`8d8f54879328d748c15ac97178bcb2ccc7d7b81c`, the reviewed BUG-103 branch
rebased onto A2 main `700128f37c60740a370ec275ff6c6d1ca6bccdf3`.
Disposition and limitations: `docs/2026-09-05_bug103-integration.md`.

## Reproduction

From the integrated repository root:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped scripts/ci --diff
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 bash spikes/gate-a1/check
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 \
  bash spikes/iris-customer/check
```

Each command exited 0. The CI full differential used its default 32 jobs;
customer differential used two jobs. A1/A2 gates ran after CI's core/eval
build phase, overlapping the independent full differential measurement.
The customer uses its own result directory, preserving the full corpus record.

## Inventory

- `ci-diff.log` and `ci-diff.exit`: complete capped CI transcript and
  exit status; 202 eval checks, 3,598 full differential rows (3,353 PASS /
  245 known FAIL), 394 negative oracle PASS, unchanged baselines.
- `gate-a1.log` / `gate-a1.exit`: fresh elaborations, 12 exports /
  529 constant audit, three deliberately poisoned imports rejected.
- `iris-customer.log` / `iris-customer.exit`: fresh elaborations, 18
  exports / 941 constant audit, three poisons rejected, fresh artifact
  match and 3/3 differential PASS.
- `full.tsv`, `negative.tsv`, `customer.tsv` and their `.meta.tsv`
  companions: original published result bytes. Customer Go oracle streams
  are preserved as `{recovered,normal,uncaught}.oracle.*`.
- `source-bindings.json`: SHA256 inventory of 3,691 tracked inputs and
  their aggregate, with original/rebased/main commit provenance.
- `source-binding.log`: exact original handoff preservation and original
  70 semantic / 31 changed-file hash checks, including the explicitly
  relocated original BUG-103 handoff.
- `integration-review.log`: integration agent's conflict/source review,
  distinguished from the two already-completed independent source reviews.
- `full-delta.log`: no ID, result, or stage delta relative to original
  BUG-103 measurement; all current baseline stage alternatives honored.
- `SHA256SUMS`: seals every other file in this evidence directory.

Combined source-inventory fingerprint:
`4a749157d16ede7064e4c27ac755469e31748914a158b008c059cc0b2e2dc8b1`.
A1 gate fingerprint:
`b6a57c42fbcd673c4798403d2b6989dca6b84a0098498f44d7b272016a29f55c`.
A2 gate fingerprint:
`6707d1ffbdc094f78df828e7209bdf404ac25334c6d1fe43e71c4a033728874e`.
These inventories have different scopes, defined by their manifest/code;
they are not intended to be equal. The fresh native wire hash remains
`5a421bbd5aba27476017ad766a9fab6a1e43dff2de58c1043647428eb62eb197`.

## Limits

One slow-tier row uses its existing cached certificate, with fresh
sampling/coupling checks; no full slow-tier recertification is claimed.
Known corpus failures and the two existing report-only reconciliation
findings remain visible. Generic full-run metadata is `unknown`; CI's
explicit 3,598/3,598 membership comparison establishes measurement scope.

Dependency caches were copied independently, exact and tracked-clean pins
checked, and each spike module freshly elaborated. Clean network bootstrap
and fresh elaboration of every upstream dependency were not performed.
All original sealed implementation/review evidence remains unchanged.
