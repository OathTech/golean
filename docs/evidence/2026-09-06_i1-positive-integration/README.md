# Positive declaration foundation integration

[AGENT], 2026-09-06. Reviewed feature `798e9c76` integrates into `414a2abe`.
The accepted serializer, total declaration identity algebra, strict parsed
wire decoder, fixture and audits retain their reviewed bytes. Only the
build/CI unions differ: the declaration library and gate are added while
every parent library and gate remains intact. Independent union review
`60f541c6` confirms this exact two-file difference and all 3,865 source hashes.

Ordinary capped CI completed with exit 0 (session 80248), including the new
declaration gate, actual Go identity fixture, malformed-wire controls,
dependency audit and compiled poison refusals. The original log is retained.
The full 3,627 executable records (3,382 PASS, 245 known FAIL) and 394
negative records are explicitly cached from the sealed observer integration.
The live records and original metadata were checked byte-identical. This
increment has no production declaration-channel caller, so shipped frontend
emission/lowering, interpreter and CLI behavior are unchanged. It is not a
fresh full differential or completed I1 claim.

The next I1 work remains exact function/method declaration envelopes,
metadata-query preservation, checked entry/argument executable closure,
removal of refusal markers, and the reserved runtime-error context fact.
Passing marker-bearing cases must retain their support. The separately
isolated uintptr identity repair must be accepted as a semantic correction
before any representation-equivalence claim crosses that change.

`source.json` binds the integration inputs; `reviewed-delta.json` and
`additive-union.patch` bind the union; `provenance.json` records gate and
cached scope. `SHA256SUMS` seals this evidence.
