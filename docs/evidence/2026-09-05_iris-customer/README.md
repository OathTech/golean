# A2 Iris customer evidence

[AGENT], 2026-09-05. Branch `gate-a2-iris`, based on
`8db2d6dad165393f4d3cdffee63b8e7d624f39e6`. This record validates the
bounded implementation; independent adversarial review and merge approval
remain owed. Main was unchanged throughout.

## Reproduction and result

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 \
  bash spikes/iris-customer/check
```

The command exited 0. `gate.log` is the complete final transcript:

- Core `lake build`: PASS (62 jobs; incremental).
- Separate package build: PASS; ten customer modules and the aggregate
  additionally elaborated freshly from source, in dependency order.
- Eighteen required exports present; transitive axioms of **941 constants**
  from the customer, complete A1 package and external audit environment
  checked against `propext`, `Classical.choice`, `Quot.sound` only.
- Three isolated poisoned-import regressions: trailing private axiom in
  `Audit`, private axiom in the aggregate, and a trailing private theorem
  using `sorry`. Each fixture compiled, then the external audit rejected it
  with exit 1 and the named forbidden axiom. These expected errors appear in
  the transcript; they are not failures in the delivered proof sources.
- Fresh native emission/lowering matched the complete derived representation
  of the artifact in `Program.lean`.
- Differential cases: **3 PASS / 0 FAIL**, native frontend, Go **go1.26.5**,
  default and harness invariance streams. Metadata reports `wide=0` and no
  exhausted choice depth on each case. The explicit manifest is a focused
  run; `full_run=unknown` in the generic metadata is not a full-corpus claim.

The source/dependency-manifest fingerprint printed by the final gate is
`defdc809abf9e1ecc019c25454e4a0993d0e85ce82b09e4fa6abac54d023b043`.
It covers the root semantic aggregate and source, A1 sources/configuration,
customer proofs/configuration/gate, source fixture, native emitter, and the
listed differential apparatus files. The exact inventory is in
`gate_checks.py`; this is not a claim to hash every repository file.
`package-sources.tsv` separately hashes every non-cache customer package file.

The fresh native wire's SHA256 is
`5a421bbd5aba27476017ad766a9fab6a1e43dff2de58c1043647428eb62eb197`.
`native-wire.json` preserves those bytes. The artifact comparison is a
regression check, not a proof that native lowering implements Go correctly.

## Evidence inventory and limits

`differential.tsv` and `differential.meta.tsv` are the harness's raw records.
The nine `*.oracle.*` files preserve the Go controls' stdout, stderr and split
error observations. `dependencies.tsv` records exact, tracked-clean pins.
`SHA256SUMS` seals this directory's artifacts; `package-sources.tsv` permits
checking the corresponding package sources from the repository root.

Lean is **4.32.2**, Linux x86_64 release, commit
`f3b06c705e6c85f5314019d5d3baab0fec5b580c`. Dependencies were independent
local copies of the pinned A1 checkouts; no shared writable symlinks were
used. Tracked upstream symlinks inside dependencies retain their original
form. A clean network installation and fresh elaboration of every upstream
dependency were not performed. Core and dependency build caches were reused;
the customer source elaborations and external axiom sweep were fresh.

The harness records the base commit and `git_dirty=true`: the new customer
was deliberately validated before its first commit. The source fingerprint
and per-file hashes identify what was checked. No runtime/frontend source or
semantics corpus baseline changed in this lane, so no full differential run
was warranted. The separately committed BUG-103 runtime lane has its own
full-run evidence; its counts do not belong to this customer gate.

These are kernel-checked facts about the current GoCore artifact, with
explicit bounds and premises in `Driver.lean` and `Readout.lean`. They do not
establish frontend correctness, full Go typing/admission, arbitrary
continuation composition, refusal freedom for an admitted language fragment,
or concurrent/labeled adequacy.
