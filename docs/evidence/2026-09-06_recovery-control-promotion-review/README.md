# Independent recovery control facade promotion review

[AGENT] `typed-preflight`, 2026-09-06 UTC. **Bounded PASS** for the four
promotion files in `promotion-source.sha256`, at parent `4a8a8ad1` with
control `f160d7ca` pending integration. This is a public-surface review;
the implementation's independent reviews remain `9e6c4234`/`ba930ba2`.

`compare.py` freshly verifies all 21 author inputs against the sealed
manifest: no semantic definition, theorem, test or dedicated gate changed.
The four promotion files and inspected claim ledger, together with those
inputs, are retained in `source.tar.gz` and `source-hashes.json`.

The facade imports `RecoverySuccessfulRuns`, whose closure retains the
earlier entry contracts. Its new prose matches the promoted statements:
actual admitted setup establishes `Inv`; arbitrary relational steps preserve
it; progress permits normal termination, a nonempty semantic abort, or a
successor. Typed readout and unchanged choices require an actual successful
driver run. Reachable control configurations have no print events. The
facade explicitly does not infer successful rendering, unconditional driver
classification, a functional result, or Iris resources from those claims.
The ledger retains arbitrary string bytes and equal repanic histories and
identifies renderer/terminal/fuel work as remaining obligations. The
promotion adds no typing or admission restriction.

All 102 required exports are distinct existing theorems. The Lean and
Python origin inventories agree; the shell freshly elaborates all 15 new
core modules and two new test/audit modules. Its four existing
core/admission prerequisites continue to be built by Lake. The post-import
audit still covers all imported GoLean/Tests and local declarations,
including unused/private/generated/trailing constants, accepts only the
classical trio and retains the constructive renderer/dependency checks.

All 19 previous compiled poisons are retained unchanged. Three additional
controls target the control grammar, invariant and trailing invariant test.
They must compile first, then fail the separate audit with the expected
forbidden-axiom marker; an elaboration failure is not counted as rejection.
The source fingerprint includes both added test modules and all GoLean
sources. No native or Iris dependency enters the public facade.

Fresh independent commands (both exit 0):

```sh
python3 docs/evidence/2026-09-06_recovery-control-promotion-review/compare.py
# From the parent, after its initial facade/test build completed:
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean ../typed-preflight/docs/evidence/2026-09-06_recovery-control-promotion-review/Probes.lean
```

The facade-only Lean probe resolves all 18 promoted contracts and reports
the axiom closures of actual setup, all-successor preservation, reachable
progress, successful readout and choice retention. Logs are retained. I
read the original statements and successful-run/terminal boundaries but did
not repeat the implementation review or run its full dedicated suite.

The parent's CI `43232` remained live at this source verdict. Fresh public
22-poison completion, affected native/spike gates and terminal CI status
remain the parent's integration obligations; this report does not assert
them passed or claim a new full differential.
