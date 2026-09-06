# Boolean storage/setup validation, 2026-09-06

This evidence covers the bounded helper and audit increment on
`typed-consumer-sprint`, starting from `a392fab0`. It does not establish full
O1, O2 or B7/I1. The [claim ledger](../../2026-09-06_boolean-storage-setup.md)
states the public contracts and outstanding obligations.

The source was uncommitted during validation. `sources.sha256` binds the
actual source and gate inputs; reported HEAD/dirty metadata must not be
interpreted as a clean-commit certification. All required commands returned
exit 0. Main remains unchanged.

## Fresh checks

All commands use `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3` and run under
`scripts/capped`; the outer cap includes subprocesses and differential tails.
Pinned toolchains: Lean 4.32.2 and Go go1.26.5. Spike dependency manifests
retain the existing iris-lean commit `e7a0a43814c4f1154ca0c8049883ca56c2288b86`.

- `scripts/capped bash scripts/check-interface`: `interface-green.log`.
  Core/facade/test build and fresh elaboration passed. The post-import audit
  required 31 exported theorems and checked 11,832 project declarations by
  module origin. All six compiled negative controls were rejected: Trace,
  BooleanStore, BooleanSetup and facade private axioms; audit-module and
  runtime-test trailing forbidden proofs. The warnings inside poison fixtures
  are intentional evidence of audit rejection, not warnings in runtime code.
- `scripts/capped scripts/ci`: `ci.log`. Warning-free default `lake build`,
  interface/admission/Boolean typing gates, frontend pins, frontend and
  lowering-diagnostic Go tests, and all 202 interpreter eval tests passed.
  The two pre-existing report-only C13/C5 findings remain visible.
- `scripts/capped bash spikes/gate-a1/check`: `a1.log`. Fresh spike source
  elaboration, 12 required exports, 12,151 project/customer declarations and
  all three compiled poison controls passed.
- `scripts/capped bash spikes/iris-customer/check`: `a2.log`. Fresh spike
  source elaboration, 18 required exports, 12,562 project/customer declarations
  and all three compiled poison controls passed. Fresh emission/lowering
  matched the entire native A2 artifact; all three differential cases passed.
  `a2-latest.tsv` and `a2-latest.meta.tsv` retain exact result/provenance data.
  The fresh wire SHA256 is
  `5a421bbd5aba27476017ad766a9fab6a1e43dff2de58c1043647428eb62eb197`.

The new five kernel regressions cover hidden dangling bindings in outer and
same-scope positions, an address-bounded but ill-typed heap, actual native
argument setup for both Boolean inputs, and aliased readout. Generic proofs,
rather than these examples, supply the public helper claims.

## Explicit cached comparisons

Ordinary CI reused the completed fresh sprint preflight records at `10fefeb3`.
The four `cached-*` files preserve their original metadata. They contain 3598
executable cases (3353 PASS and 245 known FAIL) and 394 negative Go-oracle
cases. CI reports both records as stale relative to this lane's HEAD. These
are cached baseline comparisons, not a fresh full differential run of this
increment and not GoLean frontend-negative evidence. One preflight slow
certificate is explicitly cached in that record.

This increment changes semantic proof definitions, opt-in admission exposure
and audit coverage; it changes no existing interpreter/frontend execution.
The charter still requires fresh final runtime-source integration gates.

## Review status

The independent `typed_preflight` reviewer returned **PASS for this bounded
helper increment**, with no blocking defect. It compiled six fresh adversarial
kernel probes under the cap: A3a's unbound body still has successful zero-fuel
setup for arbitrary choices; duplicate result names allocate two cells but
alias the final pin; repeated reads and writes through those aliases retain
their real behavior. These challenge the distinction between typed storage
and control/ownership guarantees and agree with the ledger's stated limits.
The complete report and probes are sealed separately in
`../2026-09-06_boolean-helper-review/`.

This is not final integrated O1 acceptance. Exact generic initial value/
location equations and distinctness are a separate follow-on, still outside
this evidence's public source; structural preservation/progress is another
lane awaiting integration and final review.

## Reproduction and retained failures

From the sprint worktree, verify `sources.sha256` with `sha256sum -c`, then
run the commands above with the stated cap/thread variables. For ordinary
CI's cached mode, copy the four `cached-*` records to the corresponding
`artifacts/coverage/` paths without rewriting their metadata. Full
conformance uses the charter's `scripts/ci --diff` separately.

During iteration the runtime test needed a concrete scope argument and a
local recursion-depth option for the closed native-artifact reduction. An
initial direct execution of the mode-0644 gate script returned exit 126;
the canonical `bash scripts/check-interface` invocation above succeeded.
The retained worktree logs `artifacts/boolean-runtime/interface.log` and
`interface-bash.log` record the invocation/parse failures; no permission,
toolchain, memory-cap or semantic-policy change was made to pass the gate.
