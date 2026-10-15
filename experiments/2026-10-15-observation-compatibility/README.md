# O1 frozen observer compatibility

This client is outside the upstream default build. Permanent semantic exports
import no downstream module. It proves agreement with frozen logic
`f314a4f7ce69f8e5dc1c835298d4f1a2832a996f` (handoff `97426cab`) through the
`GoLean.Relational` facade. The implementation pin and validation are in
`docs/2026-10-15_relational-observation-stage.md`.

Use the private RD7 extraction/setup procedure in
`docs/2026-10-15-relational-integration-reproduction.md`, substituting the O1
implementation pin and `.tmp/o1-rd7`. Keep all original Lean sources unchanged.
Use independent exact dependency clones without alternates or writable cache
symlinks; source-verified compatible caches may be copied. The frozen package's
`setup.py` and four exact pins provide the dependency setup. Never build or repin
a peer worktree.

Copy `O1Compatibility.lean` into that private package and append to its private
`lakefile.toml`:

```toml
[[lean_lib]]
name = "O1Compatibility"
```

From the private package:

```sh
mkdir -p .tmp
export TMPDIR="$PWD/.tmp" LEAN_NUM_THREADS=2
capped lake update
capped -m 64G -- lake build GoLean RelationalCodeX O1Compatibility
capped lake env lean RelationalCodeX.lean
capped lake env lean O1Compatibility.lean
capped -m 64G -- lake env leanchecker --verbose GoLean RelationalCodeX \
  GoLeanIris GoLeanIrisExamples O1Compatibility Iris Batteries Qq
```

Require successful exits and standard axioms only. Compare the complete multiset
of `replaying NAME` lines to built `.olean` names under exactly these roots, in
the private package and four dependencies. Require an output for every source
module under the local and GoLean roots. For dependencies, check the built closure,
not unused source modules. The original aggregate audits all 6,058 local
declarations; the new client prints its two headline theorem axioms. Include its
helper declarations in the exhaustive new-client audit as well.

The inherited `Memory.lean:1625` warning and recorded live **35 NOT-PUBLIC** failure
remain visible. This is not a live gate or trust-artifact migration.

For original-package agreement, at frozen `f314a4f7` compare these ten complete
declaration bodies in `packages/golean-iris/GoLeanIris/Logic/Observation.lean`
and `experiments/2026-10-14_relational-codex/GoLeanIris/Logic/Observation.lean`:
`callEntry?`, `Enters`, `entered?`, `frameExit?`, `exitValues`, `returnSite?`,
`entryEvents`, `returnEvents`, `emit`, `Silent`. Also compare `CallSite` in both
`Call.lean` files and the complete `FrameCont.lean` and `Observer.lean` files.
They are byte-identical. The compiled `Safe.Obs` in `AdequacyFrozen.lean` is the
existing execution-based history, not a new definition chosen for this bridge.

Preserve the separate RD6 original-header acceptance using the C2 reproduction
recipe, including its explicit downstream `InitAssembly`. RD7's stronger closed
program proof does not replace that historical compatibility check.

Upstream: run `capped -m 64G -- scripts/ci --diff` with the lane-local Go cache
settings from the I1 recipe. Run D1's unchanged preservation/build/audit controls
and replay its eight modules plus the five relational/audit test clients,
including `Tests.RelationalObservations`. The implementation scan's inherited
16 findings remain a failure, separately from the standard-axiom pass.

Remove private clones, logs and build products after recording conclusions.

## Exact RD8 relay

Repeat the isolated extraction with logic
`5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42` into `.tmp/o1-rd8`, changing only
its private GoLean pin to the O1 implementation pin. Use the same four exact
independent dependency clones. Copy both `O1Compatibility.lean` and
`RD8Acceptance.lean` into it and append both private library targets. Build
`GoLean RelationalCodeX O1Compatibility RD8Acceptance`, then replay the roots
above with `RD8Acceptance` added. The expected complete inventory is 423 modules:
100 GoLean, 117 local (115 frozen plus the two adapters), and 206 dependencies.

`RD8Acceptance.agreement` discharges the exact `Observed.EventAgreement events`
through a constructor-preserving sum adapter. `prefix_history` supplies that law
to `prefix_acceptance`; `guarded` is the verbatim `LiftingTarget` body with only
its agreement parameter supplied to `observed_step`. Check their axioms and
proof bodies for these direct dependencies. The original observed prefix/outcome
headers in `ObservationAcceptance.lean` are compiled unchanged. All 125 frozen
input files must match, except the private pin and added library targets.

The frozen aggregate audits 6,407 local declarations, standard axioms only. Audit
both added modules exhaustively as well, by defining-module membership; the
independent review includes a reproducible checker. The observed caller remains
unfinished downstream. Building the unchanged U1 conditional consumers in the
aggregate does not discharge their separate `SimulationLaw` or claim U1 uptake.
