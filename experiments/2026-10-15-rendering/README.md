# Renderer preservation and checked account

Use an owned checkout of the implementation pin in
`docs/2026-10-15_relational-rendering-stage.md`, Lean v4.32.2, `capped` and
`LEAN_NUM_THREADS=2`. No peer build directories or global caches are writable
inputs. The old executable input is exactly
`82353580814b66399cdc472a4c4edf9044d0c097`.

From the candidate root, populate the pinned reference checkouts with
`scripts/setup-deps --from /home/mike/projects/golean --only goose,go`.
Run the existing full CI with private temporary and Go caches:

```sh
mkdir -p .tmp/rendering
export LEAN_NUM_THREADS=2 TMPDIR="$PWD/.tmp"
export GOTOOLCHAIN=local GOPROXY=off GOTELEMETRY=off GOENV=off
export GOPATH="$PWD/.tmp/gopath" GOMODCACHE="$PWD/.tmp/gomodcache" GOCACHE="$PWD/.tmp/gocache"
capped -m 64G -- scripts/ci --diff
```

Do not run competing builds in the same output directory. Once the upstream
build finishes, this experiment checks all new equations and representative
semantic sites. Its audit reuses the established declaration/implementation
scan; standard axioms and unresolved implementation findings are separate.

```sh
cd experiments/2026-10-15-rendering
capped lake build
capped lake env lean RendererAudit.lean
capped lake env leanchecker --verbose GoLean Derivation SemanticLinks RendererAudit
capped lake env leanchecker --fresh --verbose RendererAudit
```

The author used a private copy of these three Lean files in
`.tmp/renderer-checks`, with the same dependency path `../..`. The package
location does not change their statements. Compare source bytes if copying.
Require exact equality of replayed module-name multisets and the built/source
inventory, with no duplicate, missing or extra modules and successful exits.

For the executed old/new controls, from the candidate root materialize a full
independent old source archive (never borrow an olean cache from the candidate):

```sh
python3 - <<'PY'
import io, subprocess, tarfile
from pathlib import Path
pin = '82353580814b66399cdc472a4c4edf9044d0c097'
dest = Path('.tmp/old')
if dest.exists(): raise SystemExit('Inspect existing old archive before reuse')
dest.mkdir(parents=True)
data = subprocess.check_output(['git', 'archive', pin])
with tarfile.open(fileobj=io.BytesIO(data)) as archive:
    archive.extractall(dest, filter='data')
PY
cd .tmp/old
capped lake build GoLean.GoCore.Multi
capped lake env lean -Dtrace.Elab.Deriving.repr=true GoLean/GoCore/Value.lean > ../rendering/old-value-derivation.log
capped lake env lean -Dtrace.Elab.Deriving.repr=true GoLean/GoCore/Syntax.lean > ../rendering/old-syntax-derivation.log
capped lake env lean --run ../../experiments/2026-10-15-rendering/Control.lean > ../rendering/old-control.log
capped lake env lean ../../experiments/2026-10-15-rendering/Closure.lean > ../rendering/old-closure.log
cd ../..
python3 experiments/2026-10-15-rendering/check-derivation.py \
  .tmp/rendering/old-value-derivation.log .tmp/rendering/old-syntax-derivation.log
capped lake env lean --run experiments/2026-10-15-rendering/Control.lean > .tmp/rendering/new-control.log
cmp .tmp/rendering/old-control.log .tmp/rendering/new-control.log
capped lake env lean experiments/2026-10-15-rendering/Closure.lean
```

The same control source executes in two distinct Lake environments. The old
expectation is never regenerated using the candidate printer. It includes all
88 constructors, nested/nonempty/empty containers, options, interior locations,
invalid Go byte strings, malformed values, Unicode/escaping, five precedences,
five widths, two indentation levels and two starting columns. Semantic controls
include checkedDynamicTy, valueEq, preprintDispatch, unseqAtom and projected
real stepFn results with different supplied tapes (store, remaining tape, label
and exact errors; this finite control does not serialize Config). A matching finite control is supporting
evidence; the general preservation argument is the layered source/derivation
induction in the stage record. The new checked equations are not a kernel theorem
about old opaque constants. Inspect the pinned `Lean/Elab/Deriving/Repr.lean`,
`Init/Data/Repr.lean`, `Init/Data/Array/Basic.lean`, Format operations and compiler
`Lean/Compiler/LCNF/ToDecl.lean` when reviewing that boundary.

Preserve the two older frozen acceptances separately using their existing
instructions:

- `../2026-10-15-observed-phases/README.md`: logic
  `3c9be98f8de86f04c4cec53d75490199718da066`, with PhaseAcceptance,
  CallerAcceptance and PhaseAudit. Check exact original headers and source
  hashes. This includes all three observed laws and their actual guarded
  callee/caller/history/adequacy applications.
- `../2026-10-15-o1-u1-integration/README.md`: older frozen RD8
  `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42`, reviewed `eba7d3b...`,
  with JointAudit. Preserve both O1/U1 targets and policy compatibility.

Also materialize the latest completed R2 package at logic
`6da4e8aa25066fd26f7e81281a98c4133cf2dadb` (review `64f96bd`), using the
observed-phase README's exact archive/independent-dependency procedure with
that pin, destination `.tmp/r2-consumer`, and no phase adapter copies.
Only private `lakefile.toml` and `lake-manifest.json` may change; preserve
`pins.json` as provenance while the private GoLean Lake dependency is `../..`.
From that private package:

```sh
capped -m 64G -- lake build GoLean RelationalCodeX
capped -m 64G -- lake env lean RelationalCodeX.lean
capped lake env lean --run RelationalCodeX/U1/AliasControl.lean
capped -m 64G -- lake env leanchecker --verbose GoLean RelationalCodeX \
  GoLeanIris GoLeanIrisExamples Tests.UnseqHarness Iris Batteries Qq
```

These immutable aggregates retain RD5 Set/Keep/Pair/Alias/Add, RD6's original
conditional program acceptance with InitAssembly explicit, RD7's downstream
assembly/initialized-program results, and the original observation contracts.
The R2 ordinary simulation/guarded rules and alias control remain distinct from
the conditional R1 caller in that input. Do not substitute a moving logic tree.
For the R2 implementation scan, reuse RendererAudit's declaration scan, importing
RelationalCodeX and selecting GoLean, GoLeanIris, GoLeanIrisExamples,
RelationalCodeX and Tests modules. Repeat with `import GoLean` added for the
full-root scope. Require standard axioms; report implementation failures without
waiver. Compare exact finding sets to their frozen baseline, not merely counts.

Run the existing D1 and U1 packages at this candidate (`capped lake build`,
headline/exhaustive audits and exact `leanchecker` replay), and the existing
alias control. No stronger consumer premises or modified frozen proof headers
are allowed. Remove this lane's disposable archives, package clones, logs,
`.lake` directories and generated artifacts after recording the checked
conclusions and immutable pins. No merge, push, live repin or peer writes.
