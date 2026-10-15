# I2 joint frozen RD8 acceptance

Use an owned worktree at the immutable implementation pin recorded in
`docs/2026-10-15_relational-o1-u1-integration-stage.md`. No peer source or build
directory is writable input. This experiment is outside the default build;
its Iris/Plan/observer dependencies do not enter public GoLean.

First reproduce upstream CI and dependencies with the I1 reproduction recipe,
using `LEAN_NUM_THREADS=2`, lane-private `TMPDIR` and Go cache variables, and
`capped -m 64G -- scripts/ci --diff`. The 64 GB cap is the documented cold-build
case. Do not run competing Lake builds against the same output directory.

From this candidate root, reuse U1's frozen RD8 setup:

```sh
mkdir -p .tmp/i2
export TMPDIR="$PWD/.tmp" LEAN_NUM_THREADS=2
python3 experiments/2026-10-15-unseq-rd8/setup.py \
  --logic-source /home/mike/projects/golean-logic \
  --seeds /home/mike/projects/golean-logic/.claude/worktrees/develop/packages/golean-iris/.lake/packages
python3 - <<'PY'
from pathlib import Path
import json, shutil, subprocess
root = Path.cwd()
dest = root / '.tmp/rd8'
for name in ['O1Compatibility', 'RD8Acceptance']:
    shutil.copyfile(root / 'experiments/2026-10-15-observation-compatibility' / (name + '.lean'), dest / (name + '.lean'))
for name in ['Joint', 'JointAudit']:
    shutil.copyfile(root / 'experiments/2026-10-15-o1-u1-integration' / (name + '.lean'), dest / (name + '.lean'))
config = (dest / 'lakefile.toml').read_text()
for name in ['O1Compatibility', 'RD8Acceptance', 'Joint', 'JointAudit']:
    if f'name = "{name}"' not in config:
        config += f'\n[[lean_lib]]\nname = "{name}"\n'
(dest / 'lakefile.toml').write_text(config)
pins = json.loads((dest / 'pins.json').read_text())
pins['GoLean'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
(dest / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
PY
cd .tmp/rd8
capped lake update
capped -m 64G -- lake build GoLean RelationalCodeX JointAudit
capped -m 64G -- lake env lean JointAudit.lean
capped -m 64G -- lake env leanchecker --verbose GoLean RelationalCodeX \
  GoLeanIris GoLeanIrisExamples O1Compatibility RD8Acceptance U1RD8 Joint JointAudit \
  Iris Batteries Qq
capped -m 64G -- lake env leanchecker --fresh --verbose JointAudit
```

The private GoLean dependency is the candidate root (`../..`), while all three
other dependencies are independent exact clones. The frozen package source is
RD8 `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42`; the setup uses its reviewed
handoff `eba7d3bdaa7786cfc6daad949cd3217185e2c867`. Compare all 125 original
package files to immutable objects: only generated Lake wiring/manifest and
the private GoLean pin may differ. All 115 original Lean files must agree.
Both O1 adapters and all four U1RD8 modules must match their reviewed inputs.

Compare the complete `replaying NAME` multiset against built `.olean` names
under the requested roots. Require each module exactly once and an output for
every upstream/local source module; dependency inventory is the actual built
closure. Require successful exits, not just matching counts. `JointAudit`
reuses U1's exhaustive project-closure scan and supplements it for the three
O1/joint adapter modules and the original example modules. It checks actual proof-body edges and the original
closed targets. Standard axioms and implementation findings are separate
results: implementation findings remain a visible **FAIL**, not a waived pass.

`I2.quiet_iff` connects the universal frozen policy to raw semantic events.
`source_paths` and `source_traversal` reuse the existing read/read/add proofs;
`plan_source` and `projected_source` apply only before a plan's final control.
They do not claim a new residual-plan or whole-segment-history theorem, and
do not impose silence on the following tail.

Reproduce frozen RD6 and RD7 separately using the I1/C2 recipes with this
combined GoLean source. Keep RD6's explicit `InitAssembly`, all original
headers, and RD5 Add/Alias/Pair/Set/Keep in the aggregates. Run the existing
D1 preservation/build/audit controls and replay its eight modules plus the
five relational/audit clients. Run U1's symbolic/control package, exhaustive
audit, and exact replay. Run the alias fixture from the candidate root:

```sh
capped lake env lean --run experiments/2026-10-15-unseq-compatibility/AliasControl.lean
```

It must retain both `{-2, 7}` outcomes and accept the behavior-set certificate.
This fixture enumerates schedules only as a negative control; the general U1
proof is the ranked all-ready traversal. Output and allocation controls retain
their separate meanings. No live gate, full replacement landing, executed
renderer correspondence or concurrent/infinite adequacy is claimed.

The Memory warning and recorded live **35 NOT-PUBLIC** failure remain visible.
Record conclusions and source binding, then remove private clones, logs,
artifacts and build outputs. No merge, push, live repin or peer write.
