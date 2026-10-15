# Frozen observed-phase acceptance

Run in an owned checkout of the implementation pin recorded in
`docs/2026-10-15_relational-observed-phases-stage.md`. Use `LEAN_NUM_THREADS=2`,
`capped`, and private temporary/build state. The immutable logic input is
`3c9be98f8de86f04c4cec53d75490199718da066`, reviewed at
`621316254d5a32c1489593ad0e7b8c26122df0e4`. This is separate from I2's older
`eba7d3b` acceptance. Neither package changes a live pin.

Materialize the frozen package and independent dependencies from explicit
read-only sources. This uses the same clone/cache procedure as I2; no shared
object database, symlinked build directory or writable peer is permitted.

```sh
mkdir -p .tmp
export TMPDIR="$PWD/.tmp" LEAN_NUM_THREADS=2
python3 - <<'PY'
import io, json, os, shutil, subprocess, tarfile
from pathlib import Path
root = Path.cwd()
source = Path('/home/mike/projects/golean-logic')
seeds = source / '.claude/worktrees/develop/packages/golean-iris/.lake/packages'
pin = '3c9be98f8de86f04c4cec53d75490199718da066'
package = 'experiments/2026-10-14_relational-codex'
dest = root / '.tmp/observed-consumer'
def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args],
        env={**os.environ, 'GIT_OPTIONAL_LOCKS': '0'})
if dest.exists():
    raise SystemExit('Destination already exists; inspect it before reuse/removal')
dest.mkdir(parents=True)
with tarfile.open(fileobj=io.BytesIO(git(source, 'archive', pin, package))) as archive:
    for member in archive.getmembers():
        if member.isdir(): continue
        relative = Path(member.name).relative_to(package)
        if member.issym() or member.islnk() or '..' in relative.parts:
            raise SystemExit(f'Unexpected entry: {member.name}')
        target = dest / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(archive.extractfile(member).read())
pins = json.loads((dest / 'pins.json').read_text())
for name, revision in pins.items():
    if name == 'GoLean': continue
    seed = seeds / name
    if git(seed, 'status', '--porcelain').strip():
        raise SystemExit(f'Dirty seed: {seed}')
    changes = git(seed, 'diff', '--name-only', revision, 'HEAD').decode().splitlines()
    if any(not p.startswith('docs/') or not p.endswith('.md') for p in changes):
        raise SystemExit(f'Seed code/config differs: {seed}')
    clone = dest / '.lake/packages' / name
    clone.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['git', 'clone', '--no-hardlinks', '--no-checkout', str(seed), str(clone)], check=True)
    subprocess.run(['git', '-C', str(clone), 'checkout', '--detach', revision], check=True)
    cache = Path('Iris/.lake/build' if name == 'iris' else '.lake/build')
    shutil.copytree(seed / cache, clone / cache, symlinks=False)
    assert not (clone / '.git/objects/info/alternates').exists()
(dest / 'lake-manifest.json').unlink()
config = (dest / 'lakefile.toml').read_text().replace('path = ".golean-ws"', 'path = "../.."')
for name in ['PhaseAcceptance', 'CallerAcceptance', 'PhaseAudit']:
    shutil.copyfile(root / 'experiments/2026-10-15-observed-phases' / (name + '.lean'), dest / (name + '.lean'))
    config += f'\n[[lean_lib]]\nname = "{name}"\n'
(dest / 'lakefile.toml').write_text(config)
print('Private dependency is this candidate root; frozen pins.json is provenance, not Lake wiring')
PY
cd .tmp/observed-consumer
capped lake update
capped -m 64G -- lake build GoLean RelationalCodeX PhaseAudit
capped -m 64G -- lake env lean PhaseAudit.lean
capped -m 64G -- lake env leanchecker --verbose GoLean RelationalCodeX \
  GoLeanIris GoLeanIrisExamples PhaseAcceptance CallerAcceptance PhaseAudit Iris Batteries Qq
capped -m 64G -- lake env leanchecker --fresh --verbose PhaseAudit
```

Before and after validation, compare all frozen package files with the exact
Git objects. Only private `lakefile.toml` and generated `lake-manifest.json`
may differ. The original 128 Lean files, original target definitions and
counterexample must be identical. The request SHA-256 is
`8ab37816f07b289cb1744b074e79a38132a3244d8b0a73b34aa18e741045ae50`.
`CallerAcceptance` repeats each original theorem header verbatim and discharges
only the three law parameters. Compare headers through the final `:= by`,
preserving inner `let ... :=` expressions.

Require successful replay exits and exact multiset equality between `replaying
MODULE` output and built `.olean` modules for the requested roots, every source
module present and no duplicates. Dependency inventory is the actual built
closure. `PhaseAudit` reuses U1's declaration/implementation scan and the
established visited-set proof-value traversal. Standard axioms and implementation
findings are reported separately. The inherited **FAIL: 21** inventory is not
waived by a successful build or kernel replay.

From the candidate root, reproduce upstream `capped -m 64G -- scripts/ci --diff`
with lane-private temporary/Go caches and the existing read-only reference
dependencies, as in I1/I2. Reproduce the separate old I2 package using
`experiments/2026-10-15-o1-u1-integration/README.md`; its old O1/U1 inputs remain
unchanged. Run the existing alias behavior control:

```sh
capped lake env lean --run experiments/2026-10-15-unseq-compatibility/AliasControl.lean
```

It must retain `{-2, 7}` and the behavior-set certificate. This is a regression
control, not schedule enumeration for the general U1 theorem. Record source
hashes before checks and compare them to the implementation commit and final
worktree afterward. Remove this lane's disposable clones, outputs and logs
after recording conclusions and reproduction. Retain the Memory warning,
historical live **35 NOT-PUBLIC**, and unresolved renderer correspondence.
