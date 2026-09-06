"""Read-only comparison of the exact I1 integration to its two reviewed parents."""
from pathlib import Path
import hashlib
import json
import subprocess
import tomllib

ROOT = Path('/home/dev/projects/golean/.claude/worktrees/typed-consumer-sprint')
HERE = Path(__file__).resolve().parent
PARENT = '414a2abe'
I1 = '798e9c76'


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def digest(data):
    return hashlib.sha256(data).hexdigest()


manifest = json.loads((ROOT / 'docs/evidence/2026-09-06_i1-positive-integration/source.json').read_text())
drift = [path for path, expected in manifest.items()
         if not (ROOT / path).is_file() or digest((ROOT / path).read_bytes()) != expected]
assert not drift, drift
accepted = json.loads((ROOT / 'docs/evidence/2026-09-06_i1-positive-declarations/accepted-inputs.json').read_text())
differences = {path: {'accepted': expected, 'actual': digest((ROOT / path).read_bytes())}
               for path, expected in accepted.items()
               if digest((ROOT / path).read_bytes()) != expected}
assert set(differences) == {'lakefile.toml', 'scripts/ci'}, differences
parent_lake = git('show', f'{PARENT}:lakefile.toml').decode()
i1_lake = git('show', f'{I1}:lakefile.toml').decode()
current_lake = (ROOT / 'lakefile.toml').read_text()
parsed_parent = tomllib.loads(parent_lake)
parsed_i1 = tomllib.loads(i1_lake)
parsed_current = tomllib.loads(current_lake)
parent_libs = {entry['name']: entry for entry in parsed_parent['lean_lib']}
i1_libs = {entry['name']: entry for entry in parsed_i1['lean_lib']}
current_libs = {entry['name']: entry for entry in parsed_current['lean_lib']}
assert len(current_libs) == len(parsed_current['lean_lib'])
assert current_libs == parent_libs | i1_libs
assert all(current_libs[name] == entry for name, entry in parent_libs.items())
assert all(current_libs[name] == entry for name, entry in i1_libs.items())
for key, value in parsed_parent.items():
    if key != 'lean_lib':
        assert parsed_current[key] == value
for key, value in parsed_i1.items():
    if key != 'lean_lib':
        assert parsed_current[key] == value
declaration = '\n[[lean_lib]]\nname = "DeclarationTests"\nglobs = ["Tests.DeclarationWire", "Tests.DeclarationAudit"]\n'
assert current_lake == parent_lake + declaration

parent_ci = git('show', f'{PARENT}:scripts/ci').decode()
i1_ci = git('show', f'{I1}:scripts/ci').decode()
current_ci = (ROOT / 'scripts/ci').read_text()
start = i1_ci.index('step "positive declaration identities (fresh Go/Lean fixture and post-import audit)"')
end = i1_ci.index('step "frontend unit tests (go test ./tools/nativefrontend)"', start)
block = i1_ci[start:end]
assert current_ci.count(block) == 1
assert current_ci.replace(block, '', 1) == parent_ci
assert 'if bash scripts/check-declarations; then' in block
assert 'else\n  bad "positive declaration identities and decoder (see above)"\nfi' in block

changed = git('diff', '--cached', '--name-only', PARENT).decode().splitlines()
source_changes = [path for path in changed if not path.startswith('docs/')]
nonunion_drift = []
for path in source_changes:
    if path in {'lakefile.toml', 'scripts/ci'}:
        continue
    if (ROOT / path).read_bytes() != git('show', f'{I1}:{path}'):
        nonunion_drift.append(path)
assert not nonunion_drift, nonunion_drift
ci_log = (ROOT / 'docs/evidence/2026-09-06_i1-positive-integration/ci.log').read_text()
assert 'RESULT: PASS' in ci_log

result = {
    'verdict': 'PASS; bounded additive-union and source-identity review',
    'parent': PARENT, 'reviewed_i1': I1,
    'checked_live_source_hashes': len(manifest), 'source_hash_drift': drift,
    'accepted_i1_inputs': len(accepted), 'only_declared_union_differences': differences,
    'parent_library_count': len(parent_libs), 'i1_library_count': len(i1_libs),
    'integrated_library_count': len(current_libs),
    'exact_library_union': True, 'parent_config_unchanged_except_added_library': True,
    'ci_is_byte_identical_parent_plus_exact_reviewed_i1_block': True,
    'all_existing_parent_ci_bytes_preserved': True, 'added_gate_failure_is_fatal': True,
    'non_document_source_changes': source_changes, 'nonunion_source_equals_reviewed_i1': True,
    'integrator_ordinary_ci_log_pass_confirmed': True,
    'ci_rerun_by_reviewer': False, 'runtime_semantics_reaudited': False,
}
(HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
for path in ['lakefile.toml', 'scripts/ci']:
    target = HERE / 'source' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((ROOT / path).read_bytes())
print(json.dumps(result, indent=2))
