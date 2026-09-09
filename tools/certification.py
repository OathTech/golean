#!/usr/bin/env python3
"""F8: content-bound build identity and slow observation certification.

[AGENT] 2026-09-09. One inventory for the compiled seal, cache validator,
fresh enumeration and release check. No command writes tracked records.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import tempfile
import time
import tomllib

BUILD_SCHEMA = 'golean-build-inputs-v1'
INPUT_SCHEMA = 'golean-certification-inputs-v1'
CERT_SCHEMA = 'golean-certification-v1'
CLAIM_SCHEMA = 'golean-enumeration-claim-v1'
BUILD_FILES = ('Main.lean', 'GoLean.lean', 'lean-toolchain', 'lakefile.toml',
               'lake-manifest.json', 'tools/certification.py', 'scripts/build-certified')
APPARATUS_FILES = ('baselines/go-oracle-pin',)
FORBIDDEN_ENV = ('LEAN_OPTS', 'LEAN_CC', 'LEANC_OPTS', 'CFLAGS', 'CPPFLAGS',
                 'LDFLAGS', 'CC', 'CXX', 'LEAN_SRC_PATH', 'LEAN_PATH')


class Refused(ValueError):
    pass


def require(test, cause):
    if not test:
        raise Refused(cause)


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(',', ':'))


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON field: {key}')
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object,
                      parse_constant=lambda x: (_ for _ in ()).throw(Refused('non-finite JSON: ' + x)))


def keys(value, expected, label):
    require(type(value) is dict and set(value) == set(expected),
            f'{label}: expected fields {sorted(expected)}')


def sha_field(value, label):
    require(type(value) is str and re.fullmatch('[0-9a-f]{64}', value), f'{label}: invalid sha256')


def run_output(root, args):
    result = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=60)
    require(result.returncode == 0, f'input query failed ({result.returncode}): {args}: {result.stderr.strip()}')
    return result.stdout.strip()


def inventory(root, paths):
    """Include tracked deletions (an error) and new inputs, even ignored ones.

    Directories are enumerated by Git, not a frozen file allowlist. Imports
    into excluded roots and external Lake packages are refused below.
    """
    raw = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others',
                                   '--', *paths], cwd=root)
    names = sorted(set(x.decode() for x in raw.split(b'\0') if x))
    result = {}
    for name in names:
        if name.endswith(('.md', '.pyc')) or '__pycache__' in Path(name).parts:
            continue
        path = root / name
        require(path.is_file(), f'missing dependency: {name}')
        result[name] = file_sha(path)
    return result


def lean_header(source):
    """Conservative header tokenizer. Unsupported spelling is a refusal.

    Only the import header is inspected; strings in terms are never imports.
    Block comments nest, and comments preserve token boundaries.
    """
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end + 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, 'unterminated Lean header comment')
        else:
            found = re.match(r"[A-Za-z_][A-Za-z_0-9'.]*", source[i:])
            if found:
                token = found[0]
                i += len(token)
                yield token
            else:
                yield source[i]
                i += 1


def check_imports(root, files):
    for name in ('Init', 'Std', 'Lean', 'Lake'):
        require(not (root / name).exists() and not (root / (name + '.lean')).exists(),
                'local source shadows certified toolchain root: ' + name)
    for name in files:
        if not name.endswith('.lean'):
            continue
        tokens = iter(lean_header((root / name).read_text()))
        token = next(tokens, None)
        if token == 'module':
            token = next(tokens, None)
        if token == 'prelude':
            token = next(tokens, None)
        while token in ('public', 'meta', 'import'):
            if token == 'public':
                token = next(tokens, None)
            if token == 'meta':
                token = next(tokens, None)
            require(token == 'import', f'unsupported Lean import header: {name}')
            token = next(tokens, None)
            if token == 'all':
                token = next(tokens, None)
            require(token and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", token),
                    f'unsupported Lean import spelling: {name}: {token}')
            module = token
            top = module.split('.')[0]
            require(top in ('GoLean', 'Init', 'Std', 'Lean', 'Lake'),
                    f'dependency outside certified import roots: {name}: {module}')
            if top == 'GoLean':
                dependency = module.replace('.', '/') + '.lean'
                require(dependency in files, f'import dependency omitted from inventory: {name}: {dependency}')
            token = next(tokens, None)
            # Multiple module names on one import line are uncommon here.
            # An unexpected module-shaped token cannot silently end the header.
            require(token is None or '.' not in token,
                    f'unsupported multi-module import header: {name}: {token}')


def toolchain(root):
    pin = (root / 'lean-toolchain').read_text().strip()
    require(pin.startswith('leanprover/lean4:v'), 'unsupported Lean toolchain pin')
    version = run_output(root, [str(root / 'scripts/capped'), 'lean', '--version'])
    require(version.startswith('Lean (version ' + pin.split(':v')[1] + ',') or
            version.startswith('Lean (version ' + pin.split(':v')[1] + '-') or
            version.startswith('Lean (version ' + pin.split(':v')[1] + ')'),
            f'Lean toolchain differs from pin {pin}: {version}')
    prefix = Path(run_output(root, [str(root / 'scripts/capped'), 'lean', '--print-prefix']))
    # Include precompiled standard-library artifacts and compiler headers,
    # not just version text or the compiler executable. Aggregate the sorted
    # path/hash pairs to keep the tracked record small (no installation paths).
    files = [p for directory in ('bin', 'include', 'lib')
             for p in (prefix / directory).rglob('*') if p.is_file()]
    require(files and (prefix / 'bin/lean').is_file() and (prefix / 'bin/leanc').is_file(),
            'Lean installation has no compiler/runtime inventory')
    return {'pin': pin, 'version': version, 'system': platform.system(),
            'machine': platform.machine(),
            'distribution_files': len(files),
            'distribution_sha256': digest({p.relative_to(prefix).as_posix(): file_sha(p)
                                           for p in sorted(files)})}


def check_build_configuration(root):
    override = root / 'lakefile.lean'
    require(not override.exists() and not override.is_symlink(),
            'uncertified Lake configuration override: lakefile.lean')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    require(set(config) <= {'name', 'version', 'defaultTargets', 'lean_lib', 'lean_exe'},
            'uncertified Lake build options (extend the input inventory before use)')
    require(config.get('name') == 'GoLean' and config.get('defaultTargets') == ['golean'],
            'uncertified Lake package/default target')
    for kind, allowed in [('lean_lib', {'name', 'globs'}), ('lean_exe', {'name', 'root'})]:
        entries = config.get(kind)
        require(type(entries) is list, 'missing Lake target declarations: ' + kind)
        for entry in entries:
            require(type(entry) is dict and set(entry) <= allowed and type(entry.get('name')) is str,
                    'uncertified Lake target options: ' + kind)
    require([entry for entry in config['lean_exe'] if entry['name'] == 'golean'] ==
            [{'name': 'golean', 'root': 'Main'}], 'certified golean target must have root Main')
    require([entry for entry in config['lean_lib'] if entry['name'] == 'GoLean'] ==
            [{'name': 'GoLean'}], 'uncertified GoLean library roots/options')
    manifest = read_json(root / 'lake-manifest.json')
    require(type(manifest) is dict, 'invalid Lake dependency manifest')
    require(manifest.get('packages') == [], 'external Lake dependencies need a certification inventory')


def build_inputs(root):
    for name in FORBIDDEN_ENV:
        require(not os.environ.get(name), f'uncertified build environment override: {name}')
    check_build_configuration(root)
    files = inventory(root, [*BUILD_FILES, 'GoLean'])
    require(set(BUILD_FILES) <= files.keys(), 'missing required build dependency')
    require(any(p.startswith('GoLean/GoCore/') for p in files), 'empty semantic source inventory')
    check_imports(root, files)
    return {'schema': BUILD_SCHEMA, 'files': files, 'toolchain': toolchain(root)}


def inputs(root):
    build = build_inputs(root)
    files = inventory(root, ['scripts', 'tools', *APPARATUS_FILES])
    for name in APPARATUS_FILES:
        require(name in files, f'missing apparatus dependency: {name}')
    oracle = run_output(root, ['go', 'version'])
    pin = (root / 'baselines/go-oracle-pin').read_text().strip()
    require(oracle.split()[2] == pin, f'Go toolchain differs from oracle pin {pin}: {oracle}')
    return {'schema': INPUT_SCHEMA, 'build': build, 'files': files,
            'oracle': oracle, 'python': platform.python_version()}


def executable(root):
    return root / '.lake/build/bin/golean'


def compiled_inputs(root):
    binary = executable(root)
    require(binary.is_file() and os.access(binary, os.X_OK), 'missing golean executable')
    result = subprocess.run([str(binary), '--build-provenance'], cwd=root,
                            capture_output=True, text=True, timeout=30)
    require(result.returncode == 0, 'executable has no compiled provenance; run scripts/build-certified')
    try:
        return json.loads(result.stdout, object_pairs_hook=unique_object)
    except (ValueError, TypeError) as error:
        raise Refused('executable returned malformed compiled provenance') from error


def difference(before, after, prefix=''):
    if isinstance(before, dict) and isinstance(after, dict):
        for key in sorted(before.keys() | after.keys()):
            path = f'{prefix}/{key}' if prefix else key
            if key not in before:
                return 'added dependency ' + path
            if key not in after:
                return 'removed dependency ' + path
            if before[key] != after[key]:
                return difference(before[key], after[key], path)
    return 'changed dependency ' + prefix


def check_build(root, current):
    actual = compiled_inputs(root)
    require(actual == current, 'STALE executable build: ' + difference(actual, current))
    return file_sha(executable(root))


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=path.name + '.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as output:
            output.write(json.dumps(value, indent=2, sort_keys=True) + '\n')
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def build(root):
    before = build_inputs(root)
    try:
        old = compiled_inputs(root)
    except Refused:
        old = None
    if old != before:
        # The external stamp inputs are deliberately larger than Main's Lean
        # imports. Force its elaboration/link when they change. Only owned
        # Main/executable outputs are invalidated; symlinks are unlinked.
        for directory, stem in [('lib/lean', 'Main'), ('ir', 'Main'), ('bin', 'golean')]:
            base = root / '.lake/build' / directory
            if base.is_dir():
                for path in base.iterdir():
                    if path.name == stem or path.name.startswith(stem + '.'):
                        require(not path.is_dir(), f'unexpected build output directory: {path}')
                        path.unlink()
    result = subprocess.run([str(root / 'scripts/capped'), 'lake', '--rehash', 'build', 'golean'], cwd=root)
    if result.returncode != 0:
        return result.returncode
    after = build_inputs(root)
    require(before == after, 'build inputs changed during compilation: ' + difference(before, after))
    binary_sha = check_build(root, after)
    atomic_json(root / 'artifacts/certification/build.json',
                {'schema': 'golean-build-receipt-v1', 'inputs_sha256': digest(after),
                 'binary_sha256': binary_sha, 'captured_exit': 0})
    print('Certified build: compiled inputs match; sha256=' + binary_sha)
    return 0


ENUM_FLAGS = {'--input', '--function', '--arg-int', '--fuel', '--max-width',
              '--max-sites', '--cap', '--work-cap', '--expect-status', '--backedge',
              '--engine', '--allow-nonterm'}


def claim_for(root, case_id, lane, params, row_status, argv):
    require(lane in ('membership', 'confluent'), 'certification requires membership or confluent lane')
    require(re.fullmatch(r'[A-Za-z0-9_./-]+', case_id) and
            '..' not in case_id.split('/') and not case_id.startswith('/'), 'invalid case id')
    require(argv and argv[0] == 'coverage-observations', 'certification requires coverage-observations')
    seen, normalized = {}, ['coverage-observations']
    i = 1
    while i < len(argv):
        flag = argv[i]
        require(flag in ENUM_FLAGS and i + 1 < len(argv), f'unknown/incomplete enumeration flag: {flag}')
        value = argv[i + 1]
        require(flag == '--arg-int' or flag not in seen, f'duplicate enumeration flag: {flag}')
        seen.setdefault(flag, []).append(value)
        normalized.extend([flag, '<wire>' if flag == '--input' else value])
        i += 2
    require('--input' in seen and '--function' in seen, 'enumeration requires wire and entry')
    wire = root / seen['--input'][0]
    require(wire.is_file(), f'missing enumeration wire: {wire}')
    claim = {'schema': CLAIM_SCHEMA, 'case_id': case_id, 'lane': lane,
             'params': params, 'row_status': row_status, 'wire_sha256': file_sha(wire),
             'argv': normalized, 'observation_schema': 'golean-observation-v1'}
    validate_invocation(claim)
    return claim, wire


def validate_invocation(claim):
    """Cross-check the caller's effective flags against its declared params.

    Omitted CLI defaults are bound by the CLI source fingerprint. If the
    shell changes its defaults without this cross-check, certification fails.
    v1 covers checked dedup sets (the entire active slow tier).
    """
    keys(claim, ['schema', 'case_id', 'lane', 'params', 'row_status', 'wire_sha256',
                 'argv', 'observation_schema'], 'certification claim')
    require(all(type(claim[name]) is str for name in
                ('schema', 'case_id', 'lane', 'params', 'row_status', 'wire_sha256', 'observation_schema')),
            'certification claim has invalid field types')
    require(claim['schema'] == CLAIM_SCHEMA and claim['observation_schema'] == 'golean-observation-v1',
            'unknown certification claim/observation schema')
    require(claim['lane'] in ('membership', 'confluent'), 'invalid certification lane')
    require(type(claim['params']) is str, 'invalid certification params')
    params = {}
    for field in claim['params'].split(','):
        pair = field.split('=')
        require(len(pair) == 2 and pair[0] not in params, 'invalid/duplicate certification param: ' + field)
        params[pair[0]] = pair[1]
    require(set(params) <= {'width', 'sites', 'cap', 'work', 'members', 'statuses', 'tier', 'engine'},
            'unsupported v1 certification params')
    require(params.get('engine') == 'dedup' and params.get('tier') == 'slow',
            'v1 certification requires tier=slow,engine=dedup')
    require('width' in params, 'certification requires explicit width')
    if claim['lane'] == 'membership':
        require('members' in params, 'membership certification requires members pin')
    for name in ('width', 'sites', 'cap', 'work', 'members'):
        require(name not in params or re.fullmatch('[1-9][0-9]*', params[name]),
                'invalid positive certification param: ' + name)
    statuses = params.get('statuses', claim['row_status']).split('+')
    require(len(statuses) == len(set(statuses)) and set(statuses) <= {'ok', 'panic'}
            and claim['row_status'] in statuses, 'invalid certification status set')
    require(claim['lane'] == 'membership' or 'statuses' not in params,
            'statuses param is membership-only')
    argv = claim['argv']
    require(type(argv) is list and all(type(x) is str for x in argv) and argv
            and argv[0] == 'coverage-observations' and len(argv) % 2 == 1,
            'invalid certification argv')
    flags, arguments = {}, []
    for flag, value in zip(argv[1::2], argv[2::2]):
        if flag == '--arg-int':
            require(re.fullmatch('-?[0-9]+', value), 'invalid certification integer argument')
            arguments.append(value)
        else:
            require(flag not in flags, 'duplicate certification flag: ' + flag)
            flags[flag] = value
    expected = {'--input': '<wire>', '--function': flags.get('--function'),
                '--max-width': params['width'], '--max-sites': params.get('sites', '8'),
                '--cap': params.get('cap', '64'), '--work-cap': params.get('work', '200000'),
                '--engine': 'dedup', '--expect-status': ','.join(statuses)}
    require(flags.get('--function') and flags == expected,
            'certification invocation differs from declared parameters: ' + difference(expected, flags))
    sha_field(claim['wire_sha256'], 'claim/wire_sha256')
    return params, flags['--function'], arguments, statuses


def validate_set(lines, claim):
    params, _, _, statuses = validate_invocation(claim)
    count = int(params.get('members', '1'))
    require(len(lines) == count, f'certified set cardinality differs from pin: {len(lines)} != {count}')
    require((claim['lane'] == 'confluent' and count == 1) or
            (claim['lane'] == 'membership' and count > 1), 'certified set cardinality differs from lane')
    for line in lines:
        require(json.loads(line)['status'] in statuses, 'certified observation status outside declared set')


def data_lines(path):
    lines = [line for line in path.read_text().splitlines() if line and not line.startswith('#')]
    require(lines, f'empty certified observation set: {path}')
    require(len(lines) == len(set(lines)), f'duplicate certified observation: {path}')
    for line in lines:
        value = json.loads(line, object_pairs_hook=unique_object,
                           parse_constant=lambda x: (_ for _ in ()).throw(Refused('non-finite observation JSON: ' + x)))
        require(type(value) is dict and value.get('schema') == 'golean-observation-v1',
                f'unknown certified observation schema: {path}')
    return lines


def observations_sha(lines):
    return hashlib.sha256(('\n'.join(sorted(lines)) + '\n').encode()).hexdigest()


def record_headers(record, claim):
    lines = record.read_text().splitlines()
    for label, value in [('params', claim['params']), ('wire-sha256', claim['wire_sha256'])]:
        matches = [line.removeprefix('# ' + label + ': ') for line in lines
                   if line.startswith('# ' + label + ': ')]
        require(matches == [value], f'certified record {label} missing, duplicated or STALE: {record}')


def provenance_path(record):
    return record.with_suffix('.json')


def validate_provenance(record, saved, current, claim):
    keys(saved, ['schema', 'claim', 'inputs', 'observations_sha256', 'receipt'], 'certification record')
    require(saved['schema'] == CERT_SCHEMA, 'unknown certification schema: ' + str(saved['schema']))
    keys(saved['claim'], ['schema', 'case_id', 'lane', 'params', 'row_status', 'wire_sha256',
                          'argv', 'observation_schema'], 'certification claim')
    require(saved['claim']['schema'] == CLAIM_SCHEMA, 'unknown certification claim schema')
    require(saved['claim'] == claim, 'STALE certification claim: ' + difference(saved['claim'], claim))
    keys(saved['inputs'], ['schema', 'build', 'files', 'oracle', 'python'], 'certification inputs')
    require(saved['inputs']['schema'] == INPUT_SCHEMA, 'unknown certification input schema')
    require(saved['inputs'] == current, 'STALE certification: ' + difference(saved['inputs'], current))
    keys(saved['receipt'], ['source_commit', 'git_dirty', 'started_utc', 'finished_utc',
                            'wall_seconds', 'captured_exit', 'binary_sha256', 'stats_sha256',
                            'command', 'certifier'], 'certification receipt')
    receipt = saved['receipt']
    require(type(receipt['captured_exit']) is int and receipt['captured_exit'] == 0,
            'certification receipt has no successful enumeration')
    require(receipt['certifier'] == 'tools/certification.py', 'unknown certification receipt producer')
    require(type(receipt['git_dirty']) is bool, 'certification receipt git_dirty must be Boolean')
    require(type(receipt['source_commit']) is str and re.fullmatch('[0-9a-f]{40,64}', receipt['source_commit']),
            'certification receipt source commit is missing')
    require(receipt['command'] == ['golean', *claim['argv']], 'certification receipt command differs from claim')
    require(type(receipt['wall_seconds']) in (int, float) and receipt['wall_seconds'] >= 0,
            'certification receipt has invalid wall time')
    require(math.isfinite(receipt['wall_seconds']), 'certification receipt has non-finite wall time')
    for key in ['started_utc', 'finished_utc']:
        require(type(receipt[key]) is str, 'certification receipt has invalid timestamp')
        require(datetime.fromisoformat(receipt[key]).tzinfo is not None, 'certification timestamp has no timezone')
    require(datetime.fromisoformat(receipt['finished_utc']) >= datetime.fromisoformat(receipt['started_utc']),
            'certification timestamps run backwards')
    for key in ['binary_sha256', 'stats_sha256']:
        sha_field(receipt[key], 'receipt/' + key)
    sha_field(saved['observations_sha256'], 'observations_sha256')
    record_headers(record, claim)
    lines = data_lines(record)
    validate_set(lines, claim)
    require(observations_sha(lines) == saved['observations_sha256'], 'certified observation bytes changed')
    return lines


def load_provenance(record):
    path = provenance_path(record)
    require(path.is_file(), f'missing certification provenance: {path}; run scripts/ci --slow and review the candidate')
    return read_json(path)


def assert_stable(root, before, binary_sha, wire, wire_sha):
    after = inputs(root)
    require(before == after, 'certification inputs changed during run: ' + difference(before, after))
    require(file_sha(executable(root)) == binary_sha, 'executable changed during certification')
    require(file_sha(wire) == wire_sha, 'wire changed during certification')


def cache(root, record, output, claim, wire):
    for name in ('observations.txt', 'enum-stats.txt', 'certification-candidate.json'):
        (output / name).unlink(missing_ok=True)
    current = inputs(root)
    saved = load_provenance(record)
    lines = validate_provenance(record, saved, current, claim)
    binary_sha = check_build(root, current['build'])
    assert_stable(root, current, binary_sha, wire, claim['wire_sha256'])
    output.mkdir(parents=True, exist_ok=True)
    (output / 'observations.txt').write_text('\n'.join(lines) + '\n')
    stamp = saved['receipt']['finished_utc']
    (output / 'enum-stats.txt').write_text(f'CERTIFIED-CACHED {stamp}; inputs={digest(current)}\n')
    print('CERTIFIED-CACHED ' + stamp + '; full claim and compiled inputs checked')
    return 0


def run_enumerator(root, argv, out, err, timeout):
    # A direct capped invocation may have a wrapper and child. Own the group
    # so a timeout/interrupt cannot leave enumeration running behind a failed
    # refresh. The outer CI cgroup remains an independent memory bound.
    def interrupted(signum, _frame):
        raise InterruptedError(f'enumerator interrupted by signal {signum}; no certification candidate')
    previous = signal.signal(signal.SIGTERM, interrupted)
    process = None
    try:
        process = subprocess.Popen([str(root / 'scripts/capped'), str(executable(root)), *argv],
                               cwd=root, stdout=out, stderr=err, start_new_session=True)
        return process.wait(timeout=timeout)
    except BaseException:
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
        raise
    finally:
        signal.signal(signal.SIGTERM, previous)


def enumerate_record(root, record, output, claim, wire, argv, timeout):
    output.mkdir(parents=True, exist_ok=True)
    candidate = output / 'certification-candidate.json'
    # Invalidate only the candidate owned by this invocation before any fallible
    # action. A prior successful run must not survive a failed refresh as NEW.
    candidate.unlink(missing_ok=True)
    before = inputs(root)
    binary_sha = check_build(root, before['build'])
    record_headers(record, claim)
    tracked = data_lines(record)
    source = run_output(root, ['git', 'rev-parse', 'HEAD'])
    dirty = bool(run_output(root, ['git', 'status', '--porcelain']))
    start = time.monotonic()
    started = datetime.now(timezone.utc).isoformat()
    with (output / 'observations.txt').open('w') as out, (output / 'enum-stats.txt').open('w') as err:
        try:
            exit_code = run_enumerator(root, argv, out, err, timeout)
        except subprocess.TimeoutExpired as error:
            raise Refused(f'enumerator TIMED OUT after {timeout}s; no certification candidate') from error
    elapsed = time.monotonic() - start
    if exit_code != 0:
        stats_path = output / 'enum-stats.txt'
        detail = stats_path.read_text(errors='replace')
        if len(detail) > 8192:
            detail = '[tail of stderr] ' + detail[-8192:]
        raise Refused(f'enumerator failed (exit {exit_code}); no certification candidate; '
                      f'stderr at {stats_path}: {detail.strip() or "(empty)"}')
    fresh = data_lines(output / 'observations.txt')
    validate_set(fresh, claim)
    require(set(fresh) == set(tracked), 're-certification DIFFERS from tracked observation set; no candidate, no re-pin')
    stats = (output / 'enum-stats.txt').read_text()
    # v1 admits checked state-graph certificates. Legacy records have no
    # source/build binding; unchecked bounded DFS does not mint this schema.
    require(re.search(r'\bengine=dedup\b', stats) and re.search(r'\bcertified=checkCert\b', stats),
            'fresh provenance requires checker-accepted dedup enumeration; no candidate')
    require(re.search(r'\bobservations=' + str(len(fresh)) + r'\b', stats),
            'enumerator observation count disagrees with output; no candidate')
    assert_stable(root, before, binary_sha, wire, claim['wire_sha256'])
    fresh_record = {'schema': CERT_SCHEMA, 'claim': claim, 'inputs': before,
                    'observations_sha256': observations_sha(fresh),
                    'receipt': {'source_commit': source, 'git_dirty': dirty,
                                'started_utc': started, 'finished_utc': datetime.now(timezone.utc).isoformat(),
                                'wall_seconds': round(elapsed, 3), 'captured_exit': exit_code,
                                'binary_sha256': binary_sha,
                                'stats_sha256': file_sha(output / 'enum-stats.txt'),
                                'command': ['golean', *claim['argv']], 'certifier': 'tools/certification.py'}}
    validate_provenance(record, fresh_record, before, claim)
    atomic_json(candidate, fresh_record)
    print(f'Fresh certification: unchanged set; seconds={elapsed:.3f}; candidate={candidate}')
    # Fresh evidence does not authorize replacing tracked provenance. CI stays
    # red until the candidate has been deliberately reviewed and installed.
    validate_provenance(record, load_provenance(record), before, claim)
    return 0


def case_rows(root):
    rows = {}
    # The existing normalizer owns optional columns, tag validation and case
    # ids; a second reader must not reinterpret its six-/nine-column sources.
    normalized = run_output(root, [str(root / 'scripts/coverage-manifest')])
    for line in normalized.splitlines():
        if not line or line.startswith('#'):
            continue
        fields = line.split('\t')
        require(len(fields) == 10, 'malformed normalized coverage manifest')
        case_id = fields[0]
        require(case_id not in rows, f'duplicate case id: {case_id}')
        rows[case_id] = fields[:1] + fields[2:]
    return rows


def current_claim(root, saved, rows):
    require(type(saved) is dict and type(saved.get('claim')) is dict, 'missing certification claim')
    claim = saved['claim']
    _, entry, args, _ = validate_invocation(claim)
    require(type(claim['case_id']) is str, 'invalid certification case id')
    require(claim['case_id'] in rows, 'certified case no longer in corpus: ' + claim['case_id'])
    row = rows[claim['case_id']]
    expected_args = [] if row[2] == '-' else row[2].split(',')
    require([entry, args, claim['row_status'], claim['lane'], claim['params']] ==
            [row[1], expected_args, row[3], row[6], row[8]],
            'STALE certification case metadata: ' + claim['case_id'])
    return claim


def check_records(root, *, check_executable=True):
    current = inputs(root)
    if check_executable:
        check_build(root, current['build'])
    rows = case_rows(root)
    records = sorted((root / 'baselines/certified').glob('*.certified.tsv'))
    sidecars = set((root / 'baselines/certified').glob('*.certified.json'))
    expected_sidecars = {provenance_path(p) for p in records}
    require(sidecars == expected_sidecars,
            f'certification TSV/JSON coverage differs: missing={sorted(str(p) for p in expected_sidecars - sidecars)}, '
            f'orphan={sorted(str(p) for p in sidecars - expected_sidecars)}')
    expected = {case_id for case_id, row in rows.items() if 'tier=slow' in row[8].split(',')}
    found = set()
    for record in records:
        saved = load_provenance(record)
        claim = current_claim(root, saved, rows)
        require(claim['case_id'] not in found, 'duplicate certified case: ' + claim['case_id'])
        found.add(claim['case_id'])
        require(record.name == claim['case_id'].replace('/', '__') + '.certified.tsv',
                'certification filename differs from case id')
        validate_provenance(record, saved, current, claim)
    require(found == expected, f'certification coverage differs: records={sorted(found)}, slow rows={sorted(expected)}')
    return {'records': len(records), 'inputs_sha256': digest(current), 'cases': sorted(found)}


def release_check(root, base):
    """Compare with the PRE-MERGE tip, even if the branch refreshed records.

    Exit 1 means the train owes a slow run. Invalid current evidence/query
    errors are exit 2. This shares the input inventory with both consumers.
    """
    check_records(root)
    base = run_output(root, ['git', 'rev-parse', '--verify', base + '^{commit}'])
    paths = run_output(root, ['git', 'ls-tree', '-r', '--name-only', base, '--', 'baselines/certified'])
    old_paths = {p for p in paths.splitlines() if p.endswith('.certified.json')}
    records = sorted((root / 'baselines/certified').glob('*.certified.json'))
    new_paths = {p.relative_to(root).as_posix() for p in records}
    if old_paths != new_paths:
        print('Recertification required: certification records added/removed since pre-merge tip')
        return 1
    for path in records:
        relative = path.relative_to(root).as_posix()
        previous = json.loads(run_output(root, ['git', 'show', base + ':' + relative]),
                              object_pairs_hook=unique_object)
        require(type(previous) is dict, 'invalid certification record at pre-merge tip: ' + relative)
        current = read_json(path)
        for field in ('schema', 'inputs', 'claim', 'observations_sha256'):
            if previous.get(field) != current[field]:
                print('Recertification required since pre-merge tip: ' + field + ': ' +
                      difference(previous.get(field), current[field]))
                return 1
    print('No certification inputs/claims changed since pre-merge tip ' + base)
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ['build-identity', 'inputs', 'build', 'check-build', 'check-records']:
        sub.add_parser(name)
    release = sub.add_parser('release-check')
    release.add_argument('--base', required=True, help='snapshot of main BEFORE this merge train')
    for name in ['cache', 'enumerate']:
        cmd = sub.add_parser(name)
        cmd.add_argument('--record', type=Path, required=True)
        cmd.add_argument('--output-dir', type=Path, required=True)
        cmd.add_argument('--case-id', required=True)
        cmd.add_argument('--lane', required=True)
        cmd.add_argument('--params', required=True)
        cmd.add_argument('--row-status', required=True)
        cmd.add_argument('--timeout', type=int, default=3600)
        cmd.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        if args.command == 'build-identity':
            print(canonical(build_inputs(root)))
        elif args.command == 'inputs':
            print(canonical(inputs(root)))
        elif args.command == 'build':
            return build(root)
        elif args.command == 'check-build':
            print(check_build(root, build_inputs(root)))
        elif args.command == 'check-records':
            print('Certification records: PASS; ' + canonical(check_records(root)))
        elif args.command == 'release-check':
            return release_check(root, args.base)
        elif args.command in ('cache', 'enumerate'):
            # Even malformed invocation/claim inputs invalidate prior output.
            # No failure before enumerate_record may leave an old candidate.
            output = root / args.output_dir
            for name in ('certification-candidate.json', 'observations.txt', 'enum-stats.txt'):
                (output / name).unlink(missing_ok=True)
            require(args.timeout > 0, 'enumeration timeout must be positive')
            argv = args.argv[1:] if args.argv[:1] == ['--'] else args.argv
            claim, wire = claim_for(root, args.case_id, args.lane, args.params, args.row_status, argv)
            if args.command == 'cache':
                return cache(root, root / args.record, root / args.output_dir, claim, wire)
            return enumerate_record(root, root / args.record, root / args.output_dir,
                                    claim, wire, argv, args.timeout)
        return 0
    except (Refused, OSError, subprocess.SubprocessError, ValueError, TypeError, KeyError, IndexError) as error:
        print('certification: ' + str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
