#!/usr/bin/env python3
"""[AGENT] F8 executable controls. No tracked source/record is mutated."""
from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from unittest.mock import patch

import certification as c
from typed_audit import scratch, link_package

ROOT = Path(__file__).resolve().parents[1]
COUNT = 0


def passed(label):
    global COUNT
    COUNT += 1
    print('Certification control PASS: ' + label, flush=True)


def rejected(label, needle, action):
    try:
        action()
    except (c.Refused, ValueError) as error:
        if needle not in str(error):
            raise RuntimeError(f'{label}: wrong refusal, expected {needle}: {error}') from error
    else:
        raise RuntimeError(label + ': accepted invalid evidence')
    passed(label + ' -> ' + needle)


def run(argv, root, log, expected=0, env=None, timeout=180):
    result = subprocess.run(argv, cwd=root, env=env, text=True, capture_output=True, timeout=timeout)
    log.write_text(result.stdout + result.stderr)
    if result.returncode != expected:
        raise RuntimeError(f'{argv} exited {result.returncode}, expected {expected}; {log}\n'
                           + result.stdout + result.stderr)
    return result.stdout + result.stderr


def overlay(root, target, current):
    target.mkdir()
    names = set(current['files']) | set(current['build']['files']) | {'.gitignore'}
    for name in sorted(names):
        path = target / name
        path.parent.mkdir(parents=True, exist_ok=True)
        # Go refuses symlinks as go:embed inputs. These small TSV data files
        # are copied; compiled artifacts remain symlinks throughout.
        if name == '.gitignore' or name.endswith('.tsv'):
            path.write_bytes((root / name).read_bytes())
        else:
            path.symlink_to(root / name)
    binary = c.executable(target)
    binary.parent.mkdir(parents=True)
    binary.symlink_to(c.executable(root))
    subprocess.run(['git', 'init', '-q', str(target)], check=True)
    subprocess.run(['git', 'add', '.'], cwd=target, check=True)
    subprocess.run(['git', '-c', 'user.name=F8 control', '-c', 'user.email=f8@example.invalid',
                    'commit', '-qm', 'Equivalent input fixture'], cwd=target, check=True)


def replace_source(root, name, text):
    path = root / name
    path.unlink()
    path.write_text(text)


def shell_cache(root, directory, record, claim, wire, expected=0, needle='CERTIFIED-CACHED'):
    """Execute the actual shared shell consumer with each lane's row locals.

    The full runner additionally exercises oracle/coupling; this isolates the
    cache boundary so an oracle/build failure cannot masquerade as rejection.
    """
    source = (ROOT / 'scripts/diff-coverage').read_text()
    start = source.index('certified_observations() {')
    end = source.index('\n}\n', start) + 3
    wrapper = source[start:end]
    command = '''set -uo pipefail
report_fail() { printf '%s\\n' "$4"; }
id="$1" lane="$2" params="$3" expected_status=ok features=f8
LEAN_ENUM_SLOW_TIMEOUT_SECONDS=180 GOLEAN_SLOW=0
record="$4" directory="$5"
shift 5
''' + wrapper + '\ncertified_observations "$record" "$directory" "$@"\n'
    argv = [str(wire) if x == '<wire>' else x for x in claim['argv']]
    out = run(['bash', '-c', command, 'f8-control', claim['case_id'], claim['lane'],
               claim['params'], str(record), str(directory), *argv], root,
              directory.parent / (directory.name + '.log'), expected)
    if expected == 0:
        out += (directory / 'certification.txt').read_text()
    if needle not in out:
        raise RuntimeError('shell consumer did not name ' + needle + ': ' + out)
    if expected and (directory / 'observations.txt').exists():
        raise RuntimeError('failed cache consumer left readable observations')


def main():
    started = time.monotonic()
    current = c.inputs(ROOT)
    c.check_build(ROOT, current['build'])
    with scratch(ROOT, 'certification-controls') as directory:
        fixture = directory / 'equivalent-checkout'
        overlay(ROOT, fixture, current)
        # Source mutation tests reuse the already measured toolchain value;
        # real process consumers below independently hash the installation.
        with patch.object(c, 'toolchain', return_value=current['build']['toolchain']):
            assert c.inputs(fixture) == current
            c.check_build(fixture, current['build'])
            passed('equivalent checkout and linked executable')
            (fixture / 'docs').mkdir()
            (fixture / 'docs/control.md').write_text('Documentation-only commit.\n')
            subprocess.run(['git', 'add', 'docs/control.md'], cwd=fixture, check=True)
            subprocess.run(['git', '-c', 'user.name=F8 control', '-c', 'user.email=f8@example.invalid',
                            'commit', '-qm', 'Docs only'], cwd=fixture, check=True)
            assert c.inputs(fixture) == current
            passed('docs-only commit retains input identity')

        go = directory / 'subject'
        go.mkdir()
        (go / 'main.go').write_text('''package main
func main() {}
func one() int { return 1 }
func pick() int {
 c := make(chan int, 2)
 go func() { c <- 1 }()
 go func() { c <- 2 }()
 a := <-c
 b := <-c
 return a*10+b
}
''')
        wire = directory / 'wire.json'
        env = dict(os.environ, GO111MODULE='off', GOCACHE=str(ROOT / 'artifacts/go-build-cache'))
        run(['go', 'run', './tools/nativefrontend', '--dir', str(go), '--out', str(wire)],
            ROOT, directory / 'frontend.log', env=env)
        wire_sha = c.file_sha(wire)
        saved_records = []
        for lane, entry, count in [('membership', 'pick', 2), ('confluent', 'one', 1)]:
            params = 'width=4,sites=40,work=2000000,engine=dedup,tier=slow'
            if lane == 'membership':
                params += ',members=2'
            argv = ['coverage-observations', '--input', str(wire), '--function', entry,
                    '--max-width', '4', '--max-sites', '40', '--cap', '64', '--work-cap', '2000000',
                    '--expect-status', 'ok', '--engine', 'dedup']
            claim, _ = c.claim_for(fixture, 'control/' + lane, lane, params, 'ok', argv)
            outdir = directory / (lane + '-enum')
            outdir.mkdir()
            raw = subprocess.run([str(ROOT / 'scripts/capped'), str(c.executable(ROOT)), *argv],
                                 cwd=ROOT, text=True, capture_output=True, timeout=180)
            (outdir / 'seed.log').write_text(raw.stderr)
            assert raw.returncode == 0 and 'certified=checkCert' in raw.stderr, raw.stderr
            record = directory / (lane + '.certified.tsv')
            record.write_text(f'# params: {params}\n# wire-sha256: {wire_sha}\n' + raw.stdout)
            assert len(c.data_lines(record)) == count
            # Real successful enumeration can create initial provenance only
            # after comparing the actual checker-approved output with the set.
            with patch.object(c, 'toolchain', return_value=current['build']['toolchain']):
                rejected(lane + ' missing sidecar after fresh unchanged-set run',
                         'missing certification provenance',
                         lambda: c.enumerate_record(fixture, record, outdir, claim, wire, argv, 180))
                candidate = outdir / 'certification-candidate.json'
                assert candidate.is_file()
                candidate.replace(c.provenance_path(record))
                saved = c.load_provenance(record)
                c.validate_provenance(record, saved, current, claim)
            shell_cache(fixture, directory / (lane + '-cache'), record, claim, wire)
            passed(lane + ' actual shell consumer accepts fresh unchanged set')
            saved_records.append((record, saved, claim, argv, outdir))

        record, saved, claim, argv, outdir = saved_records[0]
        def validate(value):
            return c.validate_provenance(record, value, current, claim)
        for label, path, value, needle in [
            ('schema', ['schema'], 'future', 'unknown certification schema'),
            ('missing receipt', ['receipt'], {}, 'certification receipt: expected fields'),
            ('failed receipt', ['receipt', 'captured_exit'], 137, 'no successful enumeration'),
            ('Boolean exit', ['receipt', 'captured_exit'], False, 'no successful enumeration'),
            ('bad receipt command', ['receipt', 'command'], [], 'command differs'),
            ('nonfinite wall', ['receipt', 'wall_seconds'], float('inf'), 'non-finite wall'),
            ('entry', ['claim', 'argv'], claim['argv'] + ['--function', 'other'], 'STALE certification claim'),
            ('argument', ['claim', 'argv'], claim['argv'] + ['--arg-int', '1'], 'STALE certification claim'),
            ('params', ['claim', 'params'], 'width=5', 'STALE certification claim'),
            ('wire', ['claim', 'wire_sha256'], '0' * 64, 'STALE certification claim'),
            ('lane', ['claim', 'lane'], 'confluent', 'STALE certification claim'),
            ('status', ['claim', 'row_status'], 'panic', 'STALE certification claim'),
            ('observation policy', ['claim', 'observation_schema'], 'future', 'STALE certification claim'),
            ('toolchain distribution', ['inputs', 'build', 'toolchain', 'distribution_sha256'], '0' * 64, 'distribution_sha256'),
            ('Go version', ['inputs', 'oracle'], 'go version go0.0 linux/amd64', 'oracle'),
            ('omitted dependency', ['inputs', 'build', 'files'], {}, 'STALE certification'),
            ('set bytes', ['observations_sha256'], '0' * 64, 'observation bytes changed')]:
            bad = deepcopy(saved)
            cursor = bad
            for key in path[:-1]:
                cursor = cursor[key]
            cursor[path[-1]] = value
            rejected(label, needle, lambda: validate(bad))
        malformed = directory / 'malformed.json'
        malformed.write_text('{"schema":1,"schema":1}')
        rejected('duplicate fields', 'duplicate JSON field', lambda: c.read_json(malformed))
        malformed.write_text('{"n":NaN}')
        rejected('nonfinite JSON', 'non-finite JSON', lambda: c.read_json(malformed))
        for flag in ('--max-width', '--max-sites', '--cap', '--work-cap', '--expect-status', '--engine'):
            bad = deepcopy(claim)
            bad['argv'][bad['argv'].index(flag) + 1] = '999'
            rejected('effective ' + flag, 'invocation differs', lambda: c.validate_invocation(bad))

        with patch.object(c, 'toolchain', return_value=current['build']['toolchain']):
            for name in ['GoLean/GoCore/Ops.lean', 'GoLean/CLI.lean',
                         'GoLean/EnumDedup.lean', 'GoLean/GoCore/EnumDedupCheck.lean', 'GoLean/NativeToIR.lean',
                         'scripts/diff-coverage', 'lakefile.toml']:
                assert (fixture / name).is_file(), name
                original = (ROOT / name).read_text()
                suffix = '\n-- F8 mutation\n' if name.endswith('.lean') else '\n# F8 mutation\n'
                replace_source(fixture, name, original + suffix)
                changed = c.inputs(fixture)
                rejected(name, name, lambda: c.validate_provenance(record, saved, changed, claim))
                if name.startswith('GoLean/') or name == 'lakefile.toml':
                    rejected('old binary/new ' + name, 'STALE executable build',
                             lambda: c.check_build(fixture, changed['build']))
                (fixture / name).unlink()
                (fixture / name).symlink_to(ROOT / name)
            added = fixture / 'GoLean/F8NewDependency.lean'
            added.write_text('def f8Dependency : Nat := 1\n')
            (fixture / '.git/info/exclude').write_text('GoLean/F8NewDependency.lean\n')
            changed = c.inputs(fixture)
            rejected('new ignored dependency', 'F8NewDependency.lean',
                     lambda: c.validate_provenance(record, saved, changed, claim))
            added.unlink()
            omitted = fixture / 'GoLean/GoCore/Ops.lean'
            omitted.unlink()
            rejected('tracked missing dependency', 'missing dependency: GoLean/GoCore/Ops.lean',
                     lambda: c.inputs(fixture))
            omitted.symlink_to(ROOT / 'GoLean/GoCore/Ops.lean')
            main_source = (ROOT / 'Main.lean').read_text()
            replace_source(fixture, 'Main.lean', 'import Tests.GoCoreEval\n' + main_source)
            rejected('new excluded import', 'outside certified import roots', lambda: c.inputs(fixture))
            replace_source(fixture, 'Main.lean', 'import GoLean.Missing\n' + main_source)
            rejected('omitted import', 'import dependency omitted', lambda: c.inputs(fixture))
            (fixture / 'Main.lean').unlink()
            (fixture / 'Main.lean').symlink_to(ROOT / 'Main.lean')
            with patch.dict(os.environ, {'LEAN_PATH': '/an/override'}):
                rejected('build override', 'uncertified build environment override: LEAN_PATH',
                         lambda: c.build_inputs(fixture))
            override = fixture / 'lakefile.lean'
            override.write_text('import Lake\nopen Lake DSL\npackage GoLean\n')
            rejected('Lake configuration override', 'configuration override: lakefile.lean',
                     lambda: c.build_inputs(fixture))
            override.unlink()
            config = (ROOT / 'lakefile.toml').read_text()
            replace_source(fixture, 'lakefile.toml', 'moreLinkArgs = ["external.o"]\n' + config)
            rejected('external native link input', 'uncertified Lake build options',
                     lambda: c.build_inputs(fixture))
            replace_source(fixture, 'lakefile.toml', config.replace('root = "Main"', 'root = "OtherMain"'))
            rejected('uninventoried executable root', 'target must have root Main',
                     lambda: c.build_inputs(fixture))
            replace_source(fixture, 'lakefile.toml', config + '\nmoreLeanArgs = ["-DunsafeOption=true"]\n')
            rejected('extra target options', 'uncertified Lake target options',
                     lambda: c.build_inputs(fixture))
            (fixture / 'lakefile.toml').unlink()
            (fixture / 'lakefile.toml').symlink_to(ROOT / 'lakefile.toml')

        # A real semantic diagnostic mutation compiles, at the identical wire.
        # Imported siblings are symlinks; the changed module's outputs are
        # owned by this scratch. No shared artifact can be overwritten.
        compile_dir = directory / 'compiled-core'
        link_package(ROOT, compile_dir, 'GoLean.GoCore.Ops')
        mutant = (ROOT / 'GoLean/GoCore/Ops.lean').read_text()
        assert 'unknown type index' in mutant
        mutant = mutant.replace('unknown type index', 'F8 control unknown type index', 1)
        source = compile_dir / 'GoLean/GoCore/Ops.lean'
        source.write_text(mutant)
        env = dict(os.environ, LEAN_PATH=str(compile_dir))
        run([str(ROOT / 'scripts/capped'), 'lean', '-o', str(source.with_suffix('.olean')), str(source)],
            compile_dir, compile_dir / 'compile.log', env=env)
        assert source.with_suffix('.olean').is_file() and c.file_sha(wire) == wire_sha
        replace_source(fixture, 'GoLean/GoCore/Ops.lean', mutant)
        for item, _, item_claim, _, _ in saved_records:
            shell_cache(fixture, directory / (item_claim['lane'] + '-stale'), item, item_claim, wire,
                        expected=1, needle='GoLean/GoCore/Ops.lean')
            passed(item_claim['lane'] + ' compiled core mutation rejected at unchanged wire')
        (fixture / 'GoLean/GoCore/Ops.lean').unlink()
        (fixture / 'GoLean/GoCore/Ops.lean').symlink_to(ROOT / 'GoLean/GoCore/Ops.lean')

        # A real process timeout and an injected failing exit follow the real
        # positive compiled-enumerator control. A missing tool is no PASS.
        with patch.object(c, 'toolchain', return_value=current['build']['toolchain']):
            candidate = outdir / 'certification-candidate.json'
            candidate.write_text(json.dumps(saved))
            rejected('real timeout cannot mint/retain candidate', 'TIMED OUT',
                     lambda: c.enumerate_record(fixture, record, outdir, claim, wire, argv, 0.000001))
            assert not candidate.exists()
            candidate.write_text(json.dumps(saved))
            def failed_enumerator(_root, _argv, _out, err, _timeout):
                err.write('F8 injected graph refusal\n')
                return 137
            with patch.object(c, 'run_enumerator', side_effect=failed_enumerator):
                rejected('failed exit preserves cause and cannot mint/retain candidate', 'F8 injected graph refusal',
                         lambda: c.enumerate_record(fixture, record, outdir, claim, wire, argv, 1))
            assert not candidate.exists()
            original = record.read_text()
            record.write_text(original.replace('"value":12', '"value":999'))
            assert record.read_text() != original, 'changed-set control must change actual observation bytes'
            rejected('changed set cannot mint candidate', 'DIFFERS from tracked observation set',
                     lambda: c.enumerate_record(fixture, record, outdir, claim, wire, argv, 180))
            assert not candidate.exists()
            record.write_text(original)
            c.enumerate_record(fixture, record, outdir, claim, wire, argv, 180)
            assert candidate.is_file()
            passed('fresh unchanged-set refresh restores candidate')

        # Invalid arguments fail before enumeration and must still remove a
        # prior candidate. Exercise the public command, without mocks.
        command = ['python3', 'tools/certification.py', 'enumerate', '--record', str(record),
                   '--output-dir', str(outdir), '--case-id', claim['case_id'], '--lane', 'membership',
                   '--params', claim['params'], '--row-status', 'ok', '--', 'unknown-command']
        text = run(command, fixture, directory / 'bad-command.log', expected=2)
        assert 'requires coverage-observations' in text and not candidate.exists()
        passed('invalid command removes prior candidate')
        # Current-record coverage and release comparisons use real Git
        # snapshots. Only the normalized two-row fixture is substituted.
        rows = {}
        certdir = fixture / 'baselines/certified'
        certdir.mkdir()
        for item, item_saved, item_claim, _, _ in saved_records:
            dest = certdir / (item_claim['case_id'].replace('/', '__') + '.certified.tsv')
            shutil.copyfile(item, dest)
            c.atomic_json(c.provenance_path(dest), item_saved)
            _, entry, _, _ = c.validate_invocation(item_claim)
            rows[item_claim['case_id']] = [item_claim['case_id'], entry, '-', 'ok', '-',
                                           'goroutines,channels', item_claim['lane'], 'fixture', item_claim['params']]
        with patch.object(c, 'toolchain', return_value=current['build']['toolchain']), \
                patch.object(c, 'case_rows', return_value=rows):
            assert c.check_records(fixture)['records'] == 2
            subprocess.run(['git', 'add', 'baselines/certified'], cwd=fixture, check=True)
            subprocess.run(['git', '-c', 'user.name=F8 control', '-c', 'user.email=f8@example.invalid',
                            'commit', '-qm', 'Fixture certificate metadata'], cwd=fixture, check=True)
            assert c.release_check(fixture, 'HEAD') == 0
            assert c.release_check(fixture, 'HEAD^') == 1
            passed('release rule accepts unchanged and requires legacy/new records')
            dest = certdir / 'control__membership.certified.json'
            previous = c.read_json(dest)
            bad = deepcopy(previous)
            bad['inputs']['files']['scripts/diff-coverage'] = '0' * 64
            c.atomic_json(dest, bad)
            subprocess.run(['git', 'add', str(dest)], cwd=fixture, check=True)
            subprocess.run(['git', '-c', 'user.name=F8 control', '-c', 'user.email=f8@example.invalid',
                            'commit', '-qm', 'Previous semantic input fixture'], cwd=fixture, check=True)
            c.atomic_json(dest, previous)
            assert c.release_check(fixture, 'HEAD') == 1
            passed('branch refresh does not bypass merged-tip recertification')
            orphan = certdir / 'orphan.certified.json'
            orphan.write_text('{}')
            rejected('orphan sidecar', 'TSV/JSON coverage differs', lambda: c.check_records(fixture))
            orphan.unlink()
            rows['control/new-slow'] = rows['control/membership']
            rejected('uncovered slow row', 'certification coverage differs', lambda: c.check_records(fixture))
            del rows['control/new-slow']
            rows['control/membership'][1] = 'other'
            rejected('current entry drift', 'STALE certification case metadata', lambda: c.check_records(fixture))
            rows['control/membership'][1] = 'pick'

        # Exercise the entire confluent slow-cache branch, including real
        # frontend emission, cache comparison, oracle and driver coupling.
        # The current corpus supplies full membership coverage in --slow/--diff.
        # All build outputs are overlaid; metadata is tiny and owned locally.
        for original in (ROOT / '.lake/build').rglob('*'):
            target = fixture / '.lake/build' / original.relative_to(ROOT / '.lake/build')
            if target.exists():
                continue
            if original.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                if original.suffix in ('.trace', '.hash', '.json'):
                    shutil.copyfile(original, target)
                else:
                    target.symlink_to(original)
        conf_claim = saved_records[1][2]
        manifest = directory / 'confluent-manifest.tsv'
        manifest.write_text('\t'.join(['control/confluent', str(go), 'one', '-', 'ok',
                                       'goroutines,channels', '-', 'confluent', 'F8 cache control',
                                       conf_claim['params']]) + '\n')
        env = dict(os.environ, GOLEAN_COVERAGE_JOBS='1', GOLEAN_SLOW='0', TMPDIR=str(directory))
        result = run([str(fixture / 'scripts/capped'), str(fixture / 'scripts/diff-coverage'), str(manifest)],
                     fixture, directory / 'confluent-full-run.log', env=env)
        latest = (fixture / 'artifacts/coverage/latest.tsv').read_text()
        assert 'PASS\tcontrol/confluent' in latest and 'CERTIFIED-CACHED' in latest, result + latest
        passed('complete confluent cache branch with real oracle and coupling')
        conf_record = certdir / 'control__confluent.certified.json'
        conf_saved = c.read_json(conf_record)
        bad = deepcopy(conf_saved)
        bad['inputs']['files']['scripts/diff-coverage'] = '0' * 64
        c.atomic_json(conf_record, bad)
        result = run([str(fixture / 'scripts/capped'), str(fixture / 'scripts/diff-coverage'), str(manifest)],
                     fixture, directory / 'confluent-full-negative.log', env=env, expected=1)
        latest = (fixture / 'artifacts/coverage/latest.tsv').read_text()
        assert 'FAIL\tcontrol/confluent' in latest and 'STALE certification' in latest, result + latest
        c.atomic_json(conf_record, conf_saved)
        passed('complete confluent cache branch refuses stale inputs by name')

        # Final clean positives prove controls did not leak into the source or
        # executable. Also pin both branch call sites to the shared boundary.
        source = (ROOT / 'scripts/diff-coverage').read_text()
        assert source.count('certified_observations "baselines/certified/') == 2
        for item, _, item_claim, _, _ in saved_records:
            shell_cache(fixture, directory / (item_claim['lane'] + '-clean-after'), item, item_claim, wire)
        assert c.inputs(ROOT) == current
        passed('both consumers clean after controls; root inputs unchanged')
    print(f'Certification controls: {COUNT} PASS; wall_seconds={time.monotonic() - started:.3f}', flush=True)


if __name__ == '__main__':
    main()
