#!/usr/bin/env python3
"""[AGENT] Fresh dispatch sentinels and compiled producer corruption controls."""
import csv
import io
import json
import os
import sys
from pathlib import Path
from typed_audit import ROOT, run_logged, scratch

# Independent pinned-Go results from the multi-package differential fixture.
EXPECTED = {
    'promotedBodies': [111, 222, 111, 222, 111, 222],
    'deepAndAlias': [111, 222, True, True],
    'embeddedInterfaces': [111, 222, 111, 222],
    'pointerSets': [False, False, True, True, 611, 922],
    'genericBodies': [711, 1022, 711, 1022],
    'unicodeBodies': [411, 311, 511, 822, 111, 222],
    'concreteValues': [111, 111],
    'constrainedMethods': [111, 222, 111, 222],
}


def main():
    corpus = ROOT / 'Corpus/coverage/exec/multipkg/private-method-dispatch'
    cli = ROOT / '.lake/build/bin/golean'
    with scratch(ROOT, 'method-identity-dispatch') as work:
        source = work / 'gopath/src'
        source.mkdir(parents=True)
        for package in ['red', 'blue']:
            (source / package).symlink_to(corpus / package, target_is_directory=True)
        env = os.environ | {'GO111MODULE': 'off', 'GOPATH': str(source.parent),
                            'GOCACHE': str(ROOT / 'artifacts/go-build-cache')}
        frontend = work / 'frontend'
        run_logged(['go', 'build', '-o', str(frontend), './tools/nativefrontend'],
                   work / 'clean-build.log', env=env)
        wire = work / 'clean.json'
        run_logged([str(frontend), '--dir', str(corpus), '--out', str(wire)],
                   work / 'clean-export.log', env=env)
        for subject, expected in EXPECTED.items():
            raw = run_logged([str(ROOT / 'scripts/capped'), str(cli), 'native-json-run',
                              '--input', str(wire), '--function', subject],
                             work / (subject + '.log'))
            observation = json.loads(raw)
            values = [v['value'] for v in observation.get('values', [])]
            tags = [v['tag'] for v in observation.get('values', [])]
            expected_tags = ['bool' if isinstance(v, bool) else 'int' for v in expected]
            if (observation.get('schema') != 'golean-observation-v1'
                    or observation.get('status') != 'ok' or values != expected
                    or tags != expected_tags or observation.get('output') != ''):
                raise RuntimeError(f'{subject}: wrong clean observation {observation}')
        print('Method dispatch: eight clean subjects match pinned-Go sentinels', flush=True)
        # Method table order carries no dispatch semantics. Exercise both
        # source order and its reversal: the old bare-name validator borrows
        # a foreign wrapper bit on the reversed, otherwise identical wire.
        reordered = work / 'method-order-reversed.json'
        reordered_program = json.loads(wire.read_text())
        reordered_program['methods'].reverse()
        reordered.write_text(json.dumps(reordered_program))
        for variant in [wire, reordered]:
            raw = run_logged([str(ROOT / 'scripts/capped'), str(cli), 'choice-trace',
                              '--input', str(variant), '--function', 'nilPrivateValue',
                              '--stream', '0', '--stream', '1'], work / (variant.stem + '-nil-trace.log'))
            traces = list(csv.DictReader(io.StringIO(raw), delimiter='\t'))
            if (len(traces) != 2 or {r['stream'] for r in traces} != {'0', '1'}
                    or any(r['status'] != 'panic' or r['perSite'] != 'nilValueMethodText=1'
                           or r['maxBound'] != '2' or r['violations'] != '0'
                           or r['alarms'] != '0' or r['driverAgreement'] != 'ok' for r in traces)):
                raise RuntimeError('private nil-value choice lost its package identity: ' + raw)
        print('Method choice trace: both nil-value text choices, both method orders, zero invariant violations', flush=True)
        # The graph reader must derive exactly the same target keys, and its
        # conservative interface expansion must not fuse private members.
        sys.dont_write_bytecode = True
        sys.path.insert(0, str(ROOT / 'tools/raftsubject'))
        import reachability
        program, bodies, _ = reachability.load(wire)
        for package, iface in [('red/inner', 'I'), ('blue/inner', 'J')]:
            anchor = next(m for m in program['methods'] if
                          m['recvType'] == package + '.' + iface and m['id']['name'] == 'm')
            anchor_key = reachability.method_key(anchor)
            caller = package + '.Read'
            target = next(m for m in program['methods'] if m['recvType'] == 'main.Mix'
                          and m['id'] == {'name': 'm', 'package': package})
            wrong = next(m for m in program['methods'] if m['recvType'] == 'main.Mix'
                         and m['id']['name'] == 'm' and m['id']['package'] != package)
            if (anchor_key not in bodies[caller]
                    or reachability.method_key(target) not in bodies[caller]
                    or reachability.method_key(wrong) in bodies[caller]):
                raise RuntimeError('wire call graph fused private interface dispatch: ' + caller)
        try:
            reachability.resolve_entries(program, ['main.Mix.m'])
        except ValueError as error:
            if 'ambiguous method entry main.Mix.m' not in str(error):
                raise
        else:
            raise RuntimeError('ambiguous method display label selected a target')
        for resolve in [lambda: reachability.resolve_entries(program, ['missingEntry']),
                        lambda: reachability.reach(bodies, ['missingEntry'])]:
            try:
                resolve()
            except ValueError as error:
                if str(error) != 'entry missingEntry is not on the wire':
                    raise
            else:
                raise RuntimeError('absent graph entry was silently accepted')
        print('Method graph: package-exact edges; ambiguous and absent entries rejected', flush=True)

        controls = [
            ('erase-package', 'declaration.go', 'pkg = obj.Pkg().Path()', 'pkg = ""',
             'error', 'unexported member has no package identity'),
            ('collide-wrappers', 'emit.go', 'key := methodFuncKey(tName, member)',
             'key := methodFuncKey(tName, memberID{Name: member.Name})',
             'stuck', 'dynamic type main.Mix has no method m'),
        ]
        for label, filename, old, new, status, reason in controls:
            original = ROOT / 'tools/nativefrontend' / filename
            text = original.read_text()
            if text.count(old) != 1:
                raise RuntimeError(f'{label}: mutation site changed or ambiguous')
            mutated = work / (label + '.go')
            mutated.write_text(text.replace(old, new))
            overlay = work / (label + '-overlay.json')
            overlay.write_text(json.dumps({'Replace': {str(original): str(mutated)}}))
            binary = work / label
            # Compilation and successful export are prerequisites. Neither a
            # syntax error nor an earlier frontend refusal counts as rejection.
            run_logged(['go', 'build', '-overlay', str(overlay), '-o', str(binary),
                        './tools/nativefrontend'], work / (label + '-build.log'), env=env)
            bad_wire = work / (label + '-wire.json')
            run_logged([str(binary), '--dir', str(corpus), '--out', str(bad_wire)],
                       work / (label + '-export.log'), env=env)
            raw = run_logged([str(ROOT / 'scripts/capped'), str(cli), 'native-json-run',
                              '--input', str(bad_wire), '--function', 'promotedBodies'],
                             work / (label + '-reject.log'), expected=1)
            observation = json.loads(raw)
            message = observation.get('message', '')
            if (observation.get('status') != status or reason not in message
                    or (label == 'erase-package' and '.id:' not in message)
                    or (label == 'collide-wrappers' and message != reason)):
                raise RuntimeError(f'{label}: wrong rejection {observation}')
            print(f'Method dispatch control: {label} compiled, exported, then rejected '
                  f'by {status}: {reason}', flush=True)


if __name__ == '__main__':
    main()
