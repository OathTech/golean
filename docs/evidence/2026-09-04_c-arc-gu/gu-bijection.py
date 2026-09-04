#!/usr/bin/env python3
"""gu-bijection.py — the G-U stream-bijection certificate (2026-09-04, [AGENT]).

G-U makes the consumption rule uniform: a consult pops the choice stream iff
its bound is >= 2. Before G-U the `mapIter` site also popped at bound 1 (the
last MANDATORY candidate of a range-over-map). The behaviour SET is unchanged
(a width-1 pop chose the only member), but the stream REALIZATION shifts:
every later consult in that run reads one entry earlier. The bijection on
streams is: delete from the old stream exactly the entries the width-1
`mapIter` consults drew. This script applies that deletion to the OLD
tracer dump and checks the NEW machine reproduces the old trace on the
transformed streams, byte for byte.

  expect  <before-dir> <out-dir>
      From <before-dir>/batch.tsv + dump-*.tsv (the pre-G-U tracer run over
      the corpus: 6 streams per row) write
        <out-dir>/batch.tsv           the same rows, each stream replaced by
                                      its TRANSFORMED stream (the entries the
                                      old run consumed, minus the width-1
                                      mapIter draws; "default" when empty)
        <out-dir>/expected-dump.tsv   the old dump minus the (mapIter, 1)
                                      records, idx renumbered, the stream
                                      column relabelled to the transformed
                                      spec — what the new machine MUST emit
        <out-dir>/expected-results.tsv  (id, stream-position, status, obsHash)
        <out-dir>/stats.txt           counts
  compare <out-dir> <actual-dir>
      Compare <out-dir>/expected-dump.tsv against the sorted union of
      <actual-dir>/dump-*.tsv (the new binary run on <out-dir>/batch.tsv),
      and the expected (status, obsHash) per (id, position) against
      <actual-dir>/results-*.tsv. Exit 0 iff BOTH are identical; any other
      delta is printed and exits 1 (= STOP: a member outside the old set, or
      a consult the bijection does not account for).

Dump columns: id, stream, idx, phase, site, bound, streamValue ('-' = the
stream was exhausted), pick. The batch columns are the tracer's:
id, wire, function, args, streams (';'-separated specs).
"""
import sys, os, glob, collections

def read_dumps(d):
    """(id, spec) -> list of rows (in idx order), preserving file order."""
    groups = collections.OrderedDict()
    for f in sorted(glob.glob(os.path.join(d, 'dump-*.tsv'))):
        with open(f) as fh:
            for line in fh:
                line = line.rstrip('\n')
                if not line or line.startswith('id\t'):
                    continue
                cols = line.split('\t')
                assert len(cols) == 8, (f, line)
                groups.setdefault((cols[0], cols[1]), []).append(cols)
    for k, rows in groups.items():
        rows.sort(key=lambda c: int(c[2]))
        for i, c in enumerate(rows):
            assert int(c[2]) == i, ('non-contiguous idx', k, c)
    return groups

def read_results(d):
    """id -> list of (spec, status, obsHash) in file order (= stream order)."""
    res = collections.OrderedDict()
    for f in sorted(glob.glob(os.path.join(d, 'results-*.tsv'))):
        with open(f) as fh:
            for line in fh:
                line = line.rstrip('\n')
                if not line or line.startswith('id\t'):
                    continue
                c = line.split('\t')
                res.setdefault(c[0], []).append((c[1], c[2], c[13] if len(c) > 13 else '-'))
    return res

def is_width1_mapiter(c):
    return c[4] == 'mapIter' and int(c[5]) == 1

def transform(rows):
    """Return (transformed stream entries, kept records)."""
    entries = []
    kept = []
    for c in rows:
        if is_width1_mapiter(c):
            if c[6] != '-':
                # a popped entry: deleted from the stream
                continue
            continue  # exhausted width-1 consult: no entry, no record
        if c[6] != '-':
            entries.append(c[6])
        kept.append(c)
    return entries, kept

def spec_of(entries):
    return 'default' if not entries else ','.join(entries)

def cmd_expect(before, out):
    os.makedirs(out, exist_ok=True)
    groups = read_dumps(before)
    results = read_results(before)
    n_rows = n_streams = n_records = n_deleted = n_kept = n_shifted_streams = 0
    n_deleted_exhausted = 0
    per_site_before = collections.Counter()
    exp_dump = []
    exp_res = []
    with open(os.path.join(before, 'batch.tsv')) as fh, \
         open(os.path.join(out, 'batch.tsv'), 'w') as ob:
        for line in fh:
            line = line.rstrip('\n')
            if not line:
                continue
            rid, wire, fn, args, streams = line.split('\t')
            specs = streams.split(';')
            new_specs = []
            res_rows = results.get(rid, [])
            for pos, sp in enumerate(specs):
                rows = groups.get((rid, sp), [])
                for c in rows:
                    per_site_before[c[4]] += 1
                entries, kept = transform(rows)
                deleted = [c for c in rows if is_width1_mapiter(c)]
                n_deleted += len(deleted)
                n_deleted_exhausted += sum(1 for c in deleted if c[6] == '-')
                # a stream is "shifted" when a POPPED width-1 record precedes
                # a later record that read a live entry
                popped_idx = [int(c[2]) for c in deleted if c[6] != '-']
                if popped_idx and any(int(c[2]) > popped_idx[0] and c[6] != '-' for c in kept):
                    n_shifted_streams += 1
                nsp = spec_of(entries)
                new_specs.append(nsp)
                for i, c in enumerate(kept):
                    exp_dump.append('\t'.join([rid, nsp, str(i)] + c[3:]))
                n_records += len(rows)
                n_kept += len(kept)
                n_streams += 1
                if len(res_rows) == 1 and res_rows[0][0] == '-':
                    # a setup ERROR row: ONE results line for all streams
                    exp_res.append('\t'.join([rid, str(pos), res_rows[0][1], res_rows[0][2]]))
                elif pos < len(res_rows):
                    rsp, status, oh = res_rows[pos]
                    assert rsp == sp, ('results/batch stream order mismatch', rid, pos, rsp, sp)
                    exp_res.append('\t'.join([rid, str(pos), status, oh]))
                else:
                    exp_res.append('\t'.join([rid, str(pos), 'MISSING', '-']))
            ob.write('\t'.join([rid, wire, fn, args, ';'.join(new_specs)]) + '\n')
            n_rows += 1
    with open(os.path.join(out, 'expected-dump.tsv'), 'w') as f:
        for l in sorted(exp_dump):
            f.write(l + '\n')
    with open(os.path.join(out, 'expected-results.tsv'), 'w') as f:
        for l in sorted(exp_res):
            f.write(l + '\n')
    with open(os.path.join(out, 'stats.txt'), 'w') as f:
        f.write(f'rows={n_rows}\n(row,stream)={n_streams}\nrecords_before={n_records}\n'
                f'width1_mapIter_records_deleted={n_deleted} (of which at an exhausted stream: {n_deleted_exhausted})\n'
                f'records_expected_after={n_kept}\n'
                f'(row,stream)_with_a_realization_shift={n_shifted_streams}\n')
        for s, n in sorted(per_site_before.items()):
            f.write(f'before per-site {s}={n}\n')
    print(open(os.path.join(out, 'stats.txt')).read(), end='')

def cmd_compare(out, actual):
    exp = open(os.path.join(out, 'expected-dump.tsv')).read().splitlines()
    act = []
    for f in sorted(glob.glob(os.path.join(actual, 'dump-*.tsv'))):
        for line in open(f):
            line = line.rstrip('\n')
            if line and not line.startswith('id\t'):
                act.append(line)
    act.sort()
    ok = True
    if exp == act:
        print(f'DUMP: IDENTICAL ({len(exp)} records)')
    else:
        ok = False
        se, sa = set(exp), set(act)
        print(f'DUMP: DIFFERENT expected={len(exp)} actual={len(act)}')
        for l in sorted(se - sa)[:40]:
            print('  only-expected\t' + l)
        for l in sorted(sa - se)[:40]:
            print('  only-actual\t' + l)
    exp_res = open(os.path.join(out, 'expected-results.tsv')).read().splitlines()
    results = read_results(actual)
    act_res = []
    nstreams = collections.Counter(l.split('\t')[0] for l in exp_res)
    for rid, rows in results.items():
        if len(rows) == 1 and rows[0][0] == '-':
            for pos in range(nstreams[rid]):
                act_res.append('\t'.join([rid, str(pos), rows[0][1], rows[0][2]]))
            continue
        for pos, (sp, status, oh) in enumerate(rows):
            act_res.append('\t'.join([rid, str(pos), status, oh]))
    act_res.sort()
    if exp_res == act_res:
        print(f'RESULTS (status, obsHash per (row, stream position)): IDENTICAL ({len(exp_res)} lines)')
    else:
        ok = False
        se, sa = set(exp_res), set(act_res)
        print(f'RESULTS: DIFFERENT expected={len(exp_res)} actual={len(act_res)}')
        for l in sorted(se - sa)[:40]:
            print('  only-expected\t' + l)
        for l in sorted(sa - se)[:40]:
            print('  only-actual\t' + l)
    print('BIJECTION CHECK:', 'PASS' if ok else 'FAIL (STOP)')
    return 0 if ok else 1

if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[1] == 'expect':
        cmd_expect(sys.argv[2], sys.argv[3])
    elif len(sys.argv) == 4 and sys.argv[1] == 'compare':
        sys.exit(cmd_compare(sys.argv[2], sys.argv[3]))
    else:
        print(__doc__); sys.exit(2)
