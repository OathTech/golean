#!/usr/bin/env python3
"""per-area-table.py — producer of per-area-table.tsv (docs/evidence/2026-09-03_noodler).
Reads artifacts/coverage/latest.tsv (columns: result, id, features, stage, detail)
written by the LAST `scripts/coverage run` / `scripts/ci --diff` in this tree and
tabulates the noodler/ rows per package. Usage, from the repo root, after a full run:
    python3 docs/evidence/2026-09-03_noodler/per-area-table.py > docs/evidence/2026-09-03_noodler/per-area-table.tsv
"""
import collections, sys
areas = collections.defaultdict(lambda: [0, 0, 0, []])
for line in open('artifacts/coverage/latest.tsv'):
    line = line.rstrip('\n')
    if not line or line.startswith('#') or line.startswith('result\t'):
        continue
    f = line.split('\t')
    res, cid, stage = f[0], f[1], f[3]
    if not cid.startswith('noodler/'):
        continue
    area = '/'.join(cid.split('/')[:2])
    a = areas[area]; a[0] += 1
    if res == 'PASS':
        a[1] += 1
    else:
        a[2] += 1; a[3].append(f'{cid}({stage})')
print('# producer: python3 docs/evidence/2026-09-03_noodler/per-area-table.py, reading artifacts/coverage/latest.tsv of the full `scripts/capped scripts/ci --diff` named in README.md')
print('package\trows\tpass\tfail\tborn_fail_ids(stage)')
for k in sorted(areas):
    a = areas[k]; print(f'{k}\t{a[0]}\t{a[1]}\t{a[2]}\t{" ".join(a[3]) or "-"}')
