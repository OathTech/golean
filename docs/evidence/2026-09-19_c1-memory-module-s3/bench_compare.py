#!/usr/bin/env python3
"""bench-compare.md producer (C1 S3 evidence): BEFORE / AFTER / AFTER-2 per point, medians net of each run's
empty probe, plus the four charter §6 S3 targets derived from the same numbers. Usage:
  python3 bench_compare.py bench-before.json bench-after.json bench-after2.json > bench-compare.md"""
import json, sys
def load(p):
    d = json.load(open(p)); m = d['meta']
    emp = [x for x in d['points'] if x['probe'] == 'empty'][0]['summary']['wall_median_s']
    pts = {}
    for x in d['points']:
        s = x['summary']
        pts[(x['probe'], tuple(x['args']))] = (s['wall_median_s'] - emp, '/'.join(s['statuses']), s['wall_min_s'] - emp, s['wall_max_s'] - emp)
    return m, emp, pts
runs = [load(p) for p in sys.argv[1:4]]
names = ['BEFORE', 'AFTER', 'AFTER-2']
print("# BEFORE / AFTER / AFTER-2 — every probe of `run-probes.py --plan full` (3 runs/point, medians, net of each run's empty probe)\n")
for n, (m, emp, _) in zip(names, runs):
    print(f"- **{n}**: binary `{m['golean_sha256'][:8]}…` at commit `{m['commit'][:8]}` (dirty: {m['runtime_tree_dirty']}), "
          f"{m['started_utc']}–{m['finished_utc']}, load1 {m['loadavg1_at_start']} → {m['loadavg1_at_end']}, empty probe median {emp:.4f} s")
print("\nBEFORE = main `0f114df6`'s binary; AFTER = the S3 working tree's binary (the bytes the runtime commit carries; proof-only edits followed before the commit); "
      "AFTER-2 = the committed tree `fd99b021`'s gate-built binary, re-run on a quiet box. Producer: `bench_compare.py` (reproduced in the README).\n")
keys = sorted(set().union(*[set(r[2]) for r in runs]), key=lambda k: (k[0], k[1]))
order = []
for r in runs:
    for k in r[2]:
        if k not in order: order.append(k)
print("| probe(args) | BEFORE net s | AFTER net s | AFTER-2 net s | AFTER/BEFORE | AFTER-2/BEFORE | statuses (B / A / A2) |")
print("|---|---:|---:|---:|---:|---:|---|")
def ratio(a, b):
    return f"{a/b:.3f}" if b and b > 0 and a is not None else "—"
for k in order:
    vals = [r[2].get(k) for r in runs]
    if any(v is None for v in vals): continue
    b, a, a2 = (v[0] for v in vals)
    print(f"| `{k[0]}{k[1]}` | {b:.4f} | {a:.4f} | {a2:.4f} | {ratio(a,b) if k[0]!='empty' else '—'} | {ratio(a2,b) if k[0]!='empty' else '—'} | {vals[0][1]} / {vals[1][1]} / {vals[2][1]} |")
print("\n## The four charter §6 S3 targets, derived from the table (BEFORE → AFTER → AFTER-2)\n")
def g(r, probe, *args): return r[2][(probe, tuple(args))][0]
def seq(r, probe, argl): return [g(r, probe, *a) for a in argl]
an_args = [(1000,), (4000,), (16000,), (32000,)]
ag_args = [(250,), (500,), (1000,), (2000,), (4000,)]
print("| target | BEFORE | AFTER | AFTER-2 | verdict |")
print("|---|---|---|---|---|")
def fmt_seq(v, unit='s', nd=3): return ' / '.join(f"{x:.{nd}f}" for x in v) + f" {unit}"
def rat(v): return ', '.join(f"×{v[i+1]/v[i]:.2f}" for i in range(len(v)-1))
cols = []
for r in runs:
    v = seq(r, 'alloc_new', an_args)
    cols.append(f"{fmt_seq(v)} ({rat(v)})")
verd = []
for r in runs[1:]:
    v = seq(r, 'alloc_new', an_args); rs = [v[i+1]/v[i] for i in range(3)]
    verd.append(("MET" if v[3] < 1.0 and all(x <= 4.4 for x in rs) else f"32k {'<' if v[3]<1 else '≥'} 1 s; ×4 ratios {'all ≤ 4.4' if all(x<=4.4 for x in rs) else 'one step ' + ', '.join(f'{x:.2f}' for x in rs if x>4.4) + ' > 4.4'}"))
print(f"| `alloc_new` linear: n = 1k/4k/16k/32k successive ×4 ratios ≤ 4.4; n = 32k < 1 s | {cols[0]} | {cols[1]} | {cols[2]} | AFTER **{verd[0]}**; AFTER-2 **{verd[1]}** |")
cols = []; verd = []
for i, r in enumerate(runs):
    h0 = g(r, 'heap_then_scalar', 0, 20000) - g(r, 'heap_then_scalar', 0, 0)
    hs = [(h, g(r, 'heap_then_scalar', h, 20000) - g(r, 'heap_then_scalar', h, 0)) for h in (1000, 10000, 40000)]
    cols.append(f"h=0 {h0:.3f} s; " + '; '.join(f"h={h} {x:.3f} s ({x/h0:.2f}×)" for h, x in hs))
    if i: verd.append("MET" if all(x/h0 <= 1.2 for _, x in hs) else "MISS")
print(f"| the (h) scalar phase: 20k iterations after h live cells (`heap_then_scalar(h,20000) − heap_then_scalar(h,0)`) within 1.2× of h = 0 | {cols[0]} | {cols[1]} | {cols[2]} | AFTER **{verd[0]}**; AFTER-2 **{verd[1]}** |")
cols = []; verd = []
for i, r in enumerate(runs):
    v = seq(r, 'append_grow', ag_args); cols.append(f"{fmt_seq(v, nd=4)} ({rat(v)})")
    if i:
        rs = [v[j+1]/v[j] for j in range(4)]
        verd.append("MET" if all(x <= 2.2 for x in rs) else "steps " + ', '.join(f"{ag_args[j][0]}→{ag_args[j+1][0]} ×{rs[j]:.2f}" for j in range(4) if rs[j] > 2.2) + " > 2.2 (the other steps ≤ 2.2)")
print(f"| `append_grow` successive ×2 ratios ≤ 2.2 (the S1-owed target) | {cols[0]} | {cols[1]} | {cols[2]} | AFTER **{verd[0]}**; AFTER-2 **{verd[1]}** |")
cols = []; verd = []
b = g(runs[0], 'scalar', 80000)
for i, r in enumerate(runs):
    v = g(r, 'scalar', 80000); cols.append(f"{v:.3f} s" + (f" ({(v/b-1)*100:+.1f} %)" if i else ""))
    if i: verd.append("MET" if abs(v/b - 1) <= 0.10 else "MISS")
print(f"| scalar step baseline within 10 % (`scalar(80000)`) | {cols[0]} | {cols[1]} | {cols[2]} | AFTER **{verd[0]}**; AFTER-2 **{verd[1]}** |")
print("\nNoise floor: each run's empty probe spans about ±1 ms across its repetitions (`wall_min_s`/`wall_max_s` in the json); a net below ~10 ms "
      "(`alloc_new(1000)`, `append_grow(250)`, `append_grow(500)`, the `append_cap`/`write_fixed` rows) carries that ±1 ms as ±10–20 % on the point and "
      "up to ±40 % on a ratio of two such points. Ratios between points ≥ 0.1 s are the load-bearing ones.")
