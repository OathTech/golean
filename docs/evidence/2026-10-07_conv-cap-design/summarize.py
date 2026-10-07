# [AGENT] b6 probe summary: member sets per (kind, operand class, n) vs the model.
import collections, sys
R = {}; R4 = {}
for line in open('roundup.txt'):
    _, n, r, r4 = line.split(); R[int(n)] = int(r); R4[int(n)] = int(r4)
def load(fn):
    d = collections.defaultdict(set); regimes = collections.defaultdict(dict)
    for line in open(fn):
        kind, shape, n, cap = line.split(); n = int(n); cap = int(cap)
        cls = 'lit' if shape.startswith('lit/') else 'nonlit'
        d[(kind, cls, n)].add(cap); regimes[(kind, cls, n)][shape] = cap
    return d, regimes
dflt, reg = load('conv.default.txt'); nz, _ = load('conv.nozerocopy.txt')
def model(kind, cls, n):
    if cls == 'lit': return {n}
    if kind == 'bytes': return {n, R[n]} | ({32} if n <= 32 else set())
    return {R4[n]} | ({32} if n <= 32 else set())
bad = 0; rows = []
for key in sorted(dflt, key=lambda k: (k[0], k[1], k[2])):
    kind, cls, n = key; m = model(*key); got = dflt[key]
    ok = (got == m); floor = all(c >= n for c in got)
    zc = sorted(got - nz.get(key, set()))  # members present only with zero-copy on
    if not ok or not floor: bad += 1
    rows.append((kind, cls, n, sorted(got), sorted(m), 'ok' if ok else 'MISMATCH', 'ok' if floor else 'BELOW-LEN', zc,
                 ';'.join(f"{s}={c}" for s, c in sorted(reg[key].items()))))
with open('envelope.tsv', 'w') as f:
    f.write('kind\toperand\tn\tmeasured_members\tmodel_members\tmodel_check\tspec_floor\tzero_copy_only\tper_regime\n')
    for r in rows: f.write('\t'.join(str(x) for x in r) + '\n')
print('rows', len(rows), 'mismatches', bad)
for r in rows:
    if r[5] != 'ok' or r[6] != 'ok': print('BAD', r)
# compact view: bytes nonlit and runes nonlit at the interesting lengths
for kind in ('bytes', 'runes'):
    for cls in ('nonlit', 'lit'):
        print(kind, cls, ' '.join(f"{n}:{'/'.join(map(str, sorted(dflt[(kind, cls, n)])))}" for (k, c, n) in sorted(dflt) if k == kind and c == cls))
