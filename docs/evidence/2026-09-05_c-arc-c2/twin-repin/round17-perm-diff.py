#!/usr/bin/env python3
# perm-diff.py — the C2 half of the round-17 twin structural diff: an
# ORDER-aware comparison of the two pins' sections (the fr19 producer keys
# entries by name and so cannot see a permutation). Sections other than
# `types` must be identical INCLUDING order; `types` must be the same
# multiset (byte-equal per canonicalized entry, every entry carrying the
# fr19 `display`/`pkg` fields on both sides) in a different order, with
# the new order satisfying the C2 dependency contract.
import json, sys, hashlib
old_p, new_p = sys.argv[1], sys.argv[2]
ob, nb = open(old_p,'rb').read(), open(new_p,'rb').read()
old, new = json.loads(ob), json.loads(nb)
print("old sha256", hashlib.sha256(ob).hexdigest())
print("new sha256", hashlib.sha256(nb).hexdigest())
canon = lambda e: json.dumps(e, sort_keys=True, ensure_ascii=False)
for sec in sorted(set(old)|set(new)):
    if sec == 'types': continue
    same = canon(old.get(sec)) == canon(new.get(sec))
    print(f"{sec}: {'IDENTICAL (order included)' if same else 'DIFFERS'}")
ot, nt = old['types'], new['types']
print(f"types: old {len(ot)} entries, new {len(nt)} entries")
oc, nc = sorted(map(canon, ot)), sorted(map(canon, nt))
print("types is a permutation (same multiset, byte-equal per canonicalized entry):", oc == nc)
def fields_ok(ts):
    return all(set(e) == {'name','def','display','pkg'} for e in ts)
print("every type entry carries exactly name/def/display/pkg — old:", fields_ok(ot), " new:", fields_ok(nt))
opos = {e['name']: i for i, e in enumerate(ot)}
moved = [(opos[e['name']], j, e['name']) for j, e in enumerate(nt) if opos.get(e['name']) != j]
print(f"entries that moved: {len(moved)} of {len(nt)}")
print("old_idx -> new_idx  name")
for o, n, name in moved:
    print(f"{o:>4} -> {n:>4}  {name}")
# the C2 order contract: struct fields / defined targets, through array elems, refer only to EARLIER entries
def edges(ty):
    k = ty.get('kind')
    if k == 'named': return [ty['name']]
    if k == 'array': return edges(ty['elem'])
    return []
def def_edges(d):
    if d['kind'] == 'struct': return [n for f in d['fields'] for n in edges(f['type'])]
    if d['kind'] == 'defined': return edges(d['target'])
    return []
def violations(ts):
    pos = {e['name']: i for i, e in enumerate(ts)}
    v = []
    for i, e in enumerate(ts):
        for dep in def_edges(e['def']):
            if dep == 'struct{}': continue
            if dep in pos and pos[dep] >= i: v.append((e['name'], dep, i, pos[dep]))
    return v
vo, vn = violations(ot), violations(nt)
print(f"order-contract violations: old {len(vo)}, new {len(vn)}")
for v in vo[:20]: print("  old:", v)
for v in vn: print("  NEW VIOLATION:", v)
