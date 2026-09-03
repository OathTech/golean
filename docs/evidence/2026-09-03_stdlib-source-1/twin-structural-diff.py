#!/usr/bin/env python3
# twin-structural-diff.py — structural inspection of the twin-wire pin move
# (stdlib-source-1, 2026-09-03). Compares an OLD pin (git object or file)
# with a NEW wire, after two SEMANTICALLY INERT normalizations: (1) the
# global-cell ids shift by the number of NEW library globals (library units
# initialize first, so every user gid moves by that constant); (2) the
# frontend's program-wide temporary counters ($cN, $swiN, $litN-free names,
# ...) are renamed canonically per declaration in order of first
# appearance. What remains is the semantic delta. Run from the repo root:
#   python3 docs/evidence/2026-09-03_stdlib-source-1/twin-structural-diff.py <old.json> <new.json>
import json, re, sys
old = json.load(open(sys.argv[1])); new = json.load(open(sys.argv[2]))
og = [g['name'] for g in old.get('globals', [])]; ng = [g['name'] for g in new.get('globals', [])]
lib = [g for g in ng if g not in og]; shift = len(lib)
print("# producer: docs/evidence/2026-09-03_stdlib-source-1/twin-structural-diff.py")
print("new library globals:", shift, "| user global order preserved:", [g for g in ng if g in og] == og, "| library globals precede user globals:", ng[:shift] == lib)
print("globals only-in-old:", sorted(set(og) - set(ng)))
print("globals only-in-new:", lib)
def canon(obj, shift_gid):
    s = json.dumps(obj, sort_keys=True)
    if shift_gid:
        s = re.sub(r'"gid": (\d+)', lambda m: '"gid": %d' % (int(m.group(1)) - shift), s)
    names = {}
    def ren(m):
        k = m.group(0)
        if k not in names: names[k] = '$T%d' % len(names)
        return names[k]
    return re.sub(r'\$[A-Za-z]+\d+', ren, s)
of = {f['name']: f for f in old['funcs']}; nf = {f['name']: f for f in new['funcs']}
print("funcs only-in-old:", sorted(set(of) - set(nf)))
print("funcs only-in-new:", sorted(set(nf) - set(of)))
print("funcs changed (after normalization):", sorted(n for n in of if n in nf and canon(of[n], False) != canon(nf[n], True)))
om = {(m.get('recvType'), m.get('name')): m for m in old['methods']}; nm = {(m.get('recvType'), m.get('name')): m for m in new['methods']}
print("methods only-in-old:", sorted(set(om) - set(nm)))
print("methods only-in-new:", sorted(set(nm) - set(om)))
print("methods changed (after normalization):", sorted(k for k in om if k in nm and canon(om[k], False) != canon(nm[k], True)))
ot = {t['name'] for t in old['types']}; nt = {t['name'] for t in new['types']}
print("types only-in-old:", sorted(ot - nt)); print("types only-in-new:", sorted(nt - ot))
oms = {(m['type'], m['coverage']) for m in old['methodSets']}; nms = {(m['type'], m['coverage']) for m in new['methodSets']}
print("methodSets only-in-old:", sorted(oms - nms)); print("methodSets only-in-new:", sorted(nms - oms))
print("fileOrder old:", [u['package'] for u in old['fileOrder']]); print("fileOrder new:", [u['package'] for u in new['fileOrder']])
for k in sorted(set(old) | set(new)):
    if k in ('funcs', 'methods', 'types', 'globals', 'fileOrder', 'methodSets'): continue
    if old.get(k) != new.get(k): print("top-level differs:", k)
