#!/usr/bin/env python3
# twin-structural-diff.py — the producer of structural-diff.txt (lane
# fr19-bug097; tracked since the audit fix round R12, 2026-09-05 — the
# first run used an untracked inline script that omitted the methodSets
# section). Compares the OLD twin wire pin with the NEW one section by
# section: funcs / methods / types / globals / methodSets / fileOrder, then
# the remaining top-level keys. Every changed entry is diffed leaf by leaf;
# a leaf change whose two sides are both frontend temporaries of one
# family ($cN / $swfN / $swiN / $tsN / $litN / $resN / $tmpN …) is classed
# `temp-renumber` (program-wide counters shift when a body starts
# lowering); everything else is `other` and is printed. Run from the repo
# root:
#   git show <old-commit>:baselines/pins/twin-chdriver.wire.json > .tmp/old.json
#   python3 docs/evidence/2026-09-05_fr19-bug097/twin-repin/twin-structural-diff.py \
#       .tmp/old.json baselines/pins/twin-chdriver.wire.json > structural-diff.txt
import hashlib, json, re, sys
from collections import Counter

old_path, new_path = sys.argv[1], sys.argv[2]
old_bytes, new_bytes = open(old_path, 'rb').read(), open(new_path, 'rb').read()
old, new = json.loads(old_bytes), json.loads(new_bytes)

print("# twin wire structural diff — lane fr19-bug097 (FR-19 scope-ordinal TypeIds, BUG-097 anonymous-interface keys, BUG-059 display records), 2026-09-05")
print("# producer: docs/evidence/2026-09-05_fr19-bug097/twin-repin/twin-structural-diff.py (tracked since audit fix round R12)")
print("#   old = baselines/pins/twin-chdriver.wire.json at the lane's fork (main b77f3298); new = the re-pinned file, which")
print("#   scripts/check-frontend-pins certifies byte-equal to a fresh emit over the twin assembly")
print("#   (raftsubject/{quorum,raftpb,tracker,proto,confchange,raft} + tools/raftsubject/twin-*.go;")
print("#   GO111MODULE=off go run ./tools/nativefrontend --dir <assembly> --out <new>)")
print("old sha256", hashlib.sha256(old_bytes).hexdigest())
print("new sha256", hashlib.sha256(new_bytes).hexdigest())

TEMP = re.compile(r'^\$[A-Za-z]+\d+$')

def leaves(o, path=''):
    if isinstance(o, dict):
        for k in sorted(o):
            yield from leaves(o[k], path + '.' + k)
    elif isinstance(o, list):
        for i, v in enumerate(o):
            yield from leaves(v, path + '[%d]' % i)
    else:
        yield path, o

def leaf_diff(a, b):
    """Leaf-level changes between two JSON values: list of (path, old, new).
    A declaration that goes stub -> body (an `unsupported` marker on one
    side only) is diffed at TOP-LEVEL-FIELD granularity — the body is new
    wholesale, not a set of renumbered leaves — so it reports as one
    `other` change per moved field (body / recv.id / unsupported)."""
    if isinstance(a, dict) and isinstance(b, dict) and (('unsupported' in a) != ('unsupported' in b)):
        out = []
        for k in sorted(set(a) | set(b)):
            x, y = a.get(k, '<absent>'), b.get(k, '<absent>')
            if x != y:
                if isinstance(x, dict) and isinstance(y, dict) and k == 'recv':
                    out.extend(('.%s%s' % (k, p), xx, yy) for p, xx, yy in leaf_diff(x, y))
                else:
                    out.append(('.' + k, x if not isinstance(x, (dict, list)) else json.dumps(x, sort_keys=True),
                                y if not isinstance(y, (dict, list)) else json.dumps(y, sort_keys=True)))
        return out
    la, lb = dict(leaves(a)), dict(leaves(b))
    out = []
    for p in sorted(set(la) | set(lb)):
        x, y = la.get(p, '<absent>'), lb.get(p, '<absent>')
        if x != y:
            out.append((p, x, y))
    return out

def classify(x, y):
    if isinstance(x, str) and isinstance(y, str) and TEMP.match(x) and TEMP.match(y) \
       and re.sub(r'\d+$', '', x) == re.sub(r'\d+$', '', y):
        return 'temp-renumber'
    return 'other'

def short(v):
    s = repr(v)
    return s if len(s) <= 80 else s[:77] + '..."'

def section(name, okey, nkey, keyf, note=None):
    oe = {keyf(e): e for e in old.get(okey, [])}
    ne = {keyf(e): e for e in new.get(nkey, [])}
    added = [k for k in ne if k not in oe]
    removed = [k for k in oe if k not in ne]
    changed = [k for k in oe if k in ne and oe[k] != ne[k]]
    print("%s: added %d removed %d changed %d" % (name, len(added), len(removed), len(changed)))
    for k in added:
        print("  +", k)
    for k in removed:
        print("  -", k)
    classes = Counter()
    others = []
    for k in changed:
        for p, x, y in leaf_diff(oe[k], ne[k]):
            c = classify(x, y)
            classes[c] += 1
            if c == 'other':
                others.append((k, p, x, y))
    if changed:
        print("  change classes over all changed %s: %s" % (name, dict(sorted(classes.items()))))
        if classes and set(classes) == {'temp-renumber'}:
            print("  (every changed %s differs ONLY by program-wide temporary renumbering — $cN/$swfN/$swiN/$tsN — the downstream shift of quorum.MajorityConfig.Describe now lowering)" % name)
    if note:
        note(oe, ne, changed, others)
    return added, removed, changed, others

def funcs_note(oe, ne, changed, others):
    for k, p, x, y in others:
        print("  ~ %s: %s: %s -> %s" % (k, p, short(x), short(y)))

def methods_note(oe, ne, changed, others):
    by = {}
    for k, p, x, y in others:
        by.setdefault(k, []).append("%s: %s -> %s" % (p, short(x), short(y)))
    for k, parts in by.items():
        kind = "stub->body; " if any(p.startswith('.unsupported') for p in parts) else ""
        print("  ~ %s: %s%s" % (k, kind, "; ".join(parts)))

def types_note(oe, ne, changed, others):
    for k in changed:
        o, n = oe[k], ne[k]
        addedf = sorted(set(n) - set(o)); removedf = sorted(set(o) - set(n))
        same_def = o.get('def') == n.get('def')
        extra = ""
        if addedf == ['display', 'pkg']:
            extra = "display=%r pkg=%r" % (n['display'], n['pkg'])
        print("  ~ %s (fields added: %s; fields removed: %s; %s; def identical: %s)"
              % (k, ",".join(addedf) or "-", ",".join(removedf) or "-", extra or "no display/pkg change", same_def))

def plain_note(oe, ne, changed, others):
    for k, p, x, y in others:
        print("  ~ %s: %s: %s -> %s" % (k, p, short(x), short(y)))

section("funcs", "funcs", "funcs", lambda e: e['name'], funcs_note)
section("methods", "methods", "methods", lambda e: "%s.%s" % (e.get('recvType'), e.get('name')), methods_note)
section("types", "types", "types", lambda e: e['name'], types_note)
section("globals", "globals", "globals", lambda e: e['name'], plain_note)
section("methodSets", "methodSets", "methodSets", lambda e: e['type'], plain_note)
ofo = [(u['package'], tuple(u['files'])) for u in old.get('fileOrder', [])]
nfo = [(u['package'], tuple(u['files'])) for u in new.get('fileOrder', [])]
print("fileOrder: identical: %s" % (ofo == nfo))
if ofo != nfo:
    print("  old:", ofo); print("  new:", nfo)
rest_same = all(old.get(k) == new.get(k) for k in set(old) | set(new)
                if k not in ('funcs', 'methods', 'types', 'globals', 'methodSets', 'fileOrder'))
print("top-level keys identical: %s; remaining top-level values identical: %s" % (sorted(old) == sorted(new), rest_same))
