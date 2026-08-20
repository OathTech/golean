#!/usr/bin/env python3
"""Fix round #4, item F-1: independent re-derivation of the Iris import
closure over proofs/GoLeanProofs/Examples/.

Written from scratch (NOT a reuse of .tmp/irisdep.py) so the round-3 output
serves as a cross-check, not as the source.

Module resolution: a module name A.B.C is looked up as a file in a set of
source roots. Roots here: the proofs package (proofs/ -> GoLeanProofs.*) and
the core package (repo root -> GoLean.*). Anything unresolvable is either an
Iris/Std/Lean external or a genuinely missing module; `Iris.*` is the target
marker and is never followed (it is external to this repo).
"""
import os, re, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC_ROOTS = [os.path.join(ROOT, "proofs"), ROOT]

IMPORT_RE = re.compile(r'^\s*import\s+([A-Za-z_][A-Za-z0-9_.\']*)')


def modpath(mod):
    rel = mod.replace('.', os.sep) + '.lean'
    for r in SRC_ROOTS:
        p = os.path.join(r, rel)
        if os.path.isfile(p):
            return p
    return None


def imports_of(mod):
    p = modpath(mod)
    if p is None:
        return None  # unresolvable (external)
    out = []
    with open(p, encoding='utf-8') as f:
        for line in f:
            m = IMPORT_RE.match(line)
            if m:
                out.append(m.group(1))
    return out


def is_iris(mod):
    return mod == 'Iris' or mod.startswith('Iris.')


# --- enumerate the Examples modules -------------------------------------
EX_DIR = os.path.join(ROOT, 'proofs', 'GoLeanProofs', 'Examples')
examples = []
for dirpath, dirnames, filenames in os.walk(EX_DIR):
    for fn in sorted(filenames):
        if fn.endswith('.lean'):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, os.path.join(ROOT, 'proofs'))
            examples.append(rel[:-len('.lean')].replace(os.sep, '.'))
# also the aggregator proofs/GoLeanProofs/Examples.lean if present
agg = os.path.join(ROOT, 'proofs', 'GoLeanProofs', 'Examples.lean')
examples = sorted(set(examples))

# --- closures -----------------------------------------------------------
closure_cache = {}


def closure(mod, stack=()):
    """Set of resolvable repo modules reachable from mod (excluding mod),
    plus a flag for whether Iris.* is reached."""
    if mod in closure_cache:
        return closure_cache[mod]
    if mod in stack:
        return (frozenset(), False)  # cycle guard
    imps = imports_of(mod)
    if imps is None:
        return (frozenset(), False)
    acc = set()
    hits = False
    for i in imps:
        if is_iris(i):
            hits = True
            continue
        if modpath(i) is None:
            continue
        acc.add(i)
        sub, sh = closure(i, stack + (mod,))
        acc |= sub
        hits = hits or sh
    res = (frozenset(acc), hits)
    closure_cache[mod] = res
    return res


def direct_iris(mod):
    imps = imports_of(mod)
    return bool(imps) and any(is_iris(i) for i in imps)


iris_examples = []
for m in examples:
    cl, hit = closure(m)
    if hit or direct_iris(m):
        iris_examples.append(m)

print(f"Examples modules: {len(examples)}")
print(f"transitively import Iris: {len(iris_examples)}")
print(f"Iris-free: {len(examples) - len(iris_examples)}")
print()

# Which modules in each Iris-reaching closure DIRECTLY import Iris?
gw = collections.Counter()
per_example_gws = {}
for m in iris_examples:
    cl, _ = closure(m)
    members = set(cl) | {m}
    g = sorted(x for x in members if direct_iris(x))
    per_example_gws[m] = g
    for x in g:
        gw[x] += 1

print("modules in an Iris-reaching closure that DIRECTLY import Iris:")
for k, v in gw.most_common():
    print(f"  {k:50s} {v}")
print()

universal = sorted(k for k, v in gw.items() if v == len(iris_examples))
print(f"present in ALL {len(iris_examples)} closures: {len(universal)}")
for u in universal:
    print(f"  {u}")
print()

# StmtOps specifically
S = 'GoLeanProofs.Laws.StmtOps'
in_closure = [m for m in iris_examples if S in (set(closure(m)[0]) | {m})]
print(f"{S} in closure of: {len(in_closure)} / {len(iris_examples)}")
missing = [m for m in iris_examples if m not in in_closure]
print(f"  NOT containing it: {missing}")
print(f"  StmtOps directly imports Iris? {direct_iris(S)}  imports={imports_of(S)}")
print()

direct = [m for m in in_closure if S in (imports_of(m) or [])]
print(f"  import {S} DIRECTLY: {len(direct)}")
print(f"  reach it via a sibling: {len(in_closure) - len(direct)}")
print()

# Iris-free check for the FibMemo/Rec closure
R = 'GoLeanProofs.Examples.FibMemo.Rec'
rcl, rhit = closure(R)
print(f"{R}: closure size (incl. self) = {len(rcl) + 1}, reaches Iris = {rhit}")

if len(sys.argv) > 1 and sys.argv[1] == 'detail':
    print()
    print("--- Rec closure members (excl self) ---")
    for m in sorted(rcl):
        print("  ", m)
    print()
    F = 'GoLeanProofs.Examples.Fib'
    print("Fib imports:", imports_of(F))
    fcl, fhit = closure(F)
    print("Fib direct-Iris members:",
          sorted(x for x in (set(fcl) | {F}) if direct_iris(x)))
