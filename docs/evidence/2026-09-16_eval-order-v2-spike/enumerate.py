#!/usr/bin/env python3
"""Reference enumerator over evaluation-occurrence graphs — the spike for
docs/2026-09-16_evaluation-order-model-v2.md §1–§2 (disposable; [AGENT]).

It validates the RELATION, not any lowering: a sweep is a dependency graph
over evaluation OCCURRENCES (events, reads, lvalue identities, pure ops) with
guarded regions; a legal execution picks any READY occurrence (all deps
produced, region enabled) until none is pending, then runs phase 2 (the
stores / the statement's completion); the sweep's result is (status, value or
first failure, output, state). The semantics is the SET of results over all
legal executions. Graphs are hand-encoded per witness; expected sets are
asserted (fail closed: any mismatch exits 1). Fragment: integer locals,
slices of ints (nil-able headers over named backing arrays), index read /
write, closure calls that mutate, `+`, compound assignment, tuple assignment
phases, `||` regions, a buffered receive.
"""
import copy, sys

class Panic(Exception):
    pass

class Occ:
    """An occurrence. `run(st, vals) -> value` (may raise Panic). A GUARD
    occurrence (guard=binder, when=bool) tests vals[guard] == when: enabled →
    its `region` occurrences join the pending set (one of them must produce
    `out`); disabled → vals[out] = (not when) at once and the region never
    runs (an unexecuted short-circuit region contributes nothing)."""
    def __init__(self, name, deps=(), run=None, guard=None, when=True, region=(), out=None):
        self.name, self.deps, self.run = name, tuple(deps), run
        self.guard, self.when, self.region, self.out = guard, when, tuple(region), out

# ---- state helpers: slices are (header) either None or an array id; arrays live in st['arr'].
def hdr(st, var):
    return st['v'][var]
def length(st, h):
    return 0 if h is None else len(st['arr'][h])
def elem(st, h, i):
    n = length(st, h)
    if not (0 <= i < n):
        raise Panic(f"index out of range [{i}] with length {n}")
    return st['arr'][h][i]
def store(st, h, i, v):
    n = length(st, h)
    if not (0 <= i < n):
        raise Panic(f"index out of range [{i}] with length {n}")
    st['arr'][h][i] = v
def freeze(st):
    return (tuple(sorted(st['v'].items())), tuple((k, tuple(a)) for k, a in sorted(st['arr'].items())),
            tuple(st.get('chan', ())))

def enumerate_graph(occs, init, phase2):
    """Return {result_key: (n_trajectories, final_state)}; result_key =
    (status, payload, output, frozen state) with payload = the sweep's value
    (ok) or the first failure's text (panic)."""
    results = {}
    def record(status, payload, st, trace):
        key = (status, payload, tuple(st['out']), freeze(st))
        n, _ = results.get(key, (0, None))
        results[key] = (n + 1, st)
    def rec(pending, vals, st, trace):
        if not pending:
            st2 = copy.deepcopy(st)
            try:
                record('ok', phase2(st2, vals), st2, trace)
            except Panic as p:
                record('panic', str(p), st2, trace)
            return
        ready = [o for o in pending if all(d in vals for d in o.deps)]
        assert ready, f"no ready occurrence among {[o.name for o in pending]} (cycle)"
        for o in ready:
            st2, vals2 = copy.deepcopy(st), dict(vals)
            rest = [p for p in pending if p is not o]
            try:
                if o.guard is not None:
                    vals2[o.name] = (vals2[o.guard] == o.when)
                    if vals2[o.name]:
                        rest = rest + list(o.region)
                    else:
                        vals2[o.out] = (not o.when)
                else:
                    vals2[o.name] = o.run(st2, vals2)
            except Panic as p:
                record('panic', str(p), st2, trace + (o.name,))
                continue
            rec(rest, vals2, st2, trace + (o.name,))
    rec(list(occs), {}, copy.deepcopy(init), ())
    return results

FAILS = 0
def check(name, results, summarize, expected, forbid=()):
    global FAILS
    summ = {}
    for key, (n, _) in results.items():
        s = summarize(key)
        summ[s] = summ.get(s, 0) + n
    got = set(summ)
    print(f"{name}: outcome set = {sorted(got)}")
    print(f"   trajectories per outcome: {[(k, summ[k]) for k in sorted(summ)]}")
    if got != set(expected):
        print(f"   MISMATCH: expected {sorted(expected)}"); FAILS += 1
    for f in forbid:
        if f in got:
            print(f"   FORBIDDEN outcome present: {f}"); FAILS += 1
        else:
            print(f"   forbidden hybrid absent: {f}")

def state(v=None, arr=None, chan=None):
    st = {'v': dict(v or {}), 'arr': {k: list(a) for k, a in (arr or {}).items()}, 'out': []}
    if chan is not None:
        st['chan'] = list(chan)
    return st

def println(st, *xs):
    st['out'].append(' '.join(str(x) for x in xs))

# ---------------------------------------------------------------- W1  v := mut() + a
def w1():
    def mut(st, v): st['v']['a'] = 2; return 0
    occs = [Occ('E_mut', run=mut),
            Occ('R_a', run=lambda st, v: st['v']['a']),
            Occ('Op', deps=['E_mut', 'R_a'], run=lambda st, v: v['E_mut'] + v['R_a'])]
    def phase2(st, v): println(st, 'w1', v['Op']); return v['Op']
    check('W1 mut()+a', enumerate_graph(occs, state(v={'a': 1}), phase2), lambda k: k[1], {1, 2})

# ---------------------------------------------------------------- W2  v := a[b[0]] + mut()
def w2():
    def mut(st, v): st['arr']['A'][0] = 30; st['arr']['A'][1] = 40; st['arr']['B'][0] = 1; return 0
    occs = [Occ('R_b0', run=lambda st, v: elem(st, hdr(st, 'b'), 0)),
            Occ('R_ai', deps=['R_b0'], run=lambda st, v: elem(st, hdr(st, 'a'), v['R_b0'])),
            Occ('E_mut', run=mut),
            Occ('Op', deps=['R_ai', 'E_mut'], run=lambda st, v: v['R_ai'] + v['E_mut'])]
    def phase2(st, v): println(st, 'w2', v['Op']); return v['Op']
    init = state(v={'a': 'A', 'b': 'B'}, arr={'A': [10, 20], 'B': [0]})
    check('W2 a[b[0]]+mut()', enumerate_graph(occs, init, phase2), lambda k: k[1], {10, 30, 40})

# ---------------------------------------------------------------- W3  a[i] += mut()
def w3():
    def mut(st, v): st['v']['i'] = 1; return 1
    occs = [Occ('R_a', run=lambda st, v: hdr(st, 'a')),                      # header read
            Occ('R_i', run=lambda st, v: st['v']['i']),
            Occ('L', deps=['R_a', 'R_i'], run=lambda st, v: (v['R_a'], v['R_i'])),   # identity, no check
            Occ('Rd', deps=['L'], run=lambda st, v: elem(st, *v['L'])),      # the read, checked
            Occ('E_mut', run=mut),
            Occ('Op', deps=['Rd', 'E_mut'], run=lambda st, v: v['Rd'] + v['E_mut'])]
    def phase2(st, v):                                                       # the store, same identity
        store(st, v['L'][0], v['L'][1], v['Op']); println(st, 'w3', *st['arr']['A']); return None
    init = state(v={'a': 'A', 'i': 0}, arr={'A': [10, 20]})
    check('W3 a[i]+=mut()', enumerate_graph(occs, init, phase2), lambda k: k[2][-1] if k[2] else k[1],
          {'w3 11 20', 'w3 10 21'}, forbid=('w3 10 11',))

# ---------------------------------------------------------------- W4  _ = a[1] + b[2], both nil
def w4():
    occs = [Occ('R_a1', run=lambda st, v: elem(st, hdr(st, 'a'), 1)),
            Occ('R_b2', run=lambda st, v: elem(st, hdr(st, 'b'), 2)),
            Occ('Op', deps=['R_a1', 'R_b2'], run=lambda st, v: v['R_a1'] + v['R_b2'])]
    check('W4 a[1]+b[2]', enumerate_graph(occs, state(v={'a': None, 'b': None}), lambda st, v: None),
          lambda k: (k[0], k[1]),
          {('panic', 'index out of range [1] with length 0'), ('panic', 'index out of range [2] with length 0')})

# ---------------------------------------------------------------- W5  loop: println(a[0] + mut()) twice
def w5():
    def mut(st, v): st['v']['a'] = None; return 0
    def iteration(j):
        occs = [Occ('R_a0', run=lambda st, v: elem(st, hdr(st, 'a'), 0)),
                Occ('E_mut', run=mut),
                Occ('Op', deps=['R_a0', 'E_mut'], run=lambda st, v: v['R_a0'] + v['E_mut'])]
        def phase2(st, v): println(st, 'w5 iter', j, v['Op']); return v['Op']
        return occs, phase2
    # compose two dynamic sweeps: each iteration is a fresh graph instance over the previous outcome state
    program = {}
    occs, p2 = iteration(0)
    for key, (n, st) in enumerate_graph(occs, state(v={'a': 'A'}, arr={'A': [7]}), p2).items():
        if key[0] == 'panic':
            program[(key[0], key[1], key[2])] = program.get((key[0], key[1], key[2]), 0) + n; continue
        occs2, p22 = iteration(1)
        for key2, (n2, _) in enumerate_graph(occs2, st, p22).items():
            k = (key2[0], key2[1], key2[2]); program[k] = program.get(k, 0) + n * n2
    print(f"W5 loop: program outcome set = {sorted(program)}")
    print(f"   trajectories per outcome: {[(k, program[k]) for k in sorted(program)]}")
    expected = {('panic', 'index out of range [0] with length 0', ('w5 iter 0 7',)),
                ('panic', 'index out of range [0] with length 0', ())}
    global FAILS
    if set(program) != expected:
        print(f"   MISMATCH: expected {sorted(expected)}"); FAILS += 1
    if any(k[0] == 'ok' or len(k[2]) > 1 for k in program):
        print("   FORBIDDEN: an execution completed iteration 2 (stale binder)"); FAILS += 1
    else:
        print("   forbidden hybrid absent: no execution prints 7 twice / completes iteration 2")

# ---------------------------------------------------------------- W6  v := x + inc() + inc()
def w6():
    def inc(st, v): st['v']['x'] += 1; return 0
    occs = [Occ('R_x', run=lambda st, v: st['v']['x']),
            Occ('E1', run=inc), Occ('E2', deps=['E1'], run=inc),
            Occ('Op', deps=['R_x', 'E1', 'E2'], run=lambda st, v: v['R_x'] + v['E1'] + v['E2'])]
    def phase2(st, v): println(st, 'w6', v['Op']); return v['Op']
    check('W6 x+inc()+inc()', enumerate_graph(occs, state(v={'x': 0}), phase2), lambda k: k[1], {0, 1, 2})

# ---------------------------------------------------------------- X1  xs[ys[9]], b = zs[7], 2   (phases)
def x1():
    occs = [Occ('R_xs', run=lambda st, v: hdr(st, 'xs')),
            Occ('R_ys9', run=lambda st, v: elem(st, hdr(st, 'ys'), 9)),
            Occ('L1', deps=['R_xs', 'R_ys9'], run=lambda st, v: (v['R_xs'], v['R_ys9'])),
            Occ('R_zs7', run=lambda st, v: elem(st, hdr(st, 'zs'), 7))]
    def phase2(st, v):  # stores left to right, after every phase-1 occurrence
        store(st, v['L1'][0], v['L1'][1], v['R_zs7']); st['v']['b'] = 2; println(st, 'x1 ok', 2); return None
    init = state(v={'xs': 'X', 'ys': 'Y', 'zs': 'Z', 'b': 0}, arr={'X': [0]*3, 'Y': [0]*3, 'Z': [0]*3})
    check('X1 xs[ys[9]], b = zs[7], 2', enumerate_graph(occs, init, phase2), lambda k: (k[0], k[1]),
          {('panic', 'index out of range [9] with length 3'), ('panic', 'index out of range [7] with length 3')})

# ---------------------------------------------------------------- X2  v := b2i(z || h()) + x   (guarded region)
def x2(z, label):
    def h(st, v): st['v']['x'] = 2; return True
    region = [Occ('E_h', run=h), Occ('or', deps=['E_h'], run=lambda st, v: v['E_h'])]
    occs = [Occ('R_z', run=lambda st, v: st['v']['z']),
            Occ('G', deps=['R_z'], guard='R_z', when=False, region=region, out='or'),   # || : right runs iff left false
            Occ('E_b2i', deps=['or'], run=lambda st, v: 1 if v['or'] else 0),
            Occ('R_x', run=lambda st, v: st['v']['x']),
            Occ('Op', deps=['E_b2i', 'R_x'], run=lambda st, v: v['E_b2i'] + v['R_x'])]
    def phase2(st, v): println(st, label, v['Op']); return v['Op']
    check(f'X2 b2i(z||h())+x, z={z}', enumerate_graph(occs, state(v={'x': 1, 'z': z}), phase2), lambda k: k[1],
          {2, 3} if not z else {2})

# ---------------------------------------------------------------- X3  x[f()] += <-ch   (buffered receive)
def x3():
    def recv(st, v):
        if not st['chan']: raise Panic('blocked receive outside the terminating domain')
        return st['chan'].pop(0)
    occs = [Occ('E_f', run=lambda st, v: 9),
            Occ('R_x', run=lambda st, v: hdr(st, 'x')),
            Occ('L', deps=['R_x', 'E_f'], run=lambda st, v: (v['R_x'], v['E_f'])),
            Occ('Rd', deps=['L'], run=lambda st, v: elem(st, *v['L'])),
            Occ('E_recv', deps=['E_f'], run=recv),                              # lexical order among events: f before <-ch
            Occ('Op', deps=['Rd', 'E_recv'], run=lambda st, v: v['Rd'] + v['E_recv'])]
    def phase2(st, v): store(st, v['L'][0], v['L'][1], v['Op']); return None
    init = state(v={'x': 'X'}, arr={'X': [1]}, chan=[5])
    check('X3 x[f()] += <-ch', enumerate_graph(occs, init, phase2), lambda k: (k[0], k[1], f"len(ch)={len(k[3][2])}"),
          {('panic', 'index out of range [9] with length 1', 'len(ch)=0'),
           ('panic', 'index out of range [9] with length 1', 'len(ch)=1')})

# ---------------------------------------------------------------- negative controls (forced pairs are singletons)
def controls():
    # C1: f(g()) — argument before invocation (data edge); no unordered pair remains.
    def g(st, v): st['v']['t'] = 7; return 1
    occs = [Occ('E_g', run=g), Occ('E_f', deps=['E_g'], run=lambda st, v: v['E_g'] + st['v']['t'])]
    check('C1 f(g())', enumerate_graph(occs, state(v={'t': 0}), lambda st, v: v['E_f']), lambda k: k[1], {8})
    # C2: sink(a) with a a private local read by nothing else — one occurrence, singleton.
    occs = [Occ('R_a', run=lambda st, v: st['v']['a']), Occ('E_sink', deps=['R_a'], run=lambda st, v: v['R_a'])]
    check('C2 sink(a)', enumerate_graph(occs, state(v={'a': 3}), lambda st, v: v['E_sink']), lambda k: k[1], {3})
    # C3 (F9.5): sink(a, mut()) is NOT a singleton — the argument list still holds an unordered pair.
    def mut(st, v): st['v']['a'] = 2; return 0
    occs = [Occ('R_a', run=lambda st, v: st['v']['a']), Occ('E_mut', run=mut),
            Occ('E_sink', deps=['R_a', 'E_mut'], run=lambda st, v: v['R_a'])]
    check('C3 sink(a, mut())', enumerate_graph(occs, state(v={'a': 1}), lambda st, v: v['E_sink']), lambda k: k[1], {1, 2})

if __name__ == '__main__':
    for f in (w1, w2, w3, w4, w5, w6, x1, lambda: x2(False, 'x2 v'), lambda: x2(True, 'x2 w'), x3, controls):
        f()
    print('RESULT:', 'FAIL' if FAILS else 'PASS', f'({FAILS} mismatch(es))')
    sys.exit(1 if FAILS else 0)
