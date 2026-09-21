#!/usr/bin/env python3
"""Reference enumerator over evaluation-occurrence graphs — the spike for
docs/2026-09-16_evaluation-order-model-v2.md (v2.1) §1–§2 (disposable; [AGENT]).

It validates the RELATION, not any lowering: a sweep is a dependency graph
over evaluation OCCURRENCES (events, reads, target identities, pure ops,
guard entries, completions) with guarded regions. Two edge sorts, kept apart
(second review R2): VALUE dependencies (`deps` — the binders a body
consumes) and ORDER prerequisites (`after` — E1/F edges, discharged by a
DONE or a SKIPPED occurrence; a skip never invents a value). Scheduler, the
three cases of R2: (i) no pending active work → phase 2 (the stores / the
statement's completion); (ii) ready set nonempty → branch on every ready
occurrence; (iii) pending active work with no ready occurrence → a NAMED
malformed-graph refusal, never a stuck run. A value dependency on a binder
confined to a skipped region is refused by name (the only valid join is the
region's completion binder). Every node, region nodes included, has a STATIC
canonical rank (declaration order, a region inline behind its guard); slot 0
= the least rank among the ready; the slot-0 trajectory is printed as the
canonical draw. Results: MEMBERS (status ok|panic, payload, output, frozen
state) and REFUSALS (`blocked`: a receive that would block — outside the
terminating domain, reported apart, never a member). Expected sets,
forbidden hybrids and refusals are asserted; any mismatch exits 1 (fail
closed). Fragment: int/bool locals; slices of ints (nil-able headers over
named backing arrays — rebinding a header leaves the old array observable);
index read/write with bounds panics; closure calls that mutate; `+`;
compound assignment (identity once); tuple-assignment phases; `||`/`&&`
regions, nested; a buffered receive. Graph encodings for R1/R2/R6 adapted
from the review's `check.py` (`review/eval-order-model-v2-0916` @ b788e582,
docs/evidence/2026-09-16_eval-order-v2-review/check.py), re-encoded on the
repaired protocol.
"""
import copy, sys

class Panic(Exception):
    pass

class Blocked(Exception):
    """A receive that would block: a refusal outside the domain, not a member."""

class Malformed(Exception):
    """Scheduler case (iii) and the skipped-value check: refused by name."""

class Occ:
    """An occurrence. `run(st, vals) -> value` (may raise Panic/Blocked).
    `deps`: value dependencies (binders consumed); `after`: order
    prerequisites (E1/F). A GUARD ENTRY (guard=binder, when=bool) tests
    vals[guard] == when: enabled → its `region` occurrences (which must
    contain the COMPLETION node named `out`, producing the logical result)
    join the pending set; disabled → vals[out] = (not when) at once, `out`
    counts as done, every other region node is SKIPPED (discharges `after`
    edges, produces nothing)."""
    def __init__(self, name, deps=(), after=(), run=None, guard=None, when=True, region=(), out=None):
        self.name, self.deps, self.after, self.run = name, tuple(deps), tuple(after), run
        self.guard, self.when, self.region, self.out = guard, when, tuple(region), out

def flatten(occs):
    out = []
    for o in occs:
        out.append(o); out.extend(flatten(o.region))
    return out

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
            tuple(st.get('chan', ())),
            tuple((k, tuple(sorted(m.items()))) for k, m in sorted(st.get('maps', {}).items())))

def enumerate_graph(occs, init, phase2):
    """Return ({result_key: (n_trajectories, final_state)}, canonical); result_key =
    (status, payload, output, frozen state) with payload = the sweep's value (ok),
    the first failure's text (panic) or the refusal's text (blocked); canonical =
    {'trace', 'key'} of the slot-0 trajectory."""
    rank = {o.name: i for i, o in enumerate(flatten(occs))}
    results, canonical = {}, {}
    def record(status, payload, st, trace, canon):
        key = (status, payload, tuple(st['out']), freeze(st))
        n, _ = results.get(key, (0, None))
        results[key] = (n + 1, st)
        if canon:
            canonical['key'], canonical['trace'] = key, trace
    def rec(pending, vals, done, skipped, st, trace, canon):
        if not pending:                                   # (i) no pending active work → completion
            st2 = copy.deepcopy(st)
            try:
                record('ok', phase2(st2, vals), st2, trace, canon)
            except Panic as p:
                record('panic', str(p), st2, trace, canon)
            return
        # §1 G is STATIC: the invalid-join check runs over EVERY unsettled occurrence —
        # pending, or inside a region not yet entered — as soon as the producer is
        # skipped (the machine's `skippedDep?` fires on the ACTIVE occurrence at that
        # moment). Before the Stage B audit (R2, `docs/2026-09-16_unseq-stage-b-audit.md`,
        # 2026-09-16) the loop ran over `pending` only, so a use confined to a LATER-
        # skipped region completed silently (witness R2/A3 below); the machine refused it.
        for o in flatten(occs):
            if o.name in done or o.name in skipped:
                continue
            for d in o.deps:
                if d in skipped:
                    raise Malformed(f"{o.name}: value dependency on '{d}', confined to a skipped region (no valid join)")
        ready = sorted([o for o in pending if all(d in vals for d in o.deps)
                        and all(a in done or a in skipped for a in o.after)], key=lambda o: rank[o.name])
        if not ready:                                     # (iii) pending active work, nothing ready
            raise Malformed(f"no ready occurrence among {[o.name for o in pending]}: "
                            "pending active work with no ready occurrence (malformed graph)")
        for j, o in enumerate(ready):                     # (ii) branch; slot j = j-th in canonical rank
            st2, vals2, done2, skipped2 = copy.deepcopy(st), dict(vals), set(done), set(skipped)
            rest = [p for p in pending if p is not o]
            try:
                if o.guard is not None:
                    vals2[o.name] = (vals2[o.guard] == o.when)
                    if vals2[o.name]:
                        rest = rest + list(o.region)
                    else:                                 # short-circuit result completes the region
                        vals2[o.out] = (not o.when)
                        skipped2.update(r.name for r in flatten(o.region) if r.name != o.out)
                        done2.add(o.out)
                else:
                    vals2[o.name] = o.run(st2, vals2)
            except Panic as p:
                record('panic', str(p), st2, trace + (o.name,), canon and j == 0); continue
            except Blocked as b:
                record('blocked', str(b), st2, trace + (o.name,), canon and j == 0); continue
            done2.add(o.name)
            rec(rest, vals2, done2, skipped2, st2, trace + (o.name,), canon and j == 0)
    rec(list(occs), {}, set(), set(), copy.deepcopy(init), (), True)
    return results, canonical

FAILS = 0
def check(name, run, summarize, expected, forbid=(), refused=()):
    """Assert the MEMBER set (ok/panic), the absence of forbidden hybrids, and the
    REFUSAL set (blocked), each exactly; print the slot-0 (canonical) draw."""
    global FAILS
    results, canonical = run
    summ, refs = {}, {}
    for key, (n, _) in results.items():
        if key[0] == 'blocked':
            refs[key[1]] = refs.get(key[1], 0) + n
        else:
            s = summarize(key); summ[s] = summ.get(s, 0) + n
    got = set(summ)
    print(f"{name}: outcome set = {sorted(got)}")
    print(f"   trajectories per outcome: {[(k, summ[k]) for k in sorted(summ)]}")
    ck = canonical.get('key')
    if ck is not None:
        print(f"   canonical (slot 0): {' '.join(canonical['trace'])} -> "
              f"{ck[1] if ck[0] == 'blocked' else summarize(ck)}")
    if got != set(expected):
        print(f"   MISMATCH: expected {sorted(expected)}"); FAILS += 1
    for f in forbid:
        if f in got:
            print(f"   FORBIDDEN outcome present: {f}"); FAILS += 1
        else:
            print(f"   forbidden hybrid absent: {f}")
    if refs or refused:
        print(f"   refused (outside the domain, not members): {[(k, refs[k]) for k in sorted(refs)]}")
        if set(refs) != set(refused):
            print(f"   MISMATCH: expected refusals {sorted(refused)}"); FAILS += 1

def refuse(name, thunk, needle):
    """Assert that a graph is REFUSED BY NAME (never a stuck run or a result)."""
    global FAILS
    try:
        thunk()
    except Malformed as m:
        print(f"{name}: refused by name: {m}")
        if needle not in str(m):
            print(f"   MISMATCH: the refusal should name {needle!r}"); FAILS += 1
    else:
        print(f"{name}: MISMATCH: expected a named refusal ({needle!r}), got results"); FAILS += 1

def state(v=None, arr=None, chan=None, maps=None):
    st = {'v': dict(v or {}), 'arr': {k: list(a) for k, a in (arr or {}).items()}, 'out': []}
    if chan is not None:
        st['chan'] = list(chan)
    if maps is not None:
        st['maps'] = {k: dict(m) for k, m in maps.items()}   # Stage E E2: map ids -> {key: value}
    return st

def println(st, *xs):
    st['out'].append(' '.join(str(x).lower() if isinstance(x, bool) else str(x) for x in xs))

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
    for key, (n, st) in enumerate_graph(occs, state(v={'a': 'A'}, arr={'A': [7]}), p2)[0].items():
        if key[0] == 'panic':
            program[(key[0], key[1], key[2])] = program.get((key[0], key[1], key[2]), 0) + n; continue
        occs2, p22 = iteration(1)
        for key2, (n2, _) in enumerate_graph(occs2, st, p22)[0].items():
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
            Occ('E1', run=inc), Occ('E2', after=['E1'], run=inc),               # E1 lexical: an order edge, no value
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

# ---------------------------------------------------------------- X2  v := b2i(z || h()) + x   (guarded region; the event consumes the joined result)
def x2(z, label):
    def h(st, v): st['v']['x'] = 2; return True
    region = [Occ('E_h', run=h), Occ('C_or', deps=['E_h'], run=lambda st, v: v['E_h'])]   # C_or = the || completion
    occs = [Occ('R_z', run=lambda st, v: st['v']['z']),
            Occ('G', deps=['R_z'], guard='R_z', when=False, region=region, out='C_or'),   # || : right runs iff left false
            Occ('E_b2i', deps=['C_or'], run=lambda st, v: 1 if v['C_or'] else 0),        # consumes the join (valid)
            Occ('R_x', run=lambda st, v: st['v']['x']),
            Occ('Op', deps=['E_b2i', 'R_x'], run=lambda st, v: v['E_b2i'] + v['R_x'])]
    def phase2(st, v): println(st, label, v['Op']); return v['Op']
    check(f'X2 b2i(z||h())+x, z={z}', enumerate_graph(occs, state(v={'x': 1, 'z': z}), phase2), lambda k: k[1],
          {2, 3} if not z else {2})

# ---------------------------------------------------------------- X3  x[f()] += <-ch   (receive; buffered, then empty)
def x3(chan, label, refused):
    def recv(st, v):
        if not st['chan']: raise Blocked('receive would block: outside the terminating domain')
        return st['chan'].pop(0)
    occs = [Occ('E_f', run=lambda st, v: 9),
            Occ('R_x', run=lambda st, v: hdr(st, 'x')),
            Occ('L', deps=['R_x', 'E_f'], run=lambda st, v: (v['R_x'], v['E_f'])),
            Occ('Rd', deps=['L'], run=lambda st, v: elem(st, *v['L'])),
            Occ('E_recv', after=['E_f'], run=recv),                            # E1 among events: f before <-ch
            Occ('Op', deps=['Rd', 'E_recv'], run=lambda st, v: v['Rd'] + v['E_recv'])]
    def phase2(st, v): store(st, v['L'][0], v['L'][1], v['Op']); return None
    init = state(v={'x': 'X'}, arr={'X': [1]}, chan=chan)
    check(f'X3 x[f()] += <-ch, {label}', enumerate_graph(occs, init, phase2),
          lambda k: (k[0], k[1], f"len(ch)={len(k[3][2])}"),
          {('panic', 'index out of range [9] with length 1', f'len(ch)={n}') for n in ({0, 1} if chan else {0})},
          refused=refused)

# ---------------------------------------------------------------- R1  v := x + y + mut()   (the retired read-order reduction, refuted)
def r1(reduced):
    def mut(st, v): st['v']['x'] = 1; st['v']['y'] = 2; return 0
    occs = [Occ('R_x', run=lambda st, v: st['v']['x']),
            Occ('R_y', after=['R_x'] if reduced else [], run=lambda st, v: st['v']['y']),   # the added read→read edge
            Occ('E_mut', run=mut),
            Occ('Op', deps=['R_x', 'R_y', 'E_mut'], run=lambda st, v: v['R_x'] + v['R_y'] + v['E_mut'])]
    def phase2(st, v): println(st, 'reduction', v['Op']); return v['Op']
    check(f"R1 x+y+mut(), {'REDUCED (R_x→R_y added): loses 1' if reduced else 'unreduced'}",
          enumerate_graph(occs, state(v={'x': 0, 'y': 0}), phase2), lambda k: k[1], {0, 2, 3} if reduced else {0, 1, 2, 3})

# ---------------------------------------------------------------- R2a  sink(z || h(), k())   (a skipped event discharges E1; never stuck)
def r2a(z, valid):
    def h(st, v): println(st, 'guard h'); return True
    def k(st, v): println(st, 'guard k'); return 7
    def sink(st, v): println(st, 'guard result', v['C_or'], v['E_k']); return None
    region = [Occ('E_h', run=h), Occ('C_or', deps=['E_h'], run=lambda st, v: v['E_h'])]
    occs = [Occ('R_z', run=lambda st, v: st['v']['z']),
            Occ('G', deps=['R_z'], guard='R_z', when=False, region=region, out='C_or'),
            # valid: E1 anchors k after the || COMPLETION (an order prerequisite, discharged by the skip);
            # invalid: k with a VALUE dependency on the region's event h (rejected by name when skipped).
            Occ('E_k', after=['C_or'], run=k) if valid else Occ('E_k', deps=['E_h'], run=k),
            Occ('E_sink', deps=['C_or', 'E_k'], run=sink)]
    run = lambda: enumerate_graph(occs, state(v={'z': z}), lambda st, v: None)
    if valid:
        check(f'R2a sink(z||h(), k()), z={z}', run(), lambda k: k[2],
              {('guard k', 'guard result true 7')} if z else {('guard h', 'guard k', 'guard result true 7')})
    else:
        refuse(f'R2a INVALID join: k depends on the skipped h, z={z}', run, 'confined to a skipped region')

# ---------------------------------------------------------------- R2/A3  a use confined to a LATER-skipped region, of a binder confined to an earlier-skipped one
# (Stage B audit R2, 2026-09-16: before the check above walked every unsettled occurrence, this
# completed as `sink true true` — X was never pending; the machine refused it. Both refuse now.)
def r2a3():
    def h(st, v): println(st, 'guard h'); return True
    r1 = [Occ('E_h', run=h), Occ('C1', deps=['E_h'], run=lambda st, v: v['E_h'])]
    r2 = [Occ('X', deps=['E_h'], run=lambda st, v: v['E_h']), Occ('C2', deps=['X'], run=lambda st, v: v['X'])]
    occs = [Occ('R_z1', run=lambda st, v: st['v']['z1']),
            Occ('G1', deps=['R_z1'], guard='R_z1', when=False, region=r1, out='C1'),
            Occ('R_z2', after=['C1'], run=lambda st, v: st['v']['z2']),
            Occ('G2', deps=['R_z2'], guard='R_z2', when=False, region=r2, out='C2'),
            Occ('E_sink', deps=['C1', 'C2'], run=lambda st, v: println(st, 'sink', v['C1'], v['C2']))]
    refuse('R2/A3 INVALID join confined to a LATER-skipped region: X (region G2) depends on the skipped h (region G1)',
           lambda: enumerate_graph(occs, state(v={'z1': True, 'z2': True}), lambda st, v: None), 'confined to a skipped region')

# ---------------------------------------------------------------- R2b  sink(left || b, change())   (the ordered || is anchored at COMPLETION)
def r2b(anchor):
    def change(st, v): st['v']['b'] = True; return 0
    region = [Occ('R_b', run=lambda st, v: st['v']['b']), Occ('C_or', deps=['R_b'], run=lambda st, v: v['R_b'])]
    occs = [Occ('R_left', run=lambda st, v: st['v']['left']),
            Occ('G', deps=['R_left'], guard='R_left', when=False, region=region, out='C_or'),
            Occ('E_change', after=[anchor], run=change),                      # E1: the || operation before change()
            Occ('E_sink', deps=['C_or', 'E_change'], run=lambda st, v: println(st, 'logical', v['C_or'], v['E_change']))]
    check(f"R2b sink(left||b, change()), E1 anchored at {'COMPLETION C_or' if anchor == 'C_or' else 'guard ENTRY G (refuted)'}",
          enumerate_graph(occs, state(v={'b': False, 'left': False}), lambda st, v: None), lambda k: k[2],
          {('logical false 0',)} if anchor == 'C_or' else {('logical false 0',), ('logical true 0',)})

# ---------------------------------------------------------------- R2c  sink(g(), a || (b && h()), k())   (nested guards, earlier call, a read unordered vs g)
def r2c(b):
    def g(st, v): println(st, 'g'); st['v']['a'] = True; return 1
    def h(st, v): println(st, 'h'); return True
    def k(st, v): println(st, 'k'); return 7
    inner = [Occ('E_h', run=h), Occ('C_and', deps=['E_h'], run=lambda st, v: v['E_h'])]
    outer = [Occ('R_b', run=lambda st, v: st['v']['b']),
             Occ('G2', deps=['R_b'], guard='R_b', when=True, region=inner, out='C_and'),
             Occ('C_or', deps=['C_and'], run=lambda st, v: v['C_and'])]
    occs = [Occ('E_g', run=g),
            Occ('R_a', run=lambda st, v: st['v']['a']),                          # unordered vs g (spec: «evaluation of ... z is not specified»)
            Occ('G1', deps=['R_a'], after=['E_g'], guard='R_a', when=False, region=outer, out='C_or'),   # E1: g before the || operation
            Occ('E_k', after=['C_or'], run=k),                                   # E1: the || completion before k
            Occ('E_sink', deps=['E_g', 'C_or', 'E_k'], run=lambda st, v: println(st, 'sink', v['E_g'], v['C_or'], v['E_k']))]
    exp = {('g', 'k', 'sink 1 true 7'), ('g', 'h', 'k', 'sink 1 true 7')} if b else \
          {('g', 'k', 'sink 1 true 7'), ('g', 'k', 'sink 1 false 7')}
    check(f'R2c sink(g(), a||(b&&h()), k()), b={b}', enumerate_graph(occs, state(v={'a': False, 'b': b}), lambda st, v: None),
          lambda k: k[2], exp, forbid=(('h', 'g', 'k', 'sink 1 true 7'),))

# ---------------------------------------------------------------- R4  old := a; a[0] += mut()   (mut replaces a: frozen header, old storage observable)
def r4():
    def mut(st, v): st['v']['a'] = 'B'; return 1
    occs = [Occ('R_a', run=lambda st, v: hdr(st, 'a')),
            Occ('L', deps=['R_a'], run=lambda st, v: (v['R_a'], 0)),           # identity: the FROZEN header + the index
            Occ('Rd', deps=['L'], run=lambda st, v: elem(st, *v['L'])),
            Occ('E_mut', run=mut),
            Occ('Op', deps=['Rd', 'E_mut'], run=lambda st, v: v['Rd'] + v['E_mut'])]
    def phase2(st, v):
        store(st, v['L'][0], v['L'][1], v['Op'])
        println(st, 'old', *st['arr']['A']); println(st, 'a', *st['arr'][st['v']['a']]); return None
    check('R4 old := a; a[0] += mut() with mut rebinding a', enumerate_graph(occs, state(v={'a': 'A'}, arr={'A': [10, 20], 'B': [100, 200]}), phase2),
          lambda k: k[2], {('old 11 20', 'a 100 200'), ('old 10 20', 'a 101 200')},
          forbid=(('old 10 20', 'a 11 200'), ('old 101 20', 'a 100 200')))

# ---------------------------------------------------------------- R6  v := a[f()]   (header producer split from the checked access vs fused)
def r6(split):
    def f(st, v): st['v']['a'] = 'B'; return 0
    if split:
        occs = [Occ('R_a', run=lambda st, v: hdr(st, 'a')), Occ('E_f', run=f),
                Occ('Rd', deps=['R_a', 'E_f'], run=lambda st, v: elem(st, v['R_a'], v['E_f']))]
    else:
        occs = [Occ('E_f', run=f), Occ('Rd', deps=['E_f'], run=lambda st, v: elem(st, hdr(st, 'a'), v['E_f']))]
    def phase2(st, v): println(st, 'header', v['Rd']); return v['Rd']
    check(f"R6 a[f()], {'SPLIT header/index producers + one checked access' if split else 'FUSED read (the narrowing)'}",
          enumerate_graph(occs, state(v={'a': 'A'}, arr={'A': [10], 'B': [20]}), phase2), lambda k: k[1], {10, 20} if split else {20})

# ---------------------------------------------------------------- Stage E, family E1 (2026-09-21): package-level variables
# (lane core/unseq-stage-e-0921; the width-of-P ruling «ALL mutable reads, STAGED» widened to
# package-level variables). A global is a mutable location like a captured local: its read is a
# READ occurrence unordered against a sibling call; as a compound target its identity has no
# operands (nothing to freeze), the store lands in phase 2. The reference LEADS the lowering:
# Tests/unseq-wire/{e1,e1c}.json and the corpus rows evalorder/unseq-globals/* certify these sets.
def e1a():
    def mut(st, v): st['v']['g'] = 2; return 0
    occs = [Occ('E_mut', run=mut),
            Occ('R_g', run=lambda st, v: st['v']['g']),                     # the package-level read
            Occ('Op', deps=['E_mut', 'R_g'], run=lambda st, v: v['E_mut'] + v['R_g'])]
    check('E1a mut()+g, g a package-level variable (mut: g = 2)', enumerate_graph(occs, state(v={'g': 1}), lambda st, v: v['Op']),
          lambda k: k[1], {1, 2})

def e1c():
    def f(st, v): st['v']['g'] = 10; return 1
    occs = [Occ('E_f', run=f),
            Occ('R_g', run=lambda st, v: st['v']['g']),                     # the compound target's load
            Occ('Op', deps=['R_g', 'E_f'], run=lambda st, v: v['R_g'] + v['E_f'])]
    def phase2(st, v): st['v']['g'] = v['Op']; return st['v']['g']         # the store: g's identity has no operands
    check('E1c g += f() (f: g = 10, returns 1)', enumerate_graph(occs, state(v={'g': 1}), phase2), lambda k: k[1], {2, 11})

def e1b():
    # BUG-113's c01 `sinkL(left || b, change())` with `left` a package-level variable: the SAME
    # graph as R2b (a global read is an occurrence like a captured local's) — the singleton
    # {logical false 0}; the legacy path's `logical true 0` is spec-forbidden (E1 at completion).
    def change(st, v): st['v']['b'] = True; return 0
    region = [Occ('R_b', run=lambda st, v: st['v']['b']), Occ('C_or', deps=['R_b'], run=lambda st, v: v['R_b'])]
    occs = [Occ('R_left', run=lambda st, v: st['v']['left']),               # the package-level read
            Occ('G', deps=['R_left'], guard='R_left', when=False, region=region, out='C_or'),
            Occ('E_change', after=['C_or'], run=change),
            Occ('E_sink', deps=['C_or', 'E_change'], run=lambda st, v: println(st, 'logical', v['C_or'], v['E_change']))]
    check('E1b (BUG-113) sinkL(left||b, change()), left a package-level variable', enumerate_graph(occs, state(v={'b': False, 'left': False}), lambda st, v: None),
          lambda k: k[2], {('logical false 0',)}, forbid=(('logical true 0',),))

# ---------------------------------------------------------------- Stage E, family E2 (2026-09-21): pointers, fields, maps
# A dereference `*p`, a field selection `p.f`, a map element `m[k]` are READ occurrences of mutable
# locations (nil-checked through a pointer); as targets they are FROZEN plans — the pointer VALUE,
# the struct's address, the map VALUE and key VALUE — one identity for the load and the store. The
# reference LEADS the lowering: Tests/unseq-wire/{e2ptr,e2map}.json and evalorder/unseq-ptr-field-map/*.
# Pointers are state variables holding a variable NAME ('x'); a field `q.f` is the variable 'q.f'.
def e2a():
    def mut(st, v): st['v']['x'] = 2; return 0                              # setVia(p): *p = 2
    occs = [Occ('E_mut', run=mut),
            Occ('R_deref', run=lambda st, v: st['v'][st['v']['p']]),           # *p: nil-checked read
            Occ('Op', deps=['E_mut', 'R_deref'], run=lambda st, v: v['E_mut'] + v['R_deref'])]
    check('E2a *p + setVia(p) (p -> x = 1; setVia: *p = 2)', enumerate_graph(occs, state(v={'x': 1, 'p': 'x'}), lambda st, v: v['Op']),
          lambda k: k[1], {1, 2})

def e2c():
    def mut(st, v): st['maps']['M'][1] = 2; return 0                       # setM(m): m[1] = 2
    occs = [Occ('E_mut', run=mut),
            Occ('R_m', run=lambda st, v: st['maps'][st['v']['m']].get(1, 0)),   # m[1]: the map read
            Occ('Op', deps=['E_mut', 'R_m'], run=lambda st, v: v['E_mut'] + v['R_m'])]
    check('E2c m[1] + setM(m) (m[1] = 1; setM: m[1] = 2)', enumerate_graph(occs, state(v={'m': 'M'}, maps={'M': {1: 1}}), lambda st, v: v['Op']),
          lambda k: k[1], {1, 2})

def e2d():
    # BUG-104's map row: m[t[k]] += wit(5) with t = [1], k = 5 — the key's checked access panics
    # before or after wit prints; the plan / load / store never run.
    def wit(st, v): println(st, 'wit', 5); return 5
    occs = [Occ('R_tk', run=lambda st, v: elem(st, hdr(st, 't'), 5)),
            Occ('E_wit', run=wit),
            Occ('L', deps=['R_tk'], run=lambda st, v: ('M', v['R_tk'])),
            Occ('Rd', deps=['L'], run=lambda st, v: st['maps'][v['L'][0]].get(v['L'][1], 0)),
            Occ('Op', deps=['Rd', 'E_wit'], run=lambda st, v: v['Rd'] + v['E_wit'])]
    def phase2(st, v): st['maps'][v['L'][0]][v['L'][1]] = v['Op']; return None
    check('E2d (BUG-104) m[t[k]] += wit(5), t[k] out of range', enumerate_graph(occs, state(v={'t': 'T', 'm': 'M'}, arr={'T': [1]}, maps={'M': {}}), phase2),
          lambda k: (k[0], k[1], k[2]),
          {('panic', 'index out of range [5] with length 1', ()), ('panic', 'index out of range [5] with length 1', ('wit 5',))})

def e2e():
    # *p += mut() with mut REDIRECTING the captured p to y: the plan freezes the pointer VALUE.
    def mut(st, v): st['v']['p'] = 'y'; return 1
    occs = [Occ('R_p', run=lambda st, v: st['v']['p']),                          # the pointer value (p captured)
            Occ('L', deps=['R_p'], run=lambda st, v: v['R_p']),                  # identity: the frozen pointee name
            Occ('Rd', deps=['L'], run=lambda st, v: st['v'][v['L']]),            # the load through the plan
            Occ('E_mut', run=mut),
            Occ('Op', deps=['Rd', 'E_mut'], run=lambda st, v: v['Rd'] + v['E_mut'])]
    def phase2(st, v): st['v'][v['L']] = v['Op']; println(st, 'x y', st['v']['x'], st['v']['y']); return None
    check('E2e *p += mut() with mut redirecting p (x = 10, y = 100)', enumerate_graph(occs, state(v={'x': 10, 'y': 100, 'p': 'x'}), phase2),
          lambda k: k[2], {('x y 11 100',), ('x y 10 101',)}, forbid=(('x y 10 11',), ('x y 101 100',)))

def e2f():
    # m[1] += mut() with mut REBINDING the captured m to m2: the plan freezes the map VALUE (a reference).
    def mut(st, v): st['v']['m'] = 'M2'; return 1
    occs = [Occ('R_m', run=lambda st, v: st['v']['m']),
            Occ('L', deps=['R_m'], run=lambda st, v: (v['R_m'], 1)),
            Occ('Rd', deps=['L'], run=lambda st, v: st['maps'][v['L'][0]].get(v['L'][1], 0)),
            Occ('E_mut', run=mut),
            Occ('Op', deps=['Rd', 'E_mut'], run=lambda st, v: v['Rd'] + v['E_mut'])]
    def phase2(st, v):
        st['maps'][v['L'][0]][v['L'][1]] = v['Op']
        println(st, 'old', st['maps']['M'][1], 'm', st['maps'][st['v']['m']][1]); return None
    check('E2f m[1] += mut() with mut rebinding m (m[1] = 10, m2[1] = 100)', enumerate_graph(occs, state(v={'m': 'M'}, maps={'M': {1: 10}, 'M2': {1: 100}}), phase2),
          lambda k: k[2], {('old 11 m 100',), ('old 10 m 101',)}, forbid=(('old 10 m 11',), ('old 101 m 100',)))

def e2g():
    # *p + wit(5) with p nil: the nil dereference before or after the call (E13's deref shape; gc LATE).
    def wit(st, v): println(st, 'wit', 5); return 5
    def deref(st, v):
        if st['v']['p'] is None: raise Panic('invalid memory address or nil pointer dereference')
        return st['v'][st['v']['p']]
    occs = [Occ('R_deref', run=deref), Occ('E_wit', run=wit),
            Occ('Op', deps=['R_deref', 'E_wit'], run=lambda st, v: v['R_deref'] + v['E_wit'])]
    check('E2g *p + wit(5), p nil', enumerate_graph(occs, state(v={'p': None}), lambda st, v: v['Op']),
          lambda k: (k[0], k[2]), {('panic', ()), ('panic', ('wit 5',))})

# ---------------------------------------------------------------- Stage E, family E3 (2026-09-21): receives and method calls
# A receive is an EVENT (E1-ordered among the calls, one communication); a method call is an invocation
# whose receiver sub-evaluation (E14's sub-axis) is an occurrence like any operand. The reference LEADS
# the lowering: Tests/unseq-wire/{e3recv,e3method}.json and evalorder/unseq-recv-method/*.
def e3a():
    # <-ch + x + mut(): x captured (mut: x = 2), ch buffered [1]; E1: the receive BEFORE mut.
    def recv(st, v):
        if not st['chan']: raise Blocked('receive would block: outside the terminating domain')
        return st['chan'].pop(0)
    def mut(st, v): st['v']['x'] = 2; return 0
    occs = [Occ('E_recv', run=recv), Occ('R_x', run=lambda st, v: st['v']['x']),
            Occ('E_mut', after=['E_recv'], run=mut),
            Occ('Op', deps=['E_recv', 'R_x', 'E_mut'], run=lambda st, v: v['E_recv'] + v['R_x'] + v['E_mut'])]
    check('E3a <-ch + x + mut() (x = 1, mut: x = 2)', enumerate_graph(occs, state(v={'x': 1}, chan=[1]), lambda st, v: v['Op']),
          lambda k: k[1], {2, 3})

def e3c():
    # BUG-104's map-key receive row: m[t[k]] += <-ch, t = [1], k = 5, ch buffered [3]; the witness len(ch).
    def recv(st, v):
        if not st['chan']: raise Blocked('receive would block: outside the terminating domain')
        return st['chan'].pop(0)
    occs = [Occ('R_tk', run=lambda st, v: elem(st, hdr(st, 't'), 5)),
            Occ('E_recv', run=recv),
            Occ('L', deps=['R_tk'], run=lambda st, v: ('M', v['R_tk'])),
            Occ('Rd', deps=['L'], run=lambda st, v: st['maps'][v['L'][0]].get(v['L'][1], 0)),
            Occ('Op', deps=['Rd', 'E_recv'], run=lambda st, v: v['Rd'] + v['E_recv'])]
    def phase2(st, v): st['maps'][v['L'][0]][v['L'][1]] = v['Op']; return None
    check('E3c (BUG-104) m[t[k]] += <-ch, t[k] out of range; witness len(ch)',
          enumerate_graph(occs, state(v={'t': 'T', 'm': 'M'}, arr={'T': [1]}, maps={'M': {}}, chan=[3]), phase2),
          lambda k: (k[0], f"len(ch)={len(k[3][2])}"), {('panic', 'len(ch)=1'), ('panic', 'len(ch)=0')})

def e3d():
    # BUG-104's method row: m[t[k]] += q.M() (M prints 'M', returns 7); the receiver q a pointer atom.
    def M(st, v): println(st, 'M'); return 7
    occs = [Occ('R_tk', run=lambda st, v: elem(st, hdr(st, 't'), 5)),
            Occ('E_M', run=M),
            Occ('L', deps=['R_tk'], run=lambda st, v: ('M', v['R_tk'])),
            Occ('Rd', deps=['L'], run=lambda st, v: st['maps'][v['L'][0]].get(v['L'][1], 0)),
            Occ('Op', deps=['Rd', 'E_M'], run=lambda st, v: v['Rd'] + v['E_M'])]
    def phase2(st, v): st['maps'][v['L'][0]][v['L'][1]] = v['Op']; return None
    check('E3d (BUG-104) m[t[k]] += q.M(), t[k] out of range',
          enumerate_graph(occs, state(v={'t': 'T', 'm': 'M'}, arr={'T': [1]}, maps={'M': {}}), phase2),
          lambda k: (k[0], k[2]), {('panic', ()), ('panic', ('M',))})

def e3e():
    # v.Plus(f()) with a VALUE receiver: the receiver COPY (v.n read) is an occurrence unordered against
    # the argument event f (E14's sub-axis); f writes v.n = 10; Plus returns v.n + arg. v.n = 1, f returns 5.
    def f(st, v): st['v']['v.n'] = 10; return 5
    occs = [Occ('R_recv', run=lambda st, v: st['v']['v.n']),                 # the receiver copy
            Occ('E_f', run=f),
            Occ('E_plus', deps=['R_recv', 'E_f'], run=lambda st, v: v['R_recv'] + v['E_f'])]
    check('E3e v.Plus(f()), value receiver, f writes v.n (E14)', enumerate_graph(occs, state(v={'v.n': 1}), lambda st, v: v['E_plus']),
          lambda k: k[1], {6, 15})

# ---------------------------------------------------------------- Stage E, family E4: conversions and allocations
# (2026-09-21). A conversion is a PURE OP on its operand's value (never an occurrence); a composite
# literal is an ALLOCATION node without E1 edges (v2.1 R3) whose payload reads are the occurrences;
# `make` is a function call — an E1 participant like len (spec#Built-in_functions).

def e4a():
    # int([]byte(s)[0]) + mut(): s captured (mut: s = "zz", returns 1); the conversion and the index are
    # pure ops on the fresh bytes; the READ of s is the occurrence unordered against mut.
    def mut(st, v): st['v']['s'] = 'zz'; return 1
    occs = [Occ('R_s', run=lambda st, v: st['v']['s']),
            Occ('E_mut', run=mut),
            Occ('Conv', deps=['R_s'], run=lambda st, v: ord(v['R_s'][0])),
            Occ('Op', deps=['Conv', 'E_mut'], run=lambda st, v: v['Conv'] + v['E_mut'])]
    check('E4a int([]byte(s)[0]) + mut() (s = "ab", mut: s = "zz")',
          enumerate_graph(occs, state(v={'s': 'ab'}), lambda st, v: v['Op']), lambda k: k[1], {98, 123})

def e4b():
    # (&T{x: s[i]}).x + wit(5), s = [7], i = 9 (BUG-102): the payload read panics; the allocation (no E1
    # edge) and the field read follow it by data; wit is unordered against the read.
    def wit(st, v): println(st, 'wit 5'); return 5
    occs = [Occ('R_si', run=lambda st, v: elem(st, hdr(st, 's'), 9)),
            Occ('A', deps=['R_si'], run=lambda st, v: ('T', v['R_si'])),
            Occ('F', deps=['A'], run=lambda st, v: v['A'][1]),
            Occ('E_wit', run=wit),
            Occ('Op', deps=['F', 'E_wit'], run=lambda st, v: v['F'] + v['E_wit'])]
    check('E4b (&T{x: s[i]}).x + wit(5), s[i] out of range (BUG-102)',
          enumerate_graph(occs, state(v={'s': 'S'}, arr={'S': [7]}), lambda st, v: v['Op']),
          lambda k: (k[0], k[2]), {('panic', ()), ('panic', ('wit 5',))})

def e4c():
    # []int{s[i]}[0] + <-ch (BUG-102's receive spelling), ch buffered [3]; the witness len(ch).
    def recv(st, v):
        if not st['chan']: raise Blocked('receive would block: outside the terminating domain')
        return st['chan'].pop(0)
    occs = [Occ('R_si', run=lambda st, v: elem(st, hdr(st, 's'), 9)),
            Occ('A', deps=['R_si'], run=lambda st, v: ('L', [v['R_si']])),
            Occ('Rd', deps=['A'], run=lambda st, v: v['A'][1][0]),
            Occ('E_recv', run=recv),
            Occ('Op', deps=['Rd', 'E_recv'], run=lambda st, v: v['Rd'] + v['E_recv'])]
    check('E4c []int{s[i]}[0] + <-ch, s[i] out of range; witness len(ch) (BUG-102)',
          enumerate_graph(occs, state(v={'s': 'S'}, arr={'S': [7]}, chan=[3]), lambda st, v: v['Op']),
          lambda k: (k[0], f"len(ch)={len(k[3][2])}"), {('panic', 'len(ch)=1'), ('panic', 'len(ch)=0')})

def e4d():
    # iv.(int) + len(make([]int, t[k])), iv a string, t = [1], k = 5 (E13 assert-left-make-slice): the
    # assertion and the size operand's read are unordered; make and len follow the read by data.
    def assert_int(st, v): raise Panic('interface conversion: interface {} is string, not int')
    occs = [Occ('R_iv', run=assert_int),
            Occ('R_tk', run=lambda st, v: elem(st, hdr(st, 't'), 5)),
            Occ('A_make', deps=['R_tk'], run=lambda st, v: ('M', [0] * v['R_tk'])),
            Occ('E_len', deps=['A_make'], run=lambda st, v: len(v['A_make'][1])),
            Occ('Op', deps=['R_iv', 'E_len'], run=lambda st, v: v['R_iv'] + v['E_len'])]
    check('E4d iv.(int) + len(make([]int, t[k])) (E13 assert-left-make-slice)',
          enumerate_graph(occs, state(v={'t': 'T'}, arr={'T': [1]}), lambda st, v: v['Op']),
          lambda k: (k[0], k[1]), {('panic', 'interface conversion: interface {} is string, not int'),
                                   ('panic', 'index out of range [5] with length 1')})

def e4e():
    # len(make([]int, n)) + mut() with mut writing the captured n (n = 1 -> 3, returns 10): make is an E1
    # participant BEFORE mut and n's read lies inside make's operand — forced before mut: a SINGLETON
    # (the control for the [AGENT] choice «make is a function call»; gc's draw decides it).
    def mut(st, v): st['v']['n'] = 3; return 10
    occs = [Occ('R_n', run=lambda st, v: st['v']['n']),
            Occ('A_make', deps=['R_n'], run=lambda st, v: ('M', [0] * v['R_n'])),
            Occ('E_len', deps=['A_make'], run=lambda st, v: len(v['A_make'][1])),
            Occ('E_mut', after=['E_len'], run=mut),
            Occ('Op', deps=['E_len', 'E_mut'], run=lambda st, v: v['E_len'] + v['E_mut'])]
    check('E4e len(make([]int, n)) + mut() (make an E1 participant: n forced before mut)',
          enumerate_graph(occs, state(v={'n': 1}), lambda st, v: v['Op']), lambda k: k[1], {11})

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
    # C4: a malformed graph (cycle) is refused by name — scheduler case (iii), never a stuck run.
    occs = [Occ('A', after=['B'], run=lambda st, v: 0), Occ('B', after=['A'], run=lambda st, v: 0)]
    refuse('C4 cycle A↔B', lambda: enumerate_graph(occs, state(), lambda st, v: None), 'no ready occurrence')

if __name__ == '__main__':
    for f in (w1, w2, w3, w4, w5, w6, x1, lambda: x2(False, 'x2 v'), lambda: x2(True, 'x2 w'),
              lambda: x3([5], 'buffered', ()),
              lambda: x3([], 'EMPTY channel', ('receive would block: outside the terminating domain',)),
              lambda: r1(False), lambda: r1(True),
              lambda: r2a(True, True), lambda: r2a(False, True), lambda: r2a(True, False), r2a3,
              lambda: r2b('C_or'), lambda: r2b('G'),
              lambda: r2c(True), lambda: r2c(False),
              r4, lambda: r6(True), lambda: r6(False),
              e1a, e1c, e1b, e2a, e2c, e2d, e2e, e2f, e2g, e3a, e3c, e3d, e3e,
              e4a, e4b, e4c, e4d, e4e, controls):
        f()
    print('RESULT:', 'FAIL' if FAILS else 'PASS', f'({FAILS} mismatch(es))')
    sys.exit(1 if FAILS else 0)
