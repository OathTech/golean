#!/usr/bin/env python3
"""Turn results.json (+ steps.json) into the tables the re-diagnosis note cites.

Net time = median wall minus the `empty` probe's median wall (process start,
wire decode, one call). Ratios are between successive rows of a family, with
the ratio a pure power law would give printed beside them. No fitting beyond
that; single-run rows do not occur (3 runs per point, or a named timeout).

Usage: python3 summarize.py results.json steps.json
"""
import json
import sys


def load_points(path):
    d = json.load(open(path))
    pts = {}
    for p in d["points"]:
        pts[(p["probe"], tuple(p["args"]))] = p["summary"]
    return d["meta"], pts


def fmt(x, nd=4):
    return "—" if x is None else f"{x:.{nd}f}"


def row(pts, key, base, label=None, count=None):
    s = pts.get(key)
    label = label or f"`{key[0]}{key[1]}`"
    if s is None:
        return f"| {label} | (not run) | | | | |", None
    if s.get("timed_out"):
        return f"| {label} | TIMED OUT after {s['timeout_s']} s (decides nothing) | | | | |", None
    net = s["wall_median_s"] - base
    per = (net / count) if count else None
    spread = f"{s['wall_min_s']:.4f}..{s['wall_max_s']:.4f}"
    return (f"| {label} | {s['wall_median_s']:.4f} | {spread} | {s['cpu_median_s']:.2f} | {net:.4f} | "
            f"{fmt(per * 1e6, 2) if per is not None else '—'} |"), net


def family(title, pts, base, keys, counts=None, law=None, labels=None):
    print(f"\n**{title}** (3 runs per point; wall s median, min..max; cpu = user+sys median; "
          f"net = median wall − empty-probe median)\n")
    print("| point | wall med | spread | cpu | net | per-op µs |")
    print("|---|---:|---|---:|---:|---:|")
    prev = None
    nets = []
    for i, k in enumerate(keys):
        c = counts[i] if counts else None
        line, net = row(pts, k, base, labels[i] if labels else None, c)
        print(line)
        nets.append(net)
    if law:
        ratios = []
        for i in range(1, len(keys)):
            if nets[i] is not None and nets[i - 1] and nets[i - 1] > 0.002:
                x0, x1 = law["x"](keys[i - 1]), law["x"](keys[i])
                if x0 == 0:
                    continue
                ratios.append(f"{x0}→{x1}: ×{nets[i] / nets[i - 1]:.2f} "
                              f"(linear ×{x1 / x0:.1f}, quadratic ×{(x1 / x0) ** 2:.1f}, cubic ×{(x1 / x0) ** 3:.1f})")
        if ratios:
            print("\nsuccessive net ratios — " + "; ".join(ratios))
    return nets


def main():
    meta, pts = load_points(sys.argv[1])
    steps = {}
    if len(sys.argv) > 2:
        for s in json.load(open(sys.argv[2]))["steps"]:
            steps[(s["probe"], s["n_index"])] = s["steps_per_iteration"]
    print(f"commit {meta['commit']}  golean sha256 {meta['golean_sha256'][:16]}…  "
          f"{meta['go_version']}  nproc {meta['nproc']}  load1 start {meta['loadavg1_at_start']} "
          f"end {meta.get('loadavg1_at_end')}  started {meta['started_utc']}")
    empty = pts[("empty", (0,))]
    base = empty["wall_median_s"]
    print(f"\nempty probe (startup): median {base:.4f} s over {empty['runs_completed']} runs "
          f"[{empty['wall_min_s']:.4f}..{empty['wall_max_s']:.4f}], rss {empty['maxrss_kb_max']} KB")
    if steps:
        print("\nsteps per loop iteration (fuel bisection): " + ", ".join(
            f"{k[0]}={v:.0f}" for k, v in sorted(steps.items())))

    n = lambda k: k[1][0]
    a1 = lambda k: k[1][1]
    a0 = lambda k: k[1][0]

    nets = family("(e) scalar loop — per-step baseline", pts, base,
                  [("scalar", (x,)) for x in (10000, 20000, 40000, 80000)],
                  counts=[10000, 20000, 40000, 80000], law={"x": n})
    if nets[-1] and ("scalar", 0) in steps:
        print(f"\nper machine step at n=80000: {nets[-1] / (80000 * steps[('scalar', 0)]) * 1e9:.0f} ns "
              f"({steps[('scalar', 0)]:.0f} steps/iteration)")

    family("(a) the review's loop: `append` growing from nil", pts, base,
           [("append_grow", (x,)) for x in (250, 500, 1000, 2000, 4000)],
           counts=[250, 500, 1000, 2000, 4000], law={"x": n})
    family("(f) in-place `append`, w = c (no spill)", pts, base,
           [("append_cap", (x, x)) for x in (250, 500, 1000, 2000)],
           counts=[250, 500, 1000, 2000], law={"x": a0})
    family("(f′) 100 in-place appends, capacity c varying", pts, base,
           [("append_cap", (c, 100)) for c in (100, 200, 400, 800, 1600, 3200, 6400)],
           counts=[100] * 7, law={"x": a0})
    family("(b) 100 element writes `xs[0] = v`, slice length m varying", pts, base,
           [("write_fixed", (m, 100)) for m in (10, 100, 1000, 3000, 10000)],
           counts=[100] * 5, law={"x": a0})
    family("(b′) element writes at m = 10, write count varying", pts, base,
           [("write_fixed", (10, w)) for w in (100, 1000, 10000)],
           counts=[100, 1000, 10000], law={"x": a1})
    family("(i) 1,000 element reads `xs[0]`, slice length m varying", pts, base,
           [("read_fixed", (m, 1000)) for m in (10, 100, 1000, 10000)],
           counts=[1000] * 4, law={"x": a0})
    family("(c) aggregate shape — 100 writes each", pts, base,
           [("struct_small", (100,)), ("struct_arr_100", (100,)), ("struct_arr_1000", (100,)),
            ("struct_arr_10000", (100,)), ("struct_slice", (100, 100)), ("struct_slice", (10000, 100)),
            ("flat_arr_10000", (100,)), ("nested_arr_10x1000", (100,)), ("nested_arr_100x100", (100,)),
            ("slice_inner", (10000, 100))],
           counts=[100] * 10,
           labels=["struct{y,x int}: s.x = i", "struct{a [100]byte; x int}: s.x = i",
                   "struct{a [1000]byte; x int}: s.x = i", "struct{a [10000]byte; x int}: s.x = i",
                   "struct{a []byte; x int}, len(a)=100: s.x = i",
                   "struct{a []byte; x int}, len(a)=10000: s.x = i",
                   "[10000]byte: b[0] = v", "[10][1000]byte: a[0][0] = v", "[100][100]byte: a[0][0] = v",
                   "[][]byte 10×1000 (separate cells): xs[0][0] = v"])
    family("(d) allocation-only loops", pts, base,
           [("alloc_new", (x,)) for x in (1000, 4000, 16000, 32000)],
           counts=[1000, 4000, 16000, 32000], law={"x": n})
    family("(d′) `make([]byte, 4)` per iteration (the 2026-09-03 audit probe)", pts, base,
           [("alloc_make4", (x,)) for x in (1000, 4000, 16000)],
           counts=[1000, 4000, 16000], law={"x": n})
    family("(h) live-heap size h vs a fixed 20,000-iteration scalar loop — allocation phase alone (w = 0)",
           pts, base, [("heap_then_scalar", (h, 0)) for h in (0, 1000, 10000, 40000)],
           counts=[None, 1000, 10000, 40000], law={"x": a0})
    family("(h) … allocation phase + scalar phase (w = 20000)", pts, base,
           [("heap_then_scalar", (h, 20000)) for h in (0, 1000, 10000, 40000)],
           counts=[20000] * 4)
    print("\nscalar-phase cost at heap size h (= (h, 20000) net − (h, 0) net):")
    for h in (0, 1000, 10000, 40000):
        s1, s0 = pts.get(("heap_then_scalar", (h, 20000))), pts.get(("heap_then_scalar", (h, 0)))
        if s1 and s0 and not s1.get("timed_out") and not s0.get("timed_out"):
            print(f"  h={h}: {s1['wall_median_s'] - s0['wall_median_s']:.4f} s")
    family("(h′) live-heap size h vs 300 in-place appends — allocation phase alone (w = 0)", pts, base,
           [("heap_then_append", (h, 0)) for h in (0, 10000, 40000)], counts=[None, 10000, 40000])
    family("(h′) … + 300 in-place appends (w = 300)", pts, base,
           [("heap_then_append", (h, 300)) for h in (0, 10000, 40000)], counts=[300] * 3)
    print("\nappend-phase cost at heap size h (= (h, 300) net − (h, 0) net):")
    for h in (0, 10000, 40000):
        s1, s0 = pts.get(("heap_then_append", (h, 300))), pts.get(("heap_then_append", (h, 0)))
        if s1 and s0 and not s1.get("timed_out") and not s0.get("timed_out"):
            print(f"  h={h}: {s1['wall_median_s'] - s0['wall_median_s']:.4f} s")
    family("(g) map writes, n distinct int keys", pts, base,
           [("map_write", (x,)) for x in (500, 1000, 2000, 4000)],
           counts=[500, 1000, 2000, 4000], law={"x": n})


if __name__ == "__main__":
    main()
