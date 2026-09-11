#!/usr/bin/env python3
"""BUG-090 re-diagnosis probe runner (records only; no build).

Lowers each probe under probes/<name>/main.go with the native frontend,
runs `golean native-json-run --function probe --arg-int ...` on the wire,
and records wall/CPU/RSS per run. Every subprocess timeout is recorded as a
timeout (it decides nothing); the remaining runs of a timed-out point are
skipped. Steps-per-iteration are measured by bisection on `--fuel`.

Usage (from the repository root; scratch and binaries under .tmp/):
  python3 docs/evidence/2026-09-11_bug090-rediagnosis/run-probes.py \
      --golean .tmp/golean --frontend .tmp/nativefrontend \
      --scratch .tmp/bug090 --plan full \
      --out docs/evidence/2026-09-11_bug090-rediagnosis/results.json
"""
import argparse
import hashlib
import json
import os
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROBES = HERE / "probes"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def loadavg1():
    with open("/proc/loadavg") as f:
        return float(f.read().split()[0])


def lower(frontend, name, scratch):
    case = scratch / name
    case.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PROBES / name / "main.go", case / "main.go")
    wire = case / "program.json"
    r = subprocess.run([str(frontend), "--dir", str(case), "--out", str(wire)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"lower {name}: exit {r.returncode}\n{r.stdout}{r.stderr}")
    return wire


def run_once(golean, wire, args, timeout, fuel=None):
    """One timed run. Returns a dict; on timeout the dict says so and nothing else."""
    with tempfile.NamedTemporaryFile(prefix="rusage.", suffix=".txt",
                                     dir=str(wire.parent), delete=False) as tf:
        rusage_path = tf.name
    cmd = ["/usr/bin/time", "-f", "%U %S %M", "-o", rusage_path, str(golean),
           "native-json-run", "--input", str(wire), "--function", "probe"]
    for a in args:
        cmd += ["--arg-int", str(a)]
    if fuel is not None:
        cmd += ["--fuel", str(fuel)]
    load = loadavg1()
    t0 = time.monotonic()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        # Kill only the process group we created (our own child's session).
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
        os.unlink(rusage_path)
        return {"timed_out": True, "timeout_s": timeout, "loadavg1": load,
                "note": "TIMED OUT — decides nothing about the completed runtime"}
    wall = time.monotonic() - t0
    try:
        with open(rusage_path) as f:
            parts = f.read().split()
        user_s, sys_s, maxrss_kb = float(parts[-3]), float(parts[-2]), int(parts[-1])
    except Exception:
        user_s = sys_s = maxrss_kb = None
    os.unlink(rusage_path)
    status, value = None, None
    try:
        obs = json.loads(out.strip().splitlines()[-1])
        status = obs.get("status")
        vals = obs.get("values") or []
        if vals:
            value = vals[0].get("value")
    except Exception:
        status = f"unparsed: {out.strip()[:200]} {err.strip()[:200]}"
    return {"wall_s": round(wall, 4), "user_s": user_s, "sys_s": sys_s,
            "cpu_s": None if user_s is None else round(user_s + sys_s, 4),
            "maxrss_kb": maxrss_kb, "exit": proc.returncode, "status": status,
            "value": value, "loadavg1": load}


def run_point(golean, wire, name, args, runs, timeout):
    recs = []
    for _ in range(runs):
        rec = run_once(golean, wire, args, timeout)
        recs.append(rec)
        if rec.get("timed_out"):
            break
    ok = [r for r in recs if not r.get("timed_out")]
    summary = {}
    if ok:
        walls = [r["wall_s"] for r in ok]
        cpus = [r["cpu_s"] for r in ok if r["cpu_s"] is not None]
        summary = {"runs_completed": len(ok), "wall_median_s": round(statistics.median(walls), 4),
                   "wall_min_s": min(walls), "wall_max_s": max(walls),
                   "cpu_median_s": round(statistics.median(cpus), 4) if cpus else None,
                   "maxrss_kb_max": max(r["maxrss_kb"] for r in ok if r["maxrss_kb"] is not None),
                   "statuses": sorted({str(r["status"]) for r in ok}),
                   "values": sorted({str(r["value"]) for r in ok})}
    if any(r.get("timed_out") for r in recs):
        summary["timed_out"] = True
        summary["timeout_s"] = timeout
    point = {"probe": name, "args": list(args), "runs": recs, "summary": summary}
    tag = f"{name}{tuple(args)}"
    if summary.get("timed_out"):
        print(f"  {tag:40s} TIMED OUT after {timeout}s (decides nothing)", flush=True)
    else:
        print(f"  {tag:40s} wall med {summary['wall_median_s']:.4f}s "
              f"[{summary['wall_min_s']:.4f}..{summary['wall_max_s']:.4f}] "
              f"cpu med {summary['cpu_median_s']} status={summary['statuses']} "
              f"value={summary['values']} rss={summary['maxrss_kb_max']}KB", flush=True)
    return point


def min_fuel(golean, wire, args, hi=1 << 22):
    """Smallest --fuel that completes with status ok (bisection; each run is short)."""
    def ok(f):
        r = run_once(golean, wire, args, timeout=120, fuel=f)
        return (not r.get("timed_out")) and r["status"] == "ok"
    lo = 0
    if not ok(hi):
        raise SystemExit(f"min_fuel: even fuel {hi} does not complete for {args}")
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def steps_per_iteration(golean, wire, name, base_args, n_index, n1, n2):
    a1 = list(base_args); a1[n_index] = n1
    a2 = list(base_args); a2[n_index] = n2
    f1, f2 = min_fuel(golean, wire, a1), min_fuel(golean, wire, a2)
    per = (f2 - f1) / (n2 - n1)
    print(f"  steps {name}{tuple(base_args)} n={n1}:{f1} n={n2}:{f2} -> {per:.2f} steps/iteration", flush=True)
    return {"probe": name, "args_template": base_args, "n_index": n_index,
            "fuel_at": {str(n1): f1, str(n2): f2}, "steps_per_iteration": per}


# ---- Plans -------------------------------------------------------------
# (probe, args, runs, timeout_s). Timeouts are named in the record.
def plan_full():
    P = []
    P += [("empty", (0,), 7, 60)]
    P += [("scalar", (n,), 3, 120) for n in (10_000, 20_000, 40_000, 80_000)]
    P += [("append_grow", (n,), 3, 150) for n in (250, 500, 1000, 2000, 4000)]
    # in-place appends, w = c (the fixed-cap curve BUG-090 first measured)
    P += [("append_cap", (n, n), 3, 150) for n in (250, 500, 1000, 2000)]
    # fixed 100 in-place appends, capacity varying
    P += [("append_cap", (c, 100), 3, 150) for c in (100, 200, 400, 800, 1600, 3200, 6400)]
    # fixed 100 element writes, slice length varying
    P += [("write_fixed", (m, 100), 3, 150) for m in (10, 100, 1000, 3000, 10000)]
    # write count varying at small fixed length (linearity in w)
    P += [("write_fixed", (10, w), 3, 120) for w in (1000, 10_000)]
    # reads only
    P += [("read_fixed", (m, 1000), 3, 120) for m in (10, 100, 1000, 10000)]
    # aggregate shape
    P += [("struct_small", (100,), 3, 120)]
    P += [(f"struct_arr_{m}", (100,), 3, 150) for m in (100, 1000, 10000)]
    P += [("struct_slice", (m, 100), 3, 120) for m in (100, 10000)]
    P += [("flat_arr_10000", (100,), 3, 150), ("nested_arr_10x1000", (100,), 3, 150),
          ("nested_arr_100x100", (100,), 3, 150), ("slice_inner", (10000, 100), 3, 150)]
    # allocation only
    P += [("alloc_new", (n,), 3, 150) for n in (1000, 4000, 16000, 32000)]
    P += [("alloc_make4", (n,), 3, 150) for n in (1000, 4000, 16000)]
    # live-heap size vs fixed work
    P += [("heap_then_scalar", (h, 0), 3, 150) for h in (0, 1000, 10000, 40000)]
    P += [("heap_then_scalar", (h, 20000), 3, 150) for h in (0, 1000, 10000, 40000)]
    P += [("heap_then_append", (h, 0), 3, 150) for h in (0, 10000, 40000)]
    P += [("heap_then_append", (h, 300), 3, 150) for h in (0, 10000, 40000)]
    # maps
    P += [("map_write", (n,), 3, 150) for n in (500, 1000, 2000, 4000)]
    return P


def plan_smoke():
    return [(n, tuple(2 for _ in range(k)), 1, 60) for n, k in ARITY.items()]


ARITY = {"empty": 1, "scalar": 1, "append_grow": 1, "append_cap": 2, "write_fixed": 2,
         "read_fixed": 2, "struct_arr_100": 1, "struct_arr_1000": 1, "struct_arr_10000": 1,
         "struct_small": 1, "struct_slice": 2, "flat_arr_10000": 1, "nested_arr_10x1000": 1,
         "nested_arr_100x100": 1, "slice_inner": 2, "alloc_new": 1, "alloc_make4": 1,
         "heap_then_scalar": 2, "heap_then_append": 2, "map_write": 1}

STEP_PLAN = [  # (probe, base_args, index of the varied arg, n1, n2)
    ("scalar", [0], 0, 50, 100),
    ("append_grow", [0], 0, 64, 128),
    ("append_cap", [1000, 0], 1, 50, 100),
    ("write_fixed", [10, 0], 1, 50, 100),
    ("read_fixed", [10, 0], 1, 50, 100),
    ("struct_arr_100", [0], 0, 50, 100),
    ("alloc_new", [0], 0, 50, 100),
    ("heap_then_scalar", [0, 0], 1, 50, 100),
    ("heap_then_scalar", [0, 0], 0, 50, 100),
    ("map_write", [0], 0, 50, 100),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--golean", required=True)
    ap.add_argument("--frontend", required=True)
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--plan", choices=["smoke", "full", "steps"], default="smoke")
    ap.add_argument("--only", help="comma-separated probe names to restrict the plan to")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    golean, frontend, scratch = Path(a.golean), Path(a.frontend), Path(a.scratch)
    scratch.mkdir(parents=True, exist_ok=True)
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "status", "--porcelain", "--", "GoLean", "tools", "Main.lean",
                            "lakefile.toml", "lean-toolchain"], capture_output=True, text=True).stdout.strip()
    meta = {
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "commit": commit, "runtime_tree_dirty": bool(dirty),
        "golean_sha256": sha256(golean), "frontend_sha256": sha256(frontend),
        "go_version": subprocess.run(["go", "version"], capture_output=True, text=True).stdout.strip(),
        "kernel": os.uname().release, "nproc": os.cpu_count(),
        "loadavg1_at_start": loadavg1(), "plan": a.plan,
        "timing_method": "wall = time.monotonic() around /usr/bin/time wrapper (startup included; "
                         "subtract the empty probe); cpu = user+sys of the golean child; "
                         "maxrss from /usr/bin/time %M (KB)",
    }
    print(json.dumps(meta, indent=1), flush=True)
    names = sorted(ARITY)
    if a.only:
        names = [n for n in names if n in a.only.split(",")]
    wires = {n: lower(frontend, n, scratch) for n in names}
    result = {"meta": meta, "points": [], "steps": []}
    if a.plan == "steps":
        for (name, base, idx, n1, n2) in STEP_PLAN:
            if name in wires:
                result["steps"].append(steps_per_iteration(golean, wires[name], name, base, idx, n1, n2))
    else:
        plan = plan_full() if a.plan == "full" else plan_smoke()
        for (name, args, runs, timeout) in plan:
            if name not in wires:
                continue
            result["points"].append(run_point(golean, wires[name], name, args, runs, timeout))
            Path(a.out).write_text(json.dumps(result, indent=1) + "\n")
    meta["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    meta["loadavg1_at_end"] = loadavg1()
    Path(a.out).write_text(json.dumps(result, indent=1) + "\n")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()
