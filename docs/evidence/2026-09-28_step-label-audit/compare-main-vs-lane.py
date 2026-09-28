#!/usr/bin/env python3
"""[AGENT auditor] zero-behaviour-change comparison: main 84f0a9e4 golean vs lane 61bdc65d golean.
Per sampled row: own wire export (the gate's frontend invocation), then both binaries under
identical argv; stdout, stderr and exit code compared byte-for-byte."""
import csv, os, random, re, subprocess, sys, json, hashlib
from concurrent.futures import ThreadPoolExecutor
ROOT = "/home/dev/projects/golean/.claude/worktrees/audit-step-label"
MAIN = "/home/dev/projects/golean/.claude/worktrees/audit-step-label-main/.lake/build/bin/golean"
LANE = ROOT + "/.lake/build/bin/golean"
OUT = ROOT + "/.tmp/cmp"
STREAMS = [None, "9,8,7,6,5,4,3,2,1,0", "1,3,5,7,9,2,4,6,8,0", "5,5,5,5,5,5,5,5", "1,1,1,1,1,1,1,1,1,1,1,1"]
rows = [r.rstrip("\n").split("\t") for r in open(ROOT + "/.tmp/manifest.tsv")]
rng = random.Random(20260928)
pat = re.compile(r"unseq|goroutine|select|chan|recover|init|sync|trylock|print|append|atomic|nil|wait|mutex|once")
strict = [r for r in rows if r[7] == "strict"]
focus = [r for r in strict if pat.search(r[0]) or pat.search(r[5])]
rest = [r for r in strict if r not in focus]
mp = [r for r in rest if re.search(r"map|panic|defer|range", r[0] + r[5])]
other = [r for r in rest if r not in mp]
sample_strict = focus + rng.sample(mp, min(200, len(mp))) + rng.sample(other, min(150, len(other)))
enum = [r for r in rows if r[7] != "strict" and "tier=slow" not in r[9]]
def params(p):
    d = dict(width="", sites="8", cap="64", work="200000", backedge="", nonterm="", engine="", statuses="")
    if p != "-":
        for kv in p.split(","):
            k, v = kv.split("=", 1); d[k] = v
    return d
def wire(r):
    w = f"{OUT}/wire/{r[0].replace('/', '__')}.json"
    if os.path.exists(w): return w
    flags = ["--allow-hidden-dep-init-order"] if r[0] == "init/hidden-dep-order" else []
    env = dict(os.environ, GO111MODULE="off", GOCACHE=ROOT + "/artifacts/go-build-cache")
    p = subprocess.run(["go", "run", "./tools/nativefrontend", *flags, "--dir", r[1], "--out", w], cwd=ROOT, env=env, capture_output=True, text=True)
    return w if p.returncode == 0 else None
def run(binary, argv, timeout):
    try:
        p = subprocess.run([binary, *argv], capture_output=True, timeout=timeout)
        return (p.returncode, p.stdout, p.stderr)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", b"", b"")
def jobs_for(r, w):
    base = ["--input", w, "--function", r[2]]
    ints = [] if r[3] == "-" else sum([["--arg-int", v] for v in r[3].split(",")], [])
    out = []
    if r[7] == "strict":
        for s in STREAMS:
            out.append(("run:" + (s or "default"), ["native-json-run", *base, *ints] + (["--choices", s] if s else []), 300))
    else:
        d = params(r[9])
        st = "race" if r[7] == "racy" else (d["statuses"].replace("+", ",") if d["statuses"] else r[4])
        a = ["coverage-observations", *base, "--max-width", d["width"], "--max-sites", d["sites"], "--cap", d["cap"], "--work-cap", d["work"], "--expect-status", st, *ints]
        if d["backedge"]: a += ["--backedge", d["backedge"]]
        if d["engine"]: a += ["--engine", d["engine"]]
        if d["nonterm"]: a += ["--allow-nonterm", d["nonterm"]]
        out.append(("enum", a, 900))
        out.append(("run:default", ["native-json-run", *base, *ints], 300))
    return out
def one(r):
    w = wire(r)
    if not w: return [(r[0], "export", "EXPORT-REFUSED", "", "")]
    res = []
    for tag, argv, to in jobs_for(r, w):
        a = run(MAIN, argv, to); b = run(LANE, argv, to)
        a2 = (a[0], a[1], a[2].replace(MAIN.encode(), b"BIN")); b2 = (b[0], b[1], b[2].replace(LANE.encode(), b"BIN"))
        same = "SAME" if a2 == b2 else "DIFF"
        res.append((r[0], tag, same, str(a[0]), hashlib.sha256(a[1]).hexdigest()[:12]))
        if same == "DIFF":
            with open(f"{OUT}/diff-{r[0].replace('/', '__')}-{tag.replace(':','_').replace(',','')}.txt", "wb") as f:
                f.write(b"MAIN rc=%s\n" % str(a[0]).encode() + a[1] + b"\n--stderr--\n" + a[2] + b"\nLANE rc=%s\n" % str(b[0]).encode() + b[1] + b"\n--stderr--\n" + b[2])
    return res
os.makedirs(OUT + "/wire", exist_ok=True)
todo = sample_strict + enum
print(f"sample: strict {len(sample_strict)} (focus {len(focus)}), enumerating {len(enum)}", flush=True)
with ThreadPoolExecutor(int(sys.argv[1]) if len(sys.argv) > 1 else 6) as ex, open(OUT + "/results.tsv", "w") as f:
    for res in ex.map(one, todo):
        for t in res: f.write("\t".join(t) + "\n")
        f.flush()
print("done", flush=True)
