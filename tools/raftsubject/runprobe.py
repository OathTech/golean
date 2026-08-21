#!/usr/bin/env python3
"""runprobe.py — run a raft-subject probe main under BOTH oracles.

W4.1's THE-MOMENT instrument (docs/raft-w41-log.md): copies the tracked
subject tree (`raftsubject/`) plus one tracked probe main
(default: rawnode-probe-main.go, the minimal single-node RawNode drive)
into a scratch program, runs it under

  1. `go run` (GOPATH scratch — the subject tree is stdlib-free beyond
     `errors` and `sync`), and
  2. THE MACHINE (native frontend export + `golean native-json-run`),

and compares the named subject function's observation. Exit 0 iff both
oracles produced a clean value AND agree. The machine's failure detail
(a frontend refusal, an unsupported stop, a stuck, fuel exhaustion) is
printed verbatim — this instrument's whole job is an HONEST first-stop
report.

    tools/raftsubject/runprobe.py [--function probeRawNode]
                                  [--main rawnode-probe-main.go]
                                  [--fuel N] [--keep]

Needs `artifacts/nativefrontend` and `.lake/build/bin/golean`.
Uncapped — point it only at this small tree.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

SUBJECT_PKGS = ["quorum", "raftpb", "tracker", "proto", "confchange", "raft"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--function", default="probeRawNode")
    ap.add_argument("--main", default="rawnode-probe-main.go")
    ap.add_argument("--fuel", default="200000000")
    ap.add_argument("--expect-stop", default=None, metavar="SUBSTR",
                    help="NEGATIVE probe mode (W4.2 logger-teeth): PASS iff "
                         "go run FAILS (loudly) and the machine's first stop "
                         "detail contains SUBSTR. Both refusals are printed "
                         "verbatim — the point is to witness that a "
                         "fail-closed stub has teeth, so a green run of the "
                         "same drive WITH the harness logger installed is a "
                         "meaningful negative (nothing called the stub), not "
                         "a vacuous one.")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--out", default=os.path.join(REPO, "artifacts", "runprobe"))
    ap.add_argument("--frontend", default=os.path.join(REPO, "artifacts", "nativefrontend"))
    ap.add_argument("--golean", default=os.path.join(REPO, ".lake", "build", "bin", "golean"))
    args = ap.parse_args()

    for tool, hint in ((args.frontend, "GO111MODULE=off go build -o artifacts/nativefrontend ./tools/nativefrontend"),
                       (args.golean, "scripts/capped lake build golean")):
        if not os.path.exists(tool):
            sys.exit("runprobe.py: missing %s (build it: %s)" % (tool, hint))

    out = args.out
    shutil.rmtree(out, ignore_errors=True)
    prog = os.path.join(out, "prog")
    os.makedirs(prog)
    for pkg in SUBJECT_PKGS:
        shutil.copytree(os.path.join(REPO, "raftsubject", pkg), os.path.join(prog, pkg))
    shutil.copy(os.path.join(HERE, args.main), os.path.join(prog, "main.go"))
    gopath = os.path.join(out, "gopath")
    os.makedirs(os.path.join(gopath, "src"))
    for pkg in SUBJECT_PKGS:
        shutil.copytree(os.path.join(prog, pkg), os.path.join(gopath, "src", pkg))

    env = dict(os.environ)
    env["GOCACHE"] = os.path.join(REPO, "artifacts", "go-build-cache")
    env["GO111MODULE"] = "off"
    env["GOPATH"] = gopath
    r = subprocess.run(["go", "run", "main.go"], cwd=prog, env=env,
                       capture_output=True, text=True)
    if args.expect_stop is not None:
        if r.returncode == 0:
            sys.exit("runprobe.py: expect-stop probe: go run SUCCEEDED, but "
                     "the probe expects a loud failure on both oracles:\n%s"
                     % r.stderr)
        print("runprobe: go run refused loudly, as the probe expects "
              "(last lines):\n  %s"
              % "\n  ".join(r.stderr.strip().splitlines()[-3:]))
    elif r.returncode != 0:
        sys.exit("runprobe.py: go run failed:\n%s%s" % (r.stdout, r.stderr))
    go_verdict = r.stderr.strip()  # builtin println writes to stderr
    if args.expect_stop is None:
        print("runprobe: go run %s -> %s" % (args.function, go_verdict))

    wire = os.path.join(out, "wire.json")
    r = subprocess.run([args.frontend, "--dir", prog, "--out", wire],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("runprobe.py: FRONTEND EXPORT REFUSED (the machine's first stop):\n%s" % r.stderr)
    r = subprocess.run([args.golean, "native-json-run", "--input", wire,
                        "--function", args.function, "--fuel", args.fuel],
                       capture_output=True, text=True)
    raw = r.stdout.strip()
    if not raw:
        sys.exit("runprobe.py: machine produced no observation:\n%s" % r.stderr)
    try:
        obs = json.loads(raw.splitlines()[-1])
    except ValueError:
        sys.exit("runprobe.py: unreadable machine observation:\n%s%s" % (r.stdout, r.stderr))
    if args.expect_stop is not None:
        if obs.get("status") == "ok":
            sys.exit("runprobe.py: expect-stop probe: the machine ran CLEAN "
                     "— the stub the probe aims at was never reached:\n%s" % raw)
        if args.expect_stop not in raw:
            sys.exit("runprobe.py: expect-stop probe: the machine stopped, "
                     "but not at %r (first stop, verbatim):\n%s"
                     % (args.expect_stop, raw))
        print("runprobe: machine first stop contains %r, verbatim:\n  %s"
              % (args.expect_stop, raw))
        if not args.keep:
            shutil.rmtree(out, ignore_errors=True)
        print("runprobe: PASS (expect-stop) — both oracles refuse this drive "
              "loudly; the fail-closed stub has teeth")
        return
    if obs.get("status") != "ok":
        sys.exit("runprobe.py: THE MACHINE STOPPED (first stop, verbatim):\n%s" % raw)
    vals = obs.get("values", [])
    if len(vals) != 1:
        sys.exit("runprobe.py: unexpected observation shape: %s" % raw)
    machine_verdict = str(vals[0].get("value"))
    print("runprobe: machine %s -> %s" % (args.function, machine_verdict))

    if not args.keep:
        shutil.rmtree(out, ignore_errors=True)
    if go_verdict != machine_verdict:
        sys.exit("runprobe.py: ORACLES DISAGREE (go=%s machine=%s)"
                 % (go_verdict, machine_verdict))
    print("runprobe: PASS — both oracles agree: %s" % machine_verdict)


if __name__ == "__main__":
    main()
