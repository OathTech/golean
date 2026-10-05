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
                                  [--fuel N] [--choices N,N,...] [--keep]
                                  [--expect-panic-member TEXT ...]

Since route A slice S2 (docs/2026-10-04_route-a-protobuf-design.md §5
«Through RawNode»): `--expect-panic-member TEXT` (repeatable) is the
ABORT-MEMBERSHIP mode — PASS iff `go run` aborts with a `panic: <m>` line
and the machine stops with status `panic` and message <m'>, where m and
m' are each EXACTLY one of the listed members (they need not be the same
member: the members are a latitude's admitted texts, each leg draws its
own). `\\uXXXX` escapes in TEXT are decoded (the U+00A0 spelling).
`--choices` is passed through to the machine leg verbatim.

Needs `artifacts/nativefrontend` and `.lake/build/bin/golean`.
Uncapped — point it only at this small tree.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

SUBJECT_PKGS = ["quorum", "raftpb", "tracker", "proto", "confchange", "raft"]


def decode_value(v):
    """One observation value -> comparable text. Ints/bools arrive under
    'value'; strings arrive as {'bytes': [...], 'tag': 'string'} (UTF-8
    code units). Returns None on an unrecognized shape — the caller
    fails loud, never compares a placeholder."""
    if "value" in v:
        return str(v["value"])
    if v.get("tag") == "string" and isinstance(v.get("bytes"), list):
        return bytes(v["bytes"]).decode("utf-8").strip()
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--function", default="probeRawNode")
    ap.add_argument("--main", default="rawnode-probe-main.go")
    ap.add_argument("--lib", action="append", default=[],
                    help="additional package-main library source(s) copied "
                         "beside the probe main (e.g. twin-lib.go)")
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
    ap.add_argument("--expect-panic-member", action="append", default=None,
                    metavar="TEXT",
                    help="ABORT-MEMBERSHIP mode (route A S2): PASS iff both "
                         "oracles abort with a panic whose text is EXACTLY "
                         "one of the members given (repeat the flag per "
                         "member; \\uXXXX escapes decoded). Each leg's "
                         "member is reported.")
    ap.add_argument("--choices", default=None, metavar="N,N,...",
                    help="the machine leg's choice stream (passed to "
                         "native-json-run --choices verbatim)")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--out", default=os.path.join(REPO, "artifacts", "runprobe"))
    ap.add_argument("--frontend", default=os.path.join(REPO, "artifacts", "nativefrontend"))
    ap.add_argument("--golean", default=os.path.join(REPO, ".lake", "build", "bin", "golean"))
    args = ap.parse_args()
    if args.expect_panic_member is not None and args.expect_stop is not None:
        sys.exit("runprobe.py: --expect-stop and --expect-panic-member are "
                 "different modes; give one")
    members = None
    if args.expect_panic_member is not None:
        members = [re.sub(r"\\u([0-9a-fA-F]{4})",
                          lambda mo: chr(int(mo.group(1), 16)), t)
                   for t in args.expect_panic_member]

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
    for lib in args.lib:
        shutil.copy(os.path.join(HERE, lib), os.path.join(prog, os.path.basename(lib)))
    gopath = os.path.join(out, "gopath")
    os.makedirs(os.path.join(gopath, "src"))
    for pkg in SUBJECT_PKGS:
        shutil.copytree(os.path.join(prog, pkg), os.path.join(gopath, "src", pkg))

    env = dict(os.environ)
    env["GOCACHE"] = os.path.join(REPO, "artifacts", "go-build-cache")
    env["GO111MODULE"] = "off"
    env["GOPATH"] = gopath
    r = subprocess.run(["go", "run", "."], cwd=prog, env=env,
                       capture_output=True, text=True)
    if args.expect_stop is not None:
        if r.returncode == 0:
            sys.exit("runprobe.py: expect-stop probe: go run SUCCEEDED, but "
                     "the probe expects a loud failure on both oracles:\n%s"
                     % r.stderr)
        print("runprobe: go run refused loudly, as the probe expects "
              "(last lines):\n  %s"
              % "\n  ".join(r.stderr.strip().splitlines()[-3:]))
    elif members is not None:
        if r.returncode == 0:
            sys.exit("runprobe.py: expect-panic probe: go run SUCCEEDED, but "
                     "the probe expects an abort:\n%s" % r.stderr)
        plines = [l for l in r.stderr.splitlines() if l.startswith("panic: ")]
        if len(plines) != 1:
            sys.exit("runprobe.py: expect-panic probe: go run's stderr has "
                     "%d 'panic: ' lines (want exactly 1):\n%s"
                     % (len(plines), r.stderr))
        go_text = plines[0][len("panic: "):]
        if go_text not in members:
            sys.exit("runprobe.py: expect-panic probe: go run aborted with "
                     "%r, NOT a member of %r" % (go_text, members))
        print("runprobe: go run aborted with member %d: %r"
              % (members.index(go_text), go_text))
    elif r.returncode != 0:
        sys.exit("runprobe.py: go run failed:\n%s%s" % (r.stdout, r.stderr))
    go_verdict = r.stderr.strip()  # builtin println writes to stderr
    if args.expect_stop is None and members is None:
        print("runprobe: go run %s -> %s" % (args.function, go_verdict))

    wire = os.path.join(out, "wire.json")
    r = subprocess.run([args.frontend, "--dir", prog, "--out", wire],
                       capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("runprobe.py: FRONTEND EXPORT REFUSED (the machine's first stop):\n%s" % r.stderr)
    cmd = [args.golean, "native-json-run", "--input", wire,
           "--function", args.function, "--fuel", args.fuel]
    if args.choices is not None:
        cmd += ["--choices", args.choices]
    r = subprocess.run(cmd, capture_output=True, text=True)
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
    if members is not None:
        if obs.get("status") != "panic":
            sys.exit("runprobe.py: expect-panic probe: the machine's status "
                     "is %r, not 'panic' (verbatim):\n%s"
                     % (obs.get("status"), raw[:2000]))
        m_text = obs.get("message")
        if m_text not in members:
            sys.exit("runprobe.py: expect-panic probe: the machine aborted "
                     "with %r, NOT a member of %r" % (m_text, members))
        print("runprobe: machine aborted with member %d: %r"
              % (members.index(m_text), m_text))
        if not args.keep:
            shutil.rmtree(out, ignore_errors=True)
        print("runprobe: PASS (expect-panic) — both oracles abort with a "
              "member text (go: member %d, machine: member %d)"
              % (members.index(go_text), members.index(m_text)))
        return
    if obs.get("status") != "ok":
        sys.exit("runprobe.py: THE MACHINE STOPPED (first stop, verbatim):\n%s" % raw)
    vals = obs.get("values", [])
    if len(vals) != 1:
        sys.exit("runprobe.py: unexpected observation shape: %s" % raw)
    machine_verdict = decode_value(vals[0])
    if machine_verdict is None:
        sys.exit("runprobe.py: unreadable observation value (neither 'value' "
                 "nor a string 'bytes' form): %s" % raw[:400])
    print("runprobe: machine %s -> %s" % (args.function, machine_verdict))

    if not args.keep:
        shutil.rmtree(out, ignore_errors=True)
    if go_verdict != machine_verdict:
        sys.exit("runprobe.py: ORACLES DISAGREE (go=%s machine=%s)"
                 % (go_verdict, machine_verdict))
    print("runprobe: PASS — both oracles agree: %s" % machine_verdict)


if __name__ == "__main__":
    main()
