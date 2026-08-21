#!/usr/bin/env python3
"""tracereplay.py — the datadriven-trace ok-tier differential (W4.2 item 3).

The harness design §7's ruling, mechanized: upstream's testdata traces are
COMMAND SEQUENCES, the oracle is `go run`, and the 249 literally-`ok`
expectation blocks are the free tier — they assert a command was ACCEPTED
and need no rendering. This instrument:

  1. parses every `deps/raft/testdata/*.txt` into datadriven blocks
     (command line / ---- / expected output),
  2. computes each trace's SUPPORTED PREFIX over the replay env's command
     subset (a trace is replayed up to its first unsupported command —
     later blocks depend on the skipped state, so a partial replay past
     that point would be meaningless; design §7's "a partially replayed
     trace has no meaningful pass/fail"),
  3. generates a per-trace Go driver (replayenv.go + a generated main.go
     carrying the command sequence) and runs it under `go run` AND the
     machine (native frontend + `golean native-json-run`), comparing the
     trace observation byte for byte,
  4. scores the ok-tier: for each block in the prefix whose expectation
     is literally `ok`, the driver's verdict for that block must be `ok`.

MEASUREMENT ONLY — no corpus rows land from here (the lane is scoped
corpus-free; wanted guardrails are owed rows in docs/raft-w42-log.md).

    tools/raftsubject/tracereplay.py [--traces a,b,...] [--no-machine]
                                     [--fuel N] [--keep]

Unsupported-by-design commands, each with its reason (also in the log):
  tick-election / set-randomized-election-timeout — jitter-sensitive: the
      D-11 draw's VALUE differs across oracles (that is what a choice
      site is), so same-trace-on-both-oracles cannot hold through a
      timeout-driven election; the jitter ENVELOPE is the membership
      lane's (maps/jitter-draw).
  compact / send-snapshot — the subject tree never compacts (snapshots in
      Ready fail closed).
  propose-conf-change — conf-change apply is outside the v1 subset.
  process-append-thread / process-apply-thread — async storage writes,
      §7's named deferral.
  transfer-leadership / forget-leader / report-unreachable — tier-2
      events not in the v1 vocabulary.
  add-nodes with async-storage-writes/content/read-only args — same.
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
TESTDATA = os.path.join(REPO, "deps", "raft", "testdata")
SUBJECT_PKGS = ["quorum", "raftpb", "tracker", "proto", "confchange", "raft"]

UNSUPPORTED = {
    "tick-election", "set-randomized-election-timeout", "compact",
    "send-snapshot", "propose-conf-change", "process-append-thread",
    "process-apply-thread", "transfer-leadership", "forget-leader",
    "report-unreachable",
}
ADD_NODES_ARGS = {"voters", "learners", "index", "inflight", "prevote",
                  "checkquorum", "max-committed-size-per-ready",
                  "step-down-on-removal", "disable-conf-change-validation"}


def parse_blocks(path):
    """-> [(cmdlines, expected)] in file order."""
    lines = open(path).read().split("\n")
    blocks, i = [], 0
    while i < len(lines):
        if not lines[i].strip() or lines[i].lstrip().startswith("#"):
            i += 1
            continue
        cmd = []
        while i < len(lines) and lines[i].strip() != "----":
            cmd.append(lines[i])
            i += 1
        if i >= len(lines):
            break  # trailing junk with no ----
        i += 1  # the ----
        exp = []
        while i < len(lines) and lines[i].strip() != "":
            exp.append(lines[i])
            i += 1
        blocks.append((cmd, "\n".join(exp)))
    return blocks


def parse_args_line(line):
    """'cmd a b k=(v1,v2) k2=v' -> (cmd, [bare...], {k: [vals...]})."""
    toks = re.findall(r"\S+", line)
    cmd, bare, kv = toks[0], [], {}
    for t in toks[1:]:
        m = re.match(r"^([\w-]+)=\(?([^)]*)\)?$", t)
        if m and "=" in t:
            kv[m.group(1)] = [v for v in re.split(r"[,\s]+", m.group(2)) if v]
        else:
            bare.append(t)
    return cmd, bare, kv


def message_type_values():
    """Parse MessageType_value out of the vendored plainpb file."""
    src = open(os.path.join(REPO, "raftsubject", "raftpb", "raft.pb.go")).read()
    m = re.search(r"MessageType_value = map\[string\]int32\{(.*?)\}", src, re.S)
    if not m:
        sys.exit("tracereplay.py: cannot find MessageType_value in plainpb")
    vals = {}
    for name, num in re.findall(r'"(\w+)":\s*(\d+)', m.group(1)):
        vals[name] = int(num)
    return vals


MSG_TYPES = None


def classify(cmdlines):
    """-> (kind, gocode-or-None, reason). kind in {'ok','unsupported'}.
    gocode: the statement list computing `ok` for this block."""
    if len(cmdlines) != 1:
        return "unsupported", None, "multi-line command input"
    cmd, bare, kv = parse_args_line(cmdlines[0])
    if cmd in UNSUPPORTED:
        return "unsupported", None, cmd
    if cmd == "log-level":
        return "ok", "ok := true", None
    if cmd == "add-nodes":
        extra = set(kv) - ADD_NODES_ARGS
        if extra:
            return "unsupported", None, "add-nodes %s" % ",".join(sorted(extra))
        if len(bare) != 1 or not bare[0].isdigit():
            return "unsupported", None, "add-nodes arg shape"
        n = int(bare[0])
        voters = "[]uint64{%s}" % ",".join(kv.get("voters", []))
        learners = "[]uint64{%s}" % ",".join(kv.get("learners", []))
        index = kv.get("index", ["0"])[0]
        pv = "true" if kv.get("prevote", ["false"])[0] == "true" else "false"
        cq = "true" if kv.get("checkquorum", ["false"])[0] == "true" else "false"
        infl = kv.get("inflight", ["0"])[0]
        mcs = kv.get("max-committed-size-per-ready", ["0"])[0]
        sdr = "true" if kv.get("step-down-on-removal", ["false"])[0] == "true" else "false"
        ccv = "true" if kv.get("disable-conf-change-validation", ["false"])[0] == "true" else "false"
        return "ok", ("ok := e.addNodes(%d, %s, %s, %s, %s, %s, %s, %s, %s, %s)"
                      % (n, voters, learners, index, pv, cq, infl, mcs, sdr, ccv)), None
    if cmd == "campaign":
        if len(bare) != 1:
            return "unsupported", None, "campaign arg shape"
        return "ok", "ok := e.campaign(%d)" % (int(bare[0]) - 1), None
    if cmd == "propose":
        if len(bare) != 2:
            return "unsupported", None, "propose arg shape"
        return "ok", "ok := e.propose(%d, %s)" % (int(bare[0]) - 1,
                                                  json.dumps(bare[1])), None
    if cmd == "deliver-msgs":
        deliver = [b for b in bare if b.isdigit()]
        if len(deliver) != len(bare):
            return "unsupported", None, "deliver-msgs arg shape"
        drop = kv.get("drop", [])
        typ = "-1"
        if "type" in kv:
            name = kv["type"][0]
            if name not in MSG_TYPES:
                return "unsupported", None, "deliver-msgs type %s" % name
            typ = str(MSG_TYPES[name])
        return "ok", ("ok := e.deliverMsgs([]uint64{%s}, []uint64{%s}, %s) > 0"
                      % (",".join(deliver), ",".join(drop), typ)), None
    if cmd == "process-ready":
        idxs = [str(int(b) - 1) for b in bare if b.isdigit()]
        if len(idxs) != len(bare):
            return "unsupported", None, "process-ready arg shape"
        if not idxs:
            return "unsupported", None, "process-ready with no node"
        body = "ok := true\n"
        for i in idxs:
            body += "\tif ok { ok = e.processReady(%s) }\n" % i
        return "ok", body.rstrip(), None
    if cmd == "stabilize":
        idxs = [str(int(b) - 1) for b in bare if b.isdigit()]
        if len(idxs) != len(bare):
            return "unsupported", None, "stabilize arg shape"
        # a log-level=... kv arg is rendering-only; ignored.
        extra = set(kv) - {"log-level"}
        if extra:
            return "unsupported", None, "stabilize %s" % ",".join(sorted(extra))
        return "ok", "ok := e.stabilize([]int{%s})" % ",".join(idxs), None
    if cmd == "tick-heartbeat":
        if len(bare) != 1:
            return "unsupported", None, "tick-heartbeat arg shape"
        return "ok", "e.tick(%d, 1)\n\tok := true" % (int(bare[0]) - 1), None
    if cmd in ("raft-state", "status", "raft-log"):
        # read-only inspectors: rendered expectations, never `ok`; the
        # replay treats them as state-preserving no-ops so the trace can
        # continue past them.
        return "ok", "ok := true", None
    return "unsupported", None, cmd


MAIN_TMPL = """// GENERATED by tools/raftsubject/tracereplay.py from
// deps/raft/testdata/%s — the supported command prefix (%d of %d blocks).
// DO NOT EDIT; scratch artifact.
package main

func runTrace() string {
	e := newEnv()
%s	return e.trace
}

func main() {
	println(runTrace())
}
"""


def gen_main(name, blocks, prefix):
    body = ""
    for k, (cmdlines, _exp) in enumerate(blocks[:prefix]):
        cmd = parse_args_line(cmdlines[0])[0]
        _, code, _ = classify(cmdlines)
        body += "\tif !e.halt {\n"
        for ln in code.split("\n"):
            body += "\t\t%s\n" % ln.replace("\t", "")
        body += "\t\te.block(%d, %s, ok)\n" % (k + 1, json.dumps(cmd))
        body += "\t}\n"
    return MAIN_TMPL % (name, prefix, len(blocks), body)


def run_one(name, blocks, prefix, args, report):
    scratch = os.path.join(REPO, "artifacts", "tracereplay", name)
    shutil.rmtree(scratch, ignore_errors=True)
    prog = os.path.join(scratch, "prog")
    os.makedirs(prog)
    for pkg in SUBJECT_PKGS:
        shutil.copytree(os.path.join(REPO, "raftsubject", pkg), os.path.join(prog, pkg))
    shutil.copy(os.path.join(HERE, "replayenv.go"), os.path.join(prog, "replayenv.go"))
    with open(os.path.join(prog, "main.go"), "w") as f:
        f.write(gen_main(name, blocks, prefix))
    gopath = os.path.join(scratch, "gopath")
    os.makedirs(os.path.join(gopath, "src"))
    for pkg in SUBJECT_PKGS:
        shutil.copytree(os.path.join(prog, pkg), os.path.join(gopath, "src", pkg))

    env = dict(os.environ)
    env["GOCACHE"] = os.path.join(REPO, "artifacts", "go-build-cache")
    env["GO111MODULE"] = "off"
    env["GOPATH"] = gopath
    r = subprocess.run(["go", "run", "."], cwd=prog, env=env,
                       capture_output=True, text=True)
    if r.returncode != 0:
        report[name] = {"error": "go run failed: %s" % r.stderr.strip()[-400:]}
        return
    go_trace = r.stderr.strip()

    # ok-tier scoring off the go-run trace (the oracle).
    verdicts = {}
    for ln in go_trace.split("\n"):
        m = re.match(r"^b(\d+) (\S+)( ok| err)?", ln)
        if m:
            verdicts[int(m.group(1))] = (m.group(3) or " STOP").strip()
    ok_blocks, ok_agree, diverges = 0, 0, []
    for k, (cmdlines, exp) in enumerate(blocks[:prefix]):
        if exp.strip() == "ok":
            ok_blocks += 1
            if verdicts.get(k + 1) == "ok":
                ok_agree += 1
            else:
                diverges.append((k + 1, parse_args_line(cmdlines[0])[0],
                                 verdicts.get(k + 1, "missing")))

    rep = {"blocks": len(blocks), "prefix": prefix, "ok_blocks": ok_blocks,
           "ok_agree": ok_agree, "ok_diverge": diverges}

    if not args.no_machine:
        wire = os.path.join(scratch, "wire.json")
        r = subprocess.run([args.frontend, "--dir", prog, "--out", wire],
                           capture_output=True, text=True)
        if r.returncode != 0:
            rep["machine"] = "export refused: %s" % r.stderr.strip()[-300:]
        else:
            r = subprocess.run([args.golean, "native-json-run", "--input", wire,
                                "--function", "runTrace", "--fuel", args.fuel],
                               capture_output=True, text=True)
            raw = r.stdout.strip()
            try:
                obs = json.loads(raw.splitlines()[-1])
            except (ValueError, IndexError):
                obs = None
            if obs is None:
                rep["machine"] = "no observation: %s" % (r.stderr.strip()[-300:])
            elif obs.get("status") != "ok":
                rep["machine"] = "machine stop: %s" % raw[:300]
            else:
                v = obs["values"][0]
                if "value" in v:
                    mt = str(v["value"])
                elif v.get("tag") == "string" and isinstance(v.get("bytes"), list):
                    mt = bytes(v["bytes"]).decode("utf-8").strip()
                else:
                    mt = "<undecodable observation value>"
                if mt == go_trace:
                    rep["machine"] = "AGREE"
                else:
                    # name the first diverging line, honestly
                    gl, ml = go_trace.split("\n"), mt.split("\n")
                    d = next((i for i in range(min(len(gl), len(ml)))
                              if gl[i] != ml[i]), min(len(gl), len(ml)))
                    rep["machine"] = ("DISAGREE at line %d: go=%r machine=%r"
                                      % (d + 1, gl[d] if d < len(gl) else "<eof>",
                                         ml[d] if d < len(ml) else "<eof>"))
    report[name] = rep
    with open(os.path.join(scratch, "go-trace.txt"), "w") as f:
        f.write(go_trace + "\n")
    if not args.keep and report[name].get("machine") in ("AGREE", None):
        shutil.rmtree(scratch, ignore_errors=True)


def main():
    global MSG_TYPES
    ap = argparse.ArgumentParser()
    ap.add_argument("--traces", default=None, help="comma-separated basenames")
    ap.add_argument("--no-machine", action="store_true")
    ap.add_argument("--fuel", default="4000000000")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--frontend", default=os.path.join(REPO, "artifacts", "nativefrontend"))
    ap.add_argument("--golean", default=os.path.join(REPO, ".lake", "build", "bin", "golean"))
    args = ap.parse_args()
    MSG_TYPES = message_type_values()

    names = sorted(f[:-4] for f in os.listdir(TESTDATA) if f.endswith(".txt"))
    if args.traces:
        names = [n for n in names if n in set(args.traces.split(","))]

    total_blocks = 0
    total_prefix = 0
    total_ok = 0
    total_ok_all = 0
    report = {}
    stopper = {}
    for name in names:
        blocks = parse_blocks(os.path.join(TESTDATA, name + ".txt"))
        total_blocks += len(blocks)
        total_ok_all += sum(1 for _c, e in blocks if e.strip() == "ok")
        prefix = 0
        stop_reason = None
        for cmdlines, _exp in blocks:
            kind, _code, reason = classify(cmdlines)
            if kind != "ok":
                stop_reason = reason
                break
            prefix += 1
        total_prefix += prefix
        stopper[name] = (prefix, len(blocks), stop_reason)
        if prefix == 0:
            report[name] = {"blocks": len(blocks), "prefix": 0,
                            "stopped-by": stop_reason}
            continue
        run_one(name, blocks, prefix, args, report)
        report[name]["stopped-by"] = stop_reason
        r = report[name]
        total_ok += r.get("ok_blocks", 0)

    print("# tracereplay.py — %d traces, %d blocks total (%d expect literal ok)"
          % (len(names), total_blocks, total_ok_all))
    print("# supported-prefix blocks: %d (%.1f%%); ok-blocks inside prefixes: %d"
          % (total_prefix, 100.0 * total_prefix / max(total_blocks, 1), total_ok))
    print()
    agree = sum(r.get("ok_agree", 0) for r in report.values())
    print("OK-TIER: %d/%d ok-expectation blocks agree (driver said ok where "
          "upstream expects ok)" % (agree, total_ok))
    m_agree = sum(1 for r in report.values() if r.get("machine") == "AGREE")
    m_ran = sum(1 for r in report.values() if "machine" in r)
    if not args.no_machine:
        print("MACHINE: %d/%d replayed traces agree byte-for-byte with go run"
              % (m_agree, m_ran))
    print()
    for name in names:
        r = report.get(name, {})
        line = "%-42s %3d/%3d blocks" % (name, r.get("prefix", 0), r.get("blocks", 0))
        if r.get("prefix"):
            line += "  ok-tier %d/%d" % (r.get("ok_agree", 0), r.get("ok_blocks", 0))
        if r.get("stopped-by"):
            line += "  [stops at: %s]" % r["stopped-by"]
        if "error" in r:
            line += "  ERROR %s" % r["error"][:120]
        print(line)
        if r.get("machine") and r["machine"] != "AGREE":
            print("    machine: %s" % r["machine"])
        for k, cmd, got in r.get("ok_diverge", []):
            print("    ok-diverge: block %d (%s) driver said %s" % (k, cmd, got))


if __name__ == "__main__":
    main()
