#!/usr/bin/env python3
"""tracereplay.py v2 — the datadriven-trace differential, THREE channels
(W4.3 items 2+3, docs/raft-w43-log.md; v1 was the W4.2 ok-tier).

The three channels, and what each can see (the tier-strength bound,
docs/raft-w42-log.md item 4):

  1. OK-TIER: blocks whose upstream expectation is literally `ok` must
     produce empty handler output. Asserts command acceptance only —
     blind to delivery order.
  2. MACHINE/BYTE TIER: the whole driver trace (rendered output included)
     compared byte-for-byte between `go run` and the machine. The right
     instrument for "does the machine agree with Go"; oracle-symmetric,
     so structurally unable to see a mirror bug.
  3. RENDERED TIER: every supported block's rendered output compared
     against the trace file's EXPECTED TEXT — upstream's own recorded
     output, the one oracle external to us. This is the channel that can
     FALSIFY the replay mirror (message order, drop markers, Ready
     contents, log lines). Scored per renderer family (the
     command-anchored reading of tools/raftsubject/tracefamilies.py).

  1. parses every `deps/raft/testdata/*.txt` into datadriven blocks,
  2. computes each trace's SUPPORTED PREFIX over the replay env's command
     subset (a trace is replayed up to its first unsupported command —
     later blocks depend on the skipped state; design §7),
  3. generates a per-trace Go driver (replayenv.go + a generated main.go)
     and runs it under `go run` AND the machine,
  4. scores all three channels.

    tools/raftsubject/tracereplay.py [--traces a,b,...] [--no-machine]
                                     [--fuel N] [--keep] [--go-only]

Unsupported-by-design commands, each with its reason:
  tick-election / set-randomized-election-timeout — jitter-sensitive: the
      D-11 draw's VALUE differs across oracles (that is what a choice
      site is), so same-trace-on-both-oracles cannot hold through a
      timeout-driven election; the jitter ENVELOPE is the membership
      lane's (maps/jitter-draw).
  compact / send-snapshot — the subject tree never compacts (snapshots in
      Ready fail closed); the replay env keeps no History.
  process-append-thread / process-apply-thread — async storage writes,
      §7's named deferral.
  transfer-leadership / forget-leader / report-unreachable — tier-2
      events not in the v1 vocabulary.
  add-nodes with async-storage-writes/content/read-only args — same.

propose-conf-change is SUPPORTED as of W4.3 item 2 (v1= and transition=
args, the change-string body parsed by the subject's own
ConfChangesFromString; the apply path dispatches ApplyConfChange).
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
    "send-snapshot", "process-append-thread",
    "process-apply-thread", "transfer-leadership", "forget-leader",
    "report-unreachable",
}
ADD_NODES_ARGS = {"voters", "learners", "index", "inflight", "prevote",
                  "checkquorum", "max-committed-size-per-ready",
                  "step-down-on-removal", "disable-conf-change-validation"}

TRANSITIONS = {"auto": 0, "implicit": 1, "explicit": 2}


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
    """'cmd a b k=(v1,v2) k2=v' -> (cmd, [bare...], {k: [vals...]}).
    Token ORDER is also returned for order-sensitive commands
    (deliver-msgs delivers/drops in argument-position order)."""
    toks = re.findall(r"\S+", line)
    cmd, bare, kv, ordered = toks[0], [], {}, []
    for t in toks[1:]:
        m = re.match(r"^([\w-]+)=\(?([^)]*)\)?$", t)
        if m and "=" in t:
            vals = [v for v in re.split(r"[,\s]+", m.group(2)) if v]
            kv[m.group(1)] = vals
            ordered.append((m.group(1), vals))
        else:
            bare.append(t)
            ordered.append((None, t))
    return cmd, bare, kv, ordered


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
    gocode: statements computing `err error` for this block."""
    cmd, bare, kv, ordered = parse_args_line(cmdlines[0])
    if len(cmdlines) != 1 and cmd != "propose-conf-change":
        return "unsupported", None, "multi-line command input (%s)" % cmd
    if cmd in UNSUPPORTED:
        return "unsupported", None, cmd
    if cmd == "_breakpoint":
        return "ok", "var err error", None
    if cmd == "log-level":
        if len(bare) != 1:
            return "unsupported", None, "log-level arg shape"
        return "ok", ("var err error\n"
                      "if !e.setLogLevel(%s) { err = errString(\"log levels must be "
                      "either of [DEBUG INFO WARN ERROR FATAL NONE]\") }"
                      % json.dumps(bare[0])), None
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
        return "ok", ("err := e.addNodes(%d, %s, %s, %s, %s, %s, %s, %s, %s, %s)"
                      % (n, voters, learners, index, pv, cq, infl, mcs, sdr, ccv)), None
    if cmd == "campaign":
        if len(bare) != 1:
            return "unsupported", None, "campaign arg shape"
        return "ok", "err := e.campaign(%d)" % (int(bare[0]) - 1), None
    if cmd == "propose":
        if len(bare) != 2:
            return "unsupported", None, "propose arg shape"
        return "ok", "err := e.propose(%d, %s)" % (int(bare[0]) - 1,
                                                   json.dumps(bare[1])), None
    if cmd == "propose-conf-change":
        if len(bare) != 1 or not bare[0].isdigit():
            return "unsupported", None, "propose-conf-change arg shape"
        extra = set(kv) - {"v1", "transition"}
        if extra:
            return "unsupported", None, "propose-conf-change %s" % ",".join(sorted(extra))
        v1 = "true" if kv.get("v1", ["false"])[0] == "true" else "false"
        tname = kv.get("transition", ["auto"])[0]
        if tname not in TRANSITIONS:
            return "unsupported", None, "propose-conf-change transition %s" % tname
        body = "\n".join(cmdlines[1:])
        return "ok", ("err := e.proposeConfChange(%d, %s, %s, %d)"
                      % (int(bare[0]) - 1, json.dumps(body), v1,
                         TRANSITIONS[tname])), None
    if cmd == "deliver-msgs":
        # Argument-POSITION order is the delivery order (upstream walks
        # one Recipient list); bare = deliver, drop=(...) = drop.
        recips = []
        typ = "-1"
        for key, val in ordered:
            if key is None:
                if not val.isdigit():
                    return "unsupported", None, "deliver-msgs arg shape"
                recips.append("{id: %s}" % val)
            elif key == "drop":
                for v in val:
                    if not v.isdigit():
                        return "unsupported", None, "deliver-msgs drop shape"
                    recips.append("{id: %s, drop: true}" % v)
            elif key == "type":
                name = val[0]
                if name not in MSG_TYPES:
                    return "unsupported", None, "deliver-msgs type %s" % name
                typ = str(MSG_TYPES[name])
            else:
                return "unsupported", None, "deliver-msgs %s" % key
        return "ok", ("var err error\n"
                      "e.handleDeliverMsgs([]recipient{%s}, %s)"
                      % (", ".join(recips), typ)), None
    if cmd == "process-ready":
        idxs = [str(int(b) - 1) for b in bare if b.isdigit()]
        if len(idxs) != len(bare) or not idxs:
            return "unsupported", None, "process-ready arg shape"
        return "ok", "err := e.handleProcessReady([]int{%s})" % ",".join(idxs), None
    if cmd == "stabilize":
        idxs = [str(int(b) - 1) for b in bare if b.isdigit()]
        if len(idxs) != len(bare):
            return "unsupported", None, "stabilize arg shape"
        extra = set(kv) - {"log-level"}
        if extra:
            return "unsupported", None, "stabilize %s" % ",".join(sorted(extra))
        if "log-level" in kv:
            return "ok", ("err := e.stabilizeWithLogLevel([]int{%s}, %s)"
                          % (",".join(idxs), json.dumps(kv["log-level"][0]))), None
        return "ok", "err := e.stabilize([]int{%s})" % ",".join(idxs), None
    if cmd == "tick-heartbeat":
        if len(bare) != 1:
            return "unsupported", None, "tick-heartbeat arg shape"
        return "ok", "e.tick(%d, 1)\nvar err error" % (int(bare[0]) - 1), None
    if cmd == "raft-state":
        return "ok", "e.handleRaftState()\nvar err error", None
    if cmd == "status":
        if len(bare) != 1:
            return "unsupported", None, "status arg shape"
        return "ok", "e.handleStatus(%d)\nvar err error" % (int(bare[0]) - 1), None
    if cmd == "raft-log":
        if len(bare) != 1:
            return "unsupported", None, "raft-log arg shape"
        return "ok", "err := e.handleRaftLog(%d)" % (int(bare[0]) - 1), None
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
        body += "\t\te.block(%d, %s, err)\n" % (k + 1, json.dumps(cmd))
        body += "\t}\n"
    return MAIN_TMPL % (name, prefix, len(blocks), body)


BLOCK_RE = re.compile(r"\x01B (\d+) (\S+)\n(.*?)\x01E \1 ", re.S)


def parse_trace(trace):
    """-> {k: output-string (trailing newline stripped)}."""
    outs = {}
    for m in BLOCK_RE.finditer(trace):
        outs[int(m.group(1))] = m.group(3).rstrip("\n")
    return outs


# The command-anchored family map — tools/raftsubject/tracefamilies.py's
# BY_COMMAND is the record; imported lazily to avoid a circular import
# (tracefamilies imports parse_blocks from here). A drift between the two
# is a loud KeyError at report time, not a silent recount.
def family_of(cmd):
    from tracefamilies import BY_COMMAND
    return BY_COMMAND.get(cmd, "other/mixed") if cmd != "log-level" else None


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
    go_trace = r.stderr.rstrip("\n")
    outs = parse_trace(go_trace)

    # Channel 1 (ok-tier) + channel 3 (rendered) off the go-run trace.
    ok_blocks = ok_agree = 0
    rend_blocks = rend_agree = 0
    fam_tot = {}
    fam_agree = {}
    diverges = []
    for k, (cmdlines, exp) in enumerate(blocks[:prefix]):
        cmd = parse_args_line(cmdlines[0])[0]
        got = outs.get(k + 1)
        expect = exp.rstrip("\n")
        if expect == "ok":
            ok_blocks += 1
            if got == "ok":
                ok_agree += 1
            else:
                diverges.append((k + 1, cmd, "expected ok, got %r" % (got or "<missing>")[:200]))
        else:
            fam = family_of(cmd) or "other/mixed"
            rend_blocks += 1
            fam_tot[fam] = fam_tot.get(fam, 0) + 1
            if got == expect:
                rend_agree += 1
                fam_agree[fam] = fam_agree.get(fam, 0) + 1
            else:
                # name the first diverging line, honestly
                gl = (got or "<missing>").split("\n")
                el = expect.split("\n")
                d = next((i for i in range(min(len(gl), len(el)))
                          if gl[i] != el[i]), min(len(gl), len(el)))
                diverges.append((k + 1, cmd, "line %d: exp=%r got=%r"
                                 % (d + 1, el[d] if d < len(el) else "<eof>",
                                    gl[d] if d < len(gl) else "<eof>")))

    rep = {"blocks": len(blocks), "prefix": prefix,
           "ok_blocks": ok_blocks, "ok_agree": ok_agree,
           "rend_blocks": rend_blocks, "rend_agree": rend_agree,
           "fam_tot": fam_tot, "fam_agree": fam_agree,
           "diverge": diverges}

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
                    mt = bytes(v["bytes"]).decode("utf-8").rstrip("\n")
                else:
                    mt = "<undecodable observation value>"
                if mt == go_trace:
                    rep["machine"] = "AGREE"
                else:
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
    report = {}
    for name in names:
        blocks = parse_blocks(os.path.join(TESTDATA, name + ".txt"))
        total_blocks += len(blocks)
        prefix = 0
        stop_reason = None
        for cmdlines, _exp in blocks:
            kind, _code, reason = classify(cmdlines)
            if kind != "ok":
                stop_reason = reason
                break
            prefix += 1
        total_prefix += prefix
        if prefix == 0:
            report[name] = {"blocks": len(blocks), "prefix": 0,
                            "stopped-by": stop_reason}
            continue
        run_one(name, blocks, prefix, args, report)
        report[name]["stopped-by"] = stop_reason

    ok_tot = sum(r.get("ok_blocks", 0) for r in report.values())
    ok_agr = sum(r.get("ok_agree", 0) for r in report.values())
    rend_tot = sum(r.get("rend_blocks", 0) for r in report.values())
    rend_agr = sum(r.get("rend_agree", 0) for r in report.values())

    print("# tracereplay.py v2 — %d traces, %d blocks total" % (len(names), total_blocks))
    print("# supported-prefix blocks: %d (%.1f%%)"
          % (total_prefix, 100.0 * total_prefix / max(total_blocks, 1)))
    print()
    print("OK-TIER:       %d/%d ok-expectation blocks agree (empty handler output "
          "where upstream expects ok)" % (ok_agr, ok_tot))
    print("RENDERED-TIER: %d/%d rendered-expectation blocks agree byte-for-byte "
          "with upstream's recorded output" % (rend_agr, rend_tot))
    fam_tot = {}
    fam_agr = {}
    for r in report.values():
        for f, n in r.get("fam_tot", {}).items():
            fam_tot[f] = fam_tot.get(f, 0) + n
        for f, n in r.get("fam_agree", {}).items():
            fam_agr[f] = fam_agr.get(f, 0) + n
    for f in sorted(fam_tot, key=lambda f: -fam_tot[f]):
        print("  family %-24s %4d/%4d" % (f, fam_agr.get(f, 0), fam_tot[f]))
    m_agree = sum(1 for r in report.values() if r.get("machine") == "AGREE")
    m_ran = sum(1 for r in report.values() if "machine" in r)
    if not args.no_machine:
        print("MACHINE:       %d/%d replayed traces agree byte-for-byte with go run"
              % (m_agree, m_ran))
    print()
    for name in names:
        r = report.get(name, {})
        line = "%-42s %3d/%3d blocks" % (name, r.get("prefix", 0), r.get("blocks", 0))
        if r.get("prefix"):
            line += "  ok %d/%d  rendered %d/%d" % (
                r.get("ok_agree", 0), r.get("ok_blocks", 0),
                r.get("rend_agree", 0), r.get("rend_blocks", 0))
        if r.get("stopped-by"):
            line += "  [stops at: %s]" % r["stopped-by"]
        if "error" in r:
            line += "  ERROR %s" % r["error"][:160]
        print(line)
        if r.get("machine") and r["machine"] != "AGREE":
            print("    machine: %s" % r["machine"])
        for k, cmd, why in r.get("diverge", [])[:8]:
            print("    diverge: block %d (%s) %s" % (k, cmd, why))
        if len(r.get("diverge", [])) > 8:
            print("    ... %d more divergences" % (len(r["diverge"]) - 8))


if __name__ == "__main__":
    main()
