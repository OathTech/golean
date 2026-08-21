#!/usr/bin/env python3
"""tracefamilies.py — the RENDERED-tier sizing, made reproducible (W4.2).

WHY THIS EXISTS.  `tracereplay.py` scores the FREE tier: the datadriven
blocks whose expectation is literally `ok`, which assert only that a
command was accepted and need no rendering at all.  Everything else — the
309 non-`ok` blocks — needs a Go renderer the subject tree does not yet
lower, and W4.2's handoff (docs/raft-w42-log.md item 4) sizes that work by
RENDERER FAMILY so W4.3 can pick the families in cost order.

The first cut of that table was produced by an ad hoc classification that
was never committed, so the numbers could not be re-derived from tracked
material — an audit finding (B-F5, 2026-08-21).  This file IS the method:
one classifier, one rule order, run over `deps/raft/testdata/`, printing
the table the log quotes.  Re-run it before quoting or amending any
rendered-tier number.

    tools/raftsubject/tracefamilies.py [--testdata DIR] [--per-file]

TWO READINGS ARE PRINTED, ON PURPOSE.  A datadriven block is not
single-renderer in general: one `stabilize` expectation interleaves Ready
dumps, message-describe lines and env logger lines.  So "which family is
this block" has a rule choice in it, and the honest thing is to show the
two defensible rules and where they agree:

  CONTENT-ANCHORED — assign each block to the HEAVIEST renderer its
  expectation TEXT demands, first match wins:
    1. ready dumps        a line `> N handling Ready` (DescribeReady, and
                          transitively DescribeMessage + the entry
                          formatter).
    2. raft-state tables  command `raft-state` (StateType + tracker.Config).
    3. status tables      command `status` (Progress rendering).
    4. raft-log dumps     command `raft-log` (entry describe + `%q`).
    5. pure log lines     every non-empty line is an env logger line
                          (INFO/WARN/DEBUG/ERROR) — the RECORDING-logger
                          problem, not a raft renderer (log item 4).
    6. message describe   every non-empty line is a message-describe line
                          or a `> N ...` header (DescribeMessage alone).
    7. other/mixed        the residual.

  COMMAND-ANCHORED — assign each block by the COMMAND that produced it,
  which is what a W4.3 implementer actually schedules work against (you
  make `process-ready` render, not "blocks containing a marker").

The two agree exactly on `raft-state` (30), `status` (18), `raft-log` (15)
and `pure log lines` (58) — those four are the load-bearing numbers, and
the audit's independent classifier reproduced them too.  They differ on how
the `stabilize`/`process-ready`/`deliver-msgs` mass splits, which is the
rule choice, not a fact about the corpus.

A NOTE ON THE SUPERSEDED TABLE (audit finding B-F5, 2026-08-21).  W4.2's
first cut of this table was computed ad hoc and never committed, and its
`106 ready dumps / 40 message describe / 42 other` split is NOT reproduced
by either rule here: the command-anchored rule says 128/40/20 and the
content-anchored rule says 90/11/87.  Its `40` matches the
command-anchored `deliver-msgs` count and its `58/30/18/15` match both, so
what drifted is only the split of the 148 `stabilize`+`process-ready`+
straggler blocks.  The numbers this file prints are the numbers of record.

Blocks whose expectation is literally `ok` are NOT classified — they are
`tracereplay.py`'s tier.  The two counts printed at the top (total blocks,
ok blocks) are the cross-check against that instrument's report.
"""

import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))

sys.path.insert(0, HERE)
from tracereplay import parse_blocks  # noqa: E402  (the ONE parser of record)

READY = re.compile(r"^> \d+ handling Ready\b")
RECV_HDR = re.compile(r"^> \d+ ")
LOGLINE = re.compile(r"^(INFO|WARN|WARNING|DEBUG|ERROR|FATAL) ")
MSGLINE = re.compile(r"^\d+->\d+ Msg")

FAMILIES = [
    "ready dumps",
    "raft-state tables",
    "status tables",
    "raft-log dumps",
    "pure log lines",
    "message describe lines",
    "other/mixed",
]


# The command -> family map for the COMMAND-ANCHORED reading. Every
# command that produces a rendered block must appear here; an unknown one
# is a loud failure rather than a silent "other".
BY_COMMAND = {
    "stabilize": "ready dumps",
    "process-ready": "ready dumps",
    "deliver-msgs": "message describe lines",
    "raft-state": "raft-state tables",
    "status": "status tables",
    "raft-log": "raft-log dumps",
    "campaign": "pure log lines",
    "add-nodes": "pure log lines",
    "forget-leader": "pure log lines",
    "propose": "pure log lines",
    "tick-election": "pure log lines",
    "tick-heartbeat": "pure log lines",
    "report-unreachable": "pure log lines",
    "transfer-leadership": "pure log lines",
    "process-append-thread": "other/mixed",
    "process-apply-thread": "other/mixed",
    "propose-conf-change": "other/mixed",
    "compact": "other/mixed",
    "send-snapshot": "other/mixed",
}


def command_of(cmdlines):
    return cmdlines[0].split()[0] if cmdlines and cmdlines[0].split() else ""


def family_content(cmdlines, expected):
    cmd = command_of(cmdlines)
    lines = [ln.strip() for ln in expected.split("\n") if ln.strip()]
    if any(READY.match(ln) for ln in lines):
        return "ready dumps"
    if cmd == "raft-state":
        return "raft-state tables"
    if cmd == "status":
        return "status tables"
    if cmd == "raft-log":
        return "raft-log dumps"
    if lines and all(LOGLINE.match(ln) for ln in lines):
        return "pure log lines"
    if lines and all(MSGLINE.match(ln) or RECV_HDR.match(ln) for ln in lines) \
            and any(MSGLINE.match(ln) for ln in lines):
        return "message describe lines"
    return "other/mixed"


def family_command(cmdlines, expected):
    cmd = command_of(cmdlines)
    if cmd not in BY_COMMAND:
        sys.exit("tracefamilies.py: command %r produces a rendered block but "
                 "has no family row — add it to BY_COMMAND (fail closed)" % cmd)
    return BY_COMMAND[cmd]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--testdata",
                    default=os.path.join(REPO, "deps", "raft", "testdata"))
    ap.add_argument("--per-file", action="store_true")
    args = ap.parse_args()

    if not os.path.isdir(args.testdata):
        sys.exit("tracefamilies.py: no testdata at %s (deps/raft not set up?)"
                 % args.testdata)

    files = sorted(f for f in os.listdir(args.testdata) if f.endswith(".txt"))
    counts = {"content": {f: 0 for f in FAMILIES},
              "command": {f: 0 for f in FAMILIES}}
    per_file = {}
    by_cmd = {}
    total = ok = 0
    for f in files:
        blocks = parse_blocks(os.path.join(args.testdata, f))
        total += len(blocks)
        per_file[f] = {k: 0 for k in FAMILIES}
        for cmdlines, expected in blocks:
            if expected.strip() == "ok":
                ok += 1
                continue
            counts["content"][family_content(cmdlines, expected)] += 1
            fam = family_command(cmdlines, expected)
            counts["command"][fam] += 1
            per_file[f][fam] += 1
            by_cmd[command_of(cmdlines)] = by_cmd.get(command_of(cmdlines), 0) + 1

    print("# tracefamilies.py — %s" % args.testdata)
    print("# %d trace files, %d blocks, %d expect literal ok, %d rendered"
          % (len(files), total, ok, total - ok))
    print()
    print("| blocks (command-anchored) | blocks (content-anchored) | family |")
    print("|---|---|---|")
    for fam in sorted(FAMILIES, key=lambda k: -counts["command"][k]):
        print("| %d | %d | %s |"
              % (counts["command"][fam], counts["content"][fam], fam))
    print()
    for rule in ("command", "content"):
        got = sum(counts[rule].values())
        print("TOTAL rendered-tier blocks (%s-anchored): %d" % (rule, got))
        if got != total - ok:
            sys.exit("tracefamilies.py: %s-anchored family counts do not sum "
                     "to the rendered-tier block count — the rule is not "
                     "total" % rule)
    print()
    print("rendered blocks by COMMAND (the schedulable unit for W4.3):")
    for k in sorted(by_cmd, key=lambda k: -by_cmd[k]):
        print("  %-28s %3d   -> %s" % (k, by_cmd[k], BY_COMMAND[k]))
    if args.per_file:
        print()
        print("per file (command-anchored):")
        for f in files:
            row = ", ".join("%s=%d" % (k, v) for k, v in per_file[f].items() if v)
            print("  %-52s %s" % (f, row or "-"))


if __name__ == "__main__":
    main()
