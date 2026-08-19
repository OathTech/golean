#!/usr/bin/env python3
"""reachability.py — is a QUARANTINED declaration reachable from the harness?

The W2.1 frontier instrument (`frontier.py`) answers "what refuses?".  Since
H-3 (per-declaration method quarantine, bug-fix arc) a refusal no longer blocks
the export: the declaration lands on the wire as a signature-carrying stub that
refuses WHEN CALLED.  So the question that decides whether a refusal is a GAP
moves from "does it export?" to "does the harness reach it?" — a quarantined
declaration on a dead path costs nothing, one on a live path is a run-time stop.

This walks the call graph OF THE EXPORTED WIRE — the frontend's own resolved
callees, not a re-parse of the Go — from a named entry set, and reports each
queried declaration as LIVE (reachable) or dead (not reachable from any entry).

    tools/raftsubject/reachability.py WIRE.json --entries a,b,c [--query FILE]

DIRECTION OF THE APPROXIMATION, stated because a liveness verdict is evidence:

  * Statically resolved calls and function VALUES are exact — the wire records
    `{"expr":"call","func":"raft.raft.appendEntry"}` and
    `{"expr":"func-value","func":"raft.stepLeader"}`, which is what the machine
    will actually execute.
  * INTERFACE dispatch is over-approximated: a call to an interface method
    `I.m` adds an edge to EVERY concrete method named `m` in the wire.  The
    wire names the interface's method, not the dynamic target, and the
    alternative (implementing method-set matching here) would re-derive what
    the machine decides at run time.
  * A QUARANTINED declaration has no body on the wire, so it is a SINK: its
    own callees are invisible.  That is correct for this question — a call
    into it stops the machine, so nothing behind it runs — but it means a
    liveness census must be re-run after any declaration is un-quarantined.

Hence: `dead` is the sound direction (nothing reachable names it, over an
over-approximated graph), and `LIVE` is a candidate that the log confirms by
naming the call site.  Both verdicts are printed with the shortest path found,
so the claim is checkable rather than asserted.
"""

import argparse
import json
import sys
from collections import deque


def collect_edges(node, out):
    """Every callee named anywhere in a body: call heads and function values."""
    if isinstance(node, dict):
        f = node.get("func")
        if isinstance(f, str):
            out.add(f)
        for v in node.values():
            collect_edges(v, out)
    elif isinstance(node, list):
        for v in node:
            collect_edges(v, out)


def load(path):
    wire = json.load(open(path))
    bodies = {}          # qualified name -> set of callee names
    quarantined = {}     # qualified name -> refusal text
    iface_methods = set()  # method names declared on an interface type
    by_method_name = {}  # bare method name -> [qualified names] (concrete only)

    for f in wire.get("funcs", []):
        name = f.get("name")
        if "unsupported" in f:
            quarantined[name] = f["unsupported"]
            bodies.setdefault(name, set())
            continue
        edges = set()
        collect_edges(f.get("body"), edges)
        bodies[name] = edges

    for m in wire.get("methods", []):
        name = "%s.%s" % (m.get("recvType"), m.get("name"))
        if m.get("interface"):
            iface_methods.add(name)
            bodies.setdefault(name, set())
            continue
        by_method_name.setdefault(m.get("name"), []).append(name)
        if "unsupported" in m:
            quarantined[name] = m["unsupported"]
            bodies.setdefault(name, set())
            continue
        edges = set()
        collect_edges(m.get("body"), edges)
        bodies[name] = edges

    # Interface dispatch: an edge to I.m stands for an edge to every concrete
    # method named m (see the docstring's approximation note).
    for name in list(bodies):
        expanded = set()
        for callee in bodies[name]:
            if callee in iface_methods:
                bare = callee.rsplit(".", 1)[-1]
                expanded.update(by_method_name.get(bare, []))
        bodies[name] |= expanded

    return wire, bodies, quarantined


def reach(bodies, entries):
    """BFS from the entry set; returns name -> predecessor (for paths)."""
    pred = {}
    q = deque()
    for e in entries:
        if e in bodies:
            pred[e] = None
            q.append(e)
        else:
            sys.stderr.write("reachability.py: NOTE: entry %s is not on the wire\n" % e)
    while q:
        n = q.popleft()
        for c in sorted(bodies.get(n, ())):
            if c not in pred and c in bodies:
                pred[c] = n
                q.append(c)
    return pred


def path_of(pred, name):
    out = []
    while name is not None:
        out.append(name)
        name = pred.get(name)
    return " <- ".join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wire")
    ap.add_argument("--entries", required=True,
                    help="comma-separated qualified entry declarations")
    ap.add_argument("--query", help="file of qualified names, one per line "
                                    "(default: every quarantined declaration)")
    ap.add_argument("--skip-prefix", default="",
                    help="comma-separated recvType prefixes to omit from the "
                         "default query set (e.g. imported stdlib stubs)")
    args = ap.parse_args()

    wire, bodies, quarantined = load(args.wire)
    entries = [e.strip() for e in args.entries.split(",") if e.strip()]
    pred = reach(bodies, entries)

    if args.query:
        names = [ln.strip() for ln in open(args.query) if ln.strip()]
    else:
        skip = tuple(p for p in args.skip_prefix.split(",") if p)
        names = [n for n in sorted(quarantined) if not n.startswith(skip)]

    live = 0
    print("# entries: %s" % ", ".join(entries))
    print("# wire: %s (%d funcs, %d methods, %d quarantined)"
          % (args.wire, len(wire.get("funcs", [])), len(wire.get("methods", [])),
             len(quarantined)))
    for n in names:
        if n in pred:
            live += 1
            print("LIVE %-42s %s" % (n, path_of(pred, n)))
        else:
            print("dead %-42s (unreachable from every entry)" % n)
    print("# %d LIVE / %d queried; %d of %d wire declarations reachable"
          % (live, len(names), len(pred), len(bodies)))


if __name__ == "__main__":
    main()
