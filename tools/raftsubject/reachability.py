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
    receiver/member-derived method targets and ordinary function keys, which
    are what the machine
    will actually execute.
  * INTERFACE dispatch is over-approximated: a call to an interface method
    anchor adds an edge to EVERY concrete method with the SAME package/name
    member identity in the wire. The receiver and signature remain an
    over-approximation: the wire records the anchor, not the dynamic target. The
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


def member_id(method):
    id = method["id"]
    return (id["package"], id["name"])


def method_key(method):
    receiver = method["recvType"]
    package, name = member_id(method)
    return "$method$" + str(len(receiver.encode("utf-8"))) + ":" + receiver + str(len(package.encode("utf-8"))) + ":" + package + name


def declaration_labels(wire):
    labels = {f["name"]: f["name"] for f in wire.get("funcs", [])}
    labels.update({method_key(m): m["recvType"] + "." + m["id"]["name"]
                   for m in wire.get("methods", [])})
    return labels


def resolve_entries(wire, entries):
    """Resolve display conveniences from records, refusing ambiguous labels."""
    labels = declaration_labels(wire)
    resolved = []
    for entry in entries:
        if entry in labels:
            resolved.append(entry)
            continue
        matches = [key for key, label in labels.items() if label == entry]
        if len(matches) > 1:
            raise ValueError("ambiguous method entry " + entry + "; use a full target id")
        if not matches:
            raise ValueError("entry " + entry + " is not on the wire")
        resolved.append(matches[0])
    return resolved


def load(path):
    wire = json.load(open(path))
    bodies = {}          # qualified name -> set of callee names
    quarantined = {}     # qualified name -> refusal text
    iface_methods = {}  # target -> package/name member declared on an interface
    by_member = {}  # package/name member -> concrete target ids

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
        name = method_key(m)
        if m.get("interface"):
            iface_methods[name] = member_id(m)
            bodies.setdefault(name, set())
            continue
        by_member.setdefault(member_id(m), []).append(name)
        if "unsupported" in m:
            quarantined[name] = m["unsupported"]
            bodies.setdefault(name, set())
            continue
        edges = set()
        collect_edges(m.get("body"), edges)
        bodies[name] = edges

    # Interface dispatch expands by full member identity; receiver and
    # signature are conservatively over-approximated (see the docstring).
    for name in list(bodies):
        expanded = set()
        for callee in bodies[name]:
            if callee in iface_methods:
                expanded.update(by_member.get(iface_methods[callee], []))
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
            raise ValueError("entry " + e + " is not on the wire")
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
    entries = resolve_entries(wire, [e.strip() for e in args.entries.split(",") if e.strip()])
    pred = reach(bodies, entries)

    if args.query:
        names = [ln.strip() for ln in open(args.query) if ln.strip()]
    else:
        skip = tuple(p for p in args.skip_prefix.split(",") if p)
        labels = declaration_labels(wire)
        names = [n for n in sorted(quarantined) if not labels[n].startswith(skip)]

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
