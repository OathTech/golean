#!/usr/bin/env python3
"""Spike for docs/2026-09-15_evaluation-order-model.md §6 (disposable; static).

Counts, over lowered wires, the SWEEPS (a run of hoisted statements plus the
residual statement that closes it), how many carry an ORDERED EVENT (a
hoisted call / method call / receive / spec built-in), today's `unseq-probe`
count, and — in event-bearing sweeps only — the residual operand nodes the
model would pair with a probe+use: PANICKY kinds (today's probeKind census,
approximated on the wire) and PLAIN mutable READS (non-temp ident, field-get,
globaladdr). Upper bounds: the wire cannot tell a captured/address-taken
local from a private one, nor a constant divisor from a variable one.
Also counts today's EARLY "once"-temps (BUG-104's shape) and E2's shape
(a call RHS with an addressed target).  Usage: count.py WIRE...
"""
import json, sys, collections

EVENT_STMTS = {"append", "copy", "make-slice", "make-map", "make-chan", "new", "chan-recv", "recv"}
EVENT_EXPRS = {"call", "call-value", "recv", "builtin-len", "builtin-cap", "min", "max", "recover"}
ALLOC_STMTS = {"slice-lit", "map-lit", "array-lit", "struct-lit", "func-value"}
PANICKY = {"index-get", "index-addr", "deref", "slice", "type-assert", "map-get", "field-addr"}
PLAIN = {"ident", "field-get", "globaladdr"}
BODY_KEYS = {"body", "then", "else", "cases", "clauses", "default", "init", "post"}

def is_temp_id(x):
    return isinstance(x, str) and x.startswith("$c")

def hoist_kind(s):
    """'probe' | 'event' | 'alloc' | 'temp' | None (not a hoist)."""
    st = s.get("stmt")
    if st == "unseq-probe":
        return "probe"
    tgt = s.get("target")
    if st == "assign" and s.get("define") and all(is_temp_id(t.get("id")) for t in s.get("lhs", [])) and s.get("lhs"):
        rhs = s.get("rhs", [])
        head = rhs[0].get("expr") if rhs and isinstance(rhs[0], dict) else None
        return "event" if head in EVENT_EXPRS else "temp"
    if isinstance(tgt, dict) and is_temp_id(tgt.get("id")):
        if st in EVENT_STMTS: return "event"
        if st in ALLOC_STMTS: return "alloc"
        return "temp"
    return None

def residual_nodes(o, acc):
    """Count expression heads in a residual statement, not descending into nested bodies."""
    if isinstance(o, dict):
        h = o.get("expr")
        if isinstance(h, str):
            if h in PANICKY: acc["panicky"] += 1
            elif h == "binary" and o.get("op") in ("/", "%"): acc["panicky"] += 1
            elif h == "ident" and not is_temp_id(o.get("name")): acc["plain"] += 1
            elif h in PLAIN and h != "ident": acc["plain"] += 1
        for k, v in o.items():
            if k in BODY_KEYS and isinstance(v, (list, dict)):
                continue
            residual_nodes(v, acc)
    elif isinstance(o, list):
        for v in o: residual_nodes(v, acc)

def sweeps(body, C):
    run = []
    for s in body:
        if not isinstance(s, dict):
            continue
        k = hoist_kind(s)
        if k:
            run.append(k); continue
        C["sweeps"] += 1
        nev = sum(1 for x in run if x == "event")
        C["probes"] += sum(1 for x in run if x == "probe")
        C["alloc_hoists"] += sum(1 for x in run if x == "alloc")
        if nev:
            C["event_sweeps"] += 1
            C["events_in_event_sweeps"] += nev
            acc = collections.Counter(); residual_nodes(s, acc)
            C["panicky_in_event_sweeps"] += acc["panicky"]
            C["plain_in_event_sweeps"] += acc["plain"]
            if s.get("stmt") in ("compound-assign", "incdec") and isinstance(s.get("target"), dict) \
               and s["target"].get("target") == "addr" and is_temp_id(s["target"].get("expr", {}).get("name")):
                C["bug104_early_once_temps"] += 1
            if s.get("stmt") == "map-compound-assign":
                C["bug104_early_once_temps"] += 1
        if s.get("stmt") == "assign" and not s.get("define"):
            rhs = s.get("rhs", [])
            if rhs and isinstance(rhs[0], dict) and rhs[0].get("expr") in ("call", "call-value") \
               and any(t.get("target") == "addr" and t.get("expr", {}).get("expr") != "globaladdr" for t in s.get("lhs", [])):
                C["e2_call_rhs_addr_target"] += 1
        run = []
        # nested bodies are their own sweeps
        for k, v in s.items():
            if k in BODY_KEYS:
                for b in blocks(v): sweeps(b, C)

def blocks(v):
    if isinstance(v, dict):
        if v.get("stmt") == "block" and isinstance(v.get("body"), list):
            yield v["body"]
        else:
            for vv in v.values():
                if isinstance(vv, (dict, list)): yield from blocks(vv)
    elif isinstance(v, list):
        if v and all(isinstance(x, dict) and "stmt" in x for x in v):
            yield v
        else:
            for x in v: yield from blocks(x)

def main(paths):
    T = collections.Counter(); files = 0
    for p in paths:
        try:
            w = json.load(open(p))
        except Exception as e:
            print(f"skip {p}: {e}", file=sys.stderr); continue
        files += 1
        C = collections.Counter()
        for f in w.get("funcs", []) + w.get("methods", []):
            b = f.get("body")
            for body in blocks(b): sweeps(body, C)
        T.update(C); C["files"] = 1
    T["files"] = files
    for k in sorted(T): print(f"{k}\t{T[k]}")

if __name__ == "__main__":
    main(sys.argv[1:])
