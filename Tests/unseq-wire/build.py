#!/usr/bin/env python3
"""Tests/unseq-wire/build.py — assemble the HAND-BUILT `unseq` WIRES of Stage C
(C1; lane core/unseq-stage-c-0919; design docs/2026-09-19_unseq-stage-c-design.md
§4 the schema, §5 the decoder spec; the reference sets are the v2.1 spike's,
docs/evidence/2026-09-16_eval-order-v2-spike/outcomes.txt).

Each witness is a small Go program under src/<witness>/ whose SUBJECT function's
sweep the real frontend lowers by the legacy path. This script emits the program
with the frontend (the envelope: schema, buildContext, types, the LIFTED closures
with their capture parameters, `main`), then REPLACES the subject's body with the
setup statements the frontend emitted (1:1 with the source statements — every
setup is hoist-free by construction) followed by a HAND-WRITTEN `unseq` node and
the kept tail. The result is a wire whose `unseq` node was written by hand, in the
exact byte shape the decoder (GoLean/NativeToIR.lean, the `unseq` arm) reads —
check (b) of v2.1 §2 «machine equals reference over the wire» is Tests/UnseqWire.lean
running these files through the strict byte parser, the decoder and CLI.explore.

The MUTATION fixtures (`mut-*.json`) are one-edit copies of a witness wire, each
of which the decoder must refuse BY NAME (design §5 D1–D14); a few EDGE mutations
decode but change the enumerated set (v2.1 §8: a data edge, a lexical edge, a guard
edge, a phase edge) and are checked by the exact-set test instead.

    python3 Tests/unseq-wire/build.py [--frontend BIN] [--check]

`--check` regenerates into a scratch directory and compares byte-for-byte with the
tracked files (the re-derivation guard; drift fails). The frontend defaults to
`go run ./tools/nativefrontend` (GOCACHE under artifacts/, GO111MODULE=off).
"""
import copy
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

# ---------------------------------------------------------------- wire vocabulary
INT = {"kind": "int", "int": "int"}
BOOL = {"kind": "bool"}
SLICE_INT = {"kind": "slice", "elem": INT}
STR = {"kind": "string"}


def ident(name, ty=None):
    n = {"expr": "ident", "name": name}
    if ty is not None:
        n["type"] = ty
    return n


def intc(v):
    return {"expr": "int", "value": str(v), "type": INT}


def strc(s):
    return {"expr": "string", "bytes": list(s.encode("utf-8")), "type": STR}


def boolc(v):
    return {"expr": "bool", "value": bool(v), "type": BOOL}


SLICE_STR = {"kind": "slice", "elem": STR}
PTR_INT = {"kind": "pointer", "elem": INT}
MAP_INT_INT = {"kind": "map", "key": INT, "value": INT}


def deref_target(ptr):
    """A dereference target plan `*p` on the FROZEN pointer value (Stage E E2)."""
    return {"target": "addr", "expr": ptr}


CHAN_INT = {"kind": "chan", "dir": "both", "elem": INT}


def rcv(name, binds, ch, elem, after=None, region=None):
    """A RECEIVE occurrence (Stage E E3): the channel an atom, one binder cell."""
    return occ(name, "recv", after, region, binds=list(binds), ch=ch, elem=elem)


def map_target(base, index):
    """A map-element target plan on the FROZEN map value and key value (Stage E E2)."""
    return {"target": "map", "base": base, "index": index, "keyType": INT, "valueType": INT}


def fv(func):
    """A top-level function as an already-evaluated callee value."""
    return {"expr": "func-value", "func": func, "captured": []}


def binop(op, x, y, ty, operand_type=None):
    n = {"expr": "binary", "op": op, "x": x, "y": y, "type": ty}
    if operand_type is not None:
        n["operandType"] = operand_type
    return n


def idxget(base, index, ty):
    return {"expr": "index-get", "base": base, "index": index, "type": ty}


def gaddr(gid):
    """A package-level variable's statically resolved cell (the frontend's `globaladdr`)."""
    return {"expr": "globaladdr", "gid": gid}


def gread(gid, ty):
    """The READ of a package-level variable: `deref(globaladdr)` — the frontend's own
    spelling (emitIdent), admitted as a head by D8 since Stage E E1 (2026-09-21)."""
    return {"expr": "deref", "ptr": gaddr(gid), "type": ty}


def gstore(gid, rhs):
    """`g = rhs` through the operand-free identity `addr(globaladdr)` (a `then` store)."""
    return {"stmt": "assign", "define": False,
            "lhs": [{"target": "addr", "expr": gaddr(gid)}], "rhs": [rhs]}


def _gid(wire, fn):
    """The gid of the ONE package-level variable the subject's emitted body reads or
    writes (from the frontend's own emission — an envelope fact, like a lifted closure's
    name); exactly one distinct gid is required."""
    found = set()

    def walk(o):
        if isinstance(o, dict):
            if o.get("expr") == "globaladdr":
                found.add(o["gid"])
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)
    walk(_func(wire, fn)["body"])
    if len(found) != 1:
        raise SystemExit(f"{fn}: expected exactly one package-level variable, found gids {sorted(found)}")
    return found.pop()


def occ(name, kind, after=None, region=None, **fields):
    o = {"name": name, "kind": kind}
    o.update(fields)
    if after:
        o["after"] = list(after)
    if region is not None:
        o["region"] = region
    return o


def ev(name, bind, head, after=None, region=None):
    return occ(name, "eval", after, region, bind=bind, head=head)


def inv(name, binds, callee, args, rts, after=None, region=None):
    return occ(name, "invoke", after, region, binds=list(binds), callee=callee,
               args=list(args), resultTypes=list(rts))


def tgt(name, bind, lhs, after=None, region=None):
    return occ(name, "target", after, region, bind=bind, lhs=lhs)


def ld(name, bind, target, after=None, region=None):
    return occ(name, "load", after, region, bind=bind, target=target)


def gd(name, test, when, out, after=None, region=None):
    return occ(name, "guard", after, region, test=test, when=when, out=out)


def elem_target(base, index):
    return {"target": "addr", "expr": {"expr": "index-addr", "base": base, "index": index}}


def cell(cid, ty):
    return {"id": cid, "type": ty}


def unseq(cells, occs, stores=(), then=None):
    return {"stmt": "unseq", "cells": list(cells), "occs": list(occs),
            "stores": [{"target": t, "value": v} for (t, v) in stores],
            "then": then if then is not None else {"stmt": "block", "body": []}}


def define(x, ty, rhs):
    return {"stmt": "assign", "define": True,
            "lhs": [{"target": "declare", "id": x, "type": ty}], "rhs": [rhs]}


def ret(*results):
    return {"stmt": "return", "results": list(results)}


def prn(*args):
    return {"stmt": "print", "newline": True, "args": list(args)}


# ---------------------------------------------------------------- the witness graphs
# Each entry: witness -> list of (function name, keep_head, keep_tail, node, path)
# where `path` locates the statement list inside the function body (None = the body).

def w1_graph():
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT)],
        [inv("call0", ["$u0"], ident("mut"), [], [INT]),
         ev("read1", "$u1", ident("a", INT)),
         ev("op2", "$u2", binop("+", ident("$u0", INT), ident("$u1", INT), INT))],
        then=define("v", INT, ident("$u2", INT)))


def w2_graph():
    return unseq(
        [cell("$u0", SLICE_INT), cell("$u1", SLICE_INT), cell("$u2", INT), cell("$u3", INT),
         cell("$u4", INT), cell("$u5", INT)],
        [ev("read0", "$u0", ident("a", SLICE_INT)),
         ev("read1", "$u1", ident("b", SLICE_INT)),
         ev("access2", "$u2", idxget(ident("$u1", SLICE_INT), intc(0), INT)),
         ev("access3", "$u3", idxget(ident("$u0", SLICE_INT), ident("$u2", INT), INT)),
         inv("call4", ["$u4"], ident("mut"), [], [INT]),
         ev("op5", "$u5", binop("+", ident("$u3", INT), ident("$u4", INT), INT))],
        then=define("v", INT, ident("$u5", INT)))


def w3_graph():
    # a private: its header is read at the plan step (frozen from then on); i captured.
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT)],
        [ev("read0", "$u0", ident("i", INT)),
         tgt("target1", "$t0", elem_target(ident("a", SLICE_INT), ident("$u0", INT))),
         ld("load2", "$u1", "$t0"),
         inv("call3", ["$u2"], ident("mut"), [], [INT]),
         ev("op4", "$u3", binop("+", ident("$u1", INT), ident("$u2", INT), INT))],
        stores=[("$t0", "$u3")])


def w4_graph():
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT)],
        [ev("access0", "$u0", idxget(ident("a", SLICE_INT), intc(1), INT)),
         ev("access1", "$u1", idxget(ident("b", SLICE_INT), intc(2), INT)),
         ev("op2", "$u2", binop("+", ident("$u0", INT), ident("$u1", INT), INT))])


def w5_graph():
    return unseq(
        [cell("$u0", SLICE_INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT)],
        [ev("read0", "$u0", ident("a", SLICE_INT)),
         ev("access1", "$u1", idxget(ident("$u0", SLICE_INT), intc(0), INT)),
         inv("call2", ["$u2"], ident("mut"), [], [INT]),
         ev("op3", "$u3", binop("+", ident("$u1", INT), ident("$u2", INT), INT))],
        then=prn(ident("$u3", INT)))


def w6_graph():
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT), cell("$u4", INT)],
        [ev("read0", "$u0", ident("x", INT)),
         inv("call1", ["$u1"], ident("inc"), [], [INT]),
         inv("call2", ["$u2"], ident("inc"), [], [INT], after=["call1"]),
         ev("op3", "$u3", binop("+", ident("$u0", INT), ident("$u1", INT), INT)),
         ev("op4", "$u4", binop("+", ident("$u3", INT), ident("$u2", INT), INT))],
        then=define("v", INT, ident("$u4", INT)))


def r1_graph(reduced=False):
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT), cell("$u4", INT)],
        [ev("read0", "$u0", ident("x", INT)),
         ev("read1", "$u1", ident("y", INT), after=(["read0"] if reduced else None)),
         inv("call2", ["$u2"], ident("mut"), [], [INT]),
         ev("op3", "$u3", binop("+", ident("$u0", INT), ident("$u1", INT), INT)),
         ev("op4", "$u4", binop("+", ident("$u3", INT), ident("$u2", INT), INT))],
        then=define("v", INT, ident("$u4", INT)))


def r2a_graph(valid=True):
    # sinkB(z || h(), k()): z private -> a copy into the bool test cell; h in the region;
    # k after the completion (E1); sinkB after k.
    k_call = (inv("call4", ["$u3"], fv("k"), [], [INT], after=["join3"]) if valid
              else inv("call4", ["$u3"], fv("k"), [], [INT]))
    sink_args = [ident("$u2", BOOL), ident("$u3", INT)] if valid else [ident("$u1", BOOL), ident("$u3", INT)]
    return unseq(
        [cell("$u0", BOOL), cell("$u1", BOOL), cell("$u2", BOOL), cell("$u3", INT)],
        [ev("copy0", "$u0", ident("z", BOOL)),
         gd("guard1", "$u0", False, "$u2"),
         inv("call2", ["$u1"], fv("h"), [], [BOOL], region="guard1"),
         ev("join3", "$u2", ident("$u1", BOOL), region="guard1"),
         k_call,
         inv("call5", [], fv("sinkB"), sink_args, [], after=["call4"])])


def r2b_graph(anchor="join3"):
    return unseq(
        [cell("$u0", BOOL), cell("$u1", BOOL), cell("$u2", BOOL), cell("$u3", INT)],
        [ev("copy0", "$u0", ident("left", BOOL)),
         gd("guard1", "$u0", False, "$u2"),
         ev("read2", "$u1", ident("b", BOOL), region="guard1"),
         ev("join3", "$u2", ident("$u1", BOOL), region="guard1"),
         inv("call4", ["$u3"], ident("change"), [], [INT], after=[anchor]),
         inv("call5", [], fv("sinkL"), [ident("$u2", BOOL), ident("$u3", INT)], [], after=["call4"])])


def r2c_graph():
    return unseq(
        [cell("$u0", INT), cell("$u1", BOOL), cell("$u2", BOOL), cell("$u3", BOOL),
         cell("$u4", BOOL), cell("$u5", BOOL), cell("$u6", INT)],
        [inv("call0", ["$u0"], ident("g"), [], [INT]),
         ev("read1", "$u1", ident("a", BOOL)),
         gd("guard2", "$u1", False, "$u5", after=["call0"]),
         ev("copy3", "$u2", ident("b", BOOL), region="guard2"),
         gd("guard4", "$u2", True, "$u4", region="guard2"),
         inv("call5", ["$u3"], ident("h2"), [], [BOOL], region="guard4"),
         ev("join6", "$u4", ident("$u3", BOOL), region="guard4"),
         ev("join7", "$u5", ident("$u4", BOOL), region="guard2"),
         inv("call8", ["$u6"], ident("k2"), [], [INT], after=["join7"]),
         inv("call9", [], fv("sink3"), [ident("$u0", INT), ident("$u5", BOOL), ident("$u6", INT)], [],
             after=["call8"])])


def r4_graph():
    return unseq(
        [cell("$u0", SLICE_INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT)],
        [ev("read0", "$u0", ident("a", SLICE_INT)),
         tgt("target1", "$t0", elem_target(ident("$u0", SLICE_INT), intc(0))),
         ld("load2", "$u1", "$t0"),
         inv("call3", ["$u2"], ident("mut"), [], [INT]),
         ev("op4", "$u3", binop("+", ident("$u1", INT), ident("$u2", INT), INT))],
        stores=[("$t0", "$u3")])


def r6_graph(split=True):
    if split:
        return unseq(
            [cell("$u0", SLICE_INT), cell("$u1", INT), cell("$u2", INT)],
            [ev("read0", "$u0", ident("a", SLICE_INT)),
             inv("call1", ["$u1"], ident("f"), [], [INT]),
             ev("access2", "$u2", idxget(ident("$u0", SLICE_INT), ident("$u1", INT), INT))],
            then=define("v", INT, ident("$u2", INT)))
    return unseq(
        [cell("$u1", INT), cell("$u2", INT)],
        [inv("call1", ["$u1"], ident("f"), [], [INT]),
         ev("access2", "$u2", idxget(ident("a", SLICE_INT), ident("$u1", INT), INT))],
        then=define("v", INT, ident("$u2", INT)))


# ---------------------------------------------------------------- Stage E, family E1: package-level variables
# (lane core/unseq-stage-e-0921, 2026-09-21): a PACKAGE-LEVEL variable is a mutable location —
# its read is a READ occurrence with the head `deref(globaladdr)`; as a compound target its
# identity has no operands, so the store rides `then` (`addr(globaladdr)`) and the load is the
# same READ occurrence. References: enumerate.py E1a {1, 2}, E1c {2, 11}. The gid is an
# envelope fact read off the frontend's own emission of the subject (`_gid`).

def e1_graph(native):
    gid = _gid(native, "e1")
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT)],
        [inv("call0", ["$u0"], ident("mut"), [], [INT]),
         ev("read1", "$u1", gread(gid, INT)),
         ev("op2", "$u2", binop("+", ident("$u0", INT), ident("$u1", INT), INT))],
        then=define("v", INT, ident("$u2", INT)))


def e1c_graph(native):
    gid = _gid(native, "e1c")
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT)],
        [inv("call0", ["$u0"], fv("f"), [], [INT]),
         ev("read1", "$u1", gread(gid, INT)),
         ev("op2", "$u2", binop("+", ident("$u1", INT), ident("$u0", INT), INT))],
        then=gstore(gid, ident("$u2", INT)))


# ---------------------------------------------------------------- Stage E, family E2: pointers, fields, maps
# (2026-09-21): the FROZEN target identities of v2.1 §3.4 on a pointer and a map — the Stage B
# acceptance matrix's «map/pointer deferred to E». References: enumerate.py E2e {x y 11 100, x y 10 101}
# and E2f {old 11 m 100, old 10 m 101}, returned here as the checksums 11100 / 10101.

def e2ptr_graph():
    # p is captured by mut: its VALUE is a read occurrence; the plan `addr($u0)` freezes it.
    return unseq(
        [cell("$u0", PTR_INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT)],
        [inv("call0", ["$u2"], ident("mut"), [], [INT]),
         ev("read1", "$u0", ident("p", PTR_INT)),
         tgt("target2", "$t0", deref_target(ident("$u0", PTR_INT))),
         ld("load3", "$u1", "$t0"),
         ev("op4", "$u3", binop("+", ident("$u1", INT), ident("$u2", INT), INT))],
        stores=[("$t0", "$u3")])


def e2map_graph():
    # m is captured by mut: its VALUE (a reference) is a read occurrence; the plan freezes it and the key.
    return unseq(
        [cell("$u0", MAP_INT_INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT)],
        [inv("call0", ["$u2"], ident("mut"), [], [INT]),
         ev("read1", "$u0", ident("m", MAP_INT_INT)),
         tgt("target2", "$t0", map_target(ident("$u0", MAP_INT_INT), intc(1))),
         ld("load3", "$u1", "$t0"),
         ev("op4", "$u3", binop("+", ident("$u1", INT), ident("$u2", INT), INT))],
        stores=[("$t0", "$u3")])


# ---------------------------------------------------------------- Stage E, family E3: receives and method calls
# (2026-09-21): X3 as native Go — `x[f()] += <-ch`: f, then the receive AFTER f (E1), the plan on f's
# result (x private: its header read at the plan step), the load and the op; the deferred witness prints
# len(ch). Reference enumerate.py X3/E3c; the observation {panic [9] · `len 1`, panic [9] · `len 0`}.

def e3recv_graph():
    return unseq(
        [cell("$u0", INT), cell("$u1", INT), cell("$u2", INT), cell("$u3", INT)],
        [inv("call0", ["$u0"], fv("f"), [], [INT]),
         rcv("recv1", ["$u1"], ident("ch", CHAN_INT), INT, after=["call0"]),
         tgt("target2", "$t0", elem_target(ident("x", SLICE_INT), ident("$u0", INT))),
         ld("load3", "$u2", "$t0"),
         ev("op4", "$u3", binop("+", ident("$u2", INT), ident("$u1", INT), INT))],
        stores=[("$t0", "$u3")])


# ---------------------------------------------------------------- constant heads (audit fix round F2)
# A CONSTANT copied into a cell — the emitter's `copy` occurrence where the consumer needs a
# CELL (design §6): a guard's test (`true && f()`), a phase-2 store's value (`a[f()] = 5`,
# `a[f()] = "s"`). The C1 decoder refused these heads by name — the frontend's own emission
# (docs/2026-09-20_unseq-stage-c-audit.md F2); D8 admits them since the fix round, typed by
# the wire's annotation (D9 checks the constant's type against its cell).

def cguard_graph():
    # ok := true && f(): copy0 puts the constant into the bool test cell; f in the region.
    return unseq(
        [cell("$u0", BOOL), cell("$u1", BOOL), cell("$u2", BOOL)],
        [ev("copy0", "$u0", boolc(True)),
         gd("guard1", "$u0", True, "$u1"),
         inv("call2", ["$u2"], ident("f"), [], [BOOL], region="guard1"),
         ev("join3", "$u1", ident("$u2", BOOL), region="guard1")],
        then=define("ok", BOOL, ident("$u1", BOOL)))


def celem_graph():
    # a[f()] = 5: a captured -> its header is a READ occurrence; the constant 5 copied into
    # the store's value cell; the plan on the frozen header and f's result.
    return unseq(
        [cell("$u0", SLICE_INT), cell("$u1", INT), cell("$u2", INT)],
        [inv("call0", ["$u1"], ident("f"), [], [INT]),
         ev("read1", "$u0", ident("a", SLICE_INT)),
         tgt("target2", "$t0", elem_target(ident("$u0", SLICE_INT), ident("$u1", INT))),
         ev("copy3", "$u2", intc(5))],
        stores=[("$t0", "$u2")])


def cstr_graph():
    # a[f()] = "s": a private -> the header is read at the plan step; the string constant
    # copied into the store's value cell.
    return unseq(
        [cell("$u0", INT), cell("$u1", STR)],
        [inv("call0", ["$u0"], ident("f"), [], [INT]),
         tgt("target1", "$t0", elem_target(ident("a", SLICE_STR), ident("$u0", INT))),
         ev("copy2", "$u1", strc("s"))],
        stores=[("$t0", "$u1")])


# witness -> (src dir, [(function, until_decl, keep_tail, node, path)]): the emitted
# setup statements are kept through the one that DECLARES `until_decl` (the frontend
# may emit a source statement as several — `a := make([]int, 2)` is a make-slice into
# a temp then the assign — so the boundary is the declaration, never a count);
# `until_decl` None keeps nothing; `path` locates a nested statement list.
WITNESSES = {
    "w1": ("w1", [("w1", "mut", 1, w1_graph(), None)]),
    "w2": ("w2", [("w2", "mut", 1, w2_graph(), None)]),
    "w3": ("w3", [("w3", "mut", 1, w3_graph(), None)]),
    "w4": ("w4", [("w4", "b", 0, w4_graph(), None)]),
    "w5": ("w5", [("w5", None, 1, w5_graph(), [5, "body", "body"])]),
    "w6": ("w6", [("w6", "inc", 1, w6_graph(), None)]),
    "r1": ("r1", [("r1", "mut", 1, r1_graph(), None)]),
    "r1-reduced": ("r1", [("r1", "mut", 1, r1_graph(reduced=True), None)]),
    "r2a": ("r2a", [("r2aTrue", "z", 0, r2a_graph(), None), ("r2aFalse", "z", 0, r2a_graph(), None)]),
    "r2a-invalid-join": ("r2a", [("r2aTrue", "z", 0, r2a_graph(valid=False), None),
                                 ("r2aFalse", "z", 0, r2a_graph(valid=False), None)]),
    "r2b": ("r2b", [("r2b", "change", 0, r2b_graph(), None)]),
    "r2b-entry": ("r2b", [("r2b", "change", 0, r2b_graph(anchor="guard1"), None)]),
    "r2c": ("r2c", [("r2cTrue", "k2", 0, r2c_graph(), None), ("r2cFalse", "k2", 0, r2c_graph(), None)]),
    "r4": ("r4", [("r4", "mut", 2, r4_graph(), None)]),
    "r6": ("r6", [("r6", "f", 1, r6_graph(), None)]),
    "r6-fused": ("r6", [("r6", "f", 1, r6_graph(split=False), None)]),
    # constant heads (audit fix round F2): the copy of a constant into a cell
    "cguard": ("cguard", [("cguard", "f", 2, cguard_graph(), None)]),
    "celem": ("celem", [("celem", "f", 1, celem_graph(), None)]),
    "cstr": ("cstr", [("cstr", "f", 2, cstr_graph(), None)]),
    # Stage E E1 (2026-09-21): package-level variables (the node is a callable over the
    # frontend's own emission — the global's gid is read off it)
    "e1": ("e1", [("e1", "mut", 1, e1_graph, None)]),
    "e1c": ("e1c", [("e1c", None, 1, e1c_graph, None)]),
    # Stage E E2 (2026-09-21): the frozen pointer / map identities; e2fld is NATIVE-ONLY (no
    # hand-built node — the struct type's wire name is an envelope fact)
    "e2ptr": ("e2ptr", [("e2ptr", "mut", 1, e2ptr_graph(), None)]),
    "e2map": ("e2map", [("e2map", "mut", 1, e2map_graph(), None)]),
    "e2fld": ("e2fld", []),
    # Stage E E3 (2026-09-21): the receive as a `recv` body (hand-built + native); the value-receiver
    # method call is NATIVE-ONLY (the method's `$method$…` key is an envelope fact)
    "e3recv": ("e3recv", [("e3recv", "x", 1, e3recv_graph(), None)]),
    "e3method": ("e3method", []),
}


# ---------------------------------------------------------------- mutation fixtures
def _find_unseq(stmts):
    for s in stmts:
        if isinstance(s, dict) and s.get("stmt") == "unseq":
            return s
    raise SystemExit("no unseq node")


def _func(wire, name):
    for f in wire["funcs"]:
        if f.get("name") == name:
            return f
    raise SystemExit(f"function {name} not on the wire")


def mutants(wires):
    """(name, base witness, edit, needle) — the decoder must refuse each edit BY NAME.
    The needle is the substring the refusal text must carry (design §5)."""
    out = []

    def edit(name, base, fn, mutate, needle):
        w = copy.deepcopy(wires[base])
        node = _find_unseq(_func(w, fn)["body"]["body"])
        mutate(node, w)
        out.append((name, w, needle))

    def occ(node, oname):
        for o in node["occs"]:
            if o["name"] == oname:
                return o
        raise SystemExit(oname)

    # D5 duplicate result: op2 also binds $u0
    edit("mut-dup-binder", "w1", "w1", lambda n, w: occ(n, "op2").update(bind="$u0"), "duplicate result")
    # D7 forward reference / cycle: read1 follows op2
    edit("mut-cycle", "w1", "w1", lambda n, w: occ(n, "read1").update(after=["op2"]), "not a linear extension")
    # D12 invalid branch join: the store/then use a region-confined binder (R2a's k reads $u1 = h's result)
    edit("mut-skipped-join", "r2a", "r2aTrue",
         lambda n, w: occ(n, "call5").update(args=[ident("$u1", BOOL), ident("$u3", INT)]), "invalid branch join")
    # D6 sort mismatch: a load through a VALUE cell
    edit("mut-sort", "w3", "w3", lambda n, w: occ(n, "load2").update(target="$u0"), "sort mismatch")
    # D2 a binder without the $ reservation
    def nondollar(n, w):
        n["cells"][1]["id"] = "u1"
        occ(n, "read1")["bind"] = "u1"
        occ(n, "op2")["head"]["y"]["name"] = "u1"
    edit("mut-nondollar", "w1", "w1", nondollar, "not a reserved `$` slot name")
    # unknown slot: a $-prefixed mention that is no binder
    edit("mut-unknown-slot", "w1", "w1", lambda n, w: occ(n, "op2")["head"]["y"].update(name="$zz"), "unknown slot")
    # D8 hidden read: a nested binary inside a head
    edit("mut-hidden-read", "w1", "w1",
         lambda n, w: occ(n, "op2")["head"].update(y=binop("+", ident("a", INT), intc(1), INT)), "hidden read in a pure node")
    # D8 logical operator in a head
    edit("mut-logical-head", "w1", "w1", lambda n, w: occ(n, "op2")["head"].update(op="&&"), "logical operator")
    # D9 head type vs cell type
    edit("mut-type", "w1", "w1", lambda n, w: n["cells"][2].update(type=BOOL), "disagrees with cell")
    # D14 a legacy probe inside the completion (the mixture)
    edit("mut-probe-in-then", "w1", "w1",
         lambda n, w: n.update(then={"stmt": "block", "body": [{"stmt": "unseq-probe", "expr": ident("a", INT)}, n["then"]]}),
         "legacy unseq-probe inside an unseq completion")
    # D14 a nested unseq
    edit("mut-nested", "w1", "w1",
         lambda n, w: n.update(then={"stmt": "block", "body": [copy.deepcopy(n), n["then"]]}), "nested unseq")
    # D8 recover in a head
    edit("mut-recover", "w1", "w1", lambda n, w: occ(n, "read1").update(head={"expr": "recover", "type": INT}), "recover()")
    # D4 unknown kind
    edit("mut-unknown-kind", "w1", "w1", lambda n, w: occ(n, "read1").update(kind="evil"), "unknown occurrence kind")
    # D13 a target plan anchored at the ADDRESS of the slice variable (Stage B F2, statically)
    edit("mut-target-shape", "r4", "r4",
         lambda n, w: occ(n, "target1").update(lhs=elem_target({"expr": "ref", "id": "a"}, intc(0))), "non-atom base or index")
    # D3 empty graph
    edit("mut-empty", "w1", "w1", lambda n, w: n.update(occs=[], cells=[], then={"stmt": "block", "body": []}), "empty graph")
    # D10 resultTypes arity
    edit("mut-result-arity", "w1", "w1", lambda n, w: occ(n, "call0").update(resultTypes=[INT, INT]), "resultTypes arity")
    # D11 guard test cell not bool
    edit("mut-guard-type", "r2a", "r2aTrue", lambda n, w: n["cells"][0].update(type=INT) or occ(n, "copy0")["head"].update(type=INT),
         "not a bool cell")
    # D1 an unknown key on an occurrence
    edit("mut-unknown-key", "w1", "w1", lambda n, w: occ(n, "read1").update(extra=1), "unknown key")
    # D12 for a NESTED guard (audit fix round F3, the audit's m02/m02b): R2c's sink3 consumes the
    # INNER guard4's completion binder $u4 (produced by join6 inside guard2's region) instead of
    # the outer completion $u5 — a completion binder is confined to ITS guard's enclosing region;
    # the C1 decoder admitted this (the machine refused it only dynamically when guard2 skipped).
    edit("mut-nested-completion-join", "r2c", "r2cTrue",
         lambda n, w: occ(n, "call9").update(args=[ident("$u0", INT), ident("$u4", BOOL), ident("$u6", INT)]),
         "invalid branch join")
    # D8 for the `deref` head (Stage E E1, 2026-09-21): the pointer position holds a
    # non-atom (a binary over the global's address) — a hidden read, refused by name.
    edit("mut-deref-hidden", "e1", "e1",
         lambda n, w: occ(n, "read1")["head"].update(ptr=binop("+", ident("$u0", INT), intc(1), INT)),
         "hidden read in a pure node")
    # D13 for a MAP-ELEMENT plan (Stage E E2): the key position holds a non-atom — refused by name.
    edit("mut-map-target-key", "e2map", "e2map",
         lambda n, w: occ(n, "target2")["lhs"].update(index=binop("+", intc(0), intc(1), INT)),
         "non-atom base or key")
    # D13 for a DEREFERENCE plan (Stage E E2): the pointer position holds a non-atom (an index-get
    # of a pointer slice would be the shape) — here a binary, refused by name.
    edit("mut-deref-target-nonatom", "e2ptr", "e2ptr",
         lambda n, w: occ(n, "target2")["lhs"].update(expr=binop("+", ident("$u0", INT), intc(0), INT)),
         "outside the admitted fragment")
    # the `recv` kind (Stage E E3): a non-atom channel — a hidden read; two binders — outside the fragment.
    edit("mut-recv-nonatom", "e3recv", "e3recv",
         lambda n, w: occ(n, "recv1").update(ch=binop("+", intc(0), intc(1), INT)), "hidden read in a receive")
    edit("mut-recv-two-binds", "e3recv", "e3recv",
         lambda n, w: occ(n, "recv1").update(binds=["$u1", "$u2"]), "outside the admitted fragment")
    return out


# ---------------------------------------------------------------- assembly
def emit(frontend, srcdir):
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as tf:
        out = tf.name
    try:
        env = dict(os.environ, GO111MODULE="off",
                   GOCACHE=os.environ.get("GOCACHE", os.path.join(ROOT, "artifacts", "go-build-cache")))
        subprocess.run(frontend + ["--dir", srcdir, "--out", out], check=True, cwd=ROOT, env=env)
        with open(out, "rb") as fh:
            return json.loads(fh.read().decode("utf-8"))
    finally:
        os.unlink(out)


def _declares(stmt, name):
    """Does an emitted statement declare the local `name` (an assign with a declare
    target, or a `var` statement)?"""
    if not isinstance(stmt, dict):
        return False
    if stmt.get("stmt") == "assign":
        return any(l.get("target") == "declare" and l.get("id") == name for l in stmt.get("lhs", []))
    if stmt.get("stmt") == "var":
        return any(d.get("id") == name for d in stmt.get("decls", []))
    return False


def splice(wire, fn, until_decl, keep_tail, node, path):
    f = _func(wire, fn)
    stmts_holder, key = f["body"], "body"
    if path:
        cur = f["body"]["body"]
        for p in path[:-1]:
            cur = cur[p]
        stmts_holder, key = cur, path[-1]
    stmts = stmts_holder[key]
    keep_head = 0
    if until_decl is not None:
        idx = [i for i, st in enumerate(stmts) if _declares(st, until_decl)]
        if not idx:
            raise SystemExit(f"{fn}: no emitted statement declares {until_decl}")
        keep_head = idx[-1] + 1
    if len(stmts) < keep_head + keep_tail:
        raise SystemExit(f"{fn}: body has {len(stmts)} statements, cannot keep {keep_head}+{keep_tail}")
    tail = stmts[len(stmts) - keep_tail:] if keep_tail else []
    stmts_holder[key] = stmts[:keep_head] + [node] + tail


def render(wire):
    return (json.dumps(wire, indent=1, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


# ---------------------------------------------------------------- edge mutants on the LOWERED graphs
def _unseq_in(stmts):
    for s in stmts:
        if isinstance(s, dict) and s.get("stmt") == "unseq":
            return s
        if isinstance(s, dict) and s.get("stmt") == "for":
            found = _unseq_in(s["body"]["body"])
            if found is not None:
                return found
    return None


def _native_node(wire, fn):
    node = _unseq_in(_func(wire, fn)["body"]["body"])
    if node is None:
        raise SystemExit(f"{fn}: the frontend emitted no unseq node (the sweep left the pilot grammar?)")
    return node


def _occs_of_kind(node, kind):
    return [o for o in node["occs"] if o["kind"] == kind]


def edge_mutants(natives):
    """v2.1 §8: mutate one DATA, one LEXICAL, one GUARD and one PHASE edge of a
    LOWERED graph; each decodes, and the exact-set check names the changed set."""
    out = []

    def edit(name, base, fn, mutate):
        w = copy.deepcopy(natives[base])
        mutate(_native_node(w, fn))
        out.append((name, w))

    # DATA edge (R6): the checked access reads the source local's header instead of
    # the frozen slot — the FUSED narrowing: {20} instead of {10, 20}.
    def data(n):
        acc = [o for o in _occs_of_kind(n, "eval") if o["head"].get("expr") == "index-get"][0]
        acc["head"]["base"] = ident("a", SLICE_INT)
    edit("edge-data", "r6", "r6", data)

    # LEXICAL edge (R2b): the later call anchored at the guard ENTRY instead of the
    # completion — {false, true} instead of {false}.
    def lexical(n):
        g = _occs_of_kind(n, "guard")[0]
        change = [o for o in _occs_of_kind(n, "invoke") if o.get("after")][0]
        change["after"] = [g["name"]]
    edit("edge-lexical", "r2b", "r2b", lexical)

    # GUARD edge (R2a, z true): h's invocation taken OUT of the region — it runs
    # unconditionally, unordered against k: {`guard h guard k …`, `guard k guard h …`}
    # instead of the singleton {`guard k …`}.
    def guard(n):
        h = [o for o in _occs_of_kind(n, "invoke") if o.get("region")][0]
        del h["region"]
    edit("edge-guard", "r2a", "r2aTrue", guard)

    # PHASE edge (W3): the phase-2 store writes the LOADED value instead of the op's
    # result — the RHS event never reaches the store: {`w3 10 20` → 1020}.
    def phase(n):
        ld = _occs_of_kind(n, "load")[0]
        n["stores"][0]["value"] = ld["bind"]
    edit("edge-phase", "w3", "w3", phase)
    return out


def build(frontend):
    files = {}
    wires = {}
    natives = {}
    for name, (src, specs) in WITNESSES.items():
        wire = emit(frontend, os.path.join(HERE, "src", src))
        if src not in natives:
            natives[src] = copy.deepcopy(wire)
            files[f"native-{src}.json"] = render(wire)  # the frontend's OWN lowering, unmodified
        if not specs:
            continue  # a NATIVE-ONLY witness (Stage E E2's e2fld): no hand-built node
        for (fn, head, tail, node, path) in specs:
            if callable(node):
                node = node(natives[src])
            splice(wire, fn, head, tail, copy.deepcopy(node), path)
        wires[name] = wire
        files[f"{name}.json"] = render(wire)
    for (ename, ewire) in edge_mutants(natives):
        files[f"{ename}.json"] = render(ewire)
    rows = []
    for (mname, mwire, needle) in mutants(wires):
        files[f"{mname}.json"] = render(mwire)
        rows.append(f"{mname}\t{needle}")
    files["mutants.tsv"] = ("# mutant\trefusal needle (design docs/2026-09-19_unseq-stage-c-design.md §5); generated by build.py\n"
                            + "\n".join(rows) + "\n").encode("utf-8")
    return files


def main(argv):
    frontend = None
    check = False
    i = 1
    while i < len(argv):
        if argv[i] == "--frontend":
            frontend = [argv[i + 1]]
            i += 2
        elif argv[i] == "--check":
            check = True
            i += 1
        else:
            raise SystemExit(f"unknown argument {argv[i]}")
    if frontend is None:
        frontend = ["go", "run", "./tools/nativefrontend"]
    files = build(frontend)
    if check:
        bad = 0
        for fname, data in sorted(files.items()):
            path = os.path.join(HERE, fname)
            if not os.path.exists(path):
                print(f"build.py --check: MISSING {fname}")
                bad += 1
                continue
            with open(path, "rb") as fh:
                if fh.read() != data:
                    print(f"build.py --check: DRIFT {fname} (regenerate with build.py and commit with the reason)")
                    bad += 1
        tracked = sorted(f for f in os.listdir(HERE) if f.endswith(".json") or f == "mutants.tsv")
        for f in tracked:
            if f not in files:
                print(f"build.py --check: UNTRACKED-BY-GENERATOR {f}")
                bad += 1
        if bad:
            raise SystemExit(1)
        print(f"build.py --check: {len(files)} fixture(s) byte-identical to the generator's output")
        return
    for fname, data in sorted(files.items()):
        with open(os.path.join(HERE, fname), "wb") as fh:
            fh.write(data)
    print(f"build.py: wrote {len(files)} fixture(s) under Tests/unseq-wire/")


if __name__ == "__main__":
    main(sys.argv)
