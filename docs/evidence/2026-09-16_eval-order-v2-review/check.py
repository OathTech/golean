#!/usr/bin/env python3
"""Reproduce design gaps using the exact reviewed enumerator; no lowering run."""
import subprocess
import types

REV = "9a8ed328711969455bfe1d823c65e858cb919e3a"
PATH = "docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py"
source = subprocess.run(
    ["git", "show", f"{REV}:{PATH}"], check=True, capture_output=True, text=True
).stdout
m = types.ModuleType("reviewed_enumerator")
exec(compile(source, f"{REV}:{PATH}", "exec"), m.__dict__)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read_reduction(ordered):
    def mutate(st, values):
        st["v"].update(x=1, y=2)
        return 0

    nodes = [
        m.Occ("Rx", run=lambda s, v: s["v"]["x"]),
        m.Occ("Ry", deps=["Rx"] if ordered else [], run=lambda s, v: s["v"]["y"]),
        m.Occ("E", run=mutate),
        m.Occ("sum", deps=["Rx", "Ry", "E"], run=lambda s, v: v["Rx"] + v["Ry"]),
    ]
    results = m.enumerate_graph(nodes, m.state(v={"x": 0, "y": 0}), lambda s, v: v["sum"])
    return sorted({k[1] for k in results})


full, reduced = read_reduction(False), read_reduction(True)
require(full == [0, 1, 2, 3] and reduced == [0, 2, 3], "reduction witness changed")
print(f"read-order reduction: full={full}; reduced={reduced}; lost=[1]")

for z in (False, True):
    region = [m.Occ("H", run=lambda s, v: True),
              m.Occ("or", deps=["H"], run=lambda s, v: v["H"])]
    nodes = [
        m.Occ("Z", run=lambda s, v: s["v"]["z"]),
        m.Occ("G", deps=["Z"], guard="Z", when=False, region=region, out="or"),
        # E1: H precedes the later sibling call K, when H is executed.
        m.Occ("K", deps=["G", "H"], run=lambda s, v: 7),
    ]
    try:
        results = m.enumerate_graph(nodes, m.state(v={"z": z}), lambda s, v: v["K"])
    except AssertionError as error:
        require(z and "no ready occurrence" in str(error), "unexpected guard failure")
        print(f"skipped-event z={z}: {error}")
    else:
        values = sorted({k[1] for k in results})
        require(not z and values == [7], "guard witness changed")
        print(f"skipped-event z={z}: values={values}")


def logical_completion(after_result):
    def mutate(st, values):
        st["v"]["x"] = True
        return 0

    region = [m.Occ("or", run=lambda s, v: s["v"]["x"])]
    nodes = [m.Occ("Z", run=lambda s, v: False),
             m.Occ("G", deps=["Z"], guard="Z", when=False, region=region, out="or"),
             m.Occ("M", deps=["or"] if after_result else ["G"], run=mutate)]
    results = m.enumerate_graph(nodes, m.state(v={"x": False}), lambda s, v: v["or"])
    return sorted({k[1] for k in results})


guard_only, completion = logical_completion(False), logical_completion(True)
require(guard_only == [False, True] and completion == [False], "logical completion witness changed")
print(f"logical ordering: guard-only={guard_only}; after-completion={completion}")


def header_read(split):
    def rebind(st, values):
        st["v"]["a"] = "B"
        return 0

    nodes = ([m.Occ("H", run=lambda s, v: m.hdr(s, "a"))] if split else []) + [
        m.Occ("F", run=rebind),
        m.Occ("R", deps=["F", "H"] if split else ["F"],
              run=lambda s, v: m.elem(s, v["H"] if split else m.hdr(s, "a"), v["F"])),
    ]
    results = m.enumerate_graph(nodes, m.state(v={"a": "A"}, arr={"A": [10], "B": [20]}),
                                lambda s, v: v["R"])
    return sorted({k[1] for k in results})


fused, split = header_read(False), header_read(True)
require(fused == [20] and split == [10, 20], "header witness changed")
print(f"header granularity: fused={fused}; split={split}")
print("RESULT: expected design gaps reproduced (not a GoLean conformance pass)")
