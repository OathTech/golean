#!/usr/bin/env python3
"""Compare the checked step bodies with deriving traces from the immutable old pin.

This is a focused preservation control, not a compiler correctness theorem.
Usage: python3 check-derivation.py OLD-VALUE-TRACE OLD-SYNTAX-TRACE
Generate those traces as described in README.md; never use candidate traces.
"""
from pathlib import Path
import re
import sys

if len(sys.argv) != 3:
    raise SystemExit(__doc__)
traces = [Path(p).read_text() for p in sys.argv[1:]]
checked = Path(__file__).with_name("Derivation.lean").read_text()
for typ, trace, count in [("Ty", traces[0], 14), ("GoValue", traces[0], 15),
                          ("Expr", traces[1], 59)]:
    start = trace.index(f"       partial def instRepr{typ}.repr ")
    end = trace.index("\n     end,", start)
    body = trace[start:end].replace("✝", "").translate(
        str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789"))
    body = body.replace(f"partial def instRepr{typ}.repr",
        f"def {typ.lower()}Step (rec : {typ} → Nat → Format)")
    body = body.replace(f"instRepr{typ}.repr", "rec")
    body = body.replace("let localinst : Repr", "let _ : Repr")
    if len(re.findall(r"\| @GoLean\.", body)) != count:
        raise SystemExit(f"FAIL: {typ} constructor census")
    begin = checked.index(f"def {typ.lower()}Step ")
    following = re.search(r"\n(?:def |theorem )", checked[begin + 1:])
    stop = begin + 1 + following.start() if following else len(checked)
    actual = checked[begin:stop]
    # Layout and binder decorations are immaterial; every term/token is retained.
    if " ".join(body.split()) != " ".join(actual.split()):
        raise SystemExit(f"FAIL: {typ} step body differs from the old deriving trace")
    print(f"PASS: {typ}, all {count} old constructor bodies; recursive calls parameterized")
