#!/usr/bin/env python3
"""frontier.py — the W2 REFUSAL INVENTORY instrument.

The native frontend reports ONE refusal and stops, and its message names the
construct, not the declaration.  This walks the frontier: run the frontend,
record the refusal, NEUTRALISE the declaration that carries it, run again —
until the tree exports clean.  The output is the refusal inventory: an ordered
list of (refusal, site, declaration), which is the measurement W2.2/W2.3 owe
(master plan §W2.2 "verify rendering paths are quarantine-dead under the
harness" — measured, not assumed).

Neutralisation is by DECLARATION NAME from a driver list (`--plan`), not by
guessing: each step names the file and the top-level declaration to comment
out, so the walk is reproducible and every step is auditable.  A step whose
predicted refusal does not match what the frontend actually said is a LOUD
mismatch, not a silent continue.

    tools/raftsubject/frontier.py            # raftsubject/ + probe-main.go
    tools/raftsubject/frontier.py --tree DIR --plan PLAN.tsv [--work DIR]

Everything it needs is TRACKED: the subject tree, the harness-shaped probe
main (`probe-main.go`) and the walk plan (`frontier-plan.tsv`).  Re-running it
after any frontend or subject change reproduces — or refutes — the inventory
in docs/raft-w2-log.md.

PLAN.tsv rows:  <file>\t<decl>\t<expected refusal substring>
where <decl> is `Type.Method`, `func Name`, or `*` for "no more removals;
this row asserts the tree now exports clean".
"""

import argparse
import os
import re
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def find_decl(text, decl):
    """Return (start, end) line indices of a top-level declaration."""
    lines = text.split("\n")
    if "." in decl:
        recv, meth = decl.split(".", 1)
        pat = re.compile(r"^func \(\w+ \*?%s\) %s\b" % (re.escape(recv), re.escape(meth)))
    else:
        pat = re.compile(r"^func %s\b" % re.escape(decl))
    for i, ln in enumerate(lines):
        if pat.match(ln):
            if ln.rstrip().endswith("}") and ln.count("{") == ln.count("}"):
                j = i  # single-line declaration
            else:
                j = i
                while j < len(lines) and lines[j] != "}":
                    j += 1
            # take the doc comment too
            k = i
            while k > 0 and lines[k - 1].startswith("//"):
                k -= 1
            return k, j
    return None


def neutralise(path, decl, keepalive=None):
    """Replace a declaration's BODY with a panic, keeping its signature.

    Not deletion: deleting a method changes the package's type-check and the
    next refusal you see is a CASCADE of the removal ("c[0].String undefined"
    in the W1 inventory), not an independent frontier item.  Replacing the
    body leaves every call site type-checking exactly as before, so each step
    isolates one refusal.
    """
    text = open(path).read()
    span = find_decl(text, decl)
    if span is None:
        sys.exit("frontier.py: declaration %s not found in %s" % (decl, path))
    lines = text.split("\n")
    i, j = span
    sig_start = i
    while not lines[sig_start].startswith("func "):
        sig_start += 1
    k = sig_start
    if lines[k].rstrip().endswith("}") and lines[k].count("{") == lines[k].count("}"):
        sig = lines[k][:lines[k].index("{") + 1]
    else:
        while not lines[k].rstrip().endswith("{"):
            k += 1
        sig = "\n".join(lines[sig_start:k + 1])
    body = [sig,
            '\tpanic("frontier probe: %s body replaced to walk past its refusal")' % decl,
            "}"]
    out = lines[:sig_start] + body + lines[j + 1:]
    text = "\n".join(out)
    if keepalive:
        # Replacing a body can orphan an import ("cmp imported and not used"),
        # which is a probe artifact of the walk, not a frontier item.  The
        # plan names the now-unused imports; they become BLANK imports, which
        # keeps the file type-checking without introducing any declaration the
        # frontend then has to lower.
        for pkg in keepalive.split(","):
            new, n = re.subn(r'^\t"%s"$' % re.escape(pkg), '\t_ "%s"' % pkg,
                             text, count=1, flags=re.M)
            if not n:
                new, n = re.subn(r'^import "%s"$' % re.escape(pkg),
                                 'import _ "%s"' % pkg, text, count=1, flags=re.M)
            if not n:
                sys.exit("frontier.py: keepalive import %s not found in %s"
                         % (pkg, path))
            text = new
    open(path, "w").write(text)


def run_frontend(fe, tree):
    r = subprocess.run([fe, "--dir", tree, "--out", os.devnull],
                       capture_output=True, text=True)
    if r.returncode == 0:
        return None
    msg = r.stderr.strip()
    msg = msg.replace("nativefrontend: native frontend unsupported: ", "")
    msg = msg.replace("nativefrontend: ", "")
    return msg


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", default=os.path.join(REPO, "raftsubject"))
    ap.add_argument("--probe-main",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "probe-main.go"))
    ap.add_argument("--plan",
                    default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                         "frontier-plan.tsv"))
    ap.add_argument("--work", default=os.path.join(REPO, "artifacts", "frontier-work"))
    ap.add_argument("--frontend", default=os.path.join(REPO, "artifacts", "nativefrontend"))
    args = ap.parse_args()

    shutil.rmtree(args.work, ignore_errors=True)
    shutil.copytree(args.tree, args.work,
                    ignore=shutil.ignore_patterns("README.md"))
    shutil.copy(args.probe_main, os.path.join(args.work, "main.go"))

    plan = []
    for ln in open(args.plan):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        plan.append(ln.split("\t"))

    bad = 0
    for n, row in enumerate(plan, 1):
        fil, decl, expect = row[0], row[1], row[2]
        keepalive = row[3] if len(row) > 3 else None
        msg = run_frontend(args.frontend, args.work)
        got = msg if msg else "(exports clean)"
        mark = "ok " if expect in got else "MISMATCH"
        if expect not in got:
            bad += 1
        print("%2d %s %-52s %s :: %s" % (n, mark, got, fil, decl))
        if decl == "*":
            break
        neutralise(os.path.join(args.work, fil), decl, keepalive)

    final = run_frontend(args.frontend, args.work)
    print("\nfinal: %s" % (final if final else "EXPORTS CLEAN"))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
