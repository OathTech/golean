#!/usr/bin/env python3
"""Admission inventory and native artifact link (the post-import audit controls
were removed in the 2026-10-12 gate cull, D3).

Lean invocations run under scripts/capped (the shim onto the box-wide
`capped`). Scratch is worktree-local under .tmp/: a PASSING run keeps only
its own result as .tmp/admission-<label>-last (the previous last run is
replaced); a FAILING run's scratch is retained under its random name and is
never overwritten by a later green run ([USER] 2026-10-11, D5: «keep the
last run only»). No gate accepts a poison fixture that failed to compile.
"""
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["GoLean.GoCore.AdmissionIndices", "GoLean.GoCore.AdmissionPolicy",
           "GoLean.GoCore.Admission", "Tests.GoCoreAdmissionFixture",
           "Tests.GoCoreAdmission"]
SOURCES = [m.replace(".", "/") + ".lean" for m in MODULES]


def run(args, env=None, cwd=ROOT, expect=0):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    print(result.stdout, end="", flush=True)
    if result.returncode != expect:
        raise SystemExit(f"Admission gate: {args} exited {result.returncode}, expected {expect}")
    return result.stdout


def scratch(label):
    parent = ROOT / ".tmp"
    parent.mkdir(exist_ok=True)
    path = Path(tempfile.mkdtemp(prefix=f"admission-{label}-", dir=parent))
    print(f"Admission scratch: {path} (retained if this run fails; a passing run "
          f"keeps it as {parent / f'admission-{label}-last'})", flush=True)
    return path


def keep_last(directory, label):
    """A passing run keeps exactly one scratch dir per label: its own."""
    last = ROOT / ".tmp" / f"admission-{label}-last"
    if last.is_symlink() or last.is_file():
        last.unlink()
    elif last.is_dir():
        shutil.rmtree(last)
    directory.rename(last)
    print(f"Admission scratch kept as the last passing run: {last}", flush=True)


def preflight():
    actual = sorted(str(p.relative_to(ROOT)) for pattern in
                    ["GoLean/GoCore/Admission*.lean", "Tests/GoCoreAdmission*.lean"]
                    for p in ROOT.glob(pattern))
    if actual != sorted(SOURCES):
        raise SystemExit(f"Admission module inventory changed: {actual}")
    # Conservative source check in addition to dependency auditing. Comments
    # are retained, so accidental suspicious text is reviewed rather than hidden.
    for name in SOURCES:
        text = re.sub(r'"(?:\\.|[^"\\])*"', '""', (ROOT / name).read_text())
        if re.search(r"\b(sorry|native_decide|axiom|partial)\b", text):
            raise SystemExit(f"Admission source escape-hatch token in {name}")
        print(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), name)
    print("Admission inventory: five complete modules", flush=True)


def artifact():
    directory = scratch("artifact")
    wire = directory / "native.json"
    env = os.environ.copy()
    env["GO111MODULE"] = "off"
    env["GOCACHE"] = str(ROOT / "artifacts/go-build-cache")
    # --subject (BUG-125): the fixture is a SUBJECT package (no func main;
    # scripts/check-admission's diff-coverage run supplies main around it).
    run(["go", "run", "./tools/nativefrontend", "--subject", "--dir",
         str(ROOT / "Tests/admission-fixture"), "--out", str(wire)], env=env)
    run([str(ROOT / "scripts/capped"), "lean", "--run",
         "tools/check-admission-artifact.lean", str(wire)])
    print("Admission fresh native wire SHA256:", hashlib.sha256(wire.read_bytes()).hexdigest())
    keep_last(directory, "artifact")


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in {"preflight", "artifact"}:
        raise SystemExit("usage: admission-check.py preflight|artifact")
    {"preflight": preflight, "artifact": artifact}[sys.argv[1]]()
