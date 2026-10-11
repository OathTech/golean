#!/usr/bin/env python3
"""Admission inventory, post-import audit controls, and native artifact link.

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
           "Tests.GoCoreAdmission", "Tests.GoCoreAdmissionAudit"]
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
    print("Admission inventory: six complete modules", flush=True)


def audit():
    directory = scratch("audit")
    harness = directory / "AuditAll.lean"
    harness.write_text("import Tests.GoCoreAdmissionAudit\n#eval GoLeanAdmissionAudit.run\n")
    log = run([str(ROOT / "scripts/capped"), "lean", str(harness)])
    (directory / "audit.log").write_text(log)
    mutations = [
        ("audit_private", "Tests.GoCoreAdmissionAudit", "admissionAuditHole",
         "\nprivate axiom admissionAuditHole : False\n"),
        ("core_private", "GoLean.GoCore.Admission", "admissionCoreHole",
         "\nprivate axiom admissionCoreHole : False\n"),
        ("test_trailing", "Tests.GoCoreAdmission", "sorryAx",
         "\nprivate theorem admissionTrailingHole : False := by sorry\n"),
    ]
    for label, module, marker, poison in mutations:
        fixture = directory / label
        # Lean chooses a package root before resolving its child modules.
        # Copy that root's complete compiled tree; partial overlays fail to
        # import siblings. Copies are independent, never writable symlinks.
        package = module.split(".")[0]
        shutil.copytree(ROOT / ".lake/build/lib/lean" / package, fixture / package)
        source = fixture / (module.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text((ROOT / (module.replace(".", "/") + ".lean")).read_text() + poison)
        env = os.environ.copy()
        env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
        compiled = run([str(ROOT / "scripts/capped"), "lean", "-o",
                        str(source.with_suffix(".olean")), str(source)], env=env, cwd=fixture)
        (fixture / "compile.log").write_text(compiled)
        rejected = run([str(ROOT / "scripts/capped"), "lean", str(harness)],
                       env=env, expect=1)
        (fixture / "audit.log").write_text(rejected)
        if "forbidden axiom" not in rejected or marker not in rejected:
            raise SystemExit(f"Admission gate: poison {label} did not fail for {marker}")
        print(f"Admission negative audit: {label} compiled then rejected ({marker})", flush=True)
    keep_last(directory, "audit")


def elaborate():
    for source in SOURCES:
        run([str(ROOT / "scripts/capped"), "lean", str(ROOT / source)])
        print(f"Admission fresh elaboration: {source}", flush=True)


def artifact():
    directory = scratch("artifact")
    wire = directory / "native.json"
    env = os.environ.copy()
    env["GO111MODULE"] = "off"
    env["GOCACHE"] = str(ROOT / "artifacts/go-build-cache")
    run(["go", "run", "./tools/nativefrontend", "--dir",
         str(ROOT / "Tests/admission-fixture"), "--out", str(wire)], env=env)
    run([str(ROOT / "scripts/capped"), "lean", "--run",
         "tools/check-admission-artifact.lean", str(wire)])
    print("Admission fresh native wire SHA256:", hashlib.sha256(wire.read_bytes()).hexdigest())
    keep_last(directory, "artifact")


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in {"preflight", "elaborate", "audit", "artifact"}:
        raise SystemExit("usage: admission-check.py preflight|elaborate|audit|artifact")
    {"preflight": preflight, "elaborate": elaborate, "audit": audit, "artifact": artifact}[sys.argv[1]]()
