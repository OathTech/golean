"""Source checks and a post-import axiom audit for the isolated A1 package."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

SPIKE = Path(__file__).resolve().parent
ROOT = SPIKE.parents[1]
MODULES = ["Trace", "Counterexamples", "PoolTrace", "ProgramTrace", "Language",
           "Examples", "Audit", "Probes"]
SOURCES = [SPIKE / "GateA1" / f"{name}.lean" for name in MODULES] + [SPIKE / "GateA1.lean"]


def forbidden(text):
    # An early diagnostic only. The post-import environment audit is the
    # authoritative transitive-axiom check, independent of this text scan.
    text = re.sub(r'/\-.*?\-/|--[^\n]*|"(?:\\.|[^"\\])*"', "", text, flags=re.S)
    return re.search(r"\b(axiom|partial|sorry|native_decide|ofReduceBool|ofReduceNat)\b", text)


def dependencies(required):
    manifest = json.loads((SPIKE / "lake-manifest.json").read_text())
    for dep in manifest["packages"]:
        if dep["type"] != "git":
            continue
        path = SPIKE / ".lake/packages" / dep["name"]
        if not path.exists() and not required:
            continue  # Lake may fetch it; the post-build check requires it.
        actual = subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if actual != dep["rev"]:
            raise SystemExit(f"Gate A1: wrong dependency revision for {dep['name']}: {actual}")
        if subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True
        ):
            raise SystemExit(f"Gate A1: modified dependency {dep['name']}")


def preflight():
    actual = set(SPIKE.glob("*.lean")) | set((SPIKE / "GateA1").rglob("*.lean"))
    if actual != set(SOURCES):
        raise SystemExit("Gate A1: module inventory changed; update fresh-elaboration order and audit imports")
    for path in SOURCES:
        if forbidden(path.read_text()):
            raise SystemExit(f"Gate A1: forbidden proof escape in {path}")
    dependencies(required=False)
    paths = sorted([*ROOT.glob("GoLean/**/*.lean"), ROOT / "lakefile.toml", ROOT / "lean-toolchain",
                    *SOURCES, SPIKE / "lakefile.toml", SPIKE / "lake-manifest.json",
                    SPIKE / "lean-toolchain", SPIKE / "check", Path(__file__).resolve()])
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    print("Gate A1 source/dependency-manifest fingerprint:", digest.hexdigest(), flush=True)
    print("GoLean HEAD:", subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip(), flush=True)
    print("Validation mode: incremental Lake build plus fresh spike-module elaboration", flush=True)


def audit():
    # Called through capped `lake env python3`, so child Lean processes inherit
    # the pinned toolchain, package search paths, and verified memory cap.
    scratch_root = ROOT / ".tmp"
    scratch_root.mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="gate-a1-audit-", dir=scratch_root))
    harness_text = "\n".join(
        f"import {'.'.join(path.relative_to(SPIKE).with_suffix('').parts)}" for path in SOURCES
    ) + "\n#eval GateA1Audit.run\n"
    harness = scratch / "AuditAll.lean"
    harness.write_text(harness_text)

    def lean(path, *, fixture=None, output=None):
        env = os.environ.copy()
        if fixture is not None:
            env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
        args = [str(ROOT / "scripts/capped"), "lean", f"--root={fixture or scratch}"]
        if output is not None:
            args += ["-o", str(output)]
        result = subprocess.run(args + [str(path)], cwd=SPIKE, env=env,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=120)
        print(result.stdout, end="", flush=True)
        return result

    result = lean(harness)
    if result.returncode:
        raise SystemExit(result.returncode)

    # Compile real replacement modules in isolated search paths. A bad axiom
    # compiles in Lean; the post-import audit must reject it even when unused.
    # No live source or build output is edited. Leave scratch for inspection.
    for label, target, declaration in [
        ("trailing_private", "GateA1/Audit.lean", "private axiom a1TrailingHole : False"),
        ("aggregate_private", "GateA1.lean", "private axiom a1RootHole : False"),
        ("trailing_sorry", "GateA1/Audit.lean", "private theorem a1SorryHole : False := by sorry"),
    ]:
        if not forbidden(declaration):
            raise SystemExit(f"Gate A1: lexical negative test escaped: {label}")
        fixture = scratch / label
        # Lean resolves the first matching package root, rather than falling
        # through per missing child module. Copy the complete compiled tree;
        # only the selected module and aggregate are overwritten below.
        shutil.copytree(SPIKE / ".lake/build/lib/lean/GateA1", fixture / "GateA1")
        source = fixture / target
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text((SPIKE / target).read_text() + "\n" + declaration + "\n")
        result = lean(source, fixture=fixture, output=source.with_suffix(".olean"))
        if result.returncode:
            raise SystemExit(f"Gate A1: {label} fixture failed to compile; not an audit rejection")
        if target != "GateA1.lean":
            aggregate = fixture / "GateA1.lean"
            aggregate.write_text((SPIKE / "GateA1.lean").read_text())
            if lean(aggregate, fixture=fixture, output=aggregate.with_suffix(".olean")).returncode:
                raise SystemExit(f"Gate A1: {label} aggregate failed to compile")
        external = fixture / "AuditAll.lean"
        external.write_text(harness_text)
        result = lean(external, fixture=fixture)
        marker = {"trailing_private": "a1TrailingHole", "aggregate_private": "a1RootHole",
                  "trailing_sorry": "sorryAx"}[label]
        if result.returncode != 1 or "forbidden axiom" not in result.stdout or marker not in result.stdout:
            raise SystemExit(f"Gate A1: expected named audit rejection for {label}")
        print(f"Gate A1 negative regression: {label} rejected (exit 1, {marker})", flush=True)
    print(f"Gate A1 audit scratch retained: {scratch}", flush=True)


if __name__ == "__main__":
    {"preflight": preflight, "dependencies": lambda: dependencies(required=True), "audit": audit}[sys.argv[1]]()
