"""Customer gate, derived from the reviewed A1 post-import audit harness."""
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
MODULES = ["Heap","Ghost","Lifting","Rules","Adequacy","Program","Admission","Allocation","Call","Unwind","Return","Examples","Readout","Driver","SharedProgram","SharedHelpers","SharedRecovery","SharedDrain","Shared","SharedReadout","SharedDriver","OwnershipTests","Audit"]
CORE_MODULES = ["RecoveryCallLayout","RecoverySingleton","RecoveryPool","RecoveryChoices"]
SOURCES = [SPIKE / "GoLeanIris" / f"{name}.lean" for name in MODULES] + [SPIKE / "GoLeanIris.lean"]


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
            raise SystemExit(f"Iris customer: wrong dependency revision for {dep['name']}: {actual}")
        if subprocess.check_output(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True
        ):
            raise SystemExit(f"Iris customer: modified dependency {dep['name']}")


def preflight():
    actual = set(SPIKE.glob("*.lean")) | set((SPIKE / "GoLeanIris").rglob("*.lean"))
    if actual != set(SOURCES):
        raise SystemExit("Iris customer: module inventory changed; update fresh-elaboration order and audit imports")
    for path in SOURCES:
        if forbidden(path.read_text()):
            raise SystemExit(f"Iris customer: forbidden proof escape in {path}")
    dependencies(required=False)
    paths = sorted([ROOT / "Tests/InterfaceContract.lean", ROOT / "Tests/RecoveryTypingFixture.lean",
                    ROOT / "Tests/recovery-typing-fixture/main.go", ROOT / "Tests/recovery-typing-fixture/manifest.tsv",
                    ROOT / "GoLean.lean", *ROOT.glob("GoLean/**/*.lean"),
                    ROOT / "lakefile.toml", ROOT / "lean-toolchain",
                    *SOURCES, *ROOT.glob("spikes/gate-a1/GateA1/*.lean"), ROOT / "spikes/gate-a1/GateA1.lean",
                    ROOT / "spikes/gate-a1/lakefile.toml", ROOT / "spikes/gate-a1/lake-manifest.json",
                    ROOT / "spikes/gate-a1/lean-toolchain",
                    *ROOT.glob("tools/nativefrontend/*.go"), *SPIKE.glob("fixtures/**/*.go"),
                    *ROOT.glob("tools/coverageharness/*.go"), ROOT / "scripts/diff-coverage",
                    ROOT / "scripts/capped", ROOT / "baselines/go-oracle-pin",
                    SPIKE / "fixtures/manifest.tsv", SPIKE / "tools/check_artifact.lean",
                    SPIKE / "lakefile.toml", SPIKE / "lake-manifest.json",
                    SPIKE / "lean-toolchain", SPIKE / "check", Path(__file__).resolve()])
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    print("Iris customer source/dependency-manifest fingerprint:", digest.hexdigest(), flush=True)
    print("GoLean HEAD:", subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip(), flush=True)
    print("Validation mode: incremental Lake build plus fresh spike-module elaboration", flush=True)


def audit():
    # Called through capped `lake env python3`, so child Lean processes inherit
    # the pinned toolchain, package search paths, and verified memory cap.
    scratch_root = ROOT / ".tmp"
    scratch_root.mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="iris-customer-audit-", dir=scratch_root))
    harness_text = "\n".join(
        f"import {'.'.join(path.relative_to(SPIKE).with_suffix('').parts)}" for path in SOURCES
    ) + "\n#eval GoLeanIrisAudit.run\n"
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
    mutations = [(name + "_private", ROOT, "GoLean/GoCore/" + name + ".lean",
                  "private axiom irisCoreHole : False", "irisCoreHole") for name in CORE_MODULES]
    mutations += [(name + "_private", SPIKE, "GoLeanIris/" + name + ".lean",
                   "private axiom irisHelperHole : False", "irisHelperHole")
                  for name in MODULES if name not in ["Heap", "Ghost", "Lifting", "Rules", "Adequacy", "Program", "Audit"]]
    mutations += [
        ("trailing_private", SPIKE, "GoLeanIris/Audit.lean", "private axiom irisTrailingHole : False", "irisTrailingHole"),
        ("aggregate_private", SPIKE, "GoLeanIris.lean", "private axiom irisRootHole : False", "irisRootHole"),
        ("trailing_sorry", SPIKE, "GoLeanIris/OwnershipTests.lean", "private theorem irisSorryHole : False := by sorry", "sorryAx"),
    ]
    for label, source_root, target, declaration, marker in mutations:
        if not forbidden(declaration):
            raise SystemExit(f"Iris customer: lexical negative test escaped: {label}")
        fixture = scratch / label
        # Lean resolves the first matching package root, rather than falling
        # through per missing child module. Copy the complete compiled tree;
        # only the selected module and aggregate are overwritten below.
        shutil.copytree(SPIKE / ".lake/build/lib/lean/GoLeanIris", fixture / "GoLeanIris")
        if source_root == ROOT:
            shutil.copytree(ROOT / ".lake/build/lib/lean/GoLean", fixture / "GoLean")
        source = fixture / target
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text((source_root / target).read_text() + "\n" + declaration + "\n")
        result = lean(source, fixture=fixture, output=source.with_suffix(".olean"))
        (fixture / "compile.log").write_text(result.stdout)
        if result.returncode:
            raise SystemExit(f"Iris customer: {label} fixture failed to compile; not an audit rejection")
        if target != "GoLeanIris.lean":
            aggregate = fixture / "GoLeanIris.lean"
            aggregate.write_text((SPIKE / "GoLeanIris.lean").read_text())
            if lean(aggregate, fixture=fixture, output=aggregate.with_suffix(".olean")).returncode:
                raise SystemExit(f"Iris customer: {label} aggregate failed to compile")
        external = fixture / "AuditAll.lean"
        external.write_text(harness_text)
        result = lean(external, fixture=fixture)
        (fixture / "audit.log").write_text(result.stdout)
        if result.returncode != 1 or "forbidden axiom" not in result.stdout or marker not in result.stdout:
            raise SystemExit(f"Iris customer: expected named audit rejection for {label}")
        print(f"Iris customer negative regression: {label} rejected (exit 1, {marker})", flush=True)
    print(f"Iris customer audit scratch retained: {scratch}", flush=True)



def artifact():
    # Fresh frontend evidence; no proof of translation correctness is claimed.
    scratch_root = ROOT / ".tmp"
    scratch_root.mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="iris-customer-artifact-", dir=scratch_root))
    wire = scratch / "recovery.json"
    shared_wire = scratch / "shared.json"
    env = os.environ.copy()
    env["GO111MODULE"] = "off"
    env["GOCACHE"] = str(ROOT / "artifacts/go-build-cache")
    commands = [
        (["go", "run", "./tools/nativefrontend", "--dir",
          str(SPIKE / "fixtures/recovery"), "--out", str(wire)], ROOT),
        (["go", "run", "./tools/nativefrontend", "--dir",
          str(ROOT / "Tests/recovery-typing-fixture"), "--out", str(shared_wire)], ROOT),
        ([str(ROOT / "scripts/capped"), "lean", "--run",
          "tools/check_artifact.lean", str(wire), str(shared_wire)], SPIKE),
    ]
    for args, cwd in commands:
        subprocess.run(args, cwd=cwd, env=env, check=True, timeout=120)
    for path in [wire, shared_wire]:
        print("Fresh native wire SHA256:", path.name, hashlib.sha256(path.read_bytes()).hexdigest(), flush=True)
    print(f"Iris customer artifact scratch retained: {scratch}", flush=True)


if __name__ == "__main__":
    {"preflight": preflight, "dependencies": lambda: dependencies(required=True), "audit": audit, "artifact": artifact}[sys.argv[1]]()
