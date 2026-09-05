"""Post-import audit and compiled mutation checks; run via check-interface."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
MODULES = ["GoLean/GoCore/Trace", "GoLean/GoCore/PoolTrace",
           "GoLean/GoCore/ProgramTrace", "GoLean/Interface",
           "Tests/InterfaceContract", "Tests/InterfaceAudit"]
HARNESS = "\n".join(f"import {m.replace('/', '.')}" for m in MODULES)
HARNESS += "\n#eval InterfaceAudit.run\n"


def main():
    paths = sorted([*ROOT.glob("GoLean/**/*.lean"), ROOT / "GoLean.lean",
                    ROOT / "Tests/InterfaceContract.lean", ROOT / "Tests/InterfaceAudit.lean",
                    ROOT / "lakefile.toml", ROOT / "lean-toolchain",
                    ROOT / "scripts/ci", ROOT / "scripts/capped",
                    ROOT / "scripts/check-interface", Path(__file__).resolve()])
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
    print("Semantic interface source fingerprint:", digest.hexdigest(), flush=True)
    scratch_root = ROOT / ".tmp"
    scratch_root.mkdir(exist_ok=True)
    scratch = Path(tempfile.mkdtemp(prefix="interface-audit-", dir=scratch_root))

    def lean(path, fixture=None, output=None):
        env = os.environ.copy()
        if fixture is not None:
            env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
        args = [str(ROOT / "scripts/capped"), "lean", f"--root={fixture or scratch}"]
        if output is not None:
            args += ["-o", str(output)]
        result = subprocess.run(args + [str(path)], cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        print(result.stdout, end="", flush=True)
        return result

    harness = scratch / "AuditAll.lean"
    harness.write_text(HARNESS)
    result = lean(harness)
    if result.returncode:
        raise SystemExit(result.returncode)
    for label, target, declaration, marker in [
        ("promoted_private", "GoLean/GoCore/Trace.lean",
         "private axiom promotedTraceHole : False", "promotedTraceHole"),
        ("facade_private", "GoLean/Interface.lean",
         "private axiom facadeHole : False", "facadeHole"),
        ("audit_trailing", "Tests/InterfaceAudit.lean",
         "private theorem auditHole : False := by sorry", "sorryAx"),
    ]:
        fixture = scratch / label
        for tree in ["GoLean", "Tests"]:
            shutil.copytree(ROOT / ".lake/build/lib/lean" / tree, fixture / tree)
        source = fixture / target
        source.write_text((ROOT / target).read_text() + "\n" + declaration + "\n")
        if lean(source, fixture, source.with_suffix(".olean")).returncode:
            raise SystemExit(f"Semantic interface: {label} failed to compile; not audit rejection")
        external = fixture / "AuditAll.lean"
        external.write_text(HARNESS)
        result = lean(external, fixture)
        if result.returncode != 1 or "forbidden axiom" not in result.stdout or marker not in result.stdout:
            raise SystemExit(f"Semantic interface: expected named audit rejection for {label}")
        print(f"Semantic interface negative: {label} rejected (exit 1, {marker})", flush=True)
    print(f"Semantic interface: PASS; scratch retained at {scratch}", flush=True)


if __name__ == "__main__":
    main()
