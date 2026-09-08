#!/usr/bin/env python3
"""Post-import declaration audit with compiling, unused poison controls."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(args, env=None, expected=0, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    print(result.stdout, end="", flush=True)
    if result.returncode != expected:
        raise SystemExit(f"Declaration audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


parent = Path(os.environ.get("TMPDIR", ROOT / ".tmp"))
parent.mkdir(parents=True, exist_ok=True)
directory = Path(tempfile.mkdtemp(prefix="declaration-audit-", dir=parent))
print(f"Declaration audit scratch retained: {directory}", flush=True)
harness = directory / "AuditAll.lean"
harness.write_text("import Tests.DeclarationAudit\n#eval auditDeclarations\n")
(directory / "audit.log").write_text(run([str(ROOT / "scripts/capped"), "lean", str(harness)]))

modules = ["GoLean.GoCore.Declaration", "GoLean.StrictJsonParse", "GoLean.NativeDeclaration",
           "Tests.DeclarationWire", "Tests.StrictJsonParse", "Tests.DeclarationAudit"]
for index, module in enumerate(modules):
    fixture = directory / str(index)
    package = module.split(".")[0]
    shutil.copytree(ROOT / ".lake/build/lib/lean" / package, fixture / package)
    source = fixture / (module.replace(".", "/") + ".lean")
    source.parent.mkdir(parents=True, exist_ok=True)
    marker = f"declarationUnusedHole{index}"
    source.write_text((ROOT / (module.replace(".", "/") + ".lean")).read_text()
                      + f"\nprivate axiom {marker} : False\n")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
    compiled = run([str(ROOT / "scripts/capped"), "lean", "-o",
                    str(source.with_suffix(".olean")), str(source)], env=env, cwd=fixture)
    (fixture / "compile.log").write_text(compiled)
    rejected = run([str(ROOT / "scripts/capped"), "lean", str(harness)], env=env, expected=1)
    (fixture / "audit.log").write_text(rejected)
    if "forbidden axiom" not in rejected or marker not in rejected:
        raise SystemExit(f"Declaration audit: {module} did not reject its compiled unused axiom")
    print(f"Declaration negative audit: {module} compiled then rejected ({marker})", flush=True)
