#!/usr/bin/env python3
"""Post-import recovery helper audit; every poison must compile first."""
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
        raise SystemExit(f"Recovery setup audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


parent = Path(os.environ.get("TMPDIR", ROOT / ".tmp"))
parent.mkdir(parents=True, exist_ok=True)
directory = Path(tempfile.mkdtemp(prefix="recovery-setup-audit-", dir=parent))
print(f"Recovery setup audit scratch retained: {directory}", flush=True)
harness = directory / "AuditAll.lean"
harness.write_text("import Tests.RecoverySetupAudit\n#eval RecoverySetupAudit.run\n")
log = run([str(ROOT / "scripts/capped"), "lean", str(harness)])
(directory / "audit.log").write_text(log)

mutations = [
    (stem, "GoLean.GoCore." + stem, "recoverySetupHole",
     "\nprivate axiom recoverySetupHole : False\n")
    for stem in ["RecoverySetupShape", "RecoveryInitialization", "RecoveryResultRoots",
                 "RecoverySetup", "RecoverySetupWf", "RecoverySetupReadout", "RecoveryCallEntry"]
]
mutations += [
    ("audit_private", "Tests.RecoverySetupAudit", "recoverySetupAuditHole",
     "\nprivate axiom recoverySetupAuditHole : False\n"),
    ("test_trailing", "Tests.RecoverySetup", "sorryAx",
     "\nprivate theorem recoverySetupTrailingHole : False := by sorry\n"),
]
for label, module, marker, poison in mutations:
    fixture = directory / label
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
                   env=env, expected=1)
    (fixture / "audit.log").write_text(rejected)
    if "forbidden axiom" not in rejected or marker not in rejected:
        raise SystemExit(f"Recovery setup audit: poison {label} did not fail for {marker}")
    print(f"Recovery setup negative audit: {label} compiled then rejected ({marker})", flush=True)

