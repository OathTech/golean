#!/usr/bin/env python3
"""Post-import abort observation audit; every poison must compile first."""
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
        raise SystemExit(f"Abort observation audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


parent = Path(os.environ.get("TMPDIR", ROOT / ".tmp"))
parent.mkdir(parents=True, exist_ok=True)
directory = Path(tempfile.mkdtemp(prefix="abort-observation-audit-", dir=parent))
print(f"Abort observation audit scratch retained: {directory}", flush=True)
harness = directory / "AuditAll.lean"
harness.write_text("import Tests.AbortObservationAudit\n#eval AbortObservationAudit.run\n")
log = run([str(ROOT / "scripts/capped"), "lean", str(harness)])
(directory / "audit.log").write_text(log)

mutations = [
    (stem, "GoLean.GoCore." + stem, "abortObservationHole",
     "\nprivate axiom abortObservationHole : False\n")
    for stem in ['AbortObservation', 'RecoveryObservation', 'RecoveryPoolObservation', 'RecoveryProgramObservation']
]
mutations += [
    ("audit_private", "Tests.AbortObservationAudit", "abortObservationAuditHole",
     "\nprivate axiom abortObservationAuditHole : False\n"),
    ("test_trailing", "Tests.AbortObservation", "sorryAx",
     "\nprivate theorem abortObservationTrailingHole : False := by sorry\n"),
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
        raise SystemExit(f"Abort observation audit: poison {label} did not fail for {marker}")
    print(f"Abort observation negative audit: {label} compiled then rejected ({marker})", flush=True)

