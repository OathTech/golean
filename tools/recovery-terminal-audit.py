#!/usr/bin/env python3
"""Post-import terminal audit; poisons must compile before rejection counts."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(args, env=None, expected=0, cwd=ROOT, echo=True):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    if echo or result.returncode != expected:
        print(result.stdout, end="", flush=True)
    if result.returncode != expected:
        raise SystemExit(f"Recovery terminal audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


# Repo-local scratch, like scripts/check-interface.py — never the process
# TMPDIR (landing chunk L3: a shared TMPDIR pointed outside the worktree).
parent = ROOT / ".tmp"
parent.mkdir(parents=True, exist_ok=True)
directory = Path(tempfile.mkdtemp(prefix="recovery-terminal-audit-", dir=parent))
print(f"Recovery terminal audit scratch retained: {directory}", flush=True)
harness = directory / "AuditAll.lean"
harness.write_text("import Tests.RecoveryTerminalAudit\n#eval RecoveryTerminalAudit.run\n")
log = run([str(ROOT / "scripts/capped"), "lean", str(harness)])
(directory / "audit.log").write_text(log)

capture = directory / "CaptureClaims.lean"
capture.write_text('import Tests.RecoveryTerminalAudit\n'
                   'open Lean\n'
                   '#eval show MetaM Unit from do\n'
                   '  let claims ← RecoveryTerminalAudit.claims\n'
                   '  liftM <| IO.println claims.compress\n')
captured = run([str(ROOT / "scripts/capped"), "lean", str(capture)], echo=False)
(directory / "claims.json").write_text(captured)
print(f"Recovery terminal exact theorem types: {directory / 'claims.json'}", flush=True)

mutations = [
    (stem, "GoLean.GoCore." + stem, "terminalUnusedHole",
     "\nprivate axiom terminalUnusedHole : False\n")
    for stem in ["RecoveryTerminal", "RecoveryPoolObservationTyped"]
]
mutations += [
    ("test_private", "Tests.RecoveryTerminal", "terminalUnusedTestHole",
     "\nprivate axiom terminalUnusedTestHole : False\n"),
    ("audit_private", "Tests.RecoveryTerminalAudit", "terminalUnusedAuditHole",
     "\nprivate axiom terminalUnusedAuditHole : False\n"),
    ("test_trailing", "Tests.RecoveryTerminal", "sorryAx",
     "\nprivate theorem terminalTrailingHole : False := by sorry\n"),
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
        raise SystemExit(f"Recovery terminal audit: poison {label} did not fail for {marker}")
    print(f"Recovery terminal negative audit: {label} compiled then rejected ({marker})", flush=True)
