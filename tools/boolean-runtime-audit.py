#!/usr/bin/env python3
"""Post-import audit and compiled negative controls for Boolean runtime.

Every poison must compile before the independent importing audit rejects it.
Copies are private scratch trees; source/build modules are never mutated.
"""
import os
from pathlib import Path
import subprocess

from audit_scratch import active_run, managed_audit

ROOT = Path(__file__).resolve().parents[1]


def run(args, env=None, expected=0, cwd=ROOT):
    result = active_run().run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    print(result.stdout, end="", flush=True)
    if result.returncode != expected:
        raise SystemExit(f"Boolean runtime audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


@managed_audit(ROOT, "boolean-runtime-audit")
def main():
    directory = active_run().path
    print(f"Boolean runtime audit scratch (released after evidence): {directory}", flush=True)
    harness = directory / "AuditAll.lean"
    harness.write_text("import Tests.BooleanSafetyAudit\n#eval BooleanSafetyAudit.run\n")
    log = run([str(ROOT / "scripts/capped"), "lean", str(harness)])
    (directory / "audit.log").write_text(log)

    mutations = [
        ("core_private", "GoLean.GoCore.BooleanPreservation", "booleanRuntimeCoreHole",
         "\nprivate axiom booleanRuntimeCoreHole : False\n"),
        ("program_private", "GoLean.GoCore.BooleanProgram", "booleanRuntimeProgramHole",
         "\nprivate axiom booleanRuntimeProgramHole : False\n"),
        ("pool_private", "GoLean.GoCore.BooleanPool", "booleanRuntimePoolHole",
         "\nprivate axiom booleanRuntimePoolHole : False\n"),
        ("program_test_trailing", "Tests.BooleanProgram", "sorryAx",
         "\nprivate theorem booleanRuntimeProgramTestHole : False := by sorry\n"),
        ("audit_private", "Tests.BooleanSafetyAudit", "booleanRuntimeAuditHole",
         "\nprivate axiom booleanRuntimeAuditHole : False\n"),
        ("test_trailing", "Tests.BooleanInvariant", "sorryAx",
         "\nprivate theorem booleanRuntimeTrailingHole : False := by sorry\n"),
    ]
    for label, module, marker, poison in mutations:
        with active_run().fixture(label) as fixture:
            package = module.split(".")[0]
            active_run().copy_package(ROOT / ".lake/build/lib/lean" / package, fixture / package)
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
                raise SystemExit(f"Boolean runtime audit: poison {label} did not fail for {marker}")
            print(f"Boolean runtime negative audit: {label} compiled then rejected ({marker})", flush=True)
            active_run().confirm(marker)


if __name__ == "__main__":
    main()
