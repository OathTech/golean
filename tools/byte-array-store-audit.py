#!/usr/bin/env python3
"""Exact byte append reference binding and compiling unused-axiom controls."""
import hashlib
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
        raise SystemExit(f"Byte append audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


source = (ROOT / "Tests/ByteAppendRuntime.lean").read_text()
reference = source[source.index("def applyStmtOpBeforeByteAppend (s"):
                   source.index("theorem applyStmtOp_byteAppend_exact")]
reference = reference.rstrip() + "\n\n"
reference_hash = hashlib.sha256(reference.encode()).hexdigest()
# Exact c969079a operation definition; only its name changes in the test.
EXPECTED_REFERENCE_SHA256 = "849249acf7f47e27c4f8ce2deb6d0311e94cc06f291867c804f6ced6ebdef3d0"
if reference_hash != EXPECTED_REFERENCE_SHA256:
    raise SystemExit(f"Byte append audit: frozen reference body changed: {reference_hash}")

@managed_audit(ROOT, "byte-array-store-audit")
def main():
    directory = active_run().path
    print(f"Byte append audit scratch (released after evidence): {directory}", flush=True)
    harness = directory / "AuditAll.lean"
    harness.write_text("import Tests.ByteAppendAudit\n#eval auditByteAppend\n")
    (directory / "audit.log").write_text(run([str(ROOT / "scripts/capped"), "lean", str(harness)]))

    modules = ["GoLean.GoCore.ByteArrayStore", "GoLean.GoCore.Machine",
               "Tests.ByteAppendRuntime", "Tests.ByteAppendAudit"]
    for index, module in enumerate(modules):
        with active_run().fixture(str(index)) as fixture:
            package = module.split(".")[0]
            active_run().copy_package(ROOT / ".lake/build/lib/lean" / package, fixture / package)
            source = fixture / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            marker = f"byteAppendUnusedHole{index}"
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
                raise SystemExit(f"Byte append audit: {module} did not reject its compiled unused axiom")
            print(f"Byte append negative audit: {module} compiled then rejected ({marker})", flush=True)
            active_run().confirm(marker)


if __name__ == "__main__":
    main()
