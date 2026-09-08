#!/usr/bin/env python3
"""Post-import declaration audit with compiling, unused poison controls."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(args, env=None, expected=0, cwd=ROOT, log=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    print(result.stdout, end="", flush=True)
    if log is not None:
        log.write_text(result.stdout)
    if result.returncode != expected:
        raise SystemExit(f"Declaration audit: {args} exited {result.returncode}, expected {expected}")
    return result.stdout


def link_package(fixture, module):
    """Lean resolves a package at its first directory in LEAN_PATH.

    Give that directory aliases to unchanged artifacts, not copies. The poison
    module and ALL its sidecars are omitted: compilation must never write
    through a symlink into the worktree's real build outputs.
    """
    library = ROOT / ".lake/build/lib/lean"
    module_path = Path(module.replace(".", "/"))
    for original in (library / module.split(".")[0]).rglob("*"):
        relative = original.relative_to(library)
        target = fixture / relative
        if original.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        elif not (relative.parent == module_path.parent
                  and relative.name.startswith(module_path.name + ".")):
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(original)


def audit(directory):
    harness = directory / "AuditAll.lean"
    harness.write_text("import Tests.DeclarationAudit\n#eval auditDeclarations\n")
    run([str(ROOT / "scripts/capped"), "lean", str(harness)], log=directory / "audit.log")
    modules = ["GoLean.GoCore.Declaration", "GoLean.DeclarationUnicode",
               "GoLean.StrictJsonParse", "GoLean.NativeDeclaration",
               "Tests.DeclarationWire", "Tests.StrictJsonParse", "Tests.DeclarationUnicode",
               "Tests.DeclarationAudit"]
    for index, module in enumerate(modules):
        fixture = directory / str(index)
        link_package(fixture, module)
        source = fixture / (module.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        marker = f"declarationUnusedHole{index}"
        source.write_text((ROOT / (module.replace(".", "/") + ".lean")).read_text()
                          + f"\nprivate axiom {marker} : False\n")
        env = os.environ.copy()
        env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
        run([str(ROOT / "scripts/capped"), "lean", "-o",
             str(source.with_suffix(".olean")), str(source)], env=env, cwd=fixture,
            log=fixture / "compile.log")
        rejected = run([str(ROOT / "scripts/capped"), "lean", str(harness)], env=env,
                       expected=1, log=fixture / "audit.log")
        if "forbidden axiom" not in rejected or marker not in rejected:
            raise SystemExit(f"Declaration audit: {module} did not reject its compiled unused axiom")
        print(f"Declaration negative audit: {module} compiled then rejected ({marker})", flush=True)
    # Re-import without the overlay after the final poison as well: no poison
    # (including the last audit-module control) may leak into the real library.
    run([str(ROOT / "scripts/capped"), "lean", str(harness)], log=directory / "clean-after.log")


parent = ROOT / ".tmp"
parent.mkdir(parents=True, exist_ok=True)
directory = Path(tempfile.mkdtemp(prefix="declaration-audit-", dir=parent))
print(f"Declaration audit scratch: {directory}", flush=True)
try:
    audit(directory)
except BaseException as error:
    (directory / "failure.txt").write_text(str(error) + "\n")
    print(f"Declaration audit FAILED; scratch retained: {directory}", flush=True)
    raise
else:
    owned_bytes = sum(p.stat().st_size for p in directory.rglob("*")
                      if p.is_file() and not p.is_symlink())
    # Only this invocation's newly allocated scratch is removed, after success.
    # rmtree unlinks the aliases; it never follows them into the real library.
    shutil.rmtree(directory)
    print(f"Declaration audit PASS; scratch removed ({owned_bytes} owned bytes; dependencies symlinked)", flush=True)
