"""Invocation-owned post-import audit controls for the restored typed gates.

[AGENT] 2026-09-08. Adapted from the reviewed declaration audit at dc83782d.
The declarations audited and the poison lists live in each family wrapper.
"""
from contextlib import contextmanager
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


@contextmanager
def scratch(root, label):
    parent = root / ".tmp"
    parent.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix=label + "-", dir=parent))
    reason = directory / "failure.txt"
    reason.write_text("Invocation has not completed (interruption or failure).\n")
    print(f"{label} scratch: {directory}", flush=True)
    try:
        yield directory
    except BaseException as error:
        reason.write_text(f"{type(error).__name__}: {error}\n")
        print(f"{label} FAILED; scratch retained: {directory}", flush=True)
        raise
    else:
        owned = sum(p.stat().st_size for p in directory.rglob("*")
                    if p.is_file() and not p.is_symlink())
        shutil.rmtree(directory)
        print(f"{label} PASS; scratch removed ({owned} owned bytes; dependencies symlinked)",
              flush=True)


def run_logged(args, log, *, env=None, cwd=ROOT, expected=0):
    try:
        result = subprocess.run(args, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                timeout=180)
    except subprocess.TimeoutExpired as error:
        output = error.stdout or b""
        if isinstance(output, bytes):
            output = output.decode(errors="replace")
        log.write_text(output + "\nAudit subprocess exceeded 180 seconds.\n")
        raise RuntimeError(f"audit subprocess timeout: {args}; log: {log}") from error
    log.write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    if result.returncode != expected:
        raise RuntimeError(f"{args} exited {result.returncode}, expected {expected}; log: {log}")
    return result.stdout


def link_package(root, fixture, module):
    """Overlay the first package root; exclude the poison and ALL sidecars.

    Lean chooses the first package directory on LEAN_PATH. A partial overlay
    hides its siblings; copying everything leaks hundreds of MB per control.
    Never alias outputs that compilation might overwrite.
    """
    library = root / ".lake/build/lib/lean"
    module_path = Path(module.replace(".", "/"))
    package = library / module.split(".")[0]
    if not (library / module_path).with_suffix(".olean").is_file():
        raise RuntimeError(f"poison target has no built olean: {module}")
    for original in package.rglob("*"):
        relative = original.relative_to(library)
        target = fixture / relative
        if original.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        elif not (relative.parent == module_path.parent
                  and relative.name.startswith(module_path.name + ".")):
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(original)


def audit_main(family, harness_source, mutations):
    # Lists are intentionally concrete in the family wrappers. Both kinds of
    # negative must be present; a source parser failure is never a control PASS.
    if not any("private axiom " in row[3] for row in mutations):
        raise RuntimeError(f"{family}: missing private-axiom control")
    if not any("by sorry" in row[3] for row in mutations):
        raise RuntimeError(f"{family}: missing proof-hole control")
    if len({row[0] for row in mutations}) != len(mutations):
        raise RuntimeError(f"{family}: duplicate control label")
    with scratch(ROOT, family + "-audit") as directory:
        harness = directory / "AuditAll.lean"
        harness.write_text(harness_source)
        run_logged([str(ROOT / "scripts/capped"), "lean", str(harness)],
                   directory / "audit.log")
        for label, module, marker, poison in mutations:
            fixture = directory / label
            link_package(ROOT, fixture, module)
            source = fixture / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text((ROOT / (module.replace(".", "/") + ".lean")).read_text()
                              + poison)
            env = os.environ.copy()
            env["LEAN_PATH"] = str(fixture) + os.pathsep + env.get("LEAN_PATH", "")
            run_logged([str(ROOT / "scripts/capped"), "lean", "-o",
                        str(source.with_suffix(".olean")), str(source)],
                       fixture / "compile.log", env=env, cwd=fixture)
            rejected = run_logged([str(ROOT / "scripts/capped"), "lean", str(harness)],
                                  fixture / "audit.log", env=env, expected=1)
            declaration = re.search(r"private (?:axiom|theorem) (\w+)", poison)
            if declaration is None or not any(
                    "forbidden axiom" in line and marker in line
                    and declaration[1] in line for line in rejected.splitlines()):
                raise RuntimeError(f"{family}: {label} did not reject its compiled "
                                   f"declaration by name ({marker})")
            print(f"Typed audit control: {family}/{label} compiled then rejected "
                  f"({declaration[1]}, {marker})", flush=True)
        # The final poison is included in the leakage check, too.
        run_logged([str(ROOT / "scripts/capped"), "lean", str(harness)],
                   directory / "clean-after.log")
        print(f"Typed audit: {family}: {len(mutations)} compiled controls passed", flush=True)
