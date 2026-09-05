from pathlib import Path
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
SCRATCH = Path(__file__).resolve().parent
FIXTURE = SCRATCH / "integrated-admission-private"
for tree in ["GoLean", "Tests"]:
    shutil.copytree(ROOT / ".lake/build/lib/lean" / tree, FIXTURE / tree)
source = FIXTURE / "GoLean/GoCore/Admission.lean"
source.write_text((ROOT / "GoLean/GoCore/Admission.lean").read_text() + "\nprivate axiom reviewedIntegratedAdmissionHole : False\n")

def lean(label, cwd, path, output=None):
    env = os.environ.copy()
    env["GOLEAN_MEM_MAX"] = "16G"
    env["LEAN_NUM_THREADS"] = "3"
    # Obtain each package's full Lake path, then put isolated replacements first.
    envout = subprocess.run([str(ROOT / "scripts/capped"), "lake", "env", "printenv", "LEAN_PATH"], cwd=cwd, env=env, check=True, text=True, capture_output=True)
    paths = []
    for entry in envout.stdout.strip().split(os.pathsep):
        p = Path(entry)
        paths.append(str(p if p.is_absolute() else cwd / p))
    env["LEAN_PATH"] = str(FIXTURE) + os.pathsep + os.pathsep.join(paths)
    args = [str(ROOT / "scripts/capped"), "lean", f"--root={FIXTURE}"]
    if output is not None:
        args += ["-o", str(output)]
    result = subprocess.run(args + [str(path)], cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    (SCRATCH / (label + ".log")).write_text(result.stdout + f"\nEXIT={result.returncode}\n")
    print(label, "exit", result.returncode, flush=True)
    print(result.stdout, flush=True)
    return result

compiled = lean("promoted-compile", ROOT, source, source.with_suffix(".olean"))
assert compiled.returncode == 0
for label, cwd, harness in [
    ("admission-own-rejection", ROOT, "import Tests.GoCoreAdmissionAudit\n#eval GoLeanAdmissionAudit.run\n"),
    ("promoted-core-rejection", ROOT, "import GoLean.Interface\nimport Tests.InterfaceAudit\n#eval InterfaceAudit.run\n"),
    ("promoted-a1-rejection", ROOT / "spikes/gate-a1", "import GateA1\n#eval GateA1Audit.run\n"),
    ("promoted-a2-rejection", ROOT / "spikes/iris-customer", "import GoLeanIris\n#eval GoLeanIrisAudit.run\n"),
]:
    probe = FIXTURE / (label.replace("-", "_") + ".lean")
    probe.write_text(harness)
    result = lean(label, cwd, probe)
    assert result.returncode == 1 and "forbidden axiom" in result.stdout and "reviewedIntegratedAdmissionHole" in result.stdout, label
print("Promoted Admission unused private axiom: compiled successfully and rejected by all four post-import audits.")
