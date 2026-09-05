"""Reproduce the independent review's handler-store mutation in isolated scratch."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

pkg = Path.cwd()
root = pkg.parents[1]
scratch = Path(tempfile.mkdtemp(prefix="iris-review-mutant-", dir=root / ".tmp"))
shutil.copytree(pkg / ".lake/build/lib/lean/GoLeanIris", scratch / "GoLeanIris", symlinks=True)

source = (pkg / "GoLeanIris/Program.lean").read_text()
needle = "(GoLean.GoCore.Expr.boolLit true)"
assert source.count(needle) == 2
program = scratch / "GoLeanIris/Program.lean"
program.write_text(source.replace(needle, "(GoLean.GoCore.Expr.boolLit false)", 1))
examples = scratch / "GoLeanIris/Examples.lean"
examples.write_text((pkg / "GoLeanIris/Examples.lean").read_text())

env = os.environ.copy()
env["LEAN_PATH"] = str(scratch) + os.pathsep + env.get("LEAN_PATH", "")
command = [str(root / "scripts/capped"), "lean", f"--root={scratch}"]
r = subprocess.run(command + ["-o", str(program.with_suffix(".olean")), str(program)],
                   env=env, capture_output=True, text=True, timeout=120)
(scratch / "program.log").write_text(r.stdout + r.stderr)
print("mutated Program:", r.returncode)
assert r.returncode == 0
r = subprocess.run(command + [str(examples)], env=env, capture_output=True,
                   text=True, timeout=120)
output = r.stdout + r.stderr
(scratch / "examples.log").write_text(output)
print("unchanged Examples:", r.returncode)
print(output)
assert r.returncode == 1
assert "normalizeValueForTy" in output and "GoValue.bool false" in output
assert "Except.ok (GoValue.bool true)" in output
print("Retained scratch:", scratch)
