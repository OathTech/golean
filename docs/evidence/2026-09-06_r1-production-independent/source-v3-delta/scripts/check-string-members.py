#!/usr/bin/env python3
"""Fresh source tests and compiling mutation controls for R-1 apparatus.

The corpus itself is checked separately by scripts/ci --diff. This gate
does not import stored certificate verdicts or call a refusal conformance.
"""
import hashlib
import json
import os
from pathlib import Path
import py_compile
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCRATCH = Path(tempfile.mkdtemp(prefix="string-member-gate-", dir=ROOT/".tmp"))
ENV = os.environ.copy()
ENV.update(GO111MODULE="off", GOCACHE=str(ROOT/"artifacts/go-build-cache"))


def run(label, command, cwd=ROOT, env=ENV, wanted=0):
    result = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180)
    (SCRATCH/(label+".log")).write_bytes(result.stdout)
    print(result.stdout.decode(errors="backslashreplace"), end="", flush=True)
    if (wanted == 0 and result.returncode != 0) or (wanted == 1 and result.returncode == 0):
        raise SystemExit(f"{label}: unexpected exit {result.returncode}")
    return result


print(f"String member scratch retained: {SCRATCH}", flush=True)
files = [*sorted((ROOT/"tools/coverageharness").glob("*.go")),
         ROOT/"tools/string_member.py", ROOT/"tools/string_member_runner.py",
         ROOT/"tools/test_string_member.py", ROOT/"tools/check_string_member_fixtures.py", Path(__file__).resolve()]
hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(SCRATCH/"sources.json").write_text(json.dumps(hashes, indent=2)+"\n")
print(json.dumps(hashes, sort_keys=True), flush=True)
for p in files:
    if p.suffix == ".py":
        py_compile.compile(str(p), cfile=str(SCRATCH/(p.name+"c")), doraise=True)
run("go-unit", ["go", "test", "-count=1", "./tools/coverageharness"])
run("python-unit", [sys.executable, "-m", "unittest", "discover", "-s", "tools", "-p", "test_string_member.py", "-v"])
run("native-fixtures", [sys.executable, "tools/check_string_member_fixtures.py"])

# Mutated helpers must build as actual executables before the focused byte,
# kind and exit controls reject them; compilation failure is not rejection.
go_mutations = [
    ("drop-bytes", "MessageBytes: byteIntegers(view.message)", "MessageBytes: []int{}"),
    ("replace-high-byte", "values[i] = int(b)", "values[i] = int(b); if b > 127 { values[i] = 65533 }"),
    ("false-exit", 'Status: "panic", ChildExit: 2', 'Status: "panic", ChildExit: 1'),
    ("ignore-kind", 'if view.kind != "panic" {', 'if false {'),
]
for label, old, new in go_mutations:
    tree = SCRATCH/label
    shutil.copytree(ROOT/"tools/coverageharness", tree)
    source = tree/"observe.go"
    text = source.read_text()
    if text.count(old) != 1:
        raise SystemExit(f"{label}: mutation no longer targets exactly one expression")
    source.write_text(text.replace(old, new))
    run(label+"-compile", ["go", "build", "-o", str(tree/"helper"), "."], cwd=tree)
    rejected = run(label+"-reject", ["go", "test", "-count=1", "-run", "TestRawPanicRecord", "."], cwd=tree, wanted=1)
    if b"--- FAIL: TestRawPanicRecord" not in rejected.stdout:
        raise SystemExit(f"{label}: did not reach the raw-record assertions")
    print(f"String member negative: {label} compiled then rejected", flush=True)

python_mutations = [
    ("omit-main-entrypoint", '    "Main.lean",\n', ""),
    ("omit-golean-aggregator", '    "GoLean.lean",\n', ""),
    ("omit-inittask-table", '    "tools/nativefrontend/inittask-std.tsv",\n', ""),
    ("omit-stdlib-substitutions", '    "tools/nativefrontend/stdlib-substitutions.tsv",\n', ""),
    ("omit-stdlib-overlay", '    "tools/nativefrontend/stdlib-overlay.tsv",\n', ""),
    ("omit-stdlib-pin", '    "baselines/stdlib-pin.tsv",\n', ""),
    ("allow-unknown-keys", "require(set(obj) == set(wanted),", "require(set(wanted) <= set(obj),"),
    ("ignore-output", 'require(text(machine["output"], "machine output") == bytes(raw_go["outputBytes"]),', 'require(True,'),
    ("ignore-member", 'require(machine["message"] in selected_members(bytes(head["bytes"]), head["recovered"]),', 'require(True,'),
    ("ignore-duplicate-role", 'require(invocation not in invocations,', 'require(True,'),
    ("ignore-source-hash", 'require(actual == pinned,', 'require(set(actual) == set(pinned),'),
]
test_source = ROOT/"tools/test_string_member.py"
for label, old, new in python_mutations:
    tree = SCRATCH/label
    tree.mkdir()
    text = (ROOT/"tools/string_member.py").read_text()
    if text.count(old) != 1:
        raise SystemExit(f"{label}: mutation no longer targets exactly one expression")
    mutated = tree/"string_member.py"
    mutated.write_text(text.replace(old, new))
    py_compile.compile(str(mutated), cfile=str(tree/"checker.pyc"), doraise=True)
    command = [sys.executable, "-c",
               "import importlib.util,sys,unittest; "
               "sys.path.insert(0,sys.argv[1]); "
               "s=importlib.util.spec_from_file_location('contracts',sys.argv[2]); "
               "m=importlib.util.module_from_spec(s);s.loader.exec_module(m); "
               "r=unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromModule(m)); "
               "sys.exit(0 if r.wasSuccessful() else 1)", str(tree), str(test_source)]
    rejected = run(label+"-reject", command, wanted=1)
    if b"AssertionError: Refusal not raised" not in rejected.stdout:
        raise SystemExit(f"{label}: did not reach the intended contract rejection")
    print(f"String member negative: {label} compiled then rejected", flush=True)
if hashes != {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}:
    raise SystemExit("apparatus source changed during its gate")
print("String member apparatus PASS: fresh Go/Python tests; 4 compiled Go and 11 compiled Python mutation controls rejected", flush=True)
