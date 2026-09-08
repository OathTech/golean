#!/usr/bin/env python3
"""Fail-closed Tests/library ownership and actual named CI build receipts.

[AGENT] 2026-09-08. No allowlist. The registry drives real Lake targets;
the final check requires successful receipts from this invocation, not a
textual claim that a shell file contains a build command.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
import uuid

ROOT = Path(__file__).resolve().parents[1]


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate registry key: {key}")
        result[key] = value
    return result


def coverage(root):
    config = tomllib.loads((root / "lakefile.toml").read_text())
    if config.get("srcDir", ".") != ".":
        raise ValueError("package srcDir needs explicit coverage support")
    entries = config["lean_lib"]
    libraries = {entry["name"]: entry for entry in entries}
    if len(libraries) != len(entries):
        raise ValueError("duplicate Lake library name")
    executables = {entry["name"] for entry in config.get("lean_exe", [])}
    registry = json.loads((root / "scripts/ci-libraries.json").read_text(),
                          object_pairs_hook=unique_object)
    if not isinstance(registry, dict) or not registry:
        raise ValueError("CI library registry must be a nonempty object")
    built = {}
    for step, entry in registry.items():
        if not re.fullmatch(r"[a-z][a-z0-9-]*", step):
            raise ValueError(f"invalid named CI step: {step}")
        if not isinstance(entry, dict) or set(entry) != {"libraries", "executables"}:
            raise ValueError(f"invalid registry fields: {step}")
        for kind in ("libraries", "executables"):
            names = entry[kind]
            if not isinstance(names, list) or any(not isinstance(n, str) for n in names):
                raise ValueError(f"invalid {kind} in step {step}")
            if len(names) != len(set(names)):
                raise ValueError(f"duplicate {kind} in step {step}")
        if not entry["libraries"]:
            raise ValueError(f"named CI step {step} builds no library")
        for library in entry["libraries"]:
            if library not in libraries:
                raise ValueError(f"CI step {step} names undeclared library {library}")
            if library in built:
                raise ValueError(f"library {library} has multiple CI owners")
            built[library] = step
        for executable in entry["executables"]:
            if executable not in executables:
                raise ValueError(f"undeclared executable {executable} in {step}")
    missing = set(libraries) - set(built)
    if missing:
        raise ValueError(f"declared libraries lack named CI steps: {sorted(missing)}")
    owners = {}
    for library, entry in libraries.items():
        # Current Lake declarations use exact module globs. Fail closed on a
        # future glob/roots form instead of approximating Lake's semantics.
        if "roots" in entry:
            raise ValueError(f"library {library}: roots form needs coverage support")
        if entry.get("srcDir", ".") != ".":
            raise ValueError(f"library {library}: srcDir needs explicit coverage support")
        globs = entry.get("globs", [library])
        if not isinstance(globs, list) or not globs:
            raise ValueError(f"library {library}: expected nonempty module globs")
        for module in globs:
            if not isinstance(module, str) or not re.fullmatch(r"[A-Za-z_][\w]*(?:\.[A-Za-z_]\w*)*", module):
                raise ValueError(f"library {library}: unsupported module glob {module!r}")
            source = root / (module.replace(".", "/") + ".lean")
            if not source.is_file() or source.is_symlink():
                raise ValueError(f"library {library}: missing or aliased source {module}")
            if module.startswith("Tests."):
                if module in owners:
                    raise ValueError(f"Tests module {module} belongs to multiple libraries")
                owners[module] = library
    tests = set()
    for path in (root / "Tests").rglob("*"):
        if path.is_symlink() or any(parent.is_symlink() for parent in path.parents if parent != root):
            raise ValueError(f"aliased Tests source: {path}")
        if path.suffix != ".lean":
            continue
        tests.add(".".join(path.relative_to(root).with_suffix("").parts))
    if not tests:
        raise ValueError("Tests module inventory is empty")
    if tests != set(owners):
        raise ValueError(f"Tests/library mismatch: unowned={sorted(tests-set(owners))}, "
                         f"absent={sorted(set(owners)-tests)}")
    digest = hashlib.sha256()
    for path in [root / "lakefile.toml", root / "scripts/ci-libraries.json"]:
        digest.update(path.read_bytes())
    digest.update(json.dumps(sorted(tests)).encode())
    return registry, {"libraries": len(libraries), "test_modules": len(tests),
                      "steps": len(registry), "fingerprint": digest.hexdigest()}


def initialize(root):
    _, stats = coverage(root)
    (root / ".tmp").mkdir(exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="ci-libraries-", dir=root / ".tmp"))
    state = {"run_id": uuid.uuid4().hex, "started": time.time(), **stats}
    (directory / "state.json").write_text(json.dumps(state))
    (directory / "failure.txt").write_text("CI invocation has not completed.\n")
    return directory


def load_run(root, directory):
    if (directory.is_symlink() or directory.parent != root / ".tmp"
            or not directory.name.startswith("ci-libraries-")):
        raise ValueError("CI receipts must be in an invocation-owned local directory")
    state = json.loads((directory / "state.json").read_text())
    registry, stats = coverage(root)
    if state["fingerprint"] != stats["fingerprint"]:
        raise ValueError("library coverage changed during this CI invocation")
    return registry, state


def build_targets(entry):
    # A bare library target honors defaultFacets=[] and may check no Lean at
    # all. Request the pinned Lake leanArts facet explicitly (author finding F1).
    return [name + ":leanArts" for name in entry["libraries"]] + entry["executables"]


def run_step(root, directory, step, command, *, runner=subprocess.run):
    registry, state = load_run(root, directory)
    if step not in registry:
        raise ValueError(f"unregistered CI library step: {step}")
    path = directory / (step + ".json")
    if path.exists():
        raise ValueError(f"CI library step executed twice: {step}")
    entry = registry[step]
    targets = build_targets(entry)
    started = time.monotonic()
    build = runner([str(root / "scripts/capped"), "lake", "build", *targets], cwd=root)
    built = time.monotonic()
    code = build.returncode
    if code == 0 and command:
        code = runner(command, cwd=root).returncode
    finished = time.monotonic()
    receipt = {"run_id": state["run_id"], "fingerprint": state["fingerprint"],
               "step": step, "libraries": entry["libraries"], "targets": targets,
               "exit_code": code, "build_seconds": built-started,
               "check_seconds": finished-built, "elapsed_seconds": finished-started}
    path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"CI library step {step}: exit={code}, seconds={finished-started:.3f}", flush=True)
    return code


def verify(root, directory):
    registry, state = load_run(root, directory)
    receipts = []
    for step, entry in registry.items():
        path = directory / (step + ".json")
        if not path.is_file():
            raise ValueError(f"named CI step did not run: {step} ({entry['libraries']})")
        receipt = json.loads(path.read_text())
        expected = {"run_id": state["run_id"], "fingerprint": state["fingerprint"],
                    "step": step, "libraries": entry["libraries"],
                    "targets": build_targets(entry), "exit_code": 0}
        if any(receipt.get(k) != value for k, value in expected.items()):
            raise ValueError(f"CI step has a failed, stale or mismatched build receipt: {step}")
        receipts.append(receipt)
    return {**state, "elapsed_wall_seconds": time.time()-state["started"], "receipts": receipts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["check", "init", "selftests", "run", "verify", "close"])
    parser.add_argument("args", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.action == "check" and not args.args:
        _, stats = coverage(ROOT)
        print("Tests/library coverage: PASS " + json.dumps(stats, sort_keys=True))
    elif args.action == "init" and not args.args:
        print(initialize(ROOT))
    elif args.action == "selftests" and not args.args:
        for script in ["test_ci_libraries.py", "test_typed_audit.py"]:
            result = subprocess.run([sys.executable, str(ROOT / "tools" / script)], cwd=ROOT)
            if result.returncode:
                return result.returncode
    elif args.action == "run" and len(args.args) >= 2:
        directory, step, *command = args.args
        return run_step(ROOT, Path(directory), step, command)
    elif args.action == "verify" and len(args.args) == 1:
        directory = Path(args.args[0])
        summary = verify(ROOT, directory)
        output = ROOT / "artifacts/ci-library-timings"
        output.mkdir(parents=True, exist_ok=True)
        path = output / (summary["run_id"] + ".json")
        path.write_text(json.dumps(summary, indent=2) + "\n")
        print(f"Executed library coverage: PASS; {summary['libraries']} libraries, "
              f"{summary['test_modules']} Tests modules, {summary['steps']} named steps; timings: {path}")
    elif args.action == "close" and len(args.args) == 2:
        directory, code = Path(args.args[0]), int(args.args[1])
        load_run(ROOT, directory)
        if code == 0:
            verify(ROOT, directory)
            shutil.rmtree(directory)
        else:
            (directory / "failure.txt").write_text(f"scripts/ci failed or was interrupted, exit {code}.\n")
            print(f"Failed CI receipts retained: {directory}", file=sys.stderr)
    else:
        parser.error("invalid argument count for action")
    return 0


if __name__ == "__main__":
    started = time.monotonic()
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"CI library coverage: FAIL: {error}", file=sys.stderr)
        sys.exit(1)
    finally:
        if len(sys.argv) > 1 and sys.argv[1] in {"init", "selftests", "verify", "close"}:
            print(f"CI coverage timing: {sys.argv[1]}: seconds={time.monotonic()-started:.3f}",
                  file=sys.stderr, flush=True)
