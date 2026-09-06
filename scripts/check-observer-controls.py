"""Fresh source-bound Go observer tests, shell transport probes, and mutations.

The fake oracle tests transport/classification only; it is never conformance
evidence. Native corpus rows provide the separate real-Go differential gate.
Scratch and every compiled mutant are retained for audit.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
ENV = dict(os.environ, GO111MODULE="off", GOCACHE=str(ROOT / "artifacts/go-build-cache"))


def run(args, *, cwd=ROOT, env=ENV):
    result = subprocess.run(args, cwd=cwd, env=env, capture_output=True, timeout=180)
    return result


def require(result, label):
    print(result.stdout.decode(errors="backslashreplace"), end="", flush=True)
    print(result.stderr.decode(errors="backslashreplace"), end="", flush=True)
    if result.returncode:
        raise SystemExit(f"{label}: exit {result.returncode}")


def main():
    paths = sorted([*ROOT.glob("tools/coverageharness/*.go"),
                    *ROOT.glob("Corpus/coverage/exec/panic-recover/panic-controls/*"),
                    ROOT / "scripts/diff-coverage", ROOT / "scripts/ci", Path(__file__)])
    for path in paths:
        print(hashlib.sha256(path.read_bytes()).hexdigest(), path.relative_to(ROOT), flush=True)
    scratch = Path(tempfile.mkdtemp(prefix="observer-controls-", dir=os.environ.get("TMPDIR")))
    print(f"Observer scratch: {scratch}", flush=True)
    harness = scratch / "coverageharness"
    require(run(["go", "build", "-o", str(harness), "./tools/coverageharness"]), "fresh harness build")
    require(run(["go", "test", "-count=1", "-v", "./tools/coverageharness"]), "observer Go tests")

    # Exercise the REAL exported shell functions, including go_run_oracle's
    # raw descriptor files and membership/confluent classification. Only
    # `go run .` is replaced; no observer function is reimplemented here.
    source = (ROOT / "scripts/diff-coverage").read_text()
    names = ["run_with_timeout", "go_run_oracle", "go_diagnostics", "membership_go_observation",
             "member_status_allowed", "undecided_cause", "signal_cause", "obs_eq_cause",
             "obs_eq", "lean", "one_line", "attach_output"]
    functions = []
    for name in names:
        match = re.search(rf"^{name}\(\) \{{\n.*?^\}}", source, re.M | re.S)
        if not match:
            raise SystemExit(f"missing runner function {name}")
        functions.append(match.group())
    script = scratch / "sample.sh"
    # Use the exact strict classification block as well, stopping before
    # frontend/model execution. Fail if its boundaries change, rather than
    # accidentally testing a copied implementation. The only stub is row
    # reporting (the probe asserts its stage and named refusal below).
    begin = source.index("  local go_rc=0 go_valid_rc=0 go_cause go_valid_cause\n")
    end = source.index('  if [[ "$failed" -ne 0 ]]; then\n', begin)
    strict = ("strict_probe() {\n local go_observation failed=0\n" + source[begin:end] +
              '\n if [[ "$failed" -ne 0 ]]; then return 1; fi\n printf "%s" "$go_observation"\n}\n')
    script.write_text("set -uo pipefail\n" + "\n".join(functions) + "\n" + strict +
                      'report_fail() { printf "stage=%s detail=%s" "$3" "$4"; }\n' +
                      'if [[ "$PROBE_LANE" == strict ]]; then strict_probe; else membership_go_observation; fi\n')
    fakebin = scratch / "fakebin"
    fakebin.mkdir()
    fakego = fakebin / "go"
    fakego.write_text("#!/usr/bin/env python3\nimport os,sys\nfrom pathlib import Path\n"
                      "sys.stdout.buffer.write(Path(os.environ['PROBE_STDOUT']).read_bytes())\n"
                      "sys.stderr.buffer.write(Path(os.environ['PROBE_STDERR']).read_bytes())\n"
                      "sys.exit(int(os.environ['PROBE_RC']))\n")
    fakego.chmod(0o755)
    trace = b"\n\ngoroutine 1 [running]:\nmain.main()\nexit status 2\n"
    controls = b"a\x00\x01\t\r"
    ok = b'{"schema":"golean-observation-v1","status":"ok","values":[]}'
    probes = [
        ("panic-controls", b"", b"out\x00\x01\n" + b"panic: " + controls + b"\n\tsecond" + trace,
         1, "panic", "a", {"message": controls.decode(), "output": "out\x00\x01\n"}),
        ("mixed-status-panic", b"", b"panic: " + controls + trace,
         1, "ok", "-", {"message": controls.decode(), "output": ""}),
        ("ok-controls", ok, controls + b"\n", 0, "ok", "-", {"output": controls.decode() + "\n"}),
        ("nul-stdout", b"\x00" + ok, b"", 0, "ok", "-", "not a valid observation"),
        ("soh-stdout", b'{"x":"a\x01b"}', b"", 0, "ok", "-", "not a valid observation"),
        ("invalid-utf8-stdout", b'{"x":"\xff"}', b"", 0, "ok", "-", "UTF-8"),
        ("stdout-marker", b"panic: a" + trace, b"no report\n", 1, "panic", "a", "expected Go panic"),
        ("stdout-reason", b"wanted", b"panic: other" + trace, 1, "panic", "wanted", "expected reason"),
        ("nul-reason", b"", b"panic: a\x00b" + trace, 1, "panic", "ab", "expected reason"),
        ("ambiguous", b"", b"panic: fake\npanic: a" + trace, 1, "panic", "a", "ambiguous"),
        ("invalid-utf8-panic", b"", b"panic: a\xff" + trace, 1, "panic", "a", "UTF-8"),
        ("killed", b"", b"panic: a" + trace, 137, "panic", "a", "KILLED"),
    ]
    probes = [("sampling", *p) for p in probes] + [("strict", *p) for p in probes if p[0] != "mixed-status-panic"]
    probes += [
        ("strict", "fatal-controls", b"", b"fatal error: " + controls + trace, 1, "fatal", "a",
         {"message": controls.decode(), "output": ""}),
        ("strict", "fatal-continuation", b"", b"out\x00\n" + b"panic: old [recovered]\n\tfatal error: " + controls + trace,
         1, "fatal", "a", {"message": controls.decode(), "output": "out\x00\n"}),
        ("strict", "fatal-wrong-exit", b"", b"fatal error: a" + trace.replace(b"exit status 2", b"exit status 3"),
         1, "fatal", "a", "exit status 2"),
    ]
    for lane, label, stdout, stderr, rc, status, reason, expected in probes:
        label = lane + "-" + label
        case = scratch / label
        case.mkdir()
        (case / "stdout").write_bytes(stdout)
        (case / "stderr").write_bytes(stderr)
        env = dict(ENV, PATH=str(fakebin) + os.pathsep + ENV["PATH"],
                   PROBE_STDOUT=str(case / "stdout"), PROBE_STDERR=str(case / "stderr"), PROBE_RC=str(rc), PROBE_LANE=lane,
                   HARNESS_BIN=str(harness), go_run_dir=str(case), expected_status=status,
                   expected_reason=reason, statuses="ok+panic", GO_TIMEOUT_SECONDS="10",
                   GO_BUILD_CACHE=ENV["GOCACHE"], GOLEAN_BIN=str(ROOT / ".lake/build/bin/golean"),
                   LEAN_TIMEOUT_SECONDS="10", OBS_EQ_STDERR="", id="probe", features="observer")
        result = run(["bash", str(script)], env=env)
        (case / "result.stdout").write_bytes(result.stdout)
        (case / "result.stderr").write_bytes(result.stderr)
        if (case / "oracle.stdout").read_bytes() != stdout or (case / "oracle.stderr").read_bytes() != stderr:
            raise SystemExit(f"{label}: raw descriptor files changed")
        if b"ignored null byte" in result.stderr:
            raise SystemExit(f"{label}: raw bytes entered shell substitution")
        if isinstance(expected, dict):
            require(result, label)
            got = json.loads(result.stdout)
            if any(got.get(key) != value for key, value in expected.items()):
                raise SystemExit(f"{label}: decoded bytes differ: {got!r}")
        elif result.returncode != 1 or expected.encode() not in result.stdout:
            raise SystemExit(f"{label}: expected named refusal {expected}: {result!r}")
        if lane == "strict" and not isinstance(expected, dict):
            stage = "go-run" if label in ["strict-stdout-marker", "strict-killed", "strict-fatal-wrong-exit"] else "go-observation"
            if ("stage=" + stage).encode() not in result.stdout:
                raise SystemExit(f"{label}: refusal reported wrong stage: {result.stdout!r}")
        print(f"Shell observer probe: {label} PASS", flush=True)

    # Each mutation must COMPILE before its targeted behavioral test rejects
    # it; a syntax/import failure is not evidence that a gate works.
    for label, filename, before, after, test in [
        ("drop-nul", "split.go", "enc.Encode(string(prefix))", 'enc.Encode(strings.ReplaceAll(string(prefix), "\\x00", ""))', "TestAbortMessageBytes"),
        ("raw-soh", "split.go", 'strings.TrimSuffix(sb.String(), "\\n")', 'strings.ReplaceAll(strings.TrimSuffix(sb.String(), "\\n"), `\\u0001`, "\\x01")', "TestAbortMessageBytes"),
        ("trim-cr", "split.go", "enc.Encode(string(prefix))", "enc.Encode(strings.TrimSpace(string(prefix)))", "TestAbortMessageBytes"),
        ("mask-stdout-nul", "observe.go", "func observationText(stdout []byte) (string, error) {", 'func observationText(stdout []byte) (string, error) {\nstdout = bytes.ReplaceAll(stdout, []byte{0}, nil)', "TestRawStdoutRefusals"),
    ]:
        mutant = scratch / label
        shutil.copytree(ROOT / "tools/coverageharness", mutant)
        path = mutant / filename
        text = path.read_text()
        if text.count(before) != 1:
            raise SystemExit(f"{label}: mutation anchor count changed")
        path.write_text(text.replace(before, after))
        binary = mutant / "tests"
        require(run(["go", "test", "-c", "-o", str(binary), "."], cwd=mutant), label + " compile")
        result = run([str(binary), "-test.run", "^" + test + "$"], cwd=mutant)
        print(result.stdout.decode(errors="backslashreplace"), end="", flush=True)
        if result.returncode != 1 or ("--- FAIL: " + test).encode() not in result.stdout:
            raise SystemExit(f"{label}: compiling mutation was not behaviorally rejected")
        print(f"Observer mutation: {label} rejected after successful compile", flush=True)
    print("Observer controls: PASS", flush=True)


if __name__ == "__main__":
    main()
