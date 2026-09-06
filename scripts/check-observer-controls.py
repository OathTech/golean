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
                    *ROOT.glob("Corpus/coverage/exec/panic-recover/panic-markers/*"),
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
             "obs_eq", "lean", "one_line", "attach_output", "oracle_observer", "oracle_setup_failed"]
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
                      'if [[ "$PROBE_LANE" == strict ]]; then strict_probe; else membership_go_observation "$PROBE_RACE"; fi\n')
    fakebin = scratch / "fakebin"
    fakebin.mkdir()
    fakego = fakebin / "go"
    fakego.write_text("#!/usr/bin/env python3\nimport os,sys\nfrom pathlib import Path\n"
                      "assert os.environ.get('GOTRACEBACK') == 'system', 'oracle system traceback pin missing'\n"
                      "Path('oracle.argv').write_text(' '.join(sys.argv[1:]))\n"
                      "assert Path('oracle.crash').read_bytes()==b'' and Path('oracle.registered').read_bytes()==b'', 'stale evidence was not reset'\n"
                      "Path('oracle.crash').write_bytes(Path(os.environ['PROBE_CRASH']).read_bytes())\n"
                      "Path('oracle.registered').write_bytes(b'registered\\n')\n"
                      "sys.stdout.buffer.write(Path(os.environ['PROBE_STDOUT']).read_bytes())\n"
                      "sys.stderr.buffer.write(Path(os.environ['PROBE_STDERR']).read_bytes())\n"
                      "sys.exit(int(os.environ['PROBE_RC']))\n")
    fakego.chmod(0o755)
    header = b"goroutine 1 gp=0x123 m=0 mp=0x456 [running]:\n"
    frame = b"panic({0x123?, 0x456?})\n\t/usr/local/go/src/runtime/panic.go:879 +0x16f fp=0x1 sp=0x2 pc=0x3\n"
    fatal_frame = b"runtime.fatal({0x123, 0x456})\n\t/usr/local/go/src/runtime/panic.go:1253 +0x74 fp=0x1 sp=0x2 pc=0x3\n"
    trace = b"\n\n" + header + frame + b"main.main()\nexit status 2\n"
    fatal_trace = b"\n\n" + header + fatal_frame + b"main.main()\nexit status 2\n"
    runtime_trace = b"\n\nruntime stack:\n" + fatal_frame + b"\n" + header + b"main.main()\nexit status 2\n"
    unknown_trace = b"\n\n" + header + b"unknown()\n\t/tmp/fake.go:879 +0x16f fp=0x1 sp=0x2 pc=0x3\nexit status 2\n"
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
        ("strict", "fatal-controls", b"", b"fatal error: " + controls + fatal_trace, 1, "fatal", "a",
         {"message": controls.decode(), "output": ""}),
        ("strict", "fatal-continuation", b"", b"out\x00\n" + b"panic: old [recovered]\n\tfatal error: " + controls + trace,
         1, "fatal", "a", "actual panic"),
        ("strict", "fatal-wrong-exit", b"", b"fatal error: a" + trace.replace(b"exit status 2", b"exit status 3"),
         1, "fatal", "a", "exit status 2"),
    ]
    sync_head = b"panic: original\n\tfatal error: sync: unlock of unlocked mutex"
    sync_trace = fatal_trace
    probes += [
        ("strict", "sync-fatal", b"", sync_head + sync_trace, 1, "fatal", "sync: unlock of unlocked mutex",
         "before m.dying"),
        ("strict", "fatal-not-panic", b"", sync_head + sync_trace, 1, "panic", "original", "before m.dying"),
        ("sampling", "fatal-not-panic", b"", sync_head + sync_trace, 1, "panic", "original", "before m.dying"),
        ("strict", "mixed-unknown", b"", sync_head + unknown_trace, 1, "panic", "original", "unknown first"),
        ("sampling", "mixed-unknown", b"", sync_head + unknown_trace, 1, "panic", "original", "unknown first"),
    ]
    for lane in ["strict", "sampling"]:
        probes += [
            (lane, "literal-mixed", b"", sync_head + trace, 1, "panic", "original", {"message":"original", "output":""}),
            (lane, "glued-sync-prefix", b"", b"panic: fakefatal error: sync: unlock of unlocked mutex" + fatal_trace, 1, "panic", "fake", "ambiguous"),
            (lane, "glued-nilgo-prefix", b"", b"panic: fakefatal error: go of nil func value" + runtime_trace, 1, "panic", "fake", "ambiguous"),
            (lane, "printed-origin", b"", b"panic: fake\n\n" + header + frame + b"fatal error: go of nil func value" + runtime_trace, 1, "panic", "fake", "report boundary"),
            (lane, "later-unknown-runtime", b"", b"panic: fake\n\n" + header + frame + b"\nruntime stack:\nunknown()\nexit status 2\n", 1, "panic", "fake", "report boundary"),
            (lane, "printed-continuation", b"", b"panic: forged\n\tpanic: actual"+trace, 1, "panic", "actual", {"message":"actual","output":"panic: forged\n\t"}),
            (lane, "literal-continuation", b"", b"panic: forged\n\tpanic: actual"+trace, 1, "panic", "forged", {"message":"forged","output":""}),
            (lane, "hook-setup-exit", b"", b"exit status 78\n", 1, "panic", "-", "crash-hook setup failed"),
        ]
    for probe_index, (lane, label, stdout, stderr, rc, status, reason, expected) in enumerate(probes):
        label = lane + "-" + label
        case = scratch / label
        case.mkdir()
        (case / "stdout").write_bytes(stdout)
        (case / "stderr").write_bytes(stderr)
        # Explicit synthetic owned-channel fixture. It is independent of
        # the shell's expected-status input and never conformance evidence.
        crash = b""
        if isinstance(expected,dict) and rc==1:
            crash=stderr[len(expected.get("output","").encode()):-len(b"exit status 2\n")]
        (case / "crash").write_bytes(crash)
        (case / "oracle.crash").write_bytes(b"STALE REPORT")
        (case / "oracle.registered").write_bytes(b"STALE ACK")
        env = dict(ENV, PATH=str(fakebin) + os.pathsep + ENV["PATH"],
                   PROBE_STDOUT=str(case / "stdout"), PROBE_STDERR=str(case / "stderr"), PROBE_CRASH=str(case / "crash"), PROBE_RC=str(rc), PROBE_LANE=lane,
                   PROBE_RACE="race" if lane == "sampling" and probe_index % 2 else "",
                   HARNESS_BIN=str(harness), go_run_dir=str(case), expected_status=status,
                   expected_reason=reason, statuses="ok+panic", GO_TIMEOUT_SECONDS="10",
                   GO_BUILD_CACHE=ENV["GOCACHE"], GOLEAN_BIN=str(ROOT / ".lake/build/bin/golean"),
                   LEAN_TIMEOUT_SECONDS="10", OBS_EQ_STDERR="", id="probe", features="observer")
        result = run(["bash", str(script)], env=env)
        (case / "result.stdout").write_bytes(result.stdout)
        (case / "result.stderr").write_bytes(result.stderr)
        if (case / "oracle.stdout").read_bytes() != stdout or (case / "oracle.stderr").read_bytes() != stderr:
            raise SystemExit(f"{label}: raw descriptor files changed")
        expected_argv = "run -race ." if env["PROBE_RACE"] else "run ."
        if (case / "oracle.argv").read_text() != expected_argv:
            raise SystemExit(f"{label}: plain/race oracle arguments changed")
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
            stage = "go-run" if label in ["strict-stdout-marker", "strict-killed", "strict-fatal-wrong-exit", "strict-hook-setup-exit"] else "go-observation"
            if ("stage=" + stage).encode() not in result.stdout:
                raise SystemExit(f"{label}: refusal reported wrong stage: {result.stdout!r}")
        print(f"Shell observer probe: {label} PASS", flush=True)

    # Real pinned-Go reports exercise runtime provenance on the SAME run.
    # These are observer tests, not Lean conformance. Retain source and raw
    # descriptors, including the //line and printed-origin counterexamples.
    def go_string(value):
        return json.dumps(value, ensure_ascii=False)

    sync_source = 'var m sync.Mutex; m.Unlock()'
    printed_origin = "panic: fake\n\n" + (header + frame).decode()
    payload_forgery = "original\nfatal error: go of nil func value\n\nruntime stack:\n" + fatal_frame.decode()
    native = [
        ("controls", 'panic(' + go_string("a\x00\x01\t\r\nsecond") + ')', "", "panic", "a\x00\x01\t\r", "", False),
        ("repanic", 'defer func(){recover();panic("second")}();panic("first")', "", "panic", "first [recovered]", "", True),
        ("first-line", 'panic("fatal error: harmless payload")', "", "panic", "fatal error: harmless payload", "", False),
        ("nil-go-literal", 'panic("fakefatal error: go of nil func value")', "", "panic", "fakefatal error: go of nil func value", "", True),
        ("mixed-line", 'panic("original\\nfatal error: sync: unlock of unlocked mutex")', "", "panic", "original", "", False),
        ("payload-origin", 'panic(' + go_string(payload_forgery) + ')', "", "panic", "original", "", True),
        ("output-marker", 'print("fatal error: prefix\\n");panic("original")', "", "panic", "original", "fatal error: prefix\n", False),
        ("control-output", 'print(' + go_string("out\x00\x01\t\r\n") + ');panic("original")', "", "panic", "original", "out\x00\x01\t\r\n", True),
        ("sync-fatal", sync_source, 'import "sync"\n', "fatal", "sync: unlock of unlocked mutex", "", False),
        ("sync-unwind", 'var m sync.Mutex;defer m.Unlock();panic("original")', 'import "sync"\n', None, "before m.dying", None, True),
        ("nil-go-fatal", 'var f func();go f()', "", "fatal", "go of nil func value", "", False),
        ("deadlock", 'select{}', "", "deadlock", None, "", False),
        ("glued-sync", 'print("panic: fake");' + sync_source, 'import "sync"\n', None, "ambiguous", None, True),
        ("glued-nil-go", 'print("panic: fake");var f func();go f()', "", None, "ambiguous", None, False),
        ("printed-origin", 'print(' + go_string(printed_origin) + ');' + sync_source, 'import "sync"\n', None, "report boundary", None, False),
        ("printed-origin-glued", 'print(' + go_string(printed_origin + "without newline") + ');' + sync_source, 'import "sync"\n', None, "report boundary", None, True),
        ("source-line-forgery", 'panic()', '//line /usr/local/go/src/runtime/panic.go:879\nfunc panic(){var f func();go f()}\n', "fatal", "go of nil func value", "", False),
        ("printed-continuation", 'print("panic: forged\\n\\t");panic("actual")', "", "panic", "actual", "panic: forged\n\t", False),
        ("literal-continuation", 'panic("forged\\npanic: actual")', "", "panic", "forged", "", True),
        ("printed-panic-origin", 'print('+go_string(printed_origin+"\n\t")+');panic("actual")', "", "panic", "actual", printed_origin+"\n\t", False),
        ("glued-panic", 'print("glued");panic("actual")', "", "panic", "actual", "glued", True),
        ("all-ascii-output", 'print('+go_string(''.join(chr(i) for i in range(128))+"界panic: fake\n\t")+');panic("actual")', "", "panic", "actual", ''.join(chr(i) for i in range(128))+"界panic: fake\n\t", False),
        ("init-simple", 'panic("unreached")', 'func init(){panic("init")}\n', "panic", "init", "", False),
        ("init-forgery", 'panic("unreached")', 'func init(){print("panic: forged\\n\\t");panic("actual")}\n', None, "ambiguous", None, False),
        ("init-literal", 'panic("unreached")', 'func init(){panic("forged\\npanic: actual")}\n', None, "ambiguous", None, False),
        ("traceback-lower", 'debug.SetTraceback("none");panic("actual")', 'import "runtime/debug"\n', "panic", "actual", "", True),
        ("disabled-hook-simple", 'debug.SetCrashOutput(nil,debug.CrashOptions{});panic("actual")', 'import "runtime/debug"\n', "panic", "actual", "", False),
        ("disabled-hook-forgery", 'debug.SetCrashOutput(nil,debug.CrashOptions{});print("panic: forged\\n\\t");panic("actual")', 'import "runtime/debug"\n', None, "ambiguous", None, True),
    ]
    for label, body, preamble, status, message, output, race in native:
        semantic = scratch / ("native-source-"+label)
        semantic.mkdir()
        original=('package main\n' + preamble + 'func main(){' + body + '}\n').encode()
        (semantic / "main.go").write_bytes(original)
        case = scratch / ("native-" + label)
        require(run([str(harness),"--copy-oracle",str(semantic),"--out",str(case)]),"separate oracle copy")
        if (semantic/"main.go").read_bytes()!=original:
            raise SystemExit("semantic source mutated by oracle instrumentation")
        (case/"oracle.crash").write_bytes(b"")
        (case/"oracle.registered").write_bytes(b"")
        evidence=["--crash-report",str(case/"oracle.crash"),"--crash-registered",str(case/"oracle.registered")]
        env = dict(ENV, GOFLAGS="", GODEBUG="panicnil=0", GOTRACEBACK="system")
        argv = ["go", "run", *(["-race"] if race else []), "."]
        result = run(argv, cwd=case, env=env)
        (case / "oracle.stdout").write_bytes(result.stdout)
        (case / "oracle.stderr").write_bytes(result.stderr)
        (case / "run.json").write_text(json.dumps({"argv":argv, "rc":result.returncode, "GOTRACEBACK":"system"}) + "\n")
        if result.returncode != 1 or result.stdout or not result.stderr.endswith(b"\nexit status 2\n"):
            raise SystemExit(f"native-{label}: not the intended exit-2 runtime report: {result!r}")
        kind = run([str(harness), "--abort-status", str(case / "oracle.stderr"),*evidence])
        (case / "kind.stdout").write_bytes(kind.stdout)
        (case / "kind.stderr").write_bytes(kind.stderr)
        if status is None:
            if kind.returncode != 3 or message.encode() not in kind.stderr:
                raise SystemExit(f"native-{label}: expected named boundary refusal, got {kind!r}")
        else:
            if kind.returncode or kind.stdout != status.encode():
                raise SystemExit(f"native-{label}: wrong actual terminal class: {kind!r}")
            if message is not None:
                observed = run([str(harness), "--abort-message", str(case / "oracle.stderr"), "--expected-status", status,*evidence])
                if observed.returncode or json.loads(observed.stdout) != message:
                    raise SystemExit(f"native-{label}: message bytes changed: {observed!r}")
            observed = run([str(harness), "--split-stderr", str(case / "oracle.stderr"), "--expected-status", status,*evidence])
            if observed.returncode or json.loads(observed.stdout) != output:
                raise SystemExit(f"native-{label}: output bytes changed: {observed!r}")
            if status in ["fatal", "deadlock"]:
                wrong = run([str(harness), "--abort-message", str(case / "oracle.stderr"), "--expected-status", "panic",*evidence])
                if wrong.returncode != 3 or b"actual " + status.encode() not in wrong.stderr:
                    raise SystemExit(f"native-{label}: actual {status} accepted as panic: {wrong!r}")
        print(f"Native observer probe: {label} PASS", flush=True)

    # Real IO setup failures must not execute the subject or become its
    # panic/success. Observe go run's own exit 1 and exact child exit 78.
    for broken in ["oracle.crash", "oracle.registered"]:
        semantic=scratch/("setup-source-"+broken)
        semantic.mkdir()
        (semantic/"main.go").write_text('package main\nfunc main(){print("SUBJECT EXECUTED");panic("actual")}\n')
        case=scratch/("setup-"+broken)
        require(run([str(harness),"--copy-oracle",str(semantic),"--out",str(case)]),"setup failure oracle copy")
        for name in ["oracle.crash","oracle.registered"]:
            if name==broken: (case/name).mkdir()
            else: (case/name).write_bytes(b"")
        got=run(["go","run","."],cwd=case,env=dict(ENV,GOFLAGS="",GODEBUG="panicnil=0",GOTRACEBACK="system"))
        (case/"stdout").write_bytes(got.stdout);(case/"stderr").write_bytes(got.stderr)
        if got.returncode!=1 or got.stdout or got.stderr!=b"exit status 78\n":
            raise SystemExit(f"setup failure executed subject or changed exit: {got!r}")
        print(f"Native setup refusal: {broken} PASS",flush=True)

    # Each mutation must COMPILE before its targeted behavioral test rejects
    # it; a syntax/import failure is not evidence that a gate works.
    for label, filename, before, after, test in [
        ("drop-nul", "split.go", "enc.Encode(string(prefix))", 'enc.Encode(strings.ReplaceAll(string(prefix), "\\x00", ""))', "TestAbortMessageBytes"),
        ("raw-soh", "split.go", 'strings.TrimSuffix(sb.String(), "\\n")', 'strings.ReplaceAll(strings.TrimSuffix(sb.String(), "\\n"), `\\u0001`, "\\x01")', "TestAbortMessageBytes"),
        ("trim-cr", "split.go", "enc.Encode(string(prefix))", "enc.Encode(strings.TrimSpace(string(prefix)))", "TestAbortMessageBytes"),
        ("mask-stdout-nul", "observe.go", "func observationText(stdout []byte) (string, error) {", 'func observationText(stdout []byte) (string, error) {\nif len(stdout)>0 && stdout[0]==0 {stdout=stdout[1:]}', "TestRawStdoutRefusals"),
        ("assume-panic", "abortkind.go", "func pinnedTraceKind(trace []byte) (string, error) {", 'func pinnedTraceKind(trace []byte) (string, error) {\nreturn "panic", nil', "TestAbortKind"),
        ("ignore-actual-kind", "observe.go", "if view.kind != status {", "if false && view.kind != status {", "TestAbortMessageKindGuard"),
        ("normalize-frame", "abortkind.go", "terminalFrame.FindSubmatch(lines[1])", "terminalFrame.FindSubmatch(bytes.TrimSpace(lines[1]))", "TestAbortKindRefusals"),
        ("skip-suffix", "crashview.go", 'if !bytes.HasSuffix(body, e.report) {', 'if false && !bytes.HasSuffix(body, e.report) {', "TestCrashEvidenceRefusals"),
        ("drop-output", "crashview.go", 'return abortView{kind, message, output}, nil', 'return abortView{kind, message, nil}, nil', "TestOwnedPanicPartition"),
        ("missing-ack", "crashview.go", 'if len(e.ack) == 0 && len(e.report) != 0 {', 'if false && len(e.ack) == 0 && len(e.report) != 0 {', "TestCrashEvidenceRefusals"),
        ("missing-success-ack", "crashview.go", 'len(e.report) != 0 || len(e.ack) == 0', 'len(e.report) != 0', "TestCrashEvidenceSuccessAndFiles"),
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
