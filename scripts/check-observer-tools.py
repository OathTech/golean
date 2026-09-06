"""Byte-transport probes for the three diagnostic observer copies.

Exercises source-extracted oracle blocks before frontend/model comparison.
Fake oracle output is apparatus evidence only, never Go conformance evidence.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    env = dict(os.environ, GO111MODULE="off", GOCACHE=str(ROOT / "artifacts/go-build-cache"))
    scratch = Path(tempfile.mkdtemp(prefix="observer-tools-", dir=env.get("TMPDIR")))
    print(f"Diagnostic observer scratch: {scratch}", flush=True)
    harness = scratch / "coverageharness"
    subprocess.run(["go", "build", "-o", str(harness), "./tools/coverageharness"], cwd=ROOT, env=env, check=True)
    files = [ROOT / "scripts" / name for name in ["membership-sampling", "gotest-triage", "cedar-census"]]
    for path in [*files, Path(__file__), *sorted(ROOT.glob("tools/coverageharness/*.go"))]:
        print(hashlib.sha256(path.read_bytes()).hexdigest(), path.relative_to(ROOT), flush=True)
    fakebin = scratch / "fakebin"
    fakebin.mkdir()
    go = fakebin / "go"
    go.write_text("#!/usr/bin/env python3\nimport os,sys\nfrom pathlib import Path\n"
                  "assert os.environ.get('GOTRACEBACK') == 'system', 'system traceback pin missing'\n"
                  "Path('oracle.argv').write_text(' '.join(sys.argv[1:]))\n"
                  "assert Path('oracle.crash').read_bytes()==b'' and Path('oracle.registered').read_bytes()==b'', 'stale evidence'\n"
                  "Path('oracle.crash').write_bytes(Path(os.environ['PROBE_CRASH']).read_bytes())\n"
                  "Path('oracle.registered').write_bytes(Path(os.environ['PROBE_ACK']).read_bytes())\n"
                  "sys.stdout.buffer.write(Path(os.environ['PROBE_STDOUT']).read_bytes())\n"
                  "sys.stderr.buffer.write(Path(os.environ['PROBE_STDERR']).read_bytes())\n"
                  "sys.exit(int(os.environ['PROBE_RC']))\n")
    go.chmod(0o755)
    header = b"goroutine 1 gp=0x123 m=0 mp=0x456 [running]:\n"
    frame = b"panic({0x123?, 0x456?})\n\t/usr/local/go/src/runtime/panic.go:879 +0x16f fp=0x1 sp=0x2 pc=0x3\n"
    fatal_frame = b"runtime.fatal({0x123, 0x456})\n\t/usr/local/go/src/runtime/panic.go:1253 +0x74 fp=0x1 sp=0x2 pc=0x3\n"
    trace = b"\n\n" + header + frame + b"main.main()\nexit status 2\n"
    fatal_trace = b"\n\n" + header + fatal_frame + b"main.main()\nexit status 2\n"
    ok = b'{"schema":"golean-observation-v1","status":"ok","values":[]}'
    failure = False
    count = 0
    for path in files:
        text = path.read_text()
        functions = []
        for name in ["one_line", "json_string_literal"]:
            match = re.search(rf"^{name}\(\) \{{.*?^\}}", text, re.M | re.S)
            if match:
                # one_line can be one line; do not swallow later definitions.
                first = text[text.index(name + "() {"):].splitlines()[0]
                functions.append(first if first.endswith("}") else match.group())
        if path.name == "membership-sampling":
            match = re.search(r"^oracle\(\) \{.*?^\}", text, re.M | re.S)
            if not match: raise SystemExit("missing diagnostic oracle function")
            code = match.group() + '\noracle "$dir" "$PROBE_RACE"\n'
        else:
            start = "  # Expected Go-side output" if path.name == "gotest-triage" else "  # --- Go oracle ("
            stop = "  # --- Frontend" if path.name == "gotest-triage" else "  # --- Machine"
            begin = text.index(start)
            end = text.index(stop, begin)
            code = "probe() {\n" + text[begin:end] + '\nprintf "%s" "$go_obs"\n}\nprobe\n'
        script = scratch / (path.name + ".sh")
        script.write_text("set -uo pipefail\n" + "\n".join(functions) + "\n" + code)
        probes = [
            ("panic-controls", b"", b"panic: a\x00\x01\t\r" + trace, 1, b"", {"message":"a\x00\x01\t\r","output":""}),
            ("panic-prefix", b"", b"out\x00\x01\n" + b"panic: a\x00\n\tsecond" + trace, 1, b"", {"message":"a\x00","output":"out\x00\x01\n"}),
            ("invalid-utf8", b"", b"panic: a\xff" + trace, 1, b"", "UTF-8"),
            ("stdout-marker", b"panic: a" + trace, b"", 1, b"", "UNCLASSIFIED" if path.name == "membership-sampling" else "INFRA"),
            ("success", ok if path.name == "membership-sampling" else b"", b"", 0, b"", {"status":"ok","output":""}),
            ("nul-success", b"\x00" + (ok if path.name == "membership-sampling" else b""), b"", 0, b"", "UNCLASSIFIED" if path.name == "membership-sampling" else "INFRA"),
        ]
        fatal = ({"status":"fatal", "message":"sync: unlock of unlocked mutex", "output":""}
                 if path.name == "gotest-triage" else "UNCLASSIFIED" if path.name == "membership-sampling" else "INFRA")
        for label, head in [("fatal-plain", b""), ("fatal-unwind", b"panic: original\n\t")]:
            want=fatal if label=="fatal-plain" else "UNCLASSIFIED" if path.name=="membership-sampling" else "INFRA"
            probes.append((label, b"", head + b"fatal error: sync: unlock of unlocked mutex" + fatal_trace, 1, b"", want))
        refusal = "UNCLASSIFIED" if path.name == "membership-sampling" else "INFRA"
        probes += [
            ("marker-first", b"", b"panic: fatal error: harmless" + trace, 1, b"", {"status":"panic","message":"fatal error: harmless","output":""}),
            ("marker-output", b"", b"fatal error: harmless prefix\npanic: original" + trace, 1, b"", {"status":"panic","message":"original","output":"fatal error: harmless prefix\n"}),
            ("marker-multiline", b"", b"panic: original\n\tfatal error: sync: unlock of unlocked mutex" + trace, 1, b"", {"status":"panic","message":"original","output":""}),
            ("deadlock-payload", b"", b"panic: fatal error: all goroutines are asleep - deadlock!" + trace, 1, b"", {"status":"panic","message":"fatal error: all goroutines are asleep - deadlock!","output":""}),
            ("glued-prefix", b"", b"panic: fakefatal error: sync: unlock of unlocked mutex" + fatal_trace, 1, b"", refusal),
            ("printed-origin", b"", b"panic: fake\n\n" + header + frame + b"fatal error: sync: unlock of unlocked mutex" + fatal_trace, 1, b"", refusal),
            ("unknown-origin", b"", b"panic: fake\n\n" + header + b"unknown()\nexit status 2\n", 1, b"", refusal),
            ("printed-continuation", b"", b"panic: forged\n\tpanic: actual"+trace, 1, b"", {"message":"actual","output":"panic: forged\n\t"}),
            ("literal-continuation", b"", b"panic: forged\n\tpanic: actual"+trace, 1, b"", {"message":"forged","output":""}),
            ("setup-exit", b"", b"exit status 78\n", 1, b"", "crash-hook setup failed"),
            ("success-no-ack", ok if path.name=="membership-sampling" else b"", b"", 0, b"", refusal),
            ("success-crash", ok if path.name=="membership-sampling" else b"", b"", 0, b"", refusal),
            ("malformed-ack", b"", b"panic: actual"+trace, 1, b"", refusal),
        ]
        if path.name == "gotest-triage":
            probes += [
                ("lf-not-empty", b"\n", b"", 0, b"", "INFRA"),
                ("crlf-normalized", b"a\r\n", b"", 0, b"a\n", {"status":"ok","output":""}),
                ("output-controls", b"", b"a\x00\x01\n", 0, b"a\x00\x01\n", {"status":"ok","output":"a\x00\x01\n"}),
            ]
        probe_envs={}
        for label, stdout, stderr, rc, expected_file, expected in probes:
            count += 1
            case = scratch / (path.name + "-" + label)
            case.mkdir()
            (case / "stdout").write_bytes(stdout)
            (case / "stderr").write_bytes(stderr)
            (case / "subject.out").write_bytes(expected_file)
            original=b"package main\nfunc main(){}\n"
            (case / "main.go").write_bytes(original)
            crash=b""
            if isinstance(expected,dict) and rc==1:
                crash=stderr[len(expected.get("output","").encode()):-len(b"exit status 2\n")]
            if label=="success-crash": crash=b"unexpected report"
            (case/"crash").write_bytes(crash)
            (case/"ack").write_bytes(b"" if label=="success-no-ack" else b"bad ack" if label=="malformed-ack" else b"registered\n")
            (case/"oracle.crash").write_bytes(b"STALE REPORT")
            (case/"oracle.registered").write_bytes(b"STALE ACK")
            probe_env = dict(env, PATH=str(fakebin) + os.pathsep + env["PATH"], HARNESS_BIN=str(harness),
                             GO_BUILD_CACHE=env["GOCACHE"], GO_TIMEOUT="10", PROBE_STDOUT=str(case / "stdout"),
                             PROBE_STDERR=str(case / "stderr"), PROBE_CRASH=str(case/"crash"), PROBE_ACK=str(case/"ack"), PROBE_RC=str(rc), dir=str(case),
                             src=str(case / "subject.go"), rel="subject.go", name="subject", kind="driver",
                             PROBE_RACE="race" if path.name == "membership-sampling" and count % 2 else "")
            probe_envs[label]=probe_env
            result = subprocess.run(["bash", str(script)], cwd=ROOT, env=probe_env, capture_output=True, timeout=30)
            (case / "result.stdout").write_bytes(result.stdout)
            (case / "result.stderr").write_bytes(result.stderr)
            try:
                if isinstance(expected, dict):
                    got = json.loads(result.stdout)
                    good = result.returncode == 0 and all(got.get(k) == v for k,v in expected.items())
                else:
                    good = expected.encode() in result.stdout
            except (ValueError, UnicodeDecodeError):
                good = False
            good = good and b"ignored null byte" not in result.stderr
            good = good and (case / "oracle.stdout").read_bytes() == stdout and (case / "oracle.stderr").read_bytes() == stderr
            oracle_dir=case if path.name=="membership-sampling" else Path((case/"oracle-directory.txt").read_text().strip())
            expected_argv = "run -race ." if probe_env["PROBE_RACE"] else "run ."
            good = good and (oracle_dir / "oracle.argv").read_text() == expected_argv
            good = good and (case/"main.go").read_bytes()==original
            if path.name!="membership-sampling": good=good and not (case/"zz_golean_crash.go").exists()
            good = good and result.returncode == (1 if isinstance(expected, str) and path.name == "membership-sampling" else 0)
            if not good:
                failure = True
                print(f"FAIL {path.name}/{label}: exit={result.returncode} stdout={result.stdout!r} stderr={result.stderr!r}", flush=True)
            else:
                print(f"PASS {path.name}/{label}", flush=True)
        # Mutate the actual extracted script after the positive/negative
        # controls pass. Syntax success is required before demonstrating a
        # real false acceptance which the normal gate rejects.
        mutations=[("omit-channel",' "${evidence[@]}"','',"success-no-ack")]
        if path.name=="gotest-triage":
            mutations.append(("lossy-out", ".replace(b'\\r\\n', b'\\n')", ".replace(b'\\x00', b'').rstrip(b'\\n')", "nul-success"))
        elif path.name=="cedar-census":
            mutations.append(("false-silence", 'if [[ -s "$dir/oracle.stdout" || -s "$dir/oracle.stderr" ]]; then', 'if false; then', "nul-success"))
        for label,before,after,probe_label in mutations:
            contents=script.read_text()
            if before not in contents: raise SystemExit(f"{path.name}/{label}: mutation anchor missing")
            mutant=scratch/(path.name+"-mutant-"+label+".sh")
            mutant.write_text(contents.replace(before,after))
            subprocess.run(["bash","-n",str(mutant)],check=True)
            bad=subprocess.run(["bash",str(mutant)],cwd=ROOT,env=probe_envs[probe_label],capture_output=True,timeout=30)
            (scratch/(path.name+"-mutant-"+label+".stdout")).write_bytes(bad.stdout)
            (scratch/(path.name+"-mutant-"+label+".stderr")).write_bytes(bad.stderr)
            try: exposed=bad.returncode==0 and json.loads(bad.stdout).get("status")=="ok"
            except (ValueError,UnicodeDecodeError): exposed=False
            if not exposed: raise SystemExit(f"{path.name}/{label}: mutation did not expose the targeted false acceptance: {bad!r}")
            print(f"Diagnostic script mutation: {path.name}/{label} syntactically valid, false acceptance exposed by existing negative control",flush=True)
        # Independent real-Go byte observations through each diagnostic path.
        # These exercise the actual process/runtime report; they are still
        # observer controls, not a full tool census or model conformance run.
        for label, body, expected in [
            ("native-panic", r'print("out\x00\x01\n"); panic("a\x00\x01\t\r\nsecond")',
             {"message":"a\x00\x01\t\r","output":"out\x00\x01\n"}),
            ("native-invalid-utf8", r'panic("a\xff")', "UTF-8"),
            ("native-nul-success", r'print("\x00")', "UNCLASSIFIED" if path.name == "membership-sampling" else "INFRA"),
            ("native-fatal-unwind", r'var m sync.Mutex; defer m.Unlock(); panic("original")', refusal),
            ("native-marker-first", r'panic("fatal error: harmless")', {"status":"panic","message":"fatal error: harmless","output":""}),
            ("native-marker-multiline", r'panic("original\nfatal error: sync: unlock of unlocked mutex")', {"status":"panic","message":"original","output":""}),
            ("native-marker-output", r'print("fatal error: harmless prefix\n");panic("original")', {"status":"panic","message":"original","output":"fatal error: harmless prefix\n"}),
            ("native-glued-prefix", r'print("panic: fake");var m sync.Mutex;m.Unlock()', refusal),
            ("native-nilgo-literal", r'panic("fakefatal error: go of nil func value")', {"status":"panic","message":"fakefatal error: go of nil func value","output":""}),
            ("native-printed-continuation", r'print("panic: forged\n\t");panic("actual")', {"status":"panic","message":"actual","output":"panic: forged\n\t"}),
            ("native-literal-continuation", r'panic("forged\npanic: actual")', {"status":"panic","message":"forged","output":""}),
            ("native-glued-output", r'print("glued");panic("actual")', {"status":"panic","message":"actual","output":"glued"}),
            ("native-repanic", r'defer func(){recover();panic("second")}();panic("first")', {"status":"panic","message":"first [recovered]","output":""}),
        ]:
            count += 1
            case = scratch / (path.name + "-" + label)
            imports = '\nimport "sync"\n' if "sync.Mutex" in body else "\n"
            original=("package main" + imports + "func main() { " + body + " }\n").encode()
            if path.name=="membership-sampling":
                semantic=scratch/(path.name+"-source-"+label);semantic.mkdir()
                (semantic/"main.go").write_bytes(original)
                subprocess.run([str(harness),"--copy-oracle",str(semantic),"--out",str(case)],env=env,check=True)
            else:
                case.mkdir();(case/"main.go").write_bytes(original)
            native_env = dict(env, HARNESS_BIN=str(harness), GO_BUILD_CACHE=env["GOCACHE"], GO_TIMEOUT="10",
                              dir=str(case), src=str(case / "subject.go"), rel="subject.go", name="subject", kind="driver",
                              PROBE_RACE="race" if path.name == "membership-sampling" and count % 2 else "")
            result = subprocess.run(["bash", str(script)], cwd=ROOT, env=native_env, capture_output=True, timeout=30)
            (case / "result.stdout").write_bytes(result.stdout)
            (case / "result.stderr").write_bytes(result.stderr)
            try:
                if isinstance(expected, dict):
                    got = json.loads(result.stdout)
                    good = result.returncode == 0 and all(got.get(k) == v for k,v in expected.items())
                else:
                    good = expected.encode() in result.stdout
            except (ValueError, UnicodeDecodeError):
                good = False
            good = good and result.returncode == (1 if isinstance(expected, str) and path.name == "membership-sampling" else 0)
            if path.name!="membership-sampling":
                good=good and (case/"main.go").read_bytes()==original and not (case/"zz_golean_crash.go").exists()
            else:
                good=good and (semantic/"main.go").read_bytes()==original
            if not good or b"ignored null byte" in result.stderr:
                failure = True
                print(f"FAIL {path.name}/{label}: exit={result.returncode} stdout={result.stdout!r} stderr={result.stderr!r}", flush=True)
            else:
                print(f"PASS {path.name}/{label}", flush=True)
    print(f"Diagnostic observer probes: {count} checks, {'FAIL' if failure else 'PASS'}", flush=True)
    raise SystemExit(1 if failure else 0)


if __name__ == "__main__":
    main()
