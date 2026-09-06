"""Independent native, copy-isolation and non-verdict-exit diagnostic probes."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUTHOR = ROOT.parent / "typed-observer-controls"


def main():
    manifest_path = AUTHOR / "docs/evidence/2026-09-06_observer-diagnostic-tools/hybrid-diagnostic-sources.json"
    manifest = json.loads(manifest_path.read_text())
    assert hashlib.sha256(manifest_path.read_bytes()).hexdigest() == "21b9d359558e74e873e624a744ba95ba22b9cd1b42600186c6c76a63e11d1d9a"
    for name, digest in manifest.items():
        assert hashlib.sha256((AUTHOR/name).read_bytes()).hexdigest() == digest, name
    shutil.copyfile(manifest_path, HERE/"candidate-sources.json")
    sourcefiles = sorted((AUTHOR/"tools/coverageharness").glob("*.go"))
    with tarfile.open(HERE/"source.tar.gz", "w:gz") as archive:
        for name in sorted(set(manifest) | {str(p.relative_to(AUTHOR)) for p in sourcefiles}):
            archive.add(AUTHOR/name, arcname=name)
    scratch = Path(tempfile.mkdtemp(prefix="diagnostic-review-", dir=os.environ.get("TMPDIR")))
    package = scratch/"helper"
    package.mkdir()
    for p in sourcefiles:
        shutil.copyfile(p, package/p.name)
    env = dict(os.environ, GO111MODULE="off", GOFLAGS="", GODEBUG="panicnil=0", GOTRACEBACK="system",
               GOCACHE=str(ROOT/"artifacts/go-build-cache"))
    helper = scratch/"coverageharness"
    build = subprocess.run(["go", "build", "-o", str(helper), "."], cwd=package, env=env, capture_output=True)
    (HERE/"build.log").write_bytes(build.stdout+build.stderr)
    assert build.returncode == 0
    fakebin = scratch/"fakebin"
    fakebin.mkdir()
    fake = fakebin/"go"
    fake.write_text("#!/usr/bin/env python3\nimport os,sys\nfrom pathlib import Path\n"
                    "assert Path('oracle.crash').read_bytes()==b''\n"
                    "assert Path('oracle.registered').read_bytes()==b''\n"
                    "Path('oracle.crash').write_bytes(Path(os.environ['FAKE_CRASH']).read_bytes())\n"
                    "Path('oracle.registered').write_bytes(b'registered\\n')\n"
                    "sys.stderr.buffer.write(Path(os.environ['FAKE_STDERR']).read_bytes())\n"
                    "sys.exit(int(os.environ['FAKE_RC']))\n")
    fake.chmod(0o755)
    rows = []
    for tool in ["membership-sampling", "gotest-triage", "cedar-census"]:
        source = (AUTHOR/"scripts"/tool).read_text()
        if tool == "membership-sampling":
            code = re.search(r"^oracle\(\) \{.*?^\}", source, re.M|re.S).group()+ '\noracle "$dir" "$PROBE_RACE"\n'
        else:
            start = source.index("  # Expected Go-side output" if tool=="gotest-triage" else "  # --- Go oracle (")
            stop = source.index("  # --- Frontend" if tool=="gotest-triage" else "  # --- Machine", start)
            code = "probe() {\n"+source[start:stop]+'\nprintf "%s" "$go_obs"\n}\nprobe\n'
        one_line = next((line for line in source.splitlines() if line.startswith("one_line() {")), "")
        if one_line and not one_line.endswith("}"):
            one_line = re.search(r"^one_line\(\) \{.*?^\}", source, re.M|re.S).group()
        script = scratch/(tool+".sh")
        script.write_text("set -uo pipefail\n"+one_line+"\n"+code)
        saved = None
        cases = [
            ("multifile-controls", 'func subject(){print("out\\x00\\x01\\r\\n");panic("actual\\r\\nsecond")}', "", {"status":"panic", "message":"actual\r", "output":"out\x00\x01\r\n"}),
            ("init-panic", 'func subject(){}', 'func init(){panic("early")}', {"status":"panic", "message":"early", "output":""}),
            ("init-exit-success", 'func subject(){}', 'func init(){os.Exit(0)}', None),
        ]
        for label, body, init, expected in cases:
            semantic = scratch/(tool+"-"+label+"-source")
            semantic.mkdir()
            imports = 'import "os"\n' if "os.Exit" in init else ""
            original = {"main.go":("package main\n"+imports+init+"\nfunc main(){subject()}\n").encode(),
                        "body.go":("package main\n"+body+"\n").encode()}
            for name, contents in original.items(): (semantic/name).write_bytes(contents)
            case = scratch/(tool+"-"+label+"-oracle") if tool=="membership-sampling" else semantic
            if tool=="membership-sampling":
                subprocess.run([str(helper), "--copy-oracle", str(semantic), "--out", str(case)], env=env, check=True)
            probe_env = dict(env, HARNESS_BIN=str(helper), GO_BUILD_CACHE=env["GOCACHE"], GO_TIMEOUT="10",
                             dir=str(case), src=str(case/"subject.go"), rel="subject.go", name="subject", kind="driver",
                             PROBE_RACE="race" if tool=="membership-sampling" and label=="multifile-controls" else "")
            p = subprocess.run(["bash", str(script)], cwd=ROOT, env=probe_env, capture_output=True, timeout=45)
            oracle = case if tool=="membership-sampling" else Path((case/"oracle-directory.txt").read_text().strip())
            raw = dict(stdout_hex=(case/"oracle.stdout").read_bytes().hex(), stderr_hex=(case/"oracle.stderr").read_bytes().hex(),
                       crash_hex=(oracle/"oracle.crash").read_bytes().hex(), ack_hex=(oracle/"oracle.registered").read_bytes().hex())
            row = dict(tool=tool, label=label, rc=p.returncode, result_stdout_hex=p.stdout.hex(), result_stderr_hex=p.stderr.hex(), raw=raw)
            for name, contents in original.items():
                assert (semantic/name).read_bytes()==contents, row
                copied=(oracle/name).read_bytes()
                assert copied.replace(b"\n_goleanSetupCrash();", b"", 1)==contents, row
            assert not (semantic/"zz_golean_crash.go").exists()
            if expected:
                got=json.loads(p.stdout)
                assert p.returncode==0 and all(got.get(k)==v for k,v in expected.items()), row
            else:
                assert (b"UNCLASSIFIED" if tool=="membership-sampling" else b"INFRA") in p.stdout, row
                assert raw["ack_hex"]==raw["crash_hex"]=="", row
            rows.append(row)
            print(tool, label, "PASS", flush=True)
            if label=="multifile-controls": saved=(case, oracle, probe_env)
        # Even a complete authenticated panic does not make a killed/timed-out
        # outer oracle process a verdict. The actual scripts must check exit.
        case, oracle, probe_env = saved
        raw_stderr = scratch/(tool+"-valid.stderr")
        raw_crash = scratch/(tool+"-valid.crash")
        raw_stderr.write_bytes((case/"oracle.stderr").read_bytes())
        raw_crash.write_bytes((oracle/"oracle.crash").read_bytes())
        for rc in [124, 137]:
            fenv=dict(probe_env, PATH=str(fakebin)+os.pathsep+env["PATH"], FAKE_RC=str(rc),
                      FAKE_STDERR=str(raw_stderr), FAKE_CRASH=str(raw_crash))
            p=subprocess.run(["bash", str(script)], cwd=ROOT, env=fenv, capture_output=True, timeout=30)
            row=dict(tool=tool, label="non-verdict-"+str(rc), rc=p.returncode, result_stdout_hex=p.stdout.hex(), result_stderr_hex=p.stderr.hex())
            assert (b"UNCLASSIFIED" if tool=="membership-sampling" else b"INFRA") in p.stdout, row
            rows.append(row)
            print(tool, "non-verdict", rc, "PASS", flush=True)
    for name, digest in manifest.items(): assert hashlib.sha256((AUTHOR/name).read_bytes()).hexdigest()==digest, name
    (HERE/"results.json").write_text(json.dumps(dict(scratch=str(scratch), rows=rows), indent=2)+"\n")
    print("Independent diagnostic probes: 15 PASS", flush=True)


if __name__=="__main__": main()
