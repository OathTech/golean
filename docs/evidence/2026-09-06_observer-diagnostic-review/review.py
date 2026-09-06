"""Independent diagnostic block probes; no complete census/model claim."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
META = json.loads((HERE / "provenance.json").read_text())
CANDIDATE = Path(META["candidate_root"])
BASE = Path(META["scratch"])
PHASE = sys.argv[1]
SCRATCH = BASE / PHASE
SCRATCH.mkdir()
CORE = json.loads((HERE.parent / "2026-09-06_observer-review/provenance.json").read_text())
HARNESS = Path(CORE["scratch"]) / "coverageharness"
ENV = dict(os.environ, GO111MODULE="off", GOCACHE=str(ROOT / "artifacts/go-build-cache"))
TRACE = b"\n\ngoroutine 1 [running]:\nmain.main()\nexit status 2\n"
OK = b'{"schema":"golean-observation-v1","status":"ok","values":[]}'
RECORDS = []
SOURCES = {}
fakebin = SCRATCH / "fakebin"
fakebin.mkdir()
(fakebin / "go").write_text(
    "#!/usr/bin/env python3\nimport os,sys,json\nfrom pathlib import Path\n"
    "Path(os.environ['ARGV_FILE']).write_text(json.dumps(sys.argv[1:]))\n"
    "sys.stdout.buffer.write(Path(os.environ['RAW_OUT']).read_bytes())\n"
    "sys.stderr.buffer.write(Path(os.environ['RAW_ERR']).read_bytes())\n"
    "sys.exit(int(os.environ['RAW_RC']))\n")
(fakebin / "go").chmod(0o755)


def invoke(tool, script, label, stdout=b"", stderr=b"", rc=0, expected_file=b"",
           want=None, refused=False, native=None, mode=""):
    case = SCRATCH / (tool + "-" + label)
    case.mkdir()
    (case / "raw-out").write_bytes(stdout)
    (case / "raw-err").write_bytes(stderr)
    if expected_file is not None:
        (case / "subject.out").write_bytes(expected_file)
    if native:
        (case / "main.go").write_text(native)
    env = dict(ENV, HARNESS_BIN=str(HARNESS), GO_BUILD_CACHE=ENV["GOCACHE"],
               GO_TIMEOUT="10", dir=str(case), src=str(case / "subject.go"),
               rel="subject.go", name="subject", kind="driver", MODE=mode)
    if not native:
        env.update(PATH=str(fakebin) + os.pathsep + ENV["PATH"],
                   RAW_OUT=str(case / "raw-out"), RAW_ERR=str(case / "raw-err"),
                   RAW_RC=str(rc), ARGV_FILE=str(case / "argv.json"))
    p = subprocess.run(["bash", str(script)], cwd=ROOT, env=env, capture_output=True, timeout=30)
    (case / "result.stdout").write_bytes(p.stdout)
    (case / "result.stderr").write_bytes(p.stderr)
    try:
        decoded = json.loads(p.stdout)
    except (ValueError, UnicodeDecodeError):
        decoded = None
    good = ((decoded is None and (b"INFRA" in p.stdout or b"UNCLASSIFIED" in p.stdout))
            if refused else p.returncode == 0 and decoded == want)
    good = good and b"ignored null byte" not in p.stderr
    if not native:
        good = good and (case / "oracle.stdout").read_bytes() == stdout
        good = good and (case / "oracle.stderr").read_bytes() == stderr
        argv = json.loads((case / "argv.json").read_text())
        good = good and (("-race" in argv) == (mode == "race"))
    RECORDS.append({"tool": tool, "label": label, "pass": good, "exit": p.returncode,
                    "stdout_sha256": hashlib.sha256(p.stdout).hexdigest(),
                    "stderr_sha256": hashlib.sha256(p.stderr).hexdigest()})
    print(("PASS " if good else "FAIL ") + tool + "/" + label, flush=True)


for tool in ["membership-sampling", "gotest-triage", "cedar-census"]:
    source = ((BASE / tool) if PHASE == "initial" else (CANDIDATE / "scripts" / tool)).read_bytes()
    (SCRATCH / tool).write_bytes(source)
    SOURCES["scripts/" + tool] = hashlib.sha256(source).hexdigest()
    text = source.decode()
    funcs = []
    m = re.search(r"^one_line\(\) \{.*?^\}", text, re.M | re.S)
    if m:
        first = m.group().splitlines()[0]
        funcs.append(first if first.endswith("}") else m.group())
    if tool == "membership-sampling":
        code = re.search(r"^oracle\(\) \{.*?^\}", text, re.M | re.S).group()
        code += '\noracle "$dir" "$MODE"\n'
    else:
        start = "  # Expected Go-side output" if tool == "gotest-triage" else "  # --- Go oracle ("
        end = "  # --- Frontend" if tool == "gotest-triage" else "  # --- Machine"
        a = text.index(start)
        code = "probe() {\n" + text[a:text.index(end, a)] + '\nprintf "%s" "$go_obs"\n}\nprobe\n'
    script = SCRATCH / (tool + ".sh")
    script.write_text("set -uo pipefail\n" + "\n".join(funcs) + "\n" + code)
    for n in range(32):
        payload = b"A" + bytes([n]) + b"Z"
        rendered = payload.replace(b"\n", b"\n\t")
        prefix = b"P" + bytes([n]) + b"\n"
        want = {"schema":"golean-observation-v1", "status":"panic",
                "message":payload.split(b"\n", 1)[0].decode(), "output":prefix.decode()}
        invoke(tool, script, f"control-{n:02}", stderr=prefix+b"panic: "+rendered+TRACE,
               rc=1, want=want, mode="race" if tool == "membership-sampling" and n % 2 else "")
    for rc in [2, 124, 137, 143, 255]:
        invoke(tool, script, "nonverdict-"+str(rc), stderr=b"panic: partial"+TRACE,
               rc=rc, refused=True)
    invoke(tool, script, "stdout-marker", stdout=b"panic: forged"+TRACE, rc=1, refused=True)
    invoke(tool, script, "invalid-message", stderr=b"panic: \xff"+TRACE, rc=1, refused=True)
    invoke(tool, script, "missing-trailer", stderr=b"panic: partial\n", rc=1, refused=True)
    invoke(tool, script, "silent", stdout=OK if tool == "membership-sampling" else b"",
           expected_file=None, want={"schema":"golean-observation-v1","status":"ok","values":[],"output":""})
    for n, data in enumerate([b"\x00",b"\n",b"\r",b"\t",b"\x01"]):
        invoke(tool, script, "nonempty-success-"+str(n), stderr=data, refused=True,
               stdout=b"\x00"+OK if tool == "membership-sampling" else b"")
    if tool == "gotest-triage":
        for n, (actual, expected, equal) in enumerate([
            (b"a\r\n",b"a\n",True),(b"a\r\n",b"a\r\n",False),
            (b"a\r",b"a\r",True),(b"a\n\n",b"a\n",False),
            (b"a\x00\x01\n",b"a\x00\x01\n",True),
            (b"a\x00b",b"ab",False),(b"a\n",None,False),
        ]):
            invoke(tool, script, "expected-bytes-"+str(n), stderr=actual,
                   expected_file=expected, refused=not equal,
                   want={"schema":"golean-observation-v1","status":"ok","values":[],"output":actual.decode()})
        invoke(tool, script, "invalid-output", stderr=b"\xff", expected_file=b"\xff", refused=True)
    native='package main\nimport "sync"\nfunc main(){var m sync.Mutex; defer m.Unlock(); panic("original")}\n'
    invoke(tool, script, "native-fatal-unwind", native=native,
           refused=tool != "gotest-triage",
           want={"schema":"golean-observation-v1","status":"fatal","message":"sync: unlock of unlocked mutex","output":""})

result={"phase":PHASE,"sources":SOURCES,"checks":len(RECORDS),
        "failures":sum(not r["pass"] for r in RECORDS),"records":RECORDS}
(HERE / (PHASE + "-results.json")).write_text(json.dumps(result,indent=2)+"\n")
print(f"{PHASE}: {result['checks']} checks, {result['failures']} failures")
raise SystemExit(bool(result["failures"]))
