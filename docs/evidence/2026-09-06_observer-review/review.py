"""Independent observer byte/descriptor review; synthetic probes are not conformance."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
META = json.loads((HERE / "provenance.json").read_text())
SCRATCH = Path(META["scratch"])
CANDIDATE = Path(META["candidate_root"])
BIN = SCRATCH / "coverageharness"
ENV = dict(os.environ, GO111MODULE="off", GOCACHE=str(ROOT / "artifacts/go-build-cache"))
TRACE = b"\n\ngoroutine 1 [running]:\nmain.main()\nexit status 2\n"
RECORDS = []


def call(label, args, raw=None, expected=None, rc=0, cwd=ROOT, env=ENV):
    case = SCRATCH / label
    case.mkdir(exist_ok=True)
    if raw is not None:
        (case / "input").write_bytes(raw)
        args = [str(a).replace("@INPUT@", str(case / "input")) for a in args]
    p = subprocess.run(args, cwd=cwd, env=env, capture_output=True, timeout=30)
    (case / "stdout").write_bytes(p.stdout)
    (case / "stderr").write_bytes(p.stderr)
    assert p.returncode == rc, (label, p.returncode, p.stdout, p.stderr)
    if expected is not None:
        assert json.loads(p.stdout) == expected, (label, p.stdout, expected)
    RECORDS.append({"label": label, "argv": list(map(str, args)), "exit": p.returncode,
                    "stdout_sha256": hashlib.sha256(p.stdout).hexdigest(),
                    "stderr_sha256": hashlib.sha256(p.stderr).hexdigest()})
    return p


# Sweep independently expected bytes through CLI JSON encoding. LF alone is
# the first-line delimiter; all other ASCII bytes, including CR/DEL, survive.
for i in range(128):
    payload = b"A" + bytes([i]) + b"Z"
    rendered = payload.replace(b"\n", b"\n\t")
    want = payload.split(b"\n", 1)[0].decode()
    call(f"message-{i:03}", [BIN, "--abort-message", "@INPUT@", "--expected-status", "panic"],
         b"panic: " + rendered + TRACE, want)
    prefix = b"P" + bytes([i]) + b"\n"
    call(f"prefix-{i:03}", [BIN, "--split-stderr", "@INPUT@", "--expected-status", "panic"],
         prefix + b"panic: payload" + TRACE, prefix.decode())

for n, payload in enumerate(["é界😀", "\u2028\u2029", "\"\\<>&", "\r\r\t"]):
    call(f"unicode-{n}", [BIN, "--abort-message", "@INPUT@", "--expected-status", "fatal"],
         b"panic: old [recovered]\n\tfatal error: " + payload.encode() + TRACE, payload)

for n, bad in enumerate([b"\xff", b"\xc0\xaf", b"\xed\xa0\x80", b"\xf4\x90\x80\x80"]):
    call(f"invalid-message-{n}", [BIN, "--abort-message", "@INPUT@", "--expected-status", "panic"],
         b"panic: " + bad + TRACE, rc=3)
    call(f"invalid-output-{n}", [BIN, "--split-stderr", "@INPUT@", "--expected-status", "ok"], bad, rc=3)
    call(f"invalid-json-utf8-{n}", [BIN, "--read-observation", "@INPUT@"],
         b'{"value":"' + bad + b'"}', rc=3)

for i in range(32):
    call(f"invalid-json-control-{i:03}", [BIN, "--read-observation", "@INPUT@"],
         b'{"value":"a' + bytes([i]) + b'b"}', rc=3)
raw_json = b'{"large":9007199254740993,"nul":"\\u0000","soh":"\\u0001"}\n'
p = call("json-numbers-not-reencoded", [BIN, "--read-observation", "@INPUT@"], raw_json)
assert p.stdout == raw_json
p = call("diagnostic-all-bytes", [BIN, "--quote-file", "@INPUT@"], bytes(range(256)))
assert all(c < 128 for c in p.stdout) and b"\\x00" in p.stdout and b"\\xff" in p.stdout

# Use actual changed shell functions, with only the external Go process
# substituted. Exercise repeated plain/-race sampling in the same directory.
source = (CANDIDATE / "scripts/diff-coverage").read_text()
names = ["run_with_timeout", "go_run_oracle", "go_diagnostics", "membership_go_observation",
         "member_status_allowed", "undecided_cause", "signal_cause", "obs_eq_cause",
         "obs_eq", "lean", "one_line", "attach_output"]
functions = []
for name in names:
    match = re.search(rf"^{name}\(\) \{{\n.*?^\}}", source, re.M | re.S)
    assert match, name
    functions.append(match.group())
shell = SCRATCH / "sampling.sh"
shell.write_text("set -uo pipefail\n" + "\n".join(functions) +
                 '\nmembership_go_observation "$PROBE_MODE"\n')
fakebin = SCRATCH / "fakebin"
fakebin.mkdir()
(fakebin / "go").write_text("#!/usr/bin/env python3\nimport os,sys,json\nfrom pathlib import Path\n"
    "Path(os.environ['ARG_RECORD']).write_text(json.dumps(sys.argv[1:]))\n"
    "sys.stdout.buffer.write(Path(os.environ['RAW_OUT']).read_bytes())\n"
    "sys.stderr.buffer.write(Path(os.environ['RAW_ERR']).read_bytes())\n"
    "sys.exit(int(os.environ['RAW_RC']))\n")
(fakebin / "go").chmod(0o755)
shared = SCRATCH / "shared-sample"
shared.mkdir()
for n, (mode, stdout, stderr, rc, allowed, expected_rc, expected) in enumerate([
    ("", b"", b"panic: a\x00b"+TRACE, 1, "ok+panic", 0, {"message":"a\x00b","output":"","schema":"golean-observation-v1","status":"panic"}),
    ("race", b"", b"panic: a\x01b"+TRACE, 1, "ok+panic", 0, {"message":"a\x01b","output":"","schema":"golean-observation-v1","status":"panic"}),
    ("", b"panic: a"+TRACE, b"no report\n", 1, "ok+panic", 1, None),
    ("race", b"", b"panic: a"+TRACE, 1, "ok", 1, None),
    ("", b'\x00{"schema":"golean-observation-v1","status":"ok","values":[]}', b"", 0, "ok", 1, None),
    ("race", b'{"schema":"golean-observation-v1","status":"ok","values":[]}', b"p\x00\x01\r\n", 0, "ok", 0,
     {"schema":"golean-observation-v1","status":"ok","values":[],"output":"p\x00\x01\r\n"}),
]):
    (shared/"raw-out").write_bytes(stdout); (shared/"raw-err").write_bytes(stderr)
    env=dict(ENV, PATH=str(fakebin)+os.pathsep+ENV['PATH'], RAW_OUT=str(shared/"raw-out"),
        RAW_ERR=str(shared/"raw-err"), RAW_RC=str(rc), ARG_RECORD=str(shared/"args.json"),
        PROBE_MODE=mode, HARNESS_BIN=str(BIN), go_run_dir=str(shared), expected_status="ok",
        expected_reason="-", statuses=allowed, GO_TIMEOUT_SECONDS="10", GO_BUILD_CACHE=ENV['GOCACHE'],
        GOLEAN_BIN=str(ROOT/".lake/build/bin/golean"), LEAN_TIMEOUT_SECONDS="10", OBS_EQ_STDERR="")
    p=call(f"sampling-{n}",["bash",str(shell)],rc=expected_rc,expected=expected,env=env)
    assert (shared/"oracle.stdout").read_bytes()==stdout and (shared/"oracle.stderr").read_bytes()==stderr
    argv=json.loads((shared/"args.json").read_text())
    assert ("-race" in argv)==bool(mode),argv
    assert b"ignored null byte" not in p.stderr

# Direct real-Go oracle probes independently challenge the fake report shapes.
native=SCRATCH/"native"
native.mkdir()
native_source='''package main
import ("os"; "sync")
func main() {
 print("prefix\\x00\\x01\\r\\n")
 switch os.Args[1] {
 case "plain": panic("payload\\x00\\x01\\t\\r\\nsecond")
 case "repanic": defer func(){_ = recover(); panic("replacement")}(); panic("payload\\x00\\x01\\t\\r\\nsecond")
 case "fatal": var m sync.Mutex; defer m.Unlock(); panic("original")
 case "invalid": panic(string([]byte{0xff}))
 }
}
'''
(native/"main.go").write_text(native_source)
for mode in ["plain","repanic","fatal","invalid"]:
    p=call("native-"+mode,["go","run",".",mode],rc=1,cwd=native)
    raw=p.stderr
    status="fatal" if mode=="fatal" else "panic"
    want="sync: unlock of unlocked mutex" if mode=="fatal" else "payload\x00\x01\t\r"
    call("native-message-"+mode,[BIN,"--abort-message","@INPUT@","--expected-status",status],
         raw,expected=None if mode=="invalid" else want,rc=3 if mode=="invalid" else 0)
    call("native-prefix-"+mode,[BIN,"--split-stderr","@INPUT@","--expected-status",status],
         raw,expected="prefix\x00\x01\r\n")

(HERE/"results.json").write_text(json.dumps({"checks":len(RECORDS),"records":RECORDS,
    "scope":"Raw-byte/descriptor/helper fidelity checks; synthetic shell probes are not Go conformance."},indent=2)+"\n")
print(f"Independent observer review: {len(RECORDS)} checks PASS")
