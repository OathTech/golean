"""DESIGN PROTOTYPE ONLY: same-execution crash channel and strict fallback.

No production source mutation, no Lean conformance claim. Generated wrappers
and raw descriptors remain in unique scratch. The metadata is used only to
select/call corpus subjects and report prospective baseline effects; observe
has no expected-status or expected-payload input.
"""
from pathlib import Path
import csv
import hashlib
import json
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
ENV = dict(os.environ, GO111MODULE="off", GOFLAGS="", GODEBUG="panicnil=0",
           GOTRACEBACK="system", GOCACHE=str(ROOT / "artifacts/go-build-cache"))
HEADER = re.compile(rb"(?:^|\n)(runtime stack:|goroutine [0-9]+ gp=0x[0-9a-f]+ m=(?:nil|-?[0-9]+ mp=0x[0-9a-f]+) \[[^\r\n]*\]:)\n")
FRAME = re.compile(rb"^(panic|runtime\.fatal|runtime\.throw)\([^\r\n]*\)$")
SOURCE = re.compile(rb"^\t/[^\t\r\n]*/src/runtime/panic\.go:(879|1253|1229) \+0x[0-9a-f]+ fp=0x[0-9a-f]+ sp=0x[0-9a-f]+ pc=0x[0-9a-f]+$")
SETUP = '''
 _goleanCrash, _goleanCrashErr := _golean_os.OpenFile("oracle.crash", _golean_os.O_WRONLY|_golean_os.O_TRUNC, 0600)
 if _goleanCrashErr != nil { _golean_os.Exit(78) }
 if _goleanCrashErr = _golean_debug.SetCrashOutput(_goleanCrash, _golean_debug.CrashOptions{}); _goleanCrashErr != nil { _golean_os.Exit(78) }
 _goleanCrash.Close()
 if _golean_os.WriteFile("oracle.registered", []byte("registered\\n"), 0600) != nil { _golean_os.Exit(78) }
'''


class Refusal(Exception):
    pass


def origin(packet):
    h = HEADER.search(packet)
    if h is None:
        raise Refusal("missing pinned system origin")
    lines = packet[h.end():].split(b"\n")
    if len(lines) < 2:
        raise Refusal("truncated origin")
    f, s = FRAME.fullmatch(lines[0]), SOURCE.fullmatch(lines[1])
    if f is None or s is None:
        raise Refusal("unknown runtime origin")
    key = f.group(1), s.group(1)
    if key == (b"panic", b"879") and h.group(1) != b"runtime stack:":
        kind = "panic"
    elif key in [(b"runtime.fatal", b"1253"), (b"runtime.throw", b"1229")]:
        kind = "fatal"
    else:
        raise Refusal("mismatched runtime origin")
    return kind, h


def checked_text(data):
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        raise Refusal("invalid UTF8 representation remains a separate obligation")


def observe(stderr, crash, registered, rc):
    trailer = b"exit status 2\n"
    if rc != 1 or not stderr.endswith(b"\n" + trailer):
        raise Refusal("oracle/setup exit is not child exit 2")
    body = stderr[:-len(trailer)]
    if registered and crash:
        if not body.endswith(crash):
            raise Refusal("crash channel is not the exact raw stderr suffix")
        kind, h = origin(crash)
        tail = crash[h.end():]
        if re.search(rb"\n\t?(?:panic: |fatal error: |runtime stack:)", tail):
            raise Refusal("multiple or unknown crash report blocks")
        if kind == "panic":
            if not crash.startswith(b"panic: "):
                raise Refusal("panic channel missing initial panic marker")
            prefix = body[:-len(crash)]
            message = crash.split(b"\n", 1)[0][len(b"panic: "):]
            return {"status":"panic", "message":checked_text(message),
                    "output":checked_text(prefix), "mode":"authenticated panic suffix"}
        # Fatal messages precede m.dying and are absent from crash. Do not
        # pretend the bytes before the copied trace are all program output.
    elif crash:
        raise Refusal("nonempty crash channel without registration acknowledgement")

    # Every raw marker counts: no repanic/unwind continuation exception.
    # Look for the origin AFTER the candidate marker, not a harmless fake
    # header in preceding program output. No expected status selects it.
    if body.count(b"panic: ") == 1:
        candidate = body.index(b"panic: ")
    elif body.count(b"panic: ") == 0 and body.count(b"fatal error: ") == 1:
        candidate = body.index(b"fatal error: ")
    else:
        raise Refusal("raw report has ambiguous continuation/output markers")
    report = body[candidate:]
    kind, h = origin(report)
    tail = report[h.end():]
    if b"panic: " in tail or b"fatal error: " in tail or b"\nruntime stack:" in tail:
        raise Refusal("unauthenticated later report boundary")
    if kind == "panic":
        marker = b"panic: "
        if body.count(marker) != 1:
            raise Refusal("raw panic report has ambiguous continuation/output markers")
    else:
        marker = b"fatal error: "
        if body.count(marker) != 1 or b"panic: " in body:
            raise Refusal("fatal message/output not authenticated before m.dying")
    start = body.index(marker)
    if start != 0 and body[start-1] != 10:
        raise Refusal("raw report marker glued to program output")
    if start >= candidate + h.start():
        raise Refusal("raw report marker follows origin")
    message = body[start+len(marker):].split(b"\n", 1)[0]
    if kind == "fatal" and message == b"all goroutines are asleep - deadlock!":
        kind = "deadlock"
    return {"status":kind, "message":checked_text(message),
            "output":checked_text(body[:start]), "mode":"strict single-marker fallback"}


def main():
    scratch = Path(tempfile.mkdtemp(prefix="observer-hybrid-", dir=os.environ.get("TMPDIR")))
    print(scratch, flush=True)
    harness = scratch / "coverageharness"
    subprocess.run(["go", "build", "-o", str(harness), "./tools/coverageharness"], cwd=ROOT, env=ENV, check=True)
    baseline = {r["id"]:r for r in csv.DictReader((l for l in (ROOT/"baselines/native-full.tsv").read_text().splitlines() if not l.startswith("#")), delimiter="\t")}
    selected = []
    for p in sorted((ROOT/"Corpus/coverage/exec").rglob("cases.tsv")):
        fam = str(p.parent.relative_to(ROOT/"Corpus/coverage/exec"))
        for line in p.read_text().splitlines():
            if not line or line.startswith("#"):
                continue
            f = line.split("\t")
            if len(f) >= 6 and (f[3] in ["fatal", "deadlock"] or (f[3] == "panic" and "init" in f[5].split(","))):
                rid = fam if f[0] == "-" else fam+"/"+f[0]
                selected.append((rid, p.parent, f))
    results = []
    for index, (rid, directory, fields) in enumerate(selected):
        case = scratch / str(index)
        args = [str(harness), "--input", str(directory/"main.go"), "--out", str(case), "--subject", fields[1], "--args", fields[2], "--expected-status", fields[3]]
        generated = subprocess.run(args, cwd=ROOT, env=ENV, capture_output=True)
        record = {"id":rid, "old":baseline.get(rid), "expected":fields[3]}
        if generated.returncode:
            record["refusal"] = "prototype wrapper generation failed: "+generated.stderr.decode(errors="backslashreplace")
            results.append(record)
            continue
        wrapper = case/"zz_golean_harness.go"
        source = wrapper.read_text()
        assert source.count("func main() {\n") == 1 and source.count("import (\n") == 1
        wrapper.write_text(source.replace("import (\n", 'import (\n _golean_debug "runtime/debug"\n',1).replace("func main() {\n", "func main() {\n"+SETUP,1))
        (case/"oracle.crash").write_bytes(b"")
        (case/"oracle.registered").write_bytes(b"")
        result = subprocess.run(["go", "run", "."], cwd=case, env=ENV, capture_output=True, timeout=45)
        (case/"oracle.stdout").write_bytes(result.stdout)
        (case/"oracle.stderr").write_bytes(result.stderr)
        crash = (case/"oracle.crash").read_bytes()
        ack = (case/"oracle.registered").read_bytes() == b"registered\n"
        record.update({"rc":result.returncode, "registered":ack, "crash_bytes":len(crash), "scratch":str(case),
                       "wrapper_sha256":hashlib.sha256(wrapper.read_bytes()).hexdigest()})
        try:
            record["observation"] = observe(result.stderr, crash, ack, result.returncode)
        except Refusal as e:
            record["refusal"] = str(e)
        results.append(record)
        print(rid, record.get("observation",record.get("refusal")), flush=True)
    output = {"mode":"DESIGN PROTOTYPE; actual same-run Go, no Lean run or full conformance claim",
              "go_version":subprocess.check_output(["go","version"],text=True).strip(),
              "scratch":str(scratch), "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "rows":results}
    (HERE/"hybrid-current-rows.json").write_text(json.dumps(output,indent=2)+"\n")


if __name__ == "__main__":
    main()
