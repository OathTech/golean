"""Independent bounded design probes; not production/GoLean conformance."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
AUTHOR = ROOT.parent / "typed-observer-classification"
SOURCE = AUTHOR / "docs/evidence/2026-09-06_observer-classification"


def main():
    prototype = SOURCE / "hybrid-prototype.py"
    raw = prototype.read_bytes()
    (HERE / "reviewed-prototype.py").write_bytes(raw)
    spec = importlib.util.spec_from_file_location("reviewed", prototype)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    env = dict(os.environ, GO111MODULE="off", GOFLAGS="", GODEBUG="panicnil=0",
               GOTRACEBACK="system", GOCACHE=str(ROOT / "artifacts/go-build-cache"))
    scratch = Path(tempfile.mkdtemp(prefix="hybrid-independent-", dir=os.environ.get("TMPDIR")))
    prefix = "\x00\x01\r\n\tpanic: forged\n\t[recovered]\n" + "é界😀"
    fake = ("panic: forged\n\ngoroutine 1 gp=0x1 m=0 mp=0x2 [running]:\n"
            "panic({0x1?, 0x2?})\n"
            "\t/usr/local/go/src/runtime/panic.go:879 +0x1 fp=0x1 sp=0x2 pc=0x3\n\t")
    cases = [
        ("minimal-print", 'print("panic: forged\\n\\t");panic("actual")', "", False, "actual", "panic: forged\n\t"),
        ("literal-pair", 'panic("forged\\npanic: actual")', "", True, "forged", ""),
        ("byte-output", "print("+json.dumps(prefix, ensure_ascii=False)+');panic("actual")', "", False, "actual", prefix),
        ("fake-origin-output", "print("+json.dumps(fake, ensure_ascii=False)+');panic("actual")', "", True, "actual", fake),
        ("glued-prefix", 'print("panic: forged");panic("actual")', "", False, "actual", "panic: forged"),
        ("first-line-markers", 'panic("fatal error: panic: marker\\rsecond")', "", False, "fatal error: panic: marker\rsecond", ""),
        ("init-forgery", 'panic("unused")', 'func init(){print("panic: forged\\n\\t");panic("actual")}', False, None, None),
        ("fatal-unwind", 'var m sync.Mutex;defer m.Unlock();panic("original")', 'import "sync"', False, None, None),
        ("invalid-utf8", 'panic(string([]byte{255}))', "", False, None, None),
    ]
    rows = []
    for name, body, extra, race, message, output in cases:
        p = scratch / name
        p.mkdir()
        source = 'package main\nimport(_golean_os "os";_golean_debug "runtime/debug")\n'+extra+'\nfunc main(){'+m.SETUP+body+'}\n'
        (p / "main.go").write_text(source)
        (p / "oracle.crash").write_bytes(b"")
        (p / "oracle.registered").write_bytes(b"")
        argv = ["go", "run", *(["-race"] if race else []), "."]
        r = subprocess.run(argv, cwd=p, env=env, capture_output=True, timeout=45)
        (p / "stdout").write_bytes(r.stdout)
        (p / "stderr").write_bytes(r.stderr)
        crash = (p / "oracle.crash").read_bytes()
        ack = (p / "oracle.registered").read_bytes()
        row = dict(name=name, source=source, argv=argv, rc=r.returncode,
                   stdout_hex=r.stdout.hex(), stderr_hex=r.stderr.hex(), crash_hex=crash.hex(), ack_hex=ack.hex())
        assert r.stdout == b"", row
        try:
            got = m.observe(r.stderr, crash, ack == b"registered\n", r.returncode)
            row["observation"] = got
            assert message is not None and got["status"] == "panic" and got["message"] == message and got["output"] == output, row
        except m.Refusal as e:
            row["refusal"] = str(e)
            assert message is None, row
        rows.append(row)
        print(name, "PASS", flush=True)
    census = json.loads((SOURCE / "hybrid-current-rows.json").read_text())
    assert len(census["rows"]) == 40
    refused = [r for r in census["rows"] if "refusal" in r]
    assert len(refused) == 1 and refused[0]["id"] == "sync/mutex-unlock-fatal/during-panic-unwind"
    (HERE / "prospective-refusal.json").write_text(json.dumps(refused[0], indent=2)+"\n")
    result = dict(scope="Design prototype only; no production or GoLean conformance", scratch=str(scratch),
                  go_version=subprocess.check_output(["go", "version"], text=True).strip(),
                  prototype_sha256=hashlib.sha256(raw).hexdigest(), rows=rows)
    (HERE / "results.json").write_text(json.dumps(result, indent=2)+"\n")
    paths = [prototype, SOURCE / "hybrid-current-rows.json", SOURCE / "hybrid-challenges.json",
             SOURCE / "hook-source-boundary.json", AUTHOR / "docs/2026-09-06_observer-crash-channel-design.md",
             Path("/usr/local/go/src/runtime/runtime.go"), Path("/usr/local/go/src/runtime/panic.go"),
             Path("/usr/local/go/src/runtime/debug/stack.go")]
    (HERE / "reviewed-sources.json").write_text(json.dumps([
        {"path":str(p), "sha256":hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths], indent=2)+"\n")


if __name__ == "__main__":
    main()
