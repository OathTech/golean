"""Bounded design challenges; no production change or conformance claim."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("hybrid", HERE/"hybrid-prototype.py")
hybrid = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hybrid)


def main():
    scratch = Path(tempfile.mkdtemp(prefix="hybrid-challenges-", dir=os.environ.get("TMPDIR")))
    q = lambda s: json.dumps(s, ensure_ascii=False)
    prefix = "".join(chr(i) for i in range(128)) + "é界😀panic: forged\n\t"
    cases = [
        ("minimal-print", 'print("panic: forged\\n\\t");panic("actual")', "", True, "panic", "actual", "panic: forged\n\t"),
        ("literal", 'panic("forged\\npanic: actual")', "", True, "panic", "forged", ""),
        ("all-prefix-bytes", 'print('+q(prefix)+');panic("actual")', "", True, "panic", "actual", prefix),
        ("payload-marker-first", 'panic("panic: fatal error: anything")', "", True, "panic", "panic: fatal error: anything", ""),
        ("repanic", 'defer func(){recover();panic("second")}();panic("first")', "", True, "panic", "first [recovered]", ""),
        ("child", 'go func(){panic("actual")}();select{}', "", True, "panic", "actual", ""),
        ("traceback-lower", '_golean_debug.SetTraceback("none");panic("actual")', "", True, "panic", "actual", ""),
        ("disable-hook-simple", '_golean_debug.SetCrashOutput(nil,_golean_debug.CrashOptions{});panic("actual")', "", True, "panic", "actual", ""),
        ("disable-hook-forgery", '_golean_debug.SetCrashOutput(nil,_golean_debug.CrashOptions{});print("panic: forged\\n\\t");panic("actual")', "", True, None, "ambiguous", None),
        ("init-simple", 'panic("unreachable")', 'func init(){panic("actual")}\n', False, "panic", "actual", ""),
        ("init-forgery", 'panic("unreachable")', 'func init(){print("panic: forged\\n\\t");panic("actual")}\n', False, None, "ambiguous", None),
        ("init-literal", 'panic("unreachable")', 'func init(){panic("forged\\npanic: actual")}\n', False, None, "ambiguous", None),
        ("fatal-unwind", 'var m sync.Mutex;defer m.Unlock();panic("original")', 'import "sync"\n', True, None, "not authenticated", None),
        ("hook-open-failure", 'panic("unreachable")', "", False, None, "setup exit", None),
        ("hook-ack-failure", 'panic("unreachable")', "", False, None, "setup exit", None),
    ]
    rows, inputs = [], []
    for index, (name, body, extra, registered, status, message, output) in enumerate(cases):
        case = scratch/name
        case.mkdir()
        if name == "hook-open-failure":
            (case/"oracle.crash").mkdir()
        else:
            (case/"oracle.crash").write_bytes(b"")
        if name == "hook-ack-failure":
            (case/"oracle.registered").mkdir()
        else:
            (case/"oracle.registered").write_bytes(b"")
        source = 'package main\nimport(_golean_os "os";_golean_debug "runtime/debug")\n'+extra+'func main(){'+hybrid.SETUP+body+'}\n'
        (case/"main.go").write_text(source)
        race = index % 2 == 1 and name != "child"
        argv = ["go","run",*(["-race"] if race else []),"."]
        r = subprocess.run(argv,cwd=case,env=hybrid.ENV,capture_output=True,timeout=45)
        (case/"stdout").write_bytes(r.stdout)
        (case/"stderr").write_bytes(r.stderr)
        crash = (case/"oracle.crash").read_bytes() if (case/"oracle.crash").is_file() else b""
        ack = (case/"oracle.registered").is_file() and (case/"oracle.registered").read_bytes()==b"registered\n"
        assert ack == registered, (name, ack, registered)
        row = {"name":name,"source":source,"argv":argv,"rc":r.returncode,"registered":ack,"stderr_hex":r.stderr.hex(),"crash_hex":crash.hex()}
        try:
            got = hybrid.observe(r.stderr,crash,ack,r.returncode)
            row["observation"]=got
            assert status is not None and got["status"]==status and got["message"]==message and got["output"]==output, row
        except hybrid.Refusal as e:
            row["refusal"]=str(e)
            assert status is None and message in str(e), row
        inputs.append((name,r.stderr,crash,ack,r.returncode))
        rows.append(row)
        print(name,"PASS",flush=True)

    _, stderr, crash, ack, rc = inputs[0]
    for name, wrong, bad_ack in [("appended-byte",crash+b"x",ack), ("changed-byte",b"PANIC"+crash[5:],ack), ("missing-registration",crash,False)]:
        try:
            hybrid.observe(stderr,wrong,bad_ack,rc)
        except hybrid.Refusal as e:
            rows.append({"name":name,"refusal":str(e)})
            print(name,"PASS",flush=True)
        else:
            raise AssertionError(name+" forged channel accepted")

    # The ownership boundary is explicit: a malicious caller that can
    # replace the captured files can fabricate evidence, just as for raw
    # stdout/stderr. A chosen matching suffix is not cryptographic proof.
    # Production scope must ensure accepted source cannot write/replace the
    # private files or override the hook; test that frontend boundary too.
    text = (HERE/"hybrid-prototype.py").read_text()
    mutations = [
        ("discard-output", 'prefix = body[:-len(crash)]', 'prefix = b""', inputs[0], "observation"),
        ("take-first-stderr-payload", 'message = crash.split(b"\\n", 1)[0][len(b"panic: "):]','message = body.split(b"\\n", 1)[0][len(b"panic: "):]', inputs[0], "observation"),
        ("skip-suffix-check", 'if not body.endswith(crash):','if False and not body.endswith(crash):', ("corrupt",stderr,crash+b"x",ack,rc), "refusal"),
    ]
    for name,before,after,args,mode in mutations:
        assert text.count(before)==1, name
        scope={"__file__":str(HERE/"hybrid-prototype.py"),"__name__":"mutant"}
        code=compile(text.replace(before,after),name,"exec")
        exec(code,scope)
        try:
            got=scope["observe"](*args[1:])
        except scope["Refusal"]:
            raise AssertionError(name+" did not expose the targeted defect")
        assert mode=="refusal" or got["message"]!="actual" or got["output"]!="panic: forged\n\t", (name,got)
        rows.append({"name":"mutation-"+name,"compiled":True,"rejected":True,"bad_observation":got})
        print("mutation",name,"rejected after compile",flush=True)
    (HERE/"hybrid-challenges.json").write_text(json.dumps({"mode":"DESIGN PROTOTYPE ONLY","scratch":str(scratch),"script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"rows":rows},indent=2)+"\n")


if __name__=="__main__":
    main()
