"""Bounded R-1 source evidence, not an observer/conformance acceptance gate.

Raw stdout/stderr are preserved in hex. In particular, invalid UTF-8 is
never silently decoded into a JSON string. These standalone Go executions
do not alter production sources or substitute for the pending checked view.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
ENV = dict(os.environ, GO111MODULE="off", GOFLAGS="", GODEBUG="panicnil=0",
           GOTRACEBACK="system", GOCACHE=str(ROOT / "artifacts/go-build-cache"))

CASES = {
    "equal-literal": r'''package main
func main() { defer func(){ recover(); panic("orig") }(); panic("orig") }
''',
    "recovered-rethrow": r'''package main
func main() { defer func(){ panic(recover()) }(); panic("orig") }
''',
    "computed-equal": r'''package main
//go:noinline
func join(a,b string) string { return a+b }
func main() { defer func(){ recover(); panic(join("or","ig")) }(); panic("orig") }
''',
    "invalid-before-newline": r'''package main
func main() { panic("\xff\x00\\\nZ") }
''',
    "invalid-after-newline": r'''package main
func main() { panic("head\n\xff") }
''',
    "invalid-recovered-rethrow": r'''package main
import("encoding/json";"os")
func main() {
 defer func(){
  r:=recover(); s,ok:=r.(string); bs:=[]int{}
  for _,b:=range []byte(s) { bs=append(bs,int(b)) }
  json.NewEncoder(os.Stdout).Encode(map[string]any{"string_kind":ok,"bytes":bs,"same":s=="\xff\x00\\\nZ"})
 }()
 defer func(){panic(recover())}()
 panic("\xff\x00\\\nZ")
}
''',
}

def main():
    scratch = Path(tempfile.mkdtemp(prefix="string-member-probes-", dir=os.environ.get("TMPDIR")))
    rows=[]
    for name,source in CASES.items():
        case=scratch/name
        case.mkdir()
        p=case/"main.go"
        p.write_text(source)
        got=subprocess.run(["go","run","main.go"],cwd=case,env=ENV,capture_output=True,timeout=45)
        (case/"stdout").write_bytes(got.stdout)
        (case/"stderr").write_bytes(got.stderr)
        record={"name":name,"source":source,"source_sha256":hashlib.sha256(p.read_bytes()).hexdigest(),
                "rc":got.returncode,"stdout_hex":got.stdout.hex(),"stderr_hex":got.stderr.hex(),"scratch":str(case)}
        if name == "invalid-recovered-rethrow":
            decoded=json.loads(got.stdout)
            assert got.returncode==0 and decoded=={"string_kind":True,"bytes":[255,0,92,10,90],"same":True}
            record["recovered_value_check"]=decoded
        else:
            assert got.returncode==1 and got.stderr.endswith(b"\nexit status 2\n")
        rows.append(record)
        print(name,got.returncode,flush=True)
    evidence={"scope":"standalone native source/report evidence only; no model or observer acceptance",
              "go_version":subprocess.check_output(["go","version"],env=ENV,text=True).strip(),
              "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),"rows":rows}
    (HERE/"string-member-probes.json").write_text(json.dumps(evidence,indent=2)+"\n")
    print(scratch,flush=True)

if __name__=="__main__":
    main()
