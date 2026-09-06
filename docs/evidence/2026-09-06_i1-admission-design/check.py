"""Reproduce the source-bound marker and exploratory call-closure census."""
from pathlib import Path
import collections
import csv
import hashlib
import json
import re
import tarfile

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / "2026-09-06_typed-preflight"
PARENT = json.loads((HERE / "parent-census.json").read_text())
STATUSES = {r["id"]: r for r in csv.DictReader((BASE / "full.tsv").read_text().splitlines(), delimiter="\t")}
MANIFEST = {r[0]: r for r in (line.split("\t") for line in (BASE / "full-manifest.tsv").read_text().splitlines())}
ARCHIVE = BASE / "coverage-artifacts.tar.gz"
assert hashlib.sha256(ARCHIVE.read_bytes()).hexdigest() == PARENT["archive_sha256"]


def markers(x, path="$"):
    if isinstance(x, dict):
        if x.get("kind") == "unsupported" or isinstance(x.get("unsupported"), str):
            yield {"path":path,"name":x.get("name"),"kind":x.get("kind"),
                   "reason":x.get("unsupported",x.get("feature"))}
        for k,v in x.items(): yield from markers(v,path+"."+k)
    elif isinstance(x,list):
        for i,v in enumerate(x): yield from markers(v,path+f"[{i}]")


def refs(x):
    if isinstance(x,dict):
        if isinstance(x.get("func"),str): yield x["func"]
        for v in x.values(): yield from refs(v)
    elif isinstance(x,list):
        for v in x: yield from refs(v)


rows=[];closures=[]
with tarfile.open(ARCHIVE,"r:gz") as tar:
    for m in tar:
        if not (m.name.startswith("native/") and m.name.endswith("/wire.json")): continue
        cid=m.name[len("native/"):-len("/wire.json")]
        if cid not in STATUSES: continue
        raw=tar.extractfile(m).read();wire=json.loads(raw);ms=list(markers(wire))
        if not ms: continue
        s=STATUSES[cid]
        rows.append({"id":cid,"status":s["result"],"stage":s["stage"],
                     "wire_sha256":hashlib.sha256(raw).hexdigest(),"markers":ms})
        assert all(re.fullmatch(r"\$\.(funcs|methods)\[\d+\]|\$\.types\[\d+\]\.def",m["path"]) for m in ms)
        if s["result"]!="PASS": continue
        nodes={f["name"]:f for f in wire["funcs"]};anchors={};byname=collections.defaultdict(list)
        for method in wire["methods"]:
            key=method["recvType"]+"."+method["name"];nodes[key]=method
            if method.get("interface") is True: anchors[key]=method["name"]
            else: byname[method["name"]].append(key)
        entry=MANIFEST[cid][2];roots=[entry]+(["$pkginit"] if "$pkginit" in nodes else [])
        seen={};todo=[(r,[r]) for r in roots];hits=[];missing=[]
        while todo:
            name,path=todo.pop(0)
            if name in seen: continue
            seen[name]=path
            if name not in nodes: missing.append({"target":name,"path":path});continue
            node=nodes[name]
            if "unsupported" in node:
                hits.append({"target":name,"path":path,"reason":node["unsupported"]});continue
            children=byname[anchors[name]] if name in anchors else sorted(set(refs(node.get("body"))))
            for child in children:
                if child not in seen:todo.append((child,path+[child]))
        closures.append({"id":cid,"entry":entry,"quarantined_reached":hits,
                         "missing_refs":missing,"syntactic_closure_size":len(seen)})

assert sorted(rows,key=lambda r:r["id"])==sorted(PARENT["cases"],key=lambda r:r["id"])
assert closures==json.loads((HERE/"syntactic-closure.json").read_text())["reports"]
counts=collections.Counter(r["status"] for r in rows)
assert dict(counts)=={"PASS":522,"FAIL":174}
assert len(closures)==522 and sum(bool(r["quarantined_reached"]) for r in closures)==70
print("PASS: exact696marker records; all declaration-boundary paths;522PASS/174FAIL; exact522closure records;70syntactic quarantine hits.")
