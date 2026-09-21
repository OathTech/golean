import json, copy, subprocess
G=".lake/build/bin/golean"
def load(f): return json.load(open(".tmp/mut/%s.json"%f))
def node(j, fi, path):
    cur=j["funcs"][fi]["body"]
    for p in path: cur=cur[p]
    return cur
def occ(u,name): return [o for o in u["occs"] if o["name"]==name][0]
def move_after(u, name, after):
    o=occ(u,name); u["occs"].remove(o); i=[x["name"] for x in u["occs"]].index(after); u["occs"].insert(i+1,o)
def run(tag, j, fn, extra=()):
    out=".tmp/mut/%s.json"%tag; json.dump(j,open(out,"w"))
    r=subprocess.run([G,"native-json-run","--input",out,"--function",fn,*extra],capture_output=True,text=True)
    print("%-28s exit=%d  %s"%(tag,r.returncode,(r.stdout+r.stderr).strip().replace("\n"," | ")[:330]))
INT={"int":"int","kind":"int"}
# M2b recv on an int slot, ordered after read1 and with the recv's consumers still after it
j=load("unseq-recv-method"); u=node(j,2,["body",5]); occ(u,"recv0")["ch"]={"expr":"ident","name":"$u2","type":INT}; move_after(u,"recv0","read1"); occ(u,"call3")["after"]=["recv0"]; run("M2b-recv-on-int-slot",j,"recvVsRead")
# M10a2 ref of an int binder as receiver arg, ordered after its producer
j=load("unseq-recv-method"); u=node(j,6,["body",4]); occ(u,"call1")["args"][0]={"expr":"ref","id":"$u14"}; move_after(u,"call1","access0"); run("M10a2-ref-int-binder-arg",j,"addrRecvVsSliceRead")
# M8 full set
r=subprocess.run([G,"coverage-observations","--input",".tmp/mut/M8-literal-with-after.json","--function","sliceLitVsCall","--max-width","3","--max-sites","16","--cap","64","--work-cap","200000","--expect-status","ok"],capture_output=True,text=True)
print("M8 set lines:", [json.loads(l)["values"][0]["value"] for l in r.stdout.strip().splitlines()], "exit", r.returncode)
# M16 func-value capture = ref of a binder (setG has no captures)
j=load("unseq-globals"); u=node(j,4,["body",1]); occ(u,"call1")["callee"]["captured"]=[{"expr":"ref","id":"$u3"}]; move_after(u,"call1","read0"); run("M16-capture-ref-binder",j,"compoundVsCall")
# M17 invoke arg ref of a SOURCE local slice (F2-class: an address, but of a slice variable) — is it admitted? use addrRecvVsSliceRead: ref s
j=load("unseq-recv-method"); u=node(j,6,["body",4]); occ(u,"call1")["args"][0]={"expr":"ref","id":"s"}; run("M17-ref-slice-local-arg",j,"addrRecvVsSliceRead")
