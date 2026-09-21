import json, subprocess
G=".lake/build/bin/golean"; INT={"int":"int","kind":"int"}
def load(f): return json.load(open(".tmp/mut/%s.json"%f))
def node(j, fi, path):
    cur=j["funcs"][fi]["body"]
    for p in path: cur=cur[p]
    return cur
def occ(u,name): return [o for o in u["occs"] if o["name"]==name][0]
def run(tag, j, fn):
    out=".tmp/mut/%s.json"%tag; json.dump(j,open(out,"w"))
    r=subprocess.run([G,"native-json-run","--input",out,"--function",fn],capture_output=True,text=True)
    print("%-30s exit=%d  %s"%(tag,r.returncode,(r.stdout+r.stderr).strip().replace("\n"," | ")[:300]))
# M18 ref of a binder produced by a NESTED call, passed as the outer call's argument
j=load("unseq-recv-method"); u=node(j,4,["body",2]); c=occ(u,"call2"); c["args"][1]={"expr":"ref","id":"$u7"}; run("M18-ref-binder-nested-call-arg",j,"valueRecvVsArgCall")
# M19 ref of a binder boxed inside a to-interface argument
j=load("unseq-recv-method"); u=node(j,4,["body",2]); c=occ(u,"call2"); c["args"][1]={"expr":"to-interface","operand":{"expr":"ref","id":"$u7"},"target":{"kind":"interface","name":"any"}}; run("M19-ref-binder-boxed-arg",j,"valueRecvVsArgCall")
# M20 ref of a binder as new's value payload
j=load("unseq-conv-alloc"); u=node(j,9,["body",2]); a=occ(u,"new1")["allocation"]; a["value"]={"expr":"ref","id":"$u0"}; run("M20-ref-binder-new-payload",j,"newExprVsCall")
# M21 new's value typed bool vs elemType int (the fix's type check)
j=load("unseq-conv-alloc"); u=node(j,9,["body",2]); a=occ(u,"new1")["allocation"]; a["value"]={"expr":"bool","type":{"kind":"bool"},"value":True}; run("M21-new-value-type-mismatch",j,"newExprVsCall")
# M22 make-slice constant len 2 > constant cap 1
j=load("mk"); u=node(j,1,["body",2]); a=occ(u,"make0")["allocation"]; a["len"]={"expr":"int","type":INT,"value":"2"}; a["cap"]={"expr":"int","type":INT,"value":"1"}; run("M22-make-len-over-cap",j,"makeVsRead")
# M23 run-time size class: make len from a slot holding -1 must PANIC at run, not refuse at decode
j=load("mk"); u=node(j,1,["body",2]); a=occ(u,"make0")["allocation"]; a["len"]={"expr":"ident","name":"$u2","type":INT}
# $u2 is read2 (x); reorder so make0 comes after read2 and len1/call4 after; set x := -1 in the program? simpler: leave and observe the order refusal
run("M23-make-len-slot-order",j,"makeVsRead")
