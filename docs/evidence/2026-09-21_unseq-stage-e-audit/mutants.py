import json, copy, subprocess, sys
G=".lake/build/bin/golean"
def load(f): return json.load(open(".tmp/mut/%s.json"%f))
def node(j, fi, path):
    cur=j["funcs"][fi]["body"]
    for p in path: cur=cur[p]
    return cur
def occ(u,name): return [o for o in u["occs"] if o["name"]==name][0]
def run(tag, j, fn):
    out=".tmp/mut/%s.json"%tag; json.dump(j,open(out,"w"))
    r=subprocess.run([G,"native-json-run","--input",out,"--function",fn],capture_output=True,text=True)
    msg=(r.stdout+r.stderr).strip().replace("\n"," | ")
    print("%-28s exit=%d  %s"%(tag,r.returncode,msg[:330]))
    return r
INT={"int":"int","kind":"int"}; BOOL={"kind":"bool"}
# M1 unknown binder payload
j=load("unseq-conv-alloc"); u=node(j,6,["body",2]); occ(u,"lit1")["allocation"]["elems"][0]["value"]["name"]="$u99"; run("M1-unknown-binder-payload",j,"sliceLitVsCall")
# M2 recv on an int slot
j=load("unseq-recv-method"); u=node(j,2,["body",5]); occ(u,"recv0")["ch"]={"expr":"ident","name":"$u2","type":INT}; run("M2-recv-on-int-slot",j,"recvVsRead")
# M3 non-existent global
j=load("unseq-globals"); u=node(j,3,["body",1]); occ(u,"read1")["head"]["ptr"]["gid"]=9999; run("M3-bad-gid",j,"readVsCall")
# M4 struct-lit arity (2 args for 1-field T) inside new's value
j=load("unseq-conv-alloc"); u=node(j,5,["body",2]); a=occ(u,"new1")["allocation"]["value"]["args"]; a.append(copy.deepcopy(a[0])); run("M4-structlit-extra-arg",j,"addrLitVsCall")
# M5 AllocSpec elem type vs cell type
j=load("unseq-conv-alloc"); u=node(j,6,["body",2]); occ(u,"lit1")["allocation"]["elem"]=BOOL; run("M5-allocspec-cell-mismatch",j,"sliceLitVsCall")
# M6 negative make length constant
j=load("mk"); u=node(j,1,["body",2]); occ(u,"make0")["allocation"]["len"]["value"]="-1"; run("M6-make-negative-len",j,"makeVsRead")
# M7 recv binder duplicates call's binder
j=load("unseq-recv-method"); u=node(j,2,["body",5]); occ(u,"recv0")["binds"]=["$u4"]; run("M7-recv-dup-binder",j,"recvVsRead")
# M8 allocate slice-lit WITH an after edge
j=load("unseq-conv-alloc"); u=node(j,6,["body",2]); occ(u,"lit1")["after"]=["call3"]; r=run("M8-literal-with-after",j,"sliceLitVsCall")
r2=subprocess.run([G,"coverage-observations","--input",".tmp/mut/M8-literal-with-after.json","--function","sliceLitVsCall","--max-width","3","--max-sites","16","--cap","64","--work-cap","200000","--expect-status","ok"],capture_output=True,text=True); print("   M8 set:", r2.stdout.strip().replace("\n"," | ")[:200], "| exit",r2.returncode)
# M9 conversion head type vs cell
j=load("unseq-conv-alloc"); u=node(j,3,["body",2]); occ(u,"conv1")["head"]["type"]=INT; run("M9-conv-head-cell-mismatch",j,"convReadVsCall")
# M10a ref of an int binder as the receiver arg
j=load("unseq-recv-method"); u=node(j,6,["body",4]); occ(u,"call1")["args"][0]={"expr":"ref","id":"$u14"}; run("M10a-ref-int-binder-arg",j,"addrRecvVsSliceRead")
# M10b ref of a V-typed binder as receiver of Bump (mutates through it)
j=load("unseq-recv-method"); u=node(j,4,["body",2]); c=occ(u,"call2"); c["callee"]={"captured":[],"expr":"func-value","func":"$method$6:main.V0:Bump"}; c["args"]=[{"expr":"ref","id":"$u6"}]; run("M10b-ref-V-binder-arg",j,"valueRecvVsArgCall")
# M11 slice-lit elem index >= length
j=load("unseq-conv-alloc"); u=node(j,6,["body",2]); occ(u,"lit1")["allocation"]["elems"][0]["index"]=5; run("M11-slicelit-index-oob",j,"sliceLitVsCall")
# M12 slice-lit duplicate index
j=load("unseq-conv-alloc"); u=node(j,6,["body",2]); e=occ(u,"lit1")["allocation"]["elems"]; e.append(copy.deepcopy(e[0])); run("M12-slicelit-dup-index",j,"sliceLitVsCall")
# M13 new's value an ident atom
j=load("unseq-conv-alloc"); u=node(j,5,["body",2]); occ(u,"new1")["allocation"]["value"]={"expr":"ident","name":"$u11","type":INT}; run("M13-new-value-ident",j,"addrLitVsCall")
# M14 recv elem type disagreeing with the cell
j=load("unseq-recv-method"); u=node(j,2,["body",5]); occ(u,"recv0")["elem"]=BOOL; run("M14-recv-elem-mismatch",j,"recvVsRead")
# M15 make-slice with an unknown key
j=load("mk"); u=node(j,1,["body",2]); occ(u,"make0")["allocation"]["extra"]=1; run("M15-allocation-unknown-key",j,"makeVsRead")
