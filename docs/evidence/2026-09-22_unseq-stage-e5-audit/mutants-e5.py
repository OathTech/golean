# Audit mutants for the Stage E5 decoder arms (map-lit, wide append/copy/map-lookup/type-assert, payload ref/globaladdr,
# two-binder recv, var target). One edit per mutant on a tracked hand-built wire or on the auditor's probe wire; each is
# driven through the REAL CLI (`golean native-json-run`); a mutant that RUNS (exit 0) is also enumerated.
import json, copy, subprocess, sys, os
os.chdir('/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5')
G=".lake/build/bin/golean"
INT={"int":"int","kind":"int"}; BOOL={"kind":"bool"}; STR={"kind":"string"}
def load(p): return json.load(open(p))
def unseq_of(j, fname):
    for f in j["funcs"]:
        if f.get("name")==fname:
            acc=[]
            def walk(o):
                if isinstance(o,dict):
                    if o.get("stmt")=="unseq": acc.append(o)
                    for v in o.values(): walk(v)
                elif isinstance(o,list):
                    for v in o: walk(v)
            walk(f["body"]); return acc[0]
    raise KeyError(fname)
def occ(u,name): return [o for o in u["occs"] if o["name"]==name][0]
def cell(u,cid): return [c for c in u["cells"] if c["id"]==cid][0]
results=[]
def run(tag, j, fn, expect):
    out=".tmp/mut/%s.json"%tag; json.dump(j,open(out,"w"))
    r=subprocess.run([G,"native-json-run","--input",out,"--function",fn],capture_output=True,text=True)
    msg=(r.stdout+r.stderr).strip().replace("\n"," | ")
    verdict = "REFUSED-DECODE" if r.returncode==1 and "unseq:" in msg else ("REFUSED-LATE" if r.returncode!=0 else "RAN")
    setline=""
    if r.returncode==0:
        r2=subprocess.run([G,"coverage-observations","--input",out,"--function",fn,"--max-width","8","--max-sites","32","--cap","256","--work-cap","400000","--expect-status","ok,panic"],capture_output=True,text=True)
        setline=" SET: "+(r2.stdout+r2.stderr).strip().replace("\n"," | ")[:400]
    print("%-32s %-14s exit=%d  %s%s\n    expected: %s"%(tag,verdict,r.returncode,msg[:420],setline,expect))
    results.append((tag,verdict,r.returncode,msg[:300]))
P='.tmp/wires/p_multi.nativefrontend-tip.json'
# ---- map-lit arm (Tests/unseq-wire/e5cmaplit.json, function e5cmaplit: lit2 = map-lit {1: $u1}) ----
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries'][0]['key']={"expr":"ref","id":"x"}; run("mA1-maplit-key-ref",j,'e5cmaplit',"an address as an int-keyed map's key: refuse (type) or late by type")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries'][0]['key']={"expr":"bool","value":True}; run("mA2-maplit-key-bool-on-int",j,'e5cmaplit',"key typed as a bool on keyType int: refuse or late by type")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries'][0]['value']={"expr":"ref","id":"$u1"}; run("mA3-maplit-value-ref-binder",j,'e5cmaplit',"F2: address of a binder cell as a payload — refuse by name")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); cell(u,'$u2')['type']={"kind":"map","key":INT,"value":BOOL}; run("mA4-maplit-cell-type",j,'e5cmaplit',"cell map[int]bool vs valueType int: refuse (typeMismatch)")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['after']=['call0']; run("mA5-maplit-after-edge",j,'e5cmaplit',"audit F8 / PENDING item 4: an `after` on a literal allocate DECODES (policy not on the wire)")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries'][0]['value']={"expr":"string","type":STR,"value":"z"}; run("mA6-maplit-value-string-on-int",j,'e5cmaplit',"value typed string on valueType int: refuse or late by type")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries']={}; run("mA7-maplit-entries-object",j,'e5cmaplit',"entries not an array: StrictJson refusal")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); e=occ(u,'lit2')['allocation']['entries']; e.append(copy.deepcopy(e[0])); run("mA8-maplit-dup-const-key-control",j,'e5cmaplit',"control: duplicate constant key refused (lane's mutant class)")
# ---- wide append (Tests/unseq-wire/native-e5append.json, e5append: append2 {slice $u1, elems $u2} -> $u3) ----
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['wide']['elems']={"expr":"int","type":INT,"value":"3"}; run("mW1-append-elems-int-atom",j,'e5append',"an int atom where a slice is expected: refuse or late by type")
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['wide']['slice']={"expr":"ref","id":"s"}; run("mW2-append-slice-ref-local",j,'e5append',"a ref (not an atom) as a wide operand: hidden read refusal")
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['wide']['elem']=BOOL; run("mW3-append-elem-vs-cell",j,'e5append',"elem bool vs cell []int: refuse")
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['wide']['extra']=1; run("mW4-wide-unknown-key",j,'e5append',"unknown key: refuse")
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['region']="nosuch"; run("mW5-wide-unknown-region",j,'e5append',"unknown region: refuse")
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['binds']=["$u1"]; run("mW6-append-dup-result-cell",j,'e5append',"binder = the base read's cell: duplicate result")
# ---- wide copy (Tests/unseq-wire/e5copy.json, e5copy: copy0 -> $u0; access1 -> $u1) ----
j=load('Tests/unseq-wire/e5copy.json'); u=unseq_of(j,'e5copy'); occ(u,'copy0')['binds']=["$u1"]; run("mW7-copy-dup-result",j,'e5copy',"duplicate result")
j=load('Tests/unseq-wire/e5copy.json'); u=unseq_of(j,'e5copy'); occ(u,'copy0')['wide']['src']={"expr":"int","type":INT,"value":"7"}; run("mW8-copy-src-int-atom",j,'e5copy',"an int atom as copy's source: refuse or late by type")
# ---- wide map-lookup / type-assert / two-binder recv (duplicate binders inside ONE occurrence) ----
j=load(P); u=unseq_of(j,'boolMapCommaOk'); occ(u,'lookup2')['binds']=["$u94","$u94"]; run("mW9-lookup-dup-binders-bool",j,'boolMapCommaOk',"the same bool cell twice (value and ok): duplicate result expected")
j=load(P); u=unseq_of(j,'chanBoolCommaOk'); r=[o for o in u['occs'] if o['kind']=='recv'][0]; r['binds']=[r['binds'][1],r['binds'][1]]; run("mW10-recv-dup-binders-bool",j,'chanBoolCommaOk',"the same bool cell twice on a chan bool receive: duplicate result expected")
j=load(P); u=unseq_of(j,'commaOkMapVsWriter'); occ(u,'lookup2')['wide']['index']={"expr":"string","type":STR,"value":"k"}; run("mW11-lookup-index-string-on-int",j,'commaOkMapVsWriter',"a string key atom on an int-keyed map: refuse or late by type")
j=load(P); u=unseq_of(j,'commaOkMapVsWriter'); occ(u,'lookup2')['wide']['keyType']=STR; run("mW12-lookup-keyType-vs-base",j,'commaOkMapVsWriter',"keyType string vs the map[int]int base: refuse or late by type")
j=load('Tests/unseq-wire/e5bassert.json'); u=unseq_of(j,'e5bassert'); occ(u,'assert0')['wide']['target']=STR; run("mW13-assert-target-vs-cell",j,'e5bassert',"target string vs value cell int: refuse")
j=load('Tests/unseq-wire/e5bassert.json'); u=unseq_of(j,'e5bassert'); occ(u,'assert0')['wide']['operand']={"expr":"ref","id":"$u1"}; run("mW14-assert-operand-ref-binder",j,'e5bassert',"F2 text")
j=load('Tests/unseq-wire/e5bassert.json'); u=unseq_of(j,'e5bassert'); occ(u,'assert0')['binds']=["$u0","$u0"]; run("mW15-assert-dup-binders-int",j,'e5bassert',"value and ok into the same int cell: refuse (ok cell not bool) — type check")
# ---- payload / argument addresses (e5dlit: new0 struct-lit args [ref x]; e5daddr: call0 args [ref x]) ----
j=load('Tests/unseq-wire/e5dlit.json'); u=unseq_of(j,'e5dlit'); occ(u,'new0')['allocation']['value']['args'][0]={"expr":"ref","id":"nosuch"}; run("mD1-payload-ref-undeclared",j,'e5dlit',"ref of an undeclared local as a payload: refuse or late by name")
j=load('Tests/unseq-wire/e5dlit.json'); u=unseq_of(j,'e5dlit'); occ(u,'new0')['allocation']['value']['args'][0]={"expr":"globaladdr","gid":9999}; run("mD2-payload-globaladdr-oob",j,'e5dlit',"globaladdr out of range as a payload: refuse")
j=load('Tests/unseq-wire/e5dlit.json'); u=unseq_of(j,'e5dlit'); occ(u,'new0')['allocation']['value']['args'][0]={"expr":"ref","id":"m"}; run("mD3-payload-ref-func-local",j,'e5dlit',"address of the func-typed local m as a *int field payload: type confusion — refuse or late by type")
jj=load('Tests/unseq-wire/e5daddr.json'); fn=[f['name'] for f in jj['funcs'] if any(True for _ in [0]) and 'e5daddr' in f['name']][0]
j=load('Tests/unseq-wire/e5daddr.json'); u=unseq_of(j,fn); occ(u,'call0')['args'][0]={"expr":"ref","id":"nosuch"}; run("mD4-arg-ref-undeclared",j,fn,"ref of an undeclared local as an argument: refuse or late by name")
# ---- min head (e5minmax: min0 {args [x, 100]}) ----
j=load('Tests/unseq-wire/e5minmax.json'); u=unseq_of(j,'e5minmax'); occ(u,'min0')['head']['type']=STR; run("mM1-min-type-string-int-args",j,'e5minmax',"head type string over int args, cell int: refuse (disagrees with cell) or late")
j=load('Tests/unseq-wire/e5minmax.json'); u=unseq_of(j,'e5minmax'); occ(u,'min0')['head']['args'][0]={"expr":"ref","id":"x"}; run("mM2-min-arg-ref",j,'e5minmax',"not an atom: refuse")
j=load('Tests/unseq-wire/e5minmax.json'); u=unseq_of(j,'e5minmax'); occ(u,'min0')['head']['args']=[]; run("mM3-min-no-args",j,'e5minmax',"no operands: refuse")
j=load('Tests/unseq-wire/e5minmax.json'); u=unseq_of(j,'e5minmax'); occ(u,'min0')['head']['args'][1]={"expr":"string","type":STR,"value":"a"}; run("mM4-min-mixed-int-string-args",j,'e5minmax',"mixed int/string operands: refuse or late by type")
# ---- var target plans (e5btuple: target3 {var x}; stores) ----
j=load('Tests/unseq-wire/e5btuple.json'); u=unseq_of(j,'e5btuple'); occ(u,'target3')['lhs']['id']="nosuch"; run("mB1-var-target-undeclared",j,'e5btuple',"a .var plan on an undeclared variable: refuse or late by name")
j=load('Tests/unseq-wire/e5btuple.json'); u=unseq_of(j,'e5btuple'); occ(u,'target3')['lhs']['id']="$u2"; run("mB2-var-target-binder",j,'e5btuple',"a binder as a store target: refuse (unseqCheckTargetShape)")
j=load('Tests/unseq-wire/e5btuple.json'); u=unseq_of(j,'e5btuple'); u['stores'][1]['value']="$t0"; run("mB3-store-value-target-binder",j,'e5btuple',"a TARGET binder as a store value: sort mismatch")
j=load('Tests/unseq-wire/e5btuple.json'); u=unseq_of(j,'e5btuple'); u['stores'].append(copy.deepcopy(u['stores'][0])); run("mB4-store-same-target-twice",j,'e5btuple',"the same target stored twice: Go allows x[0], x[0] = ..; a decode-level question — observe")
print("\nSUMMARY"); 
for t,v,rc,m in results: print("%-32s %-14s exit=%d"%(t,v,rc))
