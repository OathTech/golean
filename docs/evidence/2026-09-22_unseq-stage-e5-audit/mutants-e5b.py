import json, copy, subprocess, os
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
def occ(u,name): return [o for o in u["occs"] if o["name"]==name][0]
def run(tag, j, fn, expect):
    out=".tmp/mut/%s.json"%tag; json.dump(j,open(out,"w"))
    r=subprocess.run([G,"native-json-run","--input",out,"--function",fn],capture_output=True,text=True)
    msg=(r.stdout+r.stderr).strip().replace("\n"," | ")
    verdict = "REFUSED-DECODE" if r.returncode==1 and "unseq:" in msg else ("REFUSED-LATE" if r.returncode!=0 else "RAN")
    setline=""
    if r.returncode==0:
        r2=subprocess.run([G,"coverage-observations","--input",out,"--function",fn,"--max-width","8","--max-sites","32","--cap","256","--work-cap","400000","--expect-status","ok,panic"],capture_output=True,text=True)
        setline=" SET: "+(r2.stdout+r2.stderr).strip().replace("\n"," | ")[:400]
    print("%-34s %-14s exit=%d  %s%s\n    expected: %s"%(tag,verdict,r.returncode,msg[:420],setline,expect))
SC={"expr":"string","bytes":[122],"type":STR}
P='.tmp/wires/p_multi.nativefrontend-tip.json'
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries'][0]['value']=SC; run("mA6b-maplit-value-string-on-int",j,'e5cmaplit',"a string constant payload on valueType int: refuse or late by type")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'lit2')['allocation']['entries'][0]['key']=SC; run("mA9-maplit-key-string-on-int",j,'e5cmaplit',"a string constant key on keyType int: refuse or late by type")
j=load(P); u=unseq_of(j,'commaOkMapVsWriter'); occ(u,'lookup2')['wide']['index']=SC; run("mW11b-lookup-index-string-on-int",j,'commaOkMapVsWriter',"a string key atom on an int-keyed lookup: refuse or late by type")
j=load('Tests/unseq-wire/e5minmax.json'); u=unseq_of(j,'e5minmax'); occ(u,'min0')['head']['args'][1]=SC; run("mM4b-min-mixed-int-string-args",j,'e5minmax',"mixed int/string min operands: refuse or late by type")
j=load('Tests/unseq-wire/native-e5append.json'); u=unseq_of(j,'e5append'); occ(u,'append2')['wide']['slice']['type']={"kind":"slice","elem":BOOL}; run("mW16-append-slice-annotation-vs-cell",j,'e5append',"the slice atom's wire annotation []bool disagrees with its cell []int: is an operand annotation checked at decode?")
j=load(P); u=unseq_of(j,'commaOkMapVsWriter'); o=occ(u,'lookup2'); o['wide']['base']['type']={"kind":"map","key":STR,"value":INT}; o['wide']['keyType']=STR; run("mW17-lookup-base-annotation-and-keyType-string",j,'commaOkMapVsWriter',"annotation and keyType consistent with each other but not with the base cell map[int]int")
j=load('Tests/unseq-wire/e5cmaplit.json'); u=unseq_of(j,'e5cmaplit'); occ(u,'mapread3')['head']['keyType']=STR; run("mE2-mapget-head-keyType-string",j,'e5cmaplit',"PRE-EXISTING E2 map-get head: keyType string on an int-keyed base — same class as mW12?")
j=load(P); u=unseq_of(j,'commaOkMapVsWriter'); occ(u,'lookup2')['wide']['valueType']=BOOL; run("mW19-lookup-valueType-bool-cell-int",j,'commaOkMapVsWriter',"valueType bool vs value cell int: refuse (twoBinds)")
j=load(P); u=unseq_of(j,'commaOkMapVsWriter'); o=occ(u,'lookup2'); o['wide']['valueType']=BOOL; [c for c in u['cells'] if c['id']=='$u66'][0]['type']=BOOL; run("mW20-lookup-valueType-bool-cell-bool-base-int",j,'commaOkMapVsWriter',"valueType and cell both bool, base map[int]int: refuse or late by type — the store into xs[] (int) would get a bool")
