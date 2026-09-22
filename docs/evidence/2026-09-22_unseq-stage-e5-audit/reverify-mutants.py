import json, copy, subprocess, os, glob
FIX='/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5-fix'; AUD='/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5'
os.chdir(FIX)
GNEW=FIX+'/.lake/build/bin/golean'; GOLD=AUD+'/.lake/build/bin/golean'
INT={"int":"int","kind":"int"}; STR={"kind":"string"}
def run1(G,path,fn):
    r=subprocess.run([G,"native-json-run","--input",path,"--function",fn],capture_output=True,text=True)
    msg=(r.stdout+r.stderr).strip().replace("\n"," | ").replace(FIX+'/','').replace(AUD+'/','')
    v="REFUSED-DECODE" if r.returncode==1 and "unseq:" in msg else ("REFUSED-LATE" if r.returncode!=0 else "RAN")
    return v,r.returncode,msg
def both(tag,path,fn):
    for lab,G in (("OLD",GOLD),("NEW",GNEW)):
        v,rc,msg=run1(G,path,fn); print(f"{tag:44} {lab} {v:14} exit={rc}  {msg[:230]}")
def unseq_of(j,fname):
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
def occ(u,n): return [o for o in u["occs"] if o["name"]==n][0]
print("== the audit's RAN / late mutants, old vs new binary")
for tag,fn in [("mW12-lookup-keyType-vs-base","commaOkMapVsWriter"),("mW17-lookup-base-annotation-and-keyType-string","commaOkMapVsWriter"),("mE2-mapget-head-keyType-string","e5cmaplit"),("mW20-lookup-valueType-bool-cell-bool-base-int","commaOkMapVsWriter"),("mW16-append-slice-annotation-vs-cell","e5append"),("mA5-maplit-after-edge","e5cmaplit"),("mB4-store-same-target-twice","e5btuple"),("mA1-maplit-key-ref","e5cmaplit"),("mD1-payload-ref-undeclared","e5dlit")]:
    both(tag,f"{AUD}/.tmp/mut/{tag}.json",fn)
print("== the round's four mutants (tracked), old vs new")
for m,fn in [("mut-wide-lookup-keytype-vs-base","e5blookup"),("mut-wide-lookup-valuetype-vs-base","e5blookup"),("mut-mapget-keytype-vs-base","e5cmaplit"),("mut-map-target-keytype-vs-base","e2map")]:
    both(m,f"Tests/unseq-wire/{m}.json",fn)
print("== positive controls, old vs new (canonical tape)")
for w,fn in [("e5blookup","e5blookup"),("native-e5blookup","e5blookup"),("e2map","e2map"),("native-e2map","e2map"),("e5cmaplit","e5cmaplit"),("native-e5cmaplit","e5cmaplit"),("e5btuple","e5btuple"),("w1","w1")]:
    both(w,f"Tests/unseq-wire/{w}.json",fn)
print("== my own: the map TARGET plan's keyType on a `$`-cell base (probe mapCapturedKeyTargetVsWriter, fix-frontend export)")
P='.tmp/wires/p_multi.fix.json'
j=json.load(open(P)); u=unseq_of(j,'mapCapturedKeyTargetVsWriter'); t=[o for o in u['occs'] if o['kind']=='target' and o['lhs'].get('target')=='map'][0]; t['lhs']['keyType']=STR; json.dump(j,open('.tmp/mut/mT1-map-target-plan-keyType.json','w')); both("mT1-map-target-plan-keyType-string",'.tmp/mut/mT1-map-target-plan-keyType.json','mapCapturedKeyTargetVsWriter')
print("== my own: the SOURCE-LOCAL base path — a private EMPTY map, annotation AND keyType forged consistently")
P3='.tmp/wires/p_f3.fix.json'
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateEmptyMap'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; print("   base atom:",json.dumps(w['wide']['base'])[:160])
w['wide']['base']['type']={"kind":"map","key":STR,"value":INT}; w['wide']['keyType']=STR; json.dump(j,open('.tmp/mut/mS1-private-map-annotation-keyType.json','w')); both("mS1-private-empty-map-annot+keyType-string",'.tmp/mut/mS1-private-map-annotation-keyType.json','commaOkPrivateEmptyMap')
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateEmptyMap'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; w['wide']['keyType']=STR; json.dump(j,open('.tmp/mut/mS2-private-map-keyType-only.json','w')); both("mS2-private-empty-map-keyType-only",'.tmp/mut/mS2-private-map-keyType-only.json','commaOkPrivateEmptyMap')
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateEmptyMap'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; del w['wide']['base']['type']; json.dump(j,open('.tmp/mut/mS3-private-map-no-annotation.json','w')); both("mS3-private-map-base-annotation-removed",'.tmp/mut/mS3-private-map-no-annotation.json','commaOkPrivateEmptyMap')
