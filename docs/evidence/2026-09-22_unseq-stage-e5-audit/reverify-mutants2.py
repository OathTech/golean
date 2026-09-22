import json, subprocess, os
FIX='/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5-fix'; AUD='/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5'
os.chdir(FIX); GNEW=FIX+'/.lake/build/bin/golean'; GOLD=AUD+'/.lake/build/bin/golean'
INT={"int":"int","kind":"int"}; STR={"kind":"string"}
def run1(G,path,fn):
    r=subprocess.run([G,"native-json-run","--input",path,"--function",fn],capture_output=True,text=True)
    msg=(r.stdout+r.stderr).strip().replace("\n"," | ").replace(FIX+'/','').replace(AUD+'/','')
    v="REFUSED-DECODE" if r.returncode==1 and "unseq:" in msg else ("REFUSED-LATE" if r.returncode!=0 else "RAN")
    return v,r.returncode,msg
def both(tag,path,fn):
    for lab,G in (("OLD",GOLD),("NEW",GNEW)):
        v,rc,msg=run1(G,path,fn); print(f"{tag:46} {lab} {v:14} exit={rc}  {msg[:230]}")
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
P3='.tmp/wires/p_f3.fix.json'
print("== SOURCE-LOCAL base (a private empty map `m`), wide map-lookup")
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateMapKeyRead'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; print("   base atom:",json.dumps(w['wide']['base'])[:200])
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateMapKeyRead'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; w['wide']['base']['type']={"kind":"map","key":STR,"value":INT}; w['wide']['keyType']=STR; json.dump(j,open('.tmp/mut/mS1.json','w')); both("mS1-private-map: annotation+keyType both string",'.tmp/mut/mS1.json','commaOkPrivateMapKeyRead')
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateMapKeyRead'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; w['wide']['keyType']=STR; json.dump(j,open('.tmp/mut/mS2.json','w')); both("mS2-private-map: keyType string only",'.tmp/mut/mS2.json','commaOkPrivateMapKeyRead')
j=json.load(open(P3)); u=unseq_of(j,'commaOkPrivateMapKeyRead'); w=[o for o in u['occs'] if o['kind']=='wide'][0]; del w['wide']['base']['type']; json.dump(j,open('.tmp/mut/mS3.json','w')); both("mS3-private-map: base annotation removed",'.tmp/mut/mS3.json','commaOkPrivateMapKeyRead')
print("== SOURCE-LOCAL base, map TARGET plan (mapTargetPrivateVsCall: private empty map m, captured key k)")
j=json.load(open(P3)); u=unseq_of(j,'mapTargetPrivateVsCall'); t=[o for o in u['occs'] if o['kind']=='target' and o['lhs'].get('target')=='map'][0]; print("   plan base:",json.dumps(t['lhs']['base'])[:200])
j=json.load(open(P3)); u=unseq_of(j,'mapTargetPrivateVsCall'); t=[o for o in u['occs'] if o['kind']=='target' and o['lhs'].get('target')=='map'][0]; t['lhs']['base']['type']={"kind":"map","key":STR,"value":INT}; t['lhs']['keyType']=STR; json.dump(j,open('.tmp/mut/mS4.json','w')); both("mS4-private-map target plan: annotation+keyType string",'.tmp/mut/mS4.json','mapTargetPrivateVsCall')
j=json.load(open(P3)); u=unseq_of(j,'mapTargetPrivateVsCall'); t=[o for o in u['occs'] if o['kind']=='target' and o['lhs'].get('target')=='map'][0]; t['lhs']['keyType']=STR; json.dump(j,open('.tmp/mut/mS5.json','w')); both("mS5-private-map target plan: keyType string only",'.tmp/mut/mS5.json','mapTargetPrivateVsCall')
