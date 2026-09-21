import subprocess, json, random, os, collections, sys
random.seed(20260921)
differ=set(l.strip() for l in open('.tmp/differ-ids.txt'))
base={}
for l in open('baselines/native-full.tsv'):
    if l.startswith('#') or l.startswith('result\t') or not l.strip(): continue
    r,i,s=l.rstrip('\n').split('\t')[:3]; base[i]=(r,s)
main_base={}
for l in open('.tmp/baseline-main.tsv'):
    if l.startswith('#') or l.startswith('result\t') or not l.strip(): continue
    r,i,s=l.rstrip('\n').split('\t')[:3]; main_base[i]=(r,s)
man={}
for l in open('.tmp/manifest-all.tsv'):
    c=l.rstrip('\n').split('\t'); man[c[0]]=(c[3],c[4])
cands=[i for i in man if i in main_base and i not in differ and base[i][0]=='PASS']
# stratify: at most 2 per package
bypkg=collections.defaultdict(list)
for i in cands: bypkg[man[i][0]].append(i)
pkgs=sorted(bypkg); random.shuffle(pkgs)
ids=[]
for p in pkgs:
    ids+=random.sample(bypkg[p],min(2,len(bypkg[p])))
    if len(ids)>=240: break
os.makedirs('.tmp/outside',exist_ok=True)
same=diff=feerr=0; rows=[]
wires={}
for i in ids:
    d,fn=man[i]
    if d not in wires:
        wc='.tmp/outside/%s.cand.json'%d.replace('/','__'); wm='.tmp/outside/%s.main.json'%d.replace('/','__')
        rc=subprocess.run(['.tmp/nativefrontend','--dir',d,'--out',wc],capture_output=True,text=True)
        rm=subprocess.run(['.tmp/nativefrontend-main','--dir',d,'--out',wm],capture_output=True,text=True)
        wires[d]=(wc if rc.returncode==0 else None, wm if rm.returncode==0 else None, rc.returncode, rm.returncode)
    wc,wm,rc,rm=wires[d]
    if wc is None or wm is None:
        feerr+=1; rows.append((i,'FE',rc,rm)); continue
    oc=subprocess.run(['.lake/build/bin/golean','native-json-run','--input',wc,'--function',fn],capture_output=True,text=True)
    om=subprocess.run(['/home/dev/projects/golean/.lake/build/bin/golean','native-json-run','--input',wm,'--function',fn],capture_output=True,text=True)
    a=(oc.returncode,oc.stdout.strip()); b=(om.returncode,om.stdout.strip())
    if a==b: same+=1; rows.append((i,'SAME',a[0]))
    else: diff+=1; rows.append((i,'DIFF',a,b))
print("ids",len(ids),"same",same,"diff",diff,"fe-err",feerr)
for r in rows:
    if r[1]!='SAME': print(r)
with open('.tmp/outside/rows.tsv','w') as f:
    for r in rows: f.write('\t'.join(str(x) for x in r)+'\n')
