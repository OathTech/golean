# outside-family byte-identity check: baseline-PASS rows outside DIFFER ∪ born, ≤ 2 per package, both frontends
# (main dc5de785 / tip 403cde75) × both binaries (main 73734062… / tip 2159163d…), default tape; observations compared.
import subprocess, random, os, collections, glob
random.seed(20260922)
ROOT='/home/dev/projects/golean/.claude/worktrees/audit-unseq-stage-e5'; os.chdir(ROOT)
differ=set(l.split('\t')[1].strip() for l in open('docs/evidence/2026-09-22_unseq-stage-e5/choice-trace-main-vs-e5d.txt') if l.startswith(('DIFFER','ONLY_B')))
base={}
for l in open('baselines/native-full.tsv'):
    if l.startswith('#') or l.startswith('result\t') or not l.strip(): continue
    r,i,s=l.rstrip('\n').split('\t')[:3]; base[i]=(r,s)
man={}
for cf in glob.glob('Corpus/coverage/exec/**/cases.tsv', recursive=True):
    d=os.path.dirname(cf); rel=d[len('Corpus/coverage/exec/'):]
    for l in open(cf):
        if l.startswith('#') or not l.strip(): continue
        c=l.rstrip('\n').split('\t')
        if len(c)<2: continue
        cid = rel if c[0]=='-' else rel+'/'+c[0]
        man[cid]=(d,c[1])
cands=[i for i in man if i in base and i not in differ and base[i][0]=='PASS' and base[i][1]=='-']
bypkg=collections.defaultdict(list)
for i in cands: bypkg[man[i][0]].append(i)
pkgs=sorted(bypkg); random.shuffle(pkgs)
ids=[]
for p in pkgs:
    ids+=random.sample(bypkg[p],min(2,len(bypkg[p])))
    if len(ids)>=260: break
os.makedirs('.tmp/outside',exist_ok=True)
GT='.lake/build/bin/golean'; GM='/home/dev/projects/golean/.lake/build/bin/golean'
same=diff=feerr=0; rows=[]; wires={}
for i in ids:
    d,fn=man[i]
    if d not in wires:
        k=d.replace('/','__'); wt=f'.tmp/outside/{k}.tip.json'; wm=f'.tmp/outside/{k}.main.json'
        rt=subprocess.run(['.tmp/nativefrontend-tip','--dir',d,'--out',wt],capture_output=True,text=True)
        rm=subprocess.run(['.tmp/nativefrontend-main','--dir',d,'--out',wm],capture_output=True,text=True)
        wires[d]=(wt if rt.returncode==0 else None, wm if rm.returncode==0 else None, rt.returncode, rm.returncode)
    wt,wm,rt,rm=wires[d]
    if wt is None or wm is None:
        feerr+=1; rows.append((i,'FE',rt,rm)); continue
    ot=subprocess.run([GT,'native-json-run','--input',wt,'--function',fn],capture_output=True,text=True)
    om=subprocess.run([GM,'native-json-run','--input',wm,'--function',fn],capture_output=True,text=True)
    a=(ot.returncode,ot.stdout.strip()); b=(om.returncode,om.stdout.strip())
    if a==b: same+=1; rows.append((i,'SAME',a[0]))
    else: diff+=1; rows.append((i,'DIFF',a,b))
print("ids",len(ids),"same",same,"diff",diff,"fe-err",feerr,"packages",len(set(man[i][0] for i in ids)))
for r in rows:
    if r[1]!='SAME': print(r)
with open('.tmp/outside/rows.tsv','w') as f:
    for r in rows: f.write('\t'.join(str(x) for x in r)+'\n')
