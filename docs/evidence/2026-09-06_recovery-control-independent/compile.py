from pathlib import Path
import os,subprocess,json
root=Path(__file__).resolve().parent
env=os.environ.copy();env['LEAN_PATH']=str(root)+os.pathsep+env.get('LEAN_PATH','')
for rel in json.loads((root/'modules.json').read_text()):
 print('Fresh independent source: '+rel,flush=True)
 p=subprocess.run(['lean','-o',str((root/rel).with_suffix('.olean')),str(root/rel)],cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
 (root/(Path(rel).stem+'.log')).write_text(p.stdout)
 print(p.stdout,end='',flush=True)
 if p.returncode:raise SystemExit(p.returncode)
print('All 17 exact frozen control/test modules freshly elaborated',flush=True)
