from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import tarfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PARENT=ROOT.parent/'typed-consumer-sprint'
paths=['GoLean/Interface.lean','Tests/InterfaceAudit.lean','scripts/check-interface',
       'scripts/check-interface.py','tools/recovery-setup-audit.py',
       'docs/2026-09-06_recovery-entry-contract.md']
records=[]
for line in (HERE.parent/'2026-09-06_recovery-entry-review/frozen-source.sha256').read_text().splitlines():
    digest,name=line.split(maxsplit=1)
    name=name.lstrip('*')
    current=(PARENT/name).read_bytes()
    if name=='tools/recovery-setup-audit.py':
        before=subprocess.check_output(['git','show','63769964:'+name],cwd=PARENT)
        assert before==current+b'\n'
        assert ast.dump(ast.parse(before))==ast.dump(ast.parse(current))
        records.append(dict(path=name, comparison='only one trailing LF removed; AST identical'))
    else:
        assert hashlib.sha256(current).hexdigest()==digest,name
        records.append(dict(path=name, comparison='exact reviewed frozen bytes'))
    if name not in paths: paths.append(name)
audit=(PARENT/'Tests/InterfaceAudit.lean').read_text()
lean_modules=set(re.findall(r'`([\w.]+)',audit.split('let modules : List Name := [',1)[1].split(']',1)[0]))
tree=ast.parse((PARENT/'scripts/check-interface.py').read_text())
modules=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='MODULES' for t in n.targets))
python_modules={m.replace('/','.') for m in modules}
bash=(PARENT/'scripts/check-interface').read_text()
bash_modules={m.replace('/','.') for m in re.findall(r'(?:GoLean|Tests)/[\w/]+',bash.split('for module in ',1)[1].split('; do',1)[0])}
# These prerequisites are already built through lake, whereas the shell's
# fresh elaboration list begins with Trace; Python/Lean audits include all.
assert lean_modules==python_modules
assert bash_modules==lean_modules-{'GoLean.GoCore.Machine', 'GoLean.GoCore.Admission',
                                 'GoLean.GoCore.AdmissionIndices', 'GoLean.GoCore.AdmissionPolicy'}
exports=re.findall(r'``([\w.]+)',audit.split('let exports : List Name := [',1)[1].split(']\n',1)[0])
assert len(exports)==len(set(exports))==84
poisons=[]
for n in ast.walk(tree):
    if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and [t.id for t in n.target.elts]==['label','target','declaration','marker']:
        poisons=ast.literal_eval(n.iter)
assert len(poisons)==19
old=subprocess.check_output(['git','show','4158368f:scripts/check-interface.py'],cwd=PARENT).decode()
oldtree=ast.parse(old)
oldpoisons=next(ast.literal_eval(n.iter) for n in ast.walk(oldtree) if isinstance(n,ast.For) and isinstance(n.target,ast.Tuple) and [t.id for t in n.target.elts]==['label','target','declaration','marker'])
assert all(p in poisons for p in oldpoisons)
assert len(poisons)-len(oldpoisons)==4
manifest={p:hashlib.sha256((PARENT/p).read_bytes()).hexdigest() for p in paths}
with tarfile.open(HERE/'source.tar.gz','w:gz') as a:
    for p in paths: a.add(PARENT/p,arcname=p)
(HERE/'source-hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
(HERE/'comparison.json').write_text(json.dumps(dict(files=records,modules=sorted(lean_modules),exports=exports,poisons=poisons),indent=2)+'\n')
print('PASS: 13 reviewed input comparisons; module inventories agree; 84 exports; 19 poisons preserving all 15 prior controls')
