#!/usr/bin/env python3
"""Independent read-only validation of the fixed raw-JSON integration union."""
import copy, hashlib, json, pathlib, subprocess, sys, tomllib, ast
ROOT = pathlib.Path(sys.argv[1]).resolve()
OUT = pathlib.Path(__file__).resolve().parent
PARENT='c969079a13bcdbbb39c06b85824249340b348e43'
FEATURE='7ac3eb46bb3e2fe9c15b86b509569ef086327453'
def sha(x): return hashlib.sha256(x).hexdigest()
def blob(commit,path): return subprocess.check_output(['git','show',f'{commit}:{path}'],cwd=ROOT)
def read(path): return (ROOT/path).read_bytes()
def save(name,obj): (OUT/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
source_path='docs/evidence/2026-09-06_i1-json-integration/source.json'
src=json.loads(read(source_path));assert len(src)==3926
mismatch={p:{'expected':h,'actual':sha(read(p))} for p,h in src.items() if h!=sha(read(p))}
assert not mismatch,mismatch
(OUT/'source.json').write_bytes(read(source_path))
candidate_path='docs/evidence/2026-09-06_i1-json-boundary/candidate-source.json'
candidate=json.loads(read(candidate_path));assert len(candidate)==14
(OUT/'reviewed-candidate-source.json').write_bytes(read(candidate_path))
delta={p:{'feature':sha(blob(FEATURE,p)),'integration':sha(read(p))} for p in candidate if blob(FEATURE,p)!=read(p)}
assert set(delta)=={'lakefile.toml'},delta
parent_lake=blob(PARENT,'lakefile.toml')
feature_lake=blob(FEATURE,'lakefile.toml')
lake=read('lakefile.toml')
assert lake==parent_lake.replace(b'globs = ["Tests.DeclarationWire", "Tests.DeclarationAudit"]',b'globs = ["Tests.DeclarationWire", "Tests.StrictJsonParse", "Tests.DeclarationAudit"]')
assert lake==feature_lake.replace(b'"Tests.InterfaceAudit", "Tests.PanicRendering"]',b'"Tests.InterfaceAudit", "Tests.PanicRendering", "Tests.StringPanicMembers"]')
assert read('scripts/ci')==blob(PARENT,'scripts/ci')
assert read('tools/string_member.py')==blob(PARENT,'tools/string_member.py')
# Extract literal inventory constants without importing or executing the author's checker.
nodes=ast.parse(read('tools/string_member.py')); constants={}
for node in nodes.body:
 if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in ['APPARATUS_FILES','APPARATUS_ROOTS']:
  constants[node.targets[0].id]=ast.literal_eval(node.value)
assert set(constants)=={'APPARATUS_FILES','APPARATUS_ROOTS'}
assert constants['APPARATUS_ROOTS']=={'GoLean':'.lean','tools/nativefrontend':'.go','tools/coverageharness':'.go'}
actual={}
for d,suffix in constants['APPARATUS_ROOTS'].items():
 base=ROOT/d;assert base.is_dir() and not base.is_symlink()
 for p in sorted(base.rglob('*')):
  assert not p.is_symlink(),p
  if p.is_file() and p.suffix==suffix:actual[p.relative_to(ROOT).as_posix()]=sha(p.read_bytes())
for p in constants['APPARATUS_FILES']:
 assert (ROOT/p).is_file() and not (ROOT/p).is_symlink(),p
 actual[p]=sha(read(p))
assert len(actual)==170,len(actual)
root_inventory=json.loads(read('docs/evidence/2026-09-06_i1-json-integration/apparatus-inventory.json'))
assert actual==root_inventory
pins=sorted((ROOT/'baselines/string-members').rglob('*.json'));assert len(pins)==9
checks=[]
for p in pins:
 path=p.relative_to(ROOT).as_posix();current=json.loads(p.read_bytes());before=json.loads(blob(PARENT,path))
 before_inventory=before['binding'].pop('apparatus_sources');current_inventory=current['binding'].pop('apparatus_sources')
 assert current==before,path
 assert current_inventory==actual,path
 added=sorted(set(current_inventory)-set(before_inventory));removed=sorted(set(before_inventory)-set(current_inventory))
 changed=sorted(k for k in before_inventory if current_inventory.get(k)!=before_inventory[k])
 assert len(before_inventory)==169 and added==['GoLean/StrictJsonParse.lean'] and not removed
 assert changed==['GoLean/NativeDeclaration.lean','lakefile.toml']
 checks.append({'path':path,'parent_sha256':sha(blob(PARENT,path)),'integration_sha256':sha(p.read_bytes()),'added':added,'removed':removed,'changed':changed,'other_fields_identical':True})
# Verify every changed selected product file is the accepted feature or the stated nine pins / lake union.
selected_delta={}
for p,h in src.items():
 if p.startswith('docs/'):continue
 try: old=blob(PARENT,p)
 except subprocess.CalledProcessError: old=None
 if old is not None and sha(old)==h:continue
 selected_delta[p]={'parent':sha(old) if old is not None else None,'integration':h}
 if p.startswith('baselines/string-members/') or p=='lakefile.toml':continue
 assert read(p)==blob(FEATURE,p),p
save('apparatus-inventory.json',actual)
save('pin-checks.json',checks)
save('results.json',{'verdict':'PASS for the bounded additive source union','integration_parent':PARENT,'feature_tip':FEATURE,'selected_inputs':len(src),'source_sha256':sha(read(source_path)),'selected_hash_mismatches':mismatch,'candidate_inputs':len(candidate),'candidate_delta':delta,'selected_product_delta':selected_delta,'ci_identical_to_parent':True,'lake_union_exact_from_both_parents':True,'member_checker_unchanged':True,'apparatus_entries':len(actual),'pins':len(pins),'execution_validation':'Owned by root; pending separately, no new conformance claimed by this review.'})
print('PASS: 3926 exact inputs, 14 reviewed candidate inputs, exact additive Lake union, unchanged CI, 9 complete 170-source pins with no policy changes')
