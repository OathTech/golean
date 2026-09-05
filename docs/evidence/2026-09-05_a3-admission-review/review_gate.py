"""Reproduce admission gate with unchanged checks and review-owned scratch.
Run inside capped lake env. Source .olean files are read only; all mutation
copies, native output and logs live in this review directory.
"""
from pathlib import Path
import hashlib, importlib.util, os, subprocess, tempfile
root=Path.cwd()
scratch_root=Path('/home/dev/projects/golean/.tmp/a3-adversarial.04A3m2')
spec=importlib.util.spec_from_file_location('admission_check', root/'tools/admission-check.py')
gate=importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
def review_scratch(label):
    p=Path(tempfile.mkdtemp(prefix=f'admission-{label}-',dir=scratch_root))
    print('Review-owned gate scratch:',p,flush=True)
    return p
gate.scratch=review_scratch
gate.preflight()
gate.elaborate()
gate.audit()
gate.artifact()
env=os.environ.copy()
env['GOLEAN_COVERAGE_ARTIFACTS']=str(scratch_root/'differential')
env['GOLEAN_COVERAGE_JOBS']='2'
result=subprocess.run(['scripts/diff-coverage','Tests/admission-fixture/manifest.tsv'],env=env,text=True)
if result.returncode: raise SystemExit(result.returncode)
print('Independent A3 review gate PASS',flush=True)
