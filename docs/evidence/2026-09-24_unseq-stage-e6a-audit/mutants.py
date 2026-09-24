#!/usr/bin/env python3
"""Audit mutants for the E6a decoder follow-ups (R1 / F8) over the p4 probe wire (the candidate's frontend) and two
tracked Tests/unseq-wire fixtures. Each mutant is one edit; the real CLI must REFUSE naming its cause (or, for the
controls, run). Writes .tmp/audit/mutants/<name>.json and prints one line per mutant."""
import json, copy, subprocess, sys, os, re
ROOT=os.getcwd()
GL=ROOT+'/.lake/build/bin/golean'
P4=ROOT+'/.tmp/audit/probes/p4/wire-e6a.json'
OUT=ROOT+'/.tmp/audit/mutants'; os.makedirs(OUT, exist_ok=True)
def load(p): return json.load(open(p))
def func(w,name):
    for f in (w.get('funcs') or []):
        if f.get('id')==name or f.get('name')==name: return f
    raise KeyError(name)
def graphs(node,acc):
    if isinstance(node,dict):
        if node.get('stmt')=='unseq': acc.append(node)
        for v in node.values(): graphs(v,acc)
    elif isinstance(node,list):
        for v in node: graphs(v,acc)
def idents(node,acc,name):
    if isinstance(node,dict):
        if node.get('expr')=='ident' and node.get('name')==name: acc.append(node)
        for v in node.values(): idents(v,acc,name)
    elif isinstance(node,list):
        for v in node: idents(v,acc,name)
def refs(node,acc,name):
    if isinstance(node,dict):
        if node.get('expr')=='ref' and node.get('id')==name: acc.append(node)
        for v in node.values(): refs(v,acc,name)
    elif isinstance(node,list):
        for v in node: refs(v,acc,name)
INT={'kind':'int','int':'int'}; STR={'kind':'string'}; BOOL={'kind':'bool'}; INT32={'kind':'int','int':'int32'}
results=[]
def run(name, wire, fn, edit, expect, args=()):
    w=copy.deepcopy(wire)
    try:
        edit(w)
    except Exception as e:
        results.append((name,'EDIT-FAILED',str(e))); return
    p=f'{OUT}/{name}.json'; json.dump(w,open(p,'w'),indent=1)
    cmd=[GL,'native-json-run','--input',p,'--function',fn,'--fuel','2000000']+[x for a in args for x in ('--arg-int',str(a))]
    r=subprocess.run(cmd,capture_output=True,text=True)
    out=(r.stdout+r.stderr).strip().replace('\n',' ')
    if expect=='RUN':
        ok = r.returncode==0
        results.append((name,'RUN-OK' if ok else 'RUN-FAILED', out[:220]))
    else:
        refused = r.returncode!=0
        named = expect in out
        results.append((name, ('REFUSED-NAMED' if named else 'REFUSED-OTHER') if refused else 'DECODED-AND-RAN', out[:260]))
p4=load(P4)
def g(fn, i=0):
    acc=[]; graphs(func(p4,fn)['body'],acc); return acc[i]
# --- R1: annotation forgeries per declaration form ---
def forge(fn, name, ty, i=0):
    def e(w):
        acc=[]; graphs(func(w,fn)['body'],acc); ids=[]; idents(acc[i],ids,name)
        if not ids: raise Exception(f'no ident {name} in graph of {fn}')
        for x in ids: x['type']=ty
    return e
run('mR1-range-slice-valvar', p4,'pRangeSlice', forge('pRangeSlice','v',STR), 'disagrees with its declaration')
run('mR1-range-slice-keyvar', p4,'pRangeSlice', forge('pRangeSlice','i',BOOL), 'disagrees with its declaration')
run('mR1-range-map-valvar',   p4,'pRangeMap',   forge('pRangeMap','v',STR), 'disagrees with its declaration')
run('mR1-range-chan-var',     p4,'pRangeChan',  forge('pRangeChan','v',STR), 'disagrees with its declaration')
run('mR1-range-int-var',      p4,'pRangeInt',   forge('pRangeInt','i',STR), 'disagrees with its declaration')
run('mR1-range-string-rune',  p4,'pRangeString',forge('pRangeString','c',INT), 'disagrees with its declaration')
run('mR1-param',              p4,'pNamedResult',forge('pNamedResult','s',{'kind':'slice','elem':STR}), 'disagrees with its declaration', args=(0,0))
run('mR1-named-result',       p4,'pNamedResult',forge('pNamedResult','r',BOOL), 'disagrees with its declaration', args=(0,0))
run('mR1-select-binder',      p4,'pSelect',     forge('pSelect','v',STR), 'disagrees with its declaration')
run('mR1-typeswitch-binder',  p4,'pTypeSwitch', forge('pTypeSwitch','v',STR), 'disagrees with its declaration')
run('mR1-if-init-var',        p4,'pIfInit',     forge('pIfInit','v',STR), 'disagrees with its declaration')
run('mR1-comma-ok-var',       p4,'pCommaOk',    forge('pCommaOk','v',STR), 'disagrees with its declaration')
run('mR1-var-decl',           p4,'pVarDecl',    forge('pVarDecl','v',STR), 'disagrees with its declaration')
run('mR1-for-init-var',       p4,'pForInit',    forge('pForInit','i',STR), 'disagrees with its declaration')
run('mR1-captured-addr-taken',p4,'pClosureCapture', forge('pClosureCapture','x',STR), 'disagrees with its declaration')
# the shadow residual: the inner graph's string x annotated with the OTHER declaration's type (int) — the lane says this PASSES the flat check
run('mR1-shadow-other-decl-type', p4,'pShadow', forge('pShadow','x',INT,1), 'disagrees with its declaration')
# an ident renamed to a local declared in ANOTHER function (xs lives in pRangeSlice)
def rename(fn, old, new, i=0):
    def e(w):
        acc=[]; graphs(func(w,fn)['body'],acc); ids=[]; idents(acc[i],ids,old)
        if not ids: raise Exception(f'no ident {old}')
        ids[0]['name']=new
    return e
run('mR1-other-functions-local', p4,'pNew', rename('pNew','s','xs'), 'has no declaration in the enclosing function')
run('mR1-undeclared-in-select',  p4,'pSelect', rename('pSelect','s','zz'), 'has no declaration in the enclosing function')
# mS4: the map TARGET plan on a private map — the target's base annotation + the plan's keyType forged self-consistently
def ms4(w):
    acc=[]; graphs(func(w,'pMapTargetMulti')['body'],acc); gph=acc[0]
    MSI={'kind':'map','key':STR,'value':INT}
    hit=0
    for o in gph['occs']:
        if o['kind']=='target':
            lhs=o['lhs']
            if lhs.get('target')=='map':
                lhs['keyType']=STR; hit+=1
                ids=[]; idents(lhs,ids,'m')
                for x in ids: x['type']=MSI; hit+=1
    ids=[]; idents(gph,ids,'m')
    for x in ids: x['type']=MSI
    if not hit: raise Exception('no map target plan found: '+json.dumps(gph['occs'])[:300])
run('mS4-map-target-plan-forged', p4,'pMapTargetMulti', ms4, 'disagrees with its declaration')
# --- F8: an `after` edge on a literal allocation ---
def after_on(fn, tag):
    def e(w):
        acc=[]; graphs(func(w,fn)['body'],acc); gph=acc[0]
        anchor=[o['name'] for o in gph['occs'] if o['kind']=='invoke']
        hit=False
        for o in gph['occs']:
            if o['kind']=='allocate' and o['allocation'].get('stmt')==tag:
                o['after']=[anchor[0]]; hit=True
        if not hit: raise Exception('no allocate '+tag+': '+str([(o['kind'],o.get('allocation',{}).get('stmt')) for o in gph['occs']]))
    return e
run('mF8-after-on-new-struct-lit', p4,'pAddrLit', after_on('pAddrLit','new'), 'an `after` edge on a literal allocation')
run('mF8-after-on-map-lit',        p4,'pMapLit',  after_on('pMapLit','map-lit'), 'an `after` edge on a literal allocation')
# --- controls: legal wires must still run ---
run('ctl-p4-shadow-legal', p4,'pShadow', lambda w: None, 'RUN')
run('ctl-p4-typeswitch-legal', p4,'pTypeSwitch', lambda w: None, 'RUN')
e4=load(ROOT+'/Tests/unseq-wire/e4new.json')
run('ctl-e4new-new-with-after-legal', e4,'e4new', lambda w: None, 'RUN')
e5d=load(ROOT+'/Tests/unseq-wire/e5daddr.json')
def refundecl(w):
    acc=[]; graphs(func(w,'e5daddr')['body'],acc); rs=[]
    for gph in acc: refs(gph,rs,'x')
    if not rs: raise Exception('no ref x')
    rs[0]['id']='nosuch'
run('mR1-ref-undeclared', e5d,'e5daddr', refundecl, 'names no local the enclosing function declares')
for r in results: print('\t'.join(r))
