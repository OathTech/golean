import pathlib, subprocess, sys
# three-way row merge preserving ours' body interleaving (reason blocks stay above their rows):
# ours' body + theirs' row DELTAS relative to its base (changed rows replaced in place, removed rows dropped, added rows appended) + theirs' header blocks ours lacks
path = sys.argv[1]
def stage(n): return subprocess.run(['git', 'show', f':{n}:{path}'], capture_output=True, text=True, check=True).stdout
def parse(txt):
    L = txt.split('\n')
    if L and L[-1] == '': L = L[:-1]
    ch = next(k for k, l in enumerate(L) if l.startswith('result\tid'))
    rows = [l for l in L[ch+1:] if l and not l.startswith('#')]
    return L, ch, rows
bL, bCH, bR = parse(stage(1)); oL, oCH, oR = parse(stage(2)); tL, tCH, tR = parse(stage(3))
rid = lambda r: r.split('\t')[1]
b_map = {rid(r): r for r in bR}; t_map = {rid(r): r for r in tR}; o_ids = {rid(r) for r in oR}
changed = {i: t_map[i] for i in t_map if i in b_map and b_map[i] != t_map[i]}
added = [t_map[i] for i in t_map if i not in b_map and i not in o_ids]
removed = {i for i in b_map if i not in t_map}
body = []
for l in oL[oCH:]:
    if l.startswith('#') or l.startswith('result\tid') or not l: body.append(l); continue
    i = rid(l)
    if i in removed: continue
    body.append(changed.get(i, l))
body += added
rows = [l for l in body if l and not l.startswith('#') and not l.startswith('result\tid')]
pass_n = sum(1 for r in rows if r.split('\t')[0] == 'PASS'); fail_n = sum(1 for r in rows if r.split('\t')[0] == 'FAIL'); assert pass_n + fail_n == len(rows)
def blocks(H):
    idx = [k for k, l in enumerate(H) if l.startswith('# re-pinned') or (l.startswith('# 2026-') and 'lane' in l)]
    return [H[idx[i]:(idx[i+1] if i+1 < len(idx) else len(H))] for i in range(len(idx))], (idx[0] if idx else len(H))
oH, tH = oL[:oCH], tL[:tCH]; ob, o_first = blocks(oH); tb, _ = blocks(tH)
o_heads = {b[0] for b in ob}; extra = [b for b in tb if b[0] not in o_heads]
newH = list(oH)
for k, l in enumerate(newH):
    if l.startswith('# cases:'): newH[k] = f'# cases: {len(rows)} ({pass_n} PASS / {fail_n} FAIL)'; break
    if l.startswith('# manifest_cases:'): newH[k] = f'# manifest_cases: {len(rows)}  pass: {pass_n}  fail: {fail_n}'; break
ins = o_first + (len(ob[0]) if ob else 0)
newH = newH[:ins] + [l for b in extra for l in b] + newH[ins:]
pathlib.Path(path).write_text('\n'.join(newH + body) + '\n')
print(f'union3 {path}: ours {len(oR)}, theirs changed {len(changed)} removed {len(removed)} added {len(added)} → {len(rows)} ({pass_n} PASS / {fail_n} FAIL); {len(extra)} block(s) added')
