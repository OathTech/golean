#!/usr/bin/env python3
"""A4-U24: emit RoundMarEq* modules from the auto-discovery manifest.
Reads the MANIFEST section of roundmargen.out; groups segments into
modules of <= MAXW window steps; emits window/crossing theorems and
per-module spans + the equation module skeleton."""
import sys, re

out = open(sys.argv[1]).read()
lines = [l.strip() for l in out.splitlines()]
mstart = lines.index('=== MANIFEST (in order) ===')
items = []  # ('SEG', pre, len, post) | ('CROSS', pre, post, consumed, kind)
for l in lines[mstart+1:]:
    p = l.split('\t')
    if p[0] == 'SEG': items.append(('SEG', p[1], int(p[2]), p[3]))
    elif p[0] == 'CROSS': items.append(('CROSS', p[1], p[2], int(p[3]), p[4]))
    else: break

total = sum(i[2] for i in items if i[0]=='SEG') + sum(1 for i in items if i[0]=='CROSS')
draws = sum(i[3] for i in items if i[0]=='CROSS')
print(f"-- total steps {total}, draws {draws}, segments {sum(1 for i in items if i[0]=='SEG')}, crossings {sum(1 for i in items if i[0]=='CROSS')}")

# group into modules
MAXW = 7500
groups, cur, curw = [], [], 0
for it in items:
    w = it[2] if it[0]=='SEG' else 1
    if it[0]=='SEG' and curw + w > MAXW and cur:
        groups.append(cur); cur, curw = [], 0
    cur.append(it); curw += w
if cur: groups.append(cur)

lit_of = {}   # boundary name -> lit file number (5 names per file, in B-order)
names = ['B0'] + [it[3] if it[0]=='SEG' else it[2] for it in items]
for i, nm in enumerate(names): lit_of[nm] = i // 5 + 1

mods = []
winN = 0; crossN = 0; spillN = 0; mapN = 0; freeN = 0
for gi, g in enumerate(groups):
    L = chr(ord('A') + gi)
    pre = g[0][1]
    post = g[-1][3] if g[-1][0]=='SEG' else g[-1][2]
    gsteps = sum(it[2] if it[0]=='SEG' else 1 for it in g)
    gdraws = sum(it[3] for it in g if it[0]=='CROSS')
    lits = sorted(set(lit_of[pre:=pre] for _ in [0]) | set(lit_of[x] for it in g for x in ([it[1], it[3]] if it[0]=='SEG' else [it[1], it[2]])))
    body = []
    haves = []
    chain = []
    remaining = gdraws
    def stream(n): return ' :: '.join(['0']*n + ['rest']) if n else 'rest'
    for it in g:
        if it[0]=='SEG':
            winN += 1
            nm = f"mrW{L}{winN}_out"
            body.append(f"theorem {nm} : symEvalWindowTB bfTB {it[2]} mrS{it[1]} mrC{it[1]}\n    = ({it[2]}, mrS{it[3]}, mrC{it[3]}) := by\n  kernel_rfl\n")
            haves.append(f"  have h{len(haves)} := symEvalWindowTB_refines {nm} ρ σ ({stream(remaining)}) hag")
            chain.append(f"h{len(haves)-1}")
        else:
            crossN += 1
            _, cpre, cpost, consumed, kind = it
            if consumed == 1:
                thm = f"roundMar_x{crossN}"
                body.append(f"/-- Crossing {crossN} ({kind}; latitude unless noted). -/\ntheorem {thm} (ρ : Valuation) (σ : ExecState) (rest : Choices) :\n    stepFn (γS ρ σ mrS{cpre}) (γC ρ mrC{cpre}) (0 :: rest)\n      = .ok (γC ρ mrC{cpost}, γS ρ σ mrS{cpost}, rest) := by\n  kernel_rfl\n")
                remaining -= 1
                haves.append(f"  have h{len(haves)} := {thm} ρ σ ({stream(remaining)})")
            else:
                thm = f"roundMar_x{crossN}free"
                body.append(f"/-- Crossing {crossN}: CHOICE-FREE mirror quit ({kind}); holds for every stream. -/\ntheorem {thm} (ρ : Valuation) (σ : ExecState) (rest : Choices) :\n    stepFn (γS ρ σ mrS{cpre}) (γC ρ mrC{cpre}) rest\n      = .ok (γC ρ mrC{cpost}, γS ρ σ mrS{cpost}, rest) := by\n  kernel_rfl\n")
                haves.append(f"  have h{len(haves)} := {thm} ρ σ ({stream(remaining)})")
            chain.append(f"(Surface.stepFnIter_one h{len(haves)-1})")
    # span
    expr = chain[0] if chain[0].startswith('h') else chain[0]
    for c in chain[1:]:
        expr = f"(Surface.stepFnIter_chain {expr} {c})"
    expr = expr.strip('()') if len(chain)==1 else expr[1:-1]
    span = f"/-- Segment span {L}: {gsteps} steps, {gdraws} draw(s). -/\ntheorem roundMar_span{L} (ρ : Valuation) (σ : ExecState)\n    (hag : bfTB.Agrees σ) (rest : Choices) :\n    stepFnIter {gsteps} (γS ρ σ mrS{pre}) (γC ρ mrC{pre}) ({stream(gdraws)})\n      = .ok (γC ρ mrC{post}, γS ρ σ mrS{post}, rest) := by\n" + '\n'.join(haves) + f"\n  exact {expr}\n"
    mods.append((L, lits, body, span, gsteps, gdraws, pre, post))

for L, lits, body, span, gsteps, gdraws, pre, post in mods:
    imports = '\n'.join(f"import GoLeanProofs.Specs.Raft.RoundMarLit{n}" for n in lits)
    hdr = f"""{imports}
import GoLeanProofs.Specs.Raft.HandlerEqSym
import GoLeanProofs.Sym.SpillTransport
import GoLeanProofs.Sym.KernelRfl

/-! # RoundMarEq{L} — segment {L} of the MsgAppResp maybeCommit
round's canonical run (A4-U24): {pre} -> {post}, {gsteps} steps,
{gdraws} draw(s). Auto-discovered boundary schedule (the U23
template); see `RoundMarLemma.lean` for the design record. -/

namespace GoLean.RaftSeam.RoundMar

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
open GoLean.RaftSeam

set_option maxRecDepth 8000000
set_option maxHeartbeats 400000000

"""
    with open(f"RoundMarEq{L}.lean", 'w') as f:
        f.write(hdr + '\n'.join(body) + '\n' + span + '\nend GoLean.RaftSeam.RoundMar\n')
    print(f"RoundMarEq{L}.lean: {gsteps} steps {gdraws} draws lits={lits} pre={pre} post={post}")
# equation skeleton info
print("MODS:", ' '.join(f"{m[0]}:{m[4]}/{m[5]}" for m in mods), "total", total, "draws", draws)
