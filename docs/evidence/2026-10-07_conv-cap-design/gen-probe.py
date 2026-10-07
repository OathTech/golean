# [AGENT] b6 design probe generator (2026-10-07): emits probe_bytes.go / probe_runes.go
# covering (operand shape) x (escape/mutation regime) x (length).
import sys
LENS = [0,1,2,3,5,6,7,8,9,15,16,17,24,25,31,32,33,45,47,48,49,63,64,65,100,112,113,
        1016,1017,1024,1025,32760,32761,32768,32769,40000,100000]
LIT_LENS = [n for n in LENS if n <= 1025] + [65536, 65537]
def lit(n, ch='a'): return '"' + ch*n + '"'
out = []
w = out.append
w('package main\n\nimport "strings"\n\nvar sinkB []byte\nvar sinkR []rune\n')
w('//go:noinline\nfunc mkA(n int) string { return strings.Repeat("a", n) }')
w('//go:noinline\nfunc mkE(n int) string { return strings.Repeat("\\u00e9", n) }   // n runes, 2n bytes')
w('func rep(k, shape string, n, c int) { println(k, shape, n, c) }\n')
# ---- bytes, variable source
for n in LENS:
    w(f'func bV_nomut_{n}() {{ s := mkA({n}); b := []byte(s); rep("bytes", "var/nomut", {n}, cap(b)) }}')
    w(f'func bV_mut_{n}() {{ s := mkA({n}); b := []byte(s); if len(b) > 0 {{ b[0] = \'x\' }}; rep("bytes", "var/mut", {n}, cap(b)) }}')
    w(f'func bV_esc_{n}() {{ s := mkA({n}); b := []byte(s); sinkB = b; rep("bytes", "var/esc", {n}, cap(b)) }}')
    w(f'func bC_nomut_{n}() {{ s := mkA({max(n-1,0)}) + "{"a" if n>0 else ""}"; b := []byte(s); rep("bytes", "concat/nomut", {n}, cap(b)) }}')
    w(f'func bC_esc_{n}() {{ s := mkA({max(n-1,0)}) + "{"a" if n>0 else ""}"; b := []byte(s); sinkB = b; rep("bytes", "concat/esc", {n}, cap(b)) }}')
    w(f'func bC_mut_{n}() {{ s := mkA({max(n-1,0)}) + "{"a" if n>0 else ""}"; b := []byte(s); if len(b) > 0 {{ b[0] = \'x\' }}; rep("bytes", "concat/mut", {n}, cap(b)) }}')
# ---- bytes, literal source
for n in LIT_LENS:
    w(f'func bL_nomut_{n}() {{ b := []byte({lit(n)}); rep("bytes", "lit/nomut", {n}, cap(b)) }}')
    w(f'func bL_mut_{n}() {{ b := []byte({lit(n)}); if len(b) > 0 {{ b[0] = \'x\' }}; rep("bytes", "lit/mut", {n}, cap(b)) }}')
    w(f'func bL_esc_{n}() {{ b := []byte({lit(n)}); sinkB = b; rep("bytes", "lit/esc", {n}, cap(b)) }}')
# ---- runes, variable source (2-byte runes) and ASCII variable source
for n in LENS:
    w(f'func rV_nomut_{n}() {{ s := mkE({n}); r := []rune(s); rep("runes", "var/nomut", {n}, cap(r)) }}')
    w(f'func rV_mut_{n}() {{ s := mkE({n}); r := []rune(s); if len(r) > 0 {{ r[0] = \'x\' }}; rep("runes", "var/mut", {n}, cap(r)) }}')
    w(f'func rV_esc_{n}() {{ s := mkE({n}); r := []rune(s); sinkR = r; rep("runes", "var/esc", {n}, cap(r)) }}')
    w(f'func rA_nomut_{n}() {{ s := mkA({n}); r := []rune(s); rep("runes", "ascii/nomut", {n}, cap(r)) }}')
for n in LIT_LENS:
    w(f'func rL_nomut_{n}() {{ r := []rune({lit(n)}); rep("runes", "lit/nomut", {n}, cap(r)) }}')
    w(f'func rL_esc_{n}() {{ r := []rune({lit(n)}); sinkR = r; rep("runes", "lit/esc", {n}, cap(r)) }}')
w('\nfunc main() {')
for n in LENS:
    for f in ('bV_nomut','bV_mut','bV_esc','bC_nomut','bC_esc','bC_mut','rV_nomut','rV_mut','rV_esc','rA_nomut'): w(f'\t{f}_{n}()')
for n in LIT_LENS:
    for f in ('bL_nomut','bL_mut','bL_esc','rL_nomut','rL_esc'): w(f'\t{f}_{n}()')
w('}')
open(sys.argv[1], 'w').write('\n'.join(out) + '\n')
