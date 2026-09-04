package main

// The strings.Builder LIBRARY-vs-ORACLE FUZZ (stdlib source-through slice
// 2, 2026-09-03; docs/evidence/2026-09-03_stdlib-source-2/). Ten subjects
// × 300 pseudo-random Builder operations = 3,000 operations in total —
// sized by measurement (100 ops 0.26 s, 300 1.4 s, 1,000 38 s per
// subject; the machine's assoc-list heap makes the cost quadratic in
// allocation count, BUG-090; the slice brief's 100k is out of the 30 s
// row budget until the dense heap lands), driven
// by an IN-PROGRAM xorshift64* generator (so the machine and go run draw
// the identical sequence): WriteString / WriteByte / WriteRune (ASCII,
// 2-, 3-, 4-byte, RuneError-producing invalid code points) / Write /
// Grow / Len / String / Reset. Every String() result and every Len() is
// folded into an FNV-1a 64-bit hash; the observation is (hash, final
// Len, final String prefix), so any byte the overlaid String() / grow()
// / copyCheck() path gets wrong anywhere in the 100k operations changes
// the hash. Reset fires about every 64 operations to bound the buffer
// (every String() allocates and every append writes cells — BUG-090).
// Cap is never observed
// (allocator latitude — the membership suite strings/builder-cap).

import "strings"

var words = []string{"", "a", "go", "lean", "raft", "été", "日本", "\U0001F600", "tab\t", "nl\n", "0123456789", "xyzzy"}
var runes = []rune{'a', 'Z', '0', 'é', '日', '\U0001F600', -1, 0x110000, 0xD800, 0x7F, 0x80, 0x7FF, 0x800, 0xFFFF, 0x10000}

type rng struct{ s uint64 }

func (r *rng) next() uint64 {
	r.s ^= r.s >> 12
	r.s ^= r.s << 25
	r.s ^= r.s >> 27
	return r.s * 2685821657736338717
}

func fnv(h uint64, s string) uint64 {
	for i := 0; i < len(s); i++ {
		h ^= uint64(s[i])
		h *= 1099511628211
	}
	return h
}

func fnvInt(h uint64, n int) uint64 {
	h ^= uint64(n)
	h *= 1099511628211
	return h
}

func fuzz(seed uint64, ops int) (uint64, int, string) {
	r := &rng{seed}
	var b strings.Builder
	h := uint64(14695981039346656037)
	for i := 0; i < ops; i++ {
		x := r.next()
		switch x % 8 {
		case 0:
			n, _ := b.WriteString(words[int(x>>8)%len(words)])
			h = fnvInt(h, n)
		case 1:
			b.WriteByte(byte(x >> 16))
		case 2:
			n, _ := b.WriteRune(runes[int(x>>8)%len(runes)])
			h = fnvInt(h, n)
		case 3:
			n, _ := b.Write([]byte(words[int(x>>8)%len(words)]))
			h = fnvInt(h, n)
		case 4:
			b.Grow(int(x>>8) % 65)
		case 5:
			h = fnv(h, b.String())
		case 6:
			h = fnvInt(h, b.Len())
		case 7:
			if (x>>8)%8 == 0 {
				h = fnv(h, b.String())
				b.Reset()
			} else {
				h = fnvInt(h, len(b.String()))
			}
		}
	}
	s := b.String()
	if len(s) > 16 {
		s = s[:16]
	}
	return h, b.Len(), s
}

func fuzz0() (uint64, int, string) { return fuzz(0x9E3779B97F4A7C15, 300) }
func fuzz1() (uint64, int, string) { return fuzz(0xD1B54A32D192ED03, 300) }
func fuzz2() (uint64, int, string) { return fuzz(0x2545F4914F6CDD1D, 300) }
func fuzz3() (uint64, int, string) { return fuzz(0x0000000020260903, 300) }
func fuzz4() (uint64, int, string) { return fuzz(0x1234567890ABCDEF, 300) }
func fuzz5() (uint64, int, string) { return fuzz(0xFEDCBA0987654321, 300) }
func fuzz6() (uint64, int, string) { return fuzz(0x0F0F0F0F0F0F0F0F, 300) }
func fuzz7() (uint64, int, string) { return fuzz(0xA5A5A5A5A5A5A5A5, 300) }
func fuzz8() (uint64, int, string) { return fuzz(0x0000000000000007, 300) }
func fuzz9() (uint64, int, string) { return fuzz(0xFFFFFFFFFFFFFFFF, 300) }

func main() {
	for _, f := range []func() (uint64, int, string){fuzz0, fuzz1, fuzz2, fuzz3, fuzz4, fuzz5, fuzz6, fuzz7, fuzz8, fuzz9} {
		h, n, s := f()
		println(h, n, s)
	}
}
