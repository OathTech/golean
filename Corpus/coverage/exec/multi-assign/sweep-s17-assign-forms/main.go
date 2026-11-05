package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-057's line): assignment statement shapes the corpus did not hold —
// every compound operator folded into one subject, compound operators over
// strings, floats, unsigned and defined kinds, a named result and a global,
// parallel assignments through two dereferences, two fields and three slice
// elements, and the self-assignment. Expected = gc go1.26.5.

type pair struct{ a, b int }

type k int32

var g int

// A6.2
func compoundAllOps() int {
	x := 100
	x += 7
	x -= 3
	x *= 2
	x /= 3
	x %= 50
	x &= 0x3f
	x |= 0x40
	x ^= 0x11
	x <<= 2
	x >>= 1
	x &^= 0x8
	return x // 132
}

// A6.3
func compoundStringConcat() int {
	s := "a"
	s += "b"
	s += s
	return len(s)*100 + int(s[0]) // 497
}

func compoundFloat() int {
	f := 9.0
	f /= 2
	f *= 3
	f -= 0.5
	f += 1
	return int(f) // 14
}

func compoundUintOps() int {
	var u uint8 = 0xf0
	u >>= 4
	u &^= 1
	u <<= 1
	u |= 0x81
	u ^= 0xff
	return int(u) // 98
}

func compoundDefined() int {
	var v k = 3
	v <<= 2
	v -= 1
	v *= v
	return int(v) // 121
}

// A6.9
func multiDerefTargets() int {
	x, y := 0, 0
	p, q := &x, &y
	*p, *q = 1, 2
	return x*10 + y // 12
}

func multiFieldSwap() int {
	p := pair{1, 2}
	p.a, p.b = p.b, p.a
	return p.a*10 + p.b // 21
}

func threeSliceElems() int {
	s := make([]int, 3)
	s[0], s[1], s[2] = 3, 2, 1
	return s[0]*100 + s[1]*10 + s[2] // 321
}

// A6.11
func selfAssign() int {
	x, y := 3, 4
	x = x
	x, y = x, y
	y, x = x, y
	return x*10 + y // 43
}

// A6.18
func compoundNamedResult() (r int) {
	r = 5
	r *= 2
	r += 1
	return // 11
}

func compoundGlobal() int {
	g = 1
	g <<= 3
	g |= 1
	return g // 9
}

func main() {
	println(compoundAllOps(), compoundStringConcat(), compoundFloat(), compoundUintOps(), compoundDefined(),
		multiDerefTargets(), multiFieldSwap(), threeSliceElems(), selfAssign(), compoundNamedResult(), compoundGlobal())
}
