// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Comparison and concatenation chains with call operands — a short-circuited comparison
// chain, == over ints / strings / interfaces / pointers from calls, a conversion inside a
// concatenation, in a closure and in a generic function — each operand exactly once.

package main

var cnt int

func f() int       { cnt++; return 1 }
func g() int       { cnt++; return 2 }
func h() int       { cnt++; return 3 }
func fs() string   { cnt++; return "x" }
func gs() string   { cnt++; return "x" }
func fr() []rune   { cnt++; return []rune{'a'} }
func fi() any      { cnt++; return 5 }
func gi() any      { cnt++; return 5 }

var pa, pb int

func fp() *int { cnt++; return &pa }
func gp() *int { cnt++; return &pa }

func cmpChainShortCircuit() int {
	cnt = 0
	r := 0
	if f() < g() && g() < h() {
		r = 1
	}
	if f() > g() && g() < h() {
		r += 10
	}
	return cnt*100 + r
}

func eqCallsInt() int {
	cnt = 0
	r := 0
	if f() == f() {
		r = 1
	}
	return cnt*100 + r
}

func eqCallsString() int {
	cnt = 0
	r := 0
	if fs() == gs() {
		r = 1
	}
	return cnt*100 + r
}

func eqCallsIface() int {
	cnt = 0
	r := 0
	if fi() == gi() {
		r = 1
	}
	return cnt*100 + r
}

func eqCallsPtr() int {
	cnt = 0
	r := 0
	if fp() == gp() {
		r = 1
	}
	return cnt*100 + r
}

func convConcat() int {
	cnt = 0
	s := string(fr()) + fs() + gs()
	return cnt*100 + len(s)
}

func closureChain() int {
	cnt = 0
	r := 0
	inner := func() {
		if f() < g() && g() < h() {
			r = 1
		}
		s := fs() + gs()
		r += len(s) * 10
	}
	inner()
	return cnt*100 + r
}

func chainGeneric[T int | string](a, b, c func() T) int {
	if a() < b() && b() < c() {
		return 1
	}
	return 0
}

func genericChain() int {
	cnt = 0
	r := chainGeneric(f, g, h) + chainGeneric(func() string { cnt++; return "a" }, func() string { cnt++; return "b" }, func() string { cnt++; return "a" })
	return cnt*100 + r
}

func main() {
	cmpChainShortCircuit()
	eqCallsInt()
	eqCallsString()
	eqCallsIface()
	eqCallsPtr()
	convConcat()
	closureChain()
	genericChain()
}
