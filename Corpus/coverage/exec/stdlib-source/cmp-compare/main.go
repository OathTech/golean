package main

// cmp through the REAL source-through package (slice 2, 2026-09-03). The
// kind-dispatch desugar for cmp.Compare at integer/string kinds is
// RETAINED (cmpshim.go, the slice's STOP rule); everything else here is
// the real generic: float kinds (the NaN arm the desugar excluded — the
// old float-compare-bound refusal is gone), cmp.Less, cmp.Or, and
// cmp.Compare at a named float type. (`math` is not a source-through
// package: NaN, ±Inf and -0 are produced by float arithmetic on
// variables — `z/z`, `1/z`, `-z` — exactly as gc computes them.)

import "cmp"

type Score float64

var z float64 // zero at run time: z/z is NaN, 1/z is +Inf, -z is -0

func nan() float64 { return z / z }

func cmpFloatsNaN() string {
	n := nan()
	out := ""
	for _, p := range [][2]float64{{n, 1}, {1, n}, {n, n}, {1.5, 2.5}, {2.5, 1.5}, {0, -z}, {1 / z, -1 / z}, {-1 / z, n}} {
		out += string(rune('0' + 1 + cmp.Compare(p[0], p[1])))
	}
	return out
}

func cmpFloat32AndNamed() (int, int, int) {
	var a, b float32 = 1.25, 1.5
	return cmp.Compare(a, b), cmp.Compare(Score(3), Score(3)), cmp.Compare(Score(9), Score(-1))
}

func cmpLess() (bool, bool, bool, bool) {
	n := nan()
	return cmp.Less(n, 1.0), cmp.Less(1.0, n), cmp.Less("a", "b"), cmp.Less(3, 3)
}

func cmpOr() (int, string, float64) {
	return cmp.Or(0, 0, 7, 9), cmp.Or("", "", "x", "y"), cmp.Or(0.0, nan())
}

// The retained kind-dispatch desugar (cmpshim.go) intercepts EVERY integer/
// string cmp.Compare call site — including the function-local defined
// type the row slices/sortfunc-cmp/cmp-compare-kinds pins — but a
// function-local FLOAT type falls through to the real generic and hits
// mono.go's C6 naming rule: an ASYMMETRY the audit asked to row (born red
// by name; C6 is a ratified (c)-impossibility, revisitable under FR-19's
// scope-qualified TypeId plan). gc: 1000 - 1 + 1 = ... see main.
func cmpLocalFloatType() int {
	type score float64
	return cmp.Compare(score(2.5), score(1.5))*100 + cmp.Compare(score(1), score(1))*10 + cmp.Compare(score(-1), score(0)) + 1000
}

func main() {
	println(cmpLocalFloatType())
	println(cmpFloatsNaN())
	a, b, c := cmpFloat32AndNamed()
	println(a, b, c)
	l1, l2, l3, l4 := cmpLess()
	println(l1, l2, l3, l4)
	o1, o2, o3 := cmpOr()
	println(o1, o2, o3 != o3)
}
