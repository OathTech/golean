package main

// `slices.Sort` at NON-INTEGER and NAMED element kinds, and inside an
// `init()` — memo docs/2026-09-03_stdlib-boundary-design.md §3 row M
// (2026-09-04, lane fr4-rowm): the `sortSlice` MACHINE OP intercept at
// integer kinds is RETIRED and `slices.Sort` is the real source-through
// generic everywhere — `Sort` → `pdqsortOrdered` stenciled per element
// type by mono.go, gc's exact member. What these rows pin beyond the
// integer rows (`slices/slices-sort*`, green through the real generic now):
//
//   string / named-string      string ordering (byte-wise), a named kind
//   float-nan-first            NaN sorts BEFORE every other value
//                              (cmpLess: `isNaN(x) && !isNaN(y) || x < y`),
//                              ±Inf at the ends
//   float-signed-zero          -0.0 and +0.0 are EQUAL under <, so pdqsort
//                              may leave them in either order; the row
//                              observes only what Go specifies (both zeros
//                              sit between the negatives and the positives)
//   float32 / named-float      the other float kind, a named float kind
//   string-large               n > 12 elements — past insertionSortOrdered's
//                              threshold into choosePivot / partition /
//                              breakPatterns (the paths the small rows never
//                              reach)
//   init-sort                  `slices.Sort` at string inside `init()` —
//                              cedar-go's kill shape (census §10.2: 4 cases
//                              on `x/exp/schema/internal/parser/marshal.go`)

import "slices"

func sortStrings() string {
	xs := []string{"pear", "apple", "fig", "banana", "", "Apple"}
	slices.Sort(xs)
	out := ""
	for _, s := range xs {
		out += s + "|"
	}
	return out // "|Apple|apple|banana|fig|pear|"
}

type label string

func sortNamedStrings() string {
	xs := []label{"b", "a", "c"}
	slices.Sort(xs)
	return string(xs[0]) + string(xs[1]) + string(xs[2]) // "abc"
}

// Observe a float ordering as an integer code: NaN is x != x, the sign of
// a zero is 1/x < 0, infinities compare with a large finite.
func floatCode(xs []float64) int {
	code := 0
	for _, x := range xs {
		code *= 10
		switch {
		case x != x:
			code += 9 // NaN
		case x == 0 && 1/x < 0:
			code += 4 // -0
		case x == 0:
			code += 5 // +0
		case x < -1e300:
			code += 1 // -Inf
		case x > 1e300:
			code += 8 // +Inf
		case x < 0:
			code += 2
		default:
			code += 7
		}
	}
	return code
}

func sortFloatNaNFirst() int {
	zero := 0.0
	nan, pinf, ninf := zero/zero, 1/zero, -1/zero
	xs := []float64{3.5, nan, -2, pinf, 0.25, ninf, nan}
	slices.Sort(xs)
	return floatCode(xs) // 9 9 1 2 7 7 8 → 9912778
}

func sortFloatSignedZero() int {
	zero := 0.0
	negZero := -zero
	xs := []float64{1, negZero, -1, 0, 2}
	slices.Sort(xs)
	// Go specifies only: negatives, then the two zeros (either order), then
	// positives. Observe the zeros as a set.
	c := floatCode(xs)
	zeros := c / 100 % 100 // the two middle digits
	if zeros == 45 || zeros == 54 {
		return c/10000*100 + c%100 // 2 77 → 277
	}
	return c
}

func sortFloat32() int {
	xs := []float32{2.5, -1.5, 0.5, -3}
	slices.Sort(xs)
	return int(xs[0]*2) + int(xs[1]*2)*100 + int(xs[2]*2)*10000 + int(xs[3]*2)*1000000 // -6 + -300 + 10000 + 5000000
}

type score float64

func sortNamedFloats() int {
	xs := []score{2.5, -1.5, 10}
	slices.Sort(xs)
	return int(xs[0]*2)*1000 + int(xs[1]*2)*100 + int(xs[2]) // -3000 + 500 + 10
}

func sortStringsLarge() string {
	// 26 letters in a pattern that defeats a sorted/reversed shortcut:
	// pdqsort's choosePivot + partition + breakPatterns paths run.
	xs := []string{"m", "z", "a", "q", "b", "y", "c", "x", "d", "w", "e", "v",
		"f", "u", "g", "t", "h", "s", "i", "r", "j", "p", "k", "o", "l", "n"}
	slices.Sort(xs)
	out := ""
	for _, s := range xs {
		out += s
	}
	return out // "abcdefghijklmnopqrstuvwxyz"
}

var order = []string{"zeta", "alpha", "mu", "beta"}

func init() {
	slices.Sort(order)
}

func initSort() string {
	return order[0] + "," + order[1] + "," + order[2] + "," + order[3] // "alpha,beta,mu,zeta"
}

func main() {
	println(sortStrings())
	println(sortNamedStrings())
	println(sortFloatNaNFirst())
	println(sortFloatSignedZero())
	println(sortFloat32())
	println(sortNamedFloats())
	println(sortStringsLarge())
	println(initSort())
}
