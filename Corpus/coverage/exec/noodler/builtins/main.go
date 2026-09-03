// noodler probes — min/max/clear/copy/append/len/cap/new edges
// (spec#Min_and_max, spec#Clear, spec#Appending_and_copying_slices,
// spec#Length_and_capacity).
package main

// min/max with NaN and signed zeros: NaN wins; -0 < +0.
func minMaxFloatSpecials() (bool, bool, bool, bool) {
	zero := 0.0
	nan := zero / zero
	negZero := -zero
	a := min(nan, 1.0)
	b := max(1.0, nan)
	c := min(negZero, zero)
	d := max(negZero, zero)
	return a != a, b != b, 1/c < 0, 1/d > 0
}

// min/max over strings and mixed constant/variable ints.
func minMaxStringsInts() (string, string, int, int) {
	x := 5
	return min("b", "ab", "c"), max("b", "ab"), min(x, 3, 9), max(x, 7)
}

// min/max with a single argument and with defined types.
type Level int

func minMaxSingleDefined() (Level, Level) {
	a := Level(4)
	return min(a), max(a, Level(2), Level(9))
}

// clear on a slice of strings and a slice of structs zeroes elements;
// length is unchanged.
func clearSliceKinds() (int, string, int) {
	s := []string{"a", "b"}
	type P struct{ x int }
	ps := []P{{1}, {2}}
	clear(s)
	clear(ps)
	return len(s), s[0] + s[1], ps[0].x + ps[1].x
}

// clear on a nil map and nil slice is a no-op.
func clearNils() (int, int) {
	var m map[int]int
	var s []int
	clear(m)
	clear(s)
	return len(m), len(s)
}

// clear on a subslice clears only the window.
func clearSubslice() int {
	s := []int{1, 2, 3, 4, 5}
	clear(s[1:3])
	return s[0]*10000 + s[1]*1000 + s[2]*100 + s[3]*10 + s[4]
}

// copy from a string into a byte slice; count is the min length.
func copyStringToBytes() (int, string) {
	b := make([]byte, 3)
	n := copy(b, "hello")
	return n, string(b)
}

// copy with overlapping windows in both directions.
func copyOverlapBothWays() (int, int) {
	a := []int{1, 2, 3, 4, 5}
	copy(a[1:], a)
	b := []int{1, 2, 3, 4, 5}
	copy(b, b[1:])
	ra := a[0]*10000 + a[1]*1000 + a[2]*100 + a[3]*10 + a[4]
	rb := b[0]*10000 + b[1]*1000 + b[2]*100 + b[3]*10 + b[4]
	return ra, rb
}

// append to a nil slice, and append of nothing to nil stays nil.
func appendNilCases() (bool, int, bool) {
	var s []int
	t := append(s)
	u := append(s, 1)
	return t == nil, len(u), u == nil
}

// append aliasing: appending within capacity writes into the shared
// backing array.
func appendAliasingWithinCap() (int, int) {
	base := make([]int, 2, 4)
	a := append(base, 1)
	b := append(base, 2)
	return a[2], b[2]
}

// append spreads a string into a []byte.
func appendStringSpread() string {
	b := []byte("ab")
	b = append(b, "cd"...)
	return string(b)
}

// len/cap of arrays via pointer, of nil map/slice/chan.
func lenCapZeroValues() (int, int, int, int, int) {
	var s []int
	var m map[int]int
	var c chan int
	var p *[4]int
	return len(s) + cap(s), len(m), len(c) + cap(c), len(p), cap(p)
}

// new of a struct and of a slice type; pointer-to-slice zero.
func newKinds() (int, bool, bool) {
	type S struct{ a, b int }
	p := new(S)
	p.a = 3
	q := new([]int)
	r := new(map[string]int)
	return p.a + p.b, *q == nil, *r == nil
}

// append growth preserves earlier elements; len tracks exactly.
func appendGrowthLen() (int, int) {
	var s []int
	for i := 0; i < 100; i++ {
		s = append(s, i)
	}
	return len(s), s[99] + s[0]
}

// copy between slices of different lengths returns min; dst unchanged
// past n.
func copyMinLength() (int, int) {
	dst := []int{9, 9, 9, 9}
	n := copy(dst, []int{1, 2})
	return n, dst[0]*1000 + dst[1]*100 + dst[2]*10 + dst[3]
}

// min/max with mixed untyped constants and a float variable.
func minMaxUntypedWithFloat() (float64, float64) {
	f := 2.5
	return min(f, 3, 1), max(f, 3, 1)
}

// delete on a missing key and on a nil map are no-ops.
func deleteNoops() int {
	m := map[string]int{"a": 1}
	delete(m, "zzz")
	var n map[string]int
	delete(n, "a")
	return len(m)*10 + len(n)
}

// cap after a three-index slice and after slicing from the front.
func capAfterSlicing() (int, int, int) {
	s := make([]int, 3, 10)
	return cap(s[1:]), cap(s[:2:5]), cap(s[3:])
}

// max of int8 values at the boundary and min of uint.
func minMaxIntegerBoundaries() (int8, uint) {
	var a, b int8 = -128, 127
	var c, d uint = 0, 1<<64 - 1
	return max(a, b), min(c, d)
}

func main() {}
