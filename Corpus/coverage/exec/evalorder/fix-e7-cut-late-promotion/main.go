package main

// Lane frontend/fix-e7-cut-1107 (2026-11-07), the train-31 pre-merge audit's finding A on BUG-311: the
// legacy hoist's `insertMain` promoted EVERY late entry up to the one a bound statement reads, unrelated
// allocations included. An early-boxed interface method value (`j.M` into `any`) therefore dragged an
// earlier late slice literal (`[]int{n}`) or another method value's box and nil check (`i.M` into a
// func-typed parameter) ahead of the sweep's call: gc 500 / the machine 0 (n read before set()), gc 1 /
// the machine a nil-dereference panic (i.M's box nil-checked before set() assigned i). The promotion now
// follows the dependencies only; the subjects below are the audit's b13, b14, b16, b17, b1, b4.

type I interface{ M() int }
type T struct{}

func (T) M() int { return 1 }

var n int
var i I
var j I = T{}

func setN() int { n = 5; return 0 }
func setI() int { i = T{}; return 0 }

func sinkS(s []int, a any, k int) int       { return s[0]*100 + k }
func sinkF2(f func() int, a any, k int) int { return f() + k }
func sinkAny(a any, k int) int              { return k }
func sinkF(f func() int, k int) int         { return f() + k }
func sinkS2(s []int, k int) int             { return s[0]*100 + k }

func sliceThenBox() int    { return sinkS([]int{n}, j.M, setN()) }
func twoMethodValues() int { return sinkF2(i.M, j.M, setI()) }
func tupleSite() int {
	var f func() int
	var a any
	var k int
	f, a, k = i.M, j.M, setI()
	_ = a
	return f() + k
}
func three() (func() int, any, int) { return i.M, j.M, setI() }
func returnList() int {
	f, _, k := three()
	return f() + k
}
func nestedCalls() int { return sinkF(i.M, sinkAny(j.M, setI())) }
func nestedSlice() int { return sinkS2([]int{n}, sinkAny(j.M, setN())) }

func main() {
	println(sliceThenBox(), twoMethodValues(), tupleSite(), returnList(), nestedCalls(), nestedSlice())
}
