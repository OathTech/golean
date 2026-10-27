// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// A built-in's read captured at its lexical position, never re-read after a LATER call
// mutates its operand (BUG-062's len/cap hoist: len/cap are spec-ordered calls): cap of a
// slice, len of a map, len of a string, len of a call's result, and the constant len(*pa)
// of a nil pointer-to-array that is never read at all.

package main

var s = []int{1, 2, 3}
var m = map[int]int{1: 1}
var str = "abc"
var pa *[4]int
var ret = []int{1, 2, 3, 4, 5}

func mutS() int    { s = append(s, 9, 9, 9); return 1 }
func mutM() int    { m[7] = 7; m[8] = 8; return 1 }
func mutStr() int  { str = "abcdef"; return 1 }
func mutPa() int   { pa = &[4]int{}; return 1 }
func mutRet() int  { ret = ret[:1]; return 1 }
func fret() []int  { return ret }

func capThenCall() int {
	s = make([]int, 3, 3)
	x := cap(s) + mutS()
	return x*10 + len(s)
}

func lenMapThenCall() int {
	m = map[int]int{1: 1}
	x := len(m) + mutM()
	return x*10 + len(m)
}

func lenStringThenCall() int {
	str = "abc"
	x := len(str) + mutStr()
	return x*10 + len(str)
}

func lenPtrArrayConstThenCall() int {
	pa = nil
	x := len(*pa) + mutPa()
	return x*10 + len(*pa)
}

func lenCallThenMutatingCall() int {
	ret = []int{1, 2, 3, 4, 5}
	x := len(fret()) + mutRet()
	return x*10 + len(ret)
}

func main() {
	capThenCall()
	lenMapThenCall()
	lenStringThenCall()
	lenPtrArrayConstThenCall()
	lenCallThenMutatingCall()
}
