// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Range expressions — BUG-076's site (emitRange): an operand that is a call evaluated once
// before the loop for every collection kind (slice, int, map, string, channel, array with
// one and two variables, pointer-to-array index-only, a deref of a call, a slice expression
// with a call, a receive, len of a call); an array literal of calls with one variable (the
// calls run: hasCallOrRecv); an array literal of a panicking effect-free element with one
// variable (NOT evaluated: no panic); in a closure and in a generic function.

package main

var cnt int

func f() int           { cnt++; return 1 }
func g() int           { cnt++; return 2 }
func h() int           { cnt++; return 3 }
func fs() []int        { cnt++; return []int{10, 20, 30} }
func fint() int        { cnt++; return 4 }
func fm() map[int]int  { cnt++; return map[int]int{1: 1, 2: 2} }
func fstr() string     { cnt++; return "abc" }
func fch() chan int    { cnt++; c := make(chan int, 2); c <- 1; c <- 2; close(c); return c }
func farr() [3]int     { cnt++; return [3]int{5, 6, 7} }
func pf() *[4]int      { cnt++; return &[4]int{1, 2, 3, 4} }

func sliceCall() int {
	cnt = 0
	n := 0
	for i := range fs() {
		n += i
	}
	return cnt*100 + n
}

func intCall() int {
	cnt = 0
	n := 0
	for range fint() {
		n++
	}
	return cnt*100 + n
}

func mapCall() int {
	cnt = 0
	n := 0
	for k := range fm() {
		n += k
	}
	return cnt*100 + n
}

func stringCall() int {
	cnt = 0
	n := 0
	for i := range fstr() {
		n += i
	}
	return cnt*100 + n
}

func chanCall() int {
	cnt = 0
	n := 0
	for v := range fch() {
		n += v
	}
	return cnt*100 + n
}

func arrayCallTwoVars() int {
	cnt = 0
	n := 0
	for i, v := range farr() {
		n += i + v
	}
	return cnt*100 + n
}

func sliceExprCall() int {
	cnt = 0
	s := []int{10, 20, 30}
	n := 0
	for i := range s[f():] {
		n += i + 1
	}
	return cnt*100 + n
}

func recvOperand() int {
	chs := make(chan []int, 2)
	chs <- []int{1, 2, 3}
	chs <- []int{1}
	n := 0
	for range <-chs {
		n++
	}
	return len(chs)*100 + n
}

func ptrArrayCallIndexOnly() int {
	cnt = 0
	n := 0
	for i := range pf() {
		n += i
	}
	return cnt*100 + n
}

func lenCallInt() int {
	cnt = 0
	n := 0
	for i := range len(fs()) {
		n += i
	}
	return cnt*100 + n
}

func arrayLitCallsOneVar() int {
	cnt = 0
	n := 0
	for i := range [3]int{f(), g(), h()} {
		n += i
	}
	return cnt*100 + n
}

func arrayLitPanickyOneVar() (r int) {
	defer func() {
		if recover() != nil {
			r = -1
		}
	}()
	s := []int{1}
	n := 0
	for i := range [2]int{s[9], 0} {
		n += i + 1
	}
	return n
}

func sliceCallNoVar() int {
	cnt = 0
	n := 0
	for range fs() {
		n++
	}
	return cnt*100 + n
}

func derefCallOneVar() int {
	cnt = 0
	n := 0
	for i := range *pf() {
		n += i
	}
	return cnt*100 + n
}

func arrayCallOneVar() int {
	cnt = 0
	n := 0
	for i := range farr() {
		n += i
	}
	return cnt*100 + n
}

func fsg[T any](v T) []T { cnt++; return []T{v, v} }

func rangeGeneric[T any](v T) int {
	n := 0
	for i := range fsg(v) {
		n += i + 1
	}
	for range fsg[T](v) {
		n += 10
	}
	return n
}

func closureRange() int {
	cnt = 0
	n := 0
	inner := func() {
		for i := range fs() {
			n += i
		}
		for range fint() {
			n += 10
		}
	}
	inner()
	return cnt*100 + n
}

func genericRange() int {
	cnt = 0
	r := rangeGeneric(1) + rangeGeneric("s")
	return cnt*100 + r
}

func main() {
	sliceCall()
	intCall()
	mapCall()
	stringCall()
	chanCall()
	arrayCallTwoVars()
	sliceExprCall()
	recvOperand()
	ptrArrayCallIndexOnly()
	lenCallInt()
	arrayLitCallsOneVar()
	arrayLitPanickyOneVar()
	sliceCallNoVar()
	derefCallOneVar()
	arrayCallOneVar()
	closureRange()
	genericRange()
}
