// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Slice expressions with calls in the base and the bounds — BUG-066's site (emitSliceExpr's
// default-high arm): a call base with a call low / high / three-index bounds, a pointer-to-
// array call base, a local array with a call low, a receive as the base and as a bound, the
// doubly-elided nesting, an explicit high from a call, chained slicings, a string base, in a
// closure and in a generic function.

package main

var cnt int

func f() int         { cnt++; return 1 }
func g() int         { cnt++; return 2 }
func h() int         { cnt++; return 3 }
func fs() []int      { cnt++; return []int{10, 20, 30, 40} }
func fs2() []int     { cnt++; return []int{1, 2} }
func fstr() string   { cnt++; return "abcd" }
func pa() *[4]int    { cnt++; return &[4]int{10, 20, 30, 40} }
func chs() chan []int { cnt++; c := make(chan []int, 2); c <- []int{10, 20, 30}; c <- []int{1}; return c }

func callBaseCallLow() int {
	cnt = 0
	s := fs()[f():]
	return cnt*100 + len(s)*10 + s[0]%10
}

func callBaseCallHigh() int {
	cnt = 0
	s := fs()[:g()]
	return cnt*100 + len(s)*10 + s[1]%10
}

func threeIndexCalls() int {
	cnt = 0
	s := fs()[f():g():h()]
	return cnt*100 + len(s)*10 + cap(s)
}

func ptrArrayCallLow() int {
	cnt = 0
	s := pa()[f():]
	return cnt*100 + len(s)*10 + s[0]%10
}

func recvBase() int {
	cnt = 0
	c := chs()
	s := (<-c)[:]
	return cnt*100 + len(c)*10 + len(s)
}

func recvLow() int {
	cnt = 0
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	s := []int{10, 20, 30}
	t := s[<-ch:]
	return cnt*100 + len(ch)*10 + len(t)
}

func arrayCallLow() int {
	cnt = 0
	arr := [4]int{10, 20, 30, 40}
	s := arr[f():]
	return cnt*100 + len(s)*10 + s[0]%10
}

func nestedElided() int {
	cnt = 0
	s := fs()[:][:]
	return cnt*100 + len(s)*10 + s[0]%10
}

func explicitHighCall() int {
	cnt = 0
	s := fs()[:len(fs2())]
	return cnt*100 + len(s)*10 + s[0]%10
}

func chainCallLows() int {
	cnt = 0
	s := []int{10, 20, 30, 40}
	t := s[f():][g():]
	return cnt*100 + len(t)*10 + t[0]%10
}

func stringCallBaseCallLow() int {
	cnt = 0
	s := fstr()[f():]
	return cnt*100 + len(s)*10 + int(s[0]-'a')
}

func recvHigh() int {
	cnt = 0
	ch := make(chan int, 2)
	ch <- 2
	ch <- 3
	s := []int{10, 20, 30}
	t := s[:<-ch]
	return cnt*100 + len(ch)*10 + len(t)
}

func fs3() []int { cnt++; return []int{10, 20, 30} }

func fsg[T any](v T) []T { cnt++; return []T{v, v, v} }

func sliceGeneric[T any](v T) int {
	s := fsg(v)[:]
	t := fsg[T](v)[1:]
	return len(s)*10 + len(t)
}

func closureSlice() int {
	cnt = 0
	r := 0
	inner := func() {
		s := fs3()[:]
		t := fs3()[1:]
		r = len(s)*10 + len(t)
	}
	inner()
	return cnt*100 + r
}

func genericSlice() int {
	cnt = 0
	r := sliceGeneric(1) + sliceGeneric("s")
	return cnt*100 + r
}

func main() {
	callBaseCallLow()
	callBaseCallHigh()
	threeIndexCalls()
	ptrArrayCallLow()
	recvBase()
	recvLow()
	arrayCallLow()
	nestedElided()
	explicitHighCall()
	chainCallLows()
	stringCallBaseCallLow()
	recvHigh()
	closureSlice()
	genericSlice()
}
