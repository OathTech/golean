// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// defer and go — the function value and the arguments are evaluated once, at the
// statement: a call-valued callee with a call argument, a closure with a call argument,
// a receiver from a call, two call arguments, a receive argument, defer close of a call,
// conversion / len / index-with-call arguments, and the go forms of the same.

package main

var cnt int

func f() int { cnt++; return 2 }
func g() int { cnt++; return 3 }

type T struct{ n int }

func (t *T) M()        { t.n++ }
func (t *T) Add(k int) { t.n += k }

func getF() func(int) int {
	cnt++
	return func(k int) int { cnt += 10; return k }
}

func getArg() int { cnt++; return 4 }

func fs() []int { cnt++; return []int{10, 20, 30} }

func deferCallValueCallArg() int {
	cnt = 0
	r := 0
	func() {
		defer func() { r = cnt }()
		defer getF()(getArg())
	}()
	return r*100 + cnt
}

func deferClosureCallArg() int {
	cnt = 0
	r := 0
	func() {
		defer func(a int) { r = a }(f())
	}()
	return cnt*100 + r
}

func goCallValueCallArg() int {
	cnt = 0
	done := make(chan int)
	go func(k int) { done <- k }(getArg())
	v := <-done
	return cnt*100 + v
}

func deferRecvCall() int {
	cnt = 0
	t := &T{}
	pt := func() *T { cnt++; return t }
	func() {
		defer pt().M()
	}()
	return cnt*100 + t.n
}

func deferTwoCallArgs() int {
	cnt = 0
	t := &T{}
	func() {
		defer t.Add(f() + g())
		defer t.Add(f())
	}()
	return cnt*100 + t.n
}

func deferRecvArg() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	t := &T{}
	func() {
		defer t.Add(<-ch)
	}()
	return len(ch)*100 + t.n
}

func deferCloseCall() int {
	cnt = 0
	ch := make(chan int)
	fc := func() chan int { cnt++; return ch }
	func() {
		defer close(fc())
	}()
	_, ok := <-ch
	if ok {
		return -1
	}
	return cnt * 100
}

func deferConvArg() int {
	cnt = 0
	t := &T{}
	func() {
		defer t.Add(int(int64(f())))
	}()
	return cnt*100 + t.n
}

func deferLenArg() int {
	cnt = 0
	t := &T{}
	func() {
		defer t.Add(len(fs()))
	}()
	return cnt*100 + t.n
}

func deferIndexCallArg() int {
	cnt = 0
	t := &T{}
	s := []int{10, 20, 30}
	func() {
		defer t.Add(s[f()])
	}()
	return cnt*100 + t.n
}

func goRecvArg() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	done := make(chan int)
	go func(k int) { done <- k }(<-ch)
	v := <-done
	return len(ch)*100 + v
}

func goConvArg() int {
	cnt = 0
	done := make(chan int)
	go func(k int64) { done <- int(k) }(int64(f()))
	v := <-done
	return cnt*100 + v
}

func goFuncValueCall() int {
	cnt = 0
	done := make(chan int)
	gf := func() func(int) {
		cnt++
		return func(k int) { done <- k }
	}
	go gf()(getArg())
	v := <-done
	return cnt*100 + v
}

func main() {
	deferCallValueCallArg()
	deferClosureCallArg()
	goCallValueCallArg()
	deferRecvCall()
	deferTwoCallArgs()
	deferRecvArg()
	deferCloseCall()
	deferConvArg()
	deferLenArg()
	deferIndexCallArg()
	goRecvArg()
	goConvArg()
	goFuncValueCall()
}
