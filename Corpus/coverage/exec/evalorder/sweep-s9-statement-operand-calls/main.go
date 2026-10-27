// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// The remaining statement forms with call operands, each evaluated once: a map read and
// the comma-ok map / type-assertion / receive statements, a send with call operands, the
// receive assignment forms, blank assigns, reads and stores through a call, receivers from
// calls (interface, pointer, value), variadic spreads, an immediately-invoked literal,
// generic calls, unary operands, an address through a call, a shift of calls, and a
// package-level blank variable whose initializer is a call (evaluated at init).

package main

var cnt int

type T struct{ x int }

func (t *T) M(k int) int { return t.x + k }

type I interface{ M(int) int }

func f() int           { cnt++; return 2 }
func g() int           { cnt++; return 3 }
func fm() map[int]int  { cnt++; return map[int]int{1: 5} }
func fk() int          { cnt++; return 1 }
func fi() I            { cnt++; return &T{x: 10} }
func fch() chan int    { cnt++; c := make(chan int, 2); c <- 7; return c }
func fv() int          { cnt++; return 4 }
func pt() *T           { cnt++; return &T{x: 20} }
func gt() T            { cnt++; return T{x: 30} }
func fs() []int        { cnt++; return []int{1, 2, 3} }
func sum(xs ...int) int {
	t := 0
	for _, x := range xs {
		t += x
	}
	return t
}

func gen[X any](v X) X { return v }

func mapReadCalls() int {
	cnt = 0
	v := fm()[fk()]
	return cnt*100 + v
}

func commaOkMapCalls() int {
	cnt = 0
	v, ok := fm()[fk()]
	if !ok {
		return -1
	}
	return cnt*100 + v
}

func commaOkAssertCall() int {
	cnt = 0
	v, ok := fi().(*T)
	if !ok {
		return -1
	}
	return cnt*100 + v.x
}

func commaOkRecvCall() int {
	cnt = 0
	v, ok := <-fch()
	if !ok {
		return -1
	}
	return cnt*100 + v
}

func sendCalls() int {
	cnt = 0
	ch := make(chan int, 2)
	fc := func() chan int { cnt++; return ch }
	fc() <- fv()
	return cnt*100 + len(ch)*10 + <-ch
}

func recvAssignChanCall() int {
	cnt = 0
	var x int
	x = <-fch()
	return cnt*100 + x
}

func recvAssignIndexCall() int {
	cnt = 0
	s := []int{0, 0}
	ch := make(chan int, 1)
	ch <- 7
	s[fk()] = <-ch
	return cnt*100 + s[1]
}

func blankCalls() int {
	cnt = 0
	_ = f()
	_, _ = f(), g()
	return cnt * 100
}

func callReads() int {
	cnt = 0
	a := pt().x
	b := fs()[1]
	c := *pt()
	return cnt*100 + a + b + c.x
}

func storeThroughCall() int {
	cnt = 0
	t := &T{}
	p := func() *T { cnt++; return t }
	p().x = g()
	return cnt*100 + t.x
}

func ifaceCallRecvCall() int {
	cnt = 0
	v := fi().M(g())
	return cnt*100 + v
}

func ptrRecvCall() int {
	cnt = 0
	v := pt().M(1)
	return cnt*100 + v
}

func valueRecvCall() int {
	cnt = 0
	t := gt()
	v := t.M(1)
	w := (&t).M(2)
	return cnt*100 + v + w
}

func variadicSpreadCall() int {
	cnt = 0
	v := sum(fs()...)
	w := sum(f(), g())
	return cnt*100 + v + w
}

func iife() int {
	cnt = 0
	v := func() int { return f() }()
	return cnt*100 + v
}

func genericCallArg() int {
	cnt = 0
	v := gen(f())
	w := gen[int](g())
	return cnt*100 + v + w
}

func unaryCalls() int {
	cnt = 0
	a := -f()
	b := ^g()
	fb := func() bool { cnt++; return false }
	c := !fb()
	r := a + b
	if c {
		r += 100
	}
	return cnt*1000 + r + 100
}

func addrThroughCall() int {
	cnt = 0
	p := &pt().x
	*p += 1
	return cnt*100 + *p
}

func shiftCalls() int {
	cnt = 0
	v := f() << g()
	return cnt*100 + v
}

func bump() int { cnt++; return 5 }

var _ = bump()

var _, keep = bump(), bump()

func pkgBlankVarCall() int {
	return cnt*100 + keep
}

func main() {
	mapReadCalls()
	commaOkMapCalls()
	commaOkAssertCall()
	commaOkRecvCall()
	sendCalls()
	recvAssignChanCall()
	recvAssignIndexCall()
	blankCalls()
	callReads()
	storeThroughCall()
	ifaceCallRecvCall()
	ptrRecvCall()
	valueRecvCall()
	variadicSpreadCall()
	iife()
	genericCallArg()
	unaryCalls()
	addrThroughCall()
	shiftCalls()
	pkgBlankVarCall()
}
