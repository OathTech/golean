// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// select operands — BUG-074's site (emitSelect / selectRecvClause): channel operands and
// send values that are calls, evaluated exactly once on entry whether or not the clause is
// selected (with a default so nothing blocks), a receive target whose index operand is a
// call (evaluated only when the clause is selected), three clauses with every operand a
// call, a select in a loop (once per entry), the comma-ok receive, nil channels from calls,
// in a closure and in a generic function.

package main

var cnt int

func f() int { cnt++; return 1 }

func fv() int { cnt++; return 7 }

func fch(ready bool, cap int) chan int {
	cnt++
	ch := make(chan int, cap)
	if ready {
		ch <- 5
	}
	return ch
}

func fnil() chan int { cnt++; return nil }

func sendCalls() int {
	cnt = 0
	r := 0
	select {
	case fch(false, 1) <- fv():
		r = 1
	default:
		r = 2
	}
	return cnt*100 + r
}

func recvChanCallNotReady() int {
	cnt = 0
	r := 0
	select {
	case v := <-fch(false, 0):
		r = v
	default:
		r = 2
	}
	return cnt*100 + r
}

func recvTargetIndexCallSelected() int {
	cnt = 0
	a := []int{0, 0}
	ch := make(chan int, 1)
	ch <- 5
	select {
	case a[f()] = <-ch:
	default:
	}
	return cnt*100 + a[1]
}

func recvTargetIndexCallNotSelected() int {
	cnt = 0
	a := []int{0, 0}
	ch := make(chan int, 1)
	r := 0
	select {
	case a[f()] = <-ch:
		r = 1
	default:
		r = 2
	}
	return cnt*100 + r*10 + a[1]
}

func threeClauseCalls() int {
	cnt = 0
	r := 0
	select {
	case <-fch(false, 0):
		r = 1
	case fch(false, 0) <- fv():
		r = 2
	case v, ok := <-fch(false, 0):
		r = v + 3
		if !ok {
			r = 4
		}
	default:
		r = 9
	}
	return cnt*100 + r
}

func loopEntries() int {
	cnt = 0
	r := 0
	for i := 0; i < 3; i++ {
		select {
		case <-fch(false, 0):
			r += 100
		case fch(false, 0) <- fv():
			r += 10
		default:
			r++
		}
	}
	return cnt*100 + r
}

func sendValueCallNotSelected() int {
	cnt = 0
	ch := make(chan int)
	r := 0
	select {
	case ch <- fv():
		r = 1
	default:
		r = 2
	}
	return cnt*100 + r
}

func commaOkRecvCall() int {
	cnt = 0
	r := 0
	select {
	case v, ok := <-fch(true, 1):
		if ok {
			r = v
		}
	default:
		r = 9
	}
	return cnt*100 + r
}

func nilChanCall() int {
	cnt = 0
	r := 0
	select {
	case <-fnil():
		r = 1
	case fnil() <- fv():
		r = 2
	default:
		r = 3
	}
	return cnt*100 + r
}

func sendCallsSelected() int {
	cnt = 0
	ch := fch(false, 1)
	cnt = 0
	r := 0
	select {
	case ch <- fv():
		r = <-ch
	default:
		r = 9
	}
	return cnt*100 + r
}

func fchc(cap int) chan int { cnt++; return make(chan int, cap) }

func selGeneric[T any](mk func() chan T, v func() T) int {
	select {
	case mk() <- v():
		return 1
	case <-mk():
		return 2
	default:
		return 3
	}
}

func closureSelect() int {
	cnt = 0
	r := 0
	inner := func() {
		select {
		case fchc(0) <- fv():
			r = 1
		case <-fchc(0):
			r = 2
		default:
			r = 3
		}
	}
	inner()
	return cnt*100 + r
}

func genericSelect() int {
	cnt = 0
	r := selGeneric(func() chan int { return fchc(0) }, fv)
	s := selGeneric(func() chan string { cnt++; return make(chan string, 1) }, func() string { cnt++; return "x" })
	return cnt*100 + r*10 + s
}

func main() {
	sendCalls()
	recvChanCallNotReady()
	recvTargetIndexCallSelected()
	recvTargetIndexCallNotSelected()
	threeClauseCalls()
	loopEntries()
	sendValueCallNotSelected()
	commaOkRecvCall()
	nilChanCall()
	sendCallsSelected()
	closureSelect()
	genericSelect()
}
