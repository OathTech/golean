package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-024's line): select statements at the receive-clause TARGET shapes
// spec#Select_statements admits — the assignment forms into existing
// variables with every blank combination, targets that are a field, an
// array element, a dereference, a map element or a slice element beside an
// ok flag — plus the degenerate bodies (empty, single receive, single
// send), a channel operand that is a slice element or a conversion, a
// return from a case, and a select in a closure and a generic body.
// Expected = gc go1.26.5.

type box struct{ v int }

func b2i(b bool) int {
	if b {
		return 1
	}
	return 0
}

// A18.2
func assignOne() int {
	ch := make(chan int, 1)
	ch <- 3
	var v int
	select {
	case v = <-ch:
	}
	return v // 3
}

func assignTwo() int {
	ch := make(chan int, 1)
	ch <- 4
	var v int
	var ok bool
	select {
	case v, ok = <-ch:
	}
	return v*10 + b2i(ok) // 41
}

func assignBlankValue(closed int) int {
	ch := make(chan int, 1)
	if closed != 0 {
		close(ch)
	} else {
		ch <- 1
	}
	var ok bool
	select {
	case _, ok = <-ch:
	}
	return b2i(ok)
}

func assignBlankBoth() int {
	ch := make(chan int, 1)
	ch <- 1
	r := 0
	select {
	case _, _ = <-ch:
		r = 1
	}
	return r*10 + len(ch) // 10
}

func defineBlankOk() int {
	ch := make(chan int, 1)
	ch <- 6
	r := 0
	select {
	case v, _ := <-ch:
		r = v
	}
	return r // 6
}

func defineBlankValue() int {
	ch := make(chan int, 1)
	ch <- 1
	r := 0
	select {
	case _, ok := <-ch:
		if ok {
			r = 1
		}
	}
	return r // 1
}

// A18.3
func targetField() int {
	ch := make(chan int, 1)
	ch <- 8
	var s box
	select {
	case s.v = <-ch:
	}
	return s.v // 8
}

func targetArrayElem() int {
	ch := make(chan int, 1)
	ch <- 9
	var a [3]int
	select {
	case a[1] = <-ch:
	}
	return a[0]*100 + a[1]*10 + a[2] // 90
}

func targetDeref() int {
	ch := make(chan int, 1)
	ch <- 11
	x := 0
	p := &x
	select {
	case *p = <-ch:
	}
	return x // 11
}

func targetMapElem() int {
	ch := make(chan int, 1)
	ch <- 12
	m := map[string]int{}
	select {
	case m["k"] = <-ch:
	}
	return m["k"] + len(m)*100 // 112
}

func targetSliceElemOk() int {
	ch := make(chan int, 1)
	ch <- 13
	sl := make([]int, 2)
	var ok bool
	select {
	case sl[0], ok = <-ch:
	}
	return sl[0]*10 + b2i(ok) // 131
}

// A18.4
func emptySelectDeadlock() int {
	select {}
}

func singleRecvCase() int {
	ch := make(chan int, 1)
	ch <- 14
	r := 0
	select {
	case v := <-ch:
		r = v
	}
	return r // 14
}

func singleSendCase() int {
	ch := make(chan int, 1)
	r := 0
	select {
	case ch <- 4:
		r = 1
	}
	return r*10 + <-ch // 14
}

// A18.5
func recvFromSliceElem() int {
	chs := []chan int{make(chan int, 1), make(chan int, 1)}
	chs[1] <- 15
	r := 0
	select {
	case v := <-chs[1]:
		r = v
	}
	return r // 15
}

// A18.6
func returnFromCase() int {
	ch := make(chan int, 1)
	ch <- 16
	for {
		select {
		case v := <-ch:
			return v * 2 // 32
		}
	}
}

// A18.7
func selectInClosure() int {
	ch := make(chan int, 1)
	ch <- 17
	f := func() int {
		select {
		case v := <-ch:
			return v
		default:
			return -1
		}
	}
	return f()*10 + f() // 170 - 1 = 169
}

func selG[T any](ch chan T, d T) T {
	select {
	case v := <-ch:
		return v
	default:
		return d
	}
}

func selectInGeneric() int {
	ch := make(chan int, 1)
	ch <- 18
	cs := make(chan string, 1)
	return selG(ch, -1)*100 + selG(ch, -1) + len(selG(cs, "xyz")) // 1800 - 1 + 3 = 1802
}

// A18.10
func recvConvertedChan() int {
	ch := make(chan int, 1)
	ch <- 19
	r := 0
	select {
	case v := <-(<-chan int)(ch):
		r = v
	}
	return r // 19
}

func main() {
	println(assignOne(), assignTwo(), assignBlankValue(0), assignBlankValue(1), assignBlankBoth(), defineBlankOk(),
		defineBlankValue(), targetField(), targetArrayElem(), targetDeref(), targetMapElem(), targetSliceElemOk(),
		singleRecvCase(), singleSendCase(), recvFromSliceElem(), returnFromCase(), selectInClosure(), selectInGeneric(),
		recvConvertedChan())
}
