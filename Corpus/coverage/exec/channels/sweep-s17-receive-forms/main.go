package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-024's line): the receive operator in expression positions the
// corpus did not hold — a receive of a receive, a field / dereference /
// comparison / len of a received value, a parenthesised and a call-result
// channel operand; a receive as a switch tag, an if condition, a for
// condition, a return operand, a defer and a go argument, a case
// expression, a map key, a composite-literal element; a receive inside a
// closure. Expected = gc go1.26.5.

var calls int

type pt struct{ x, y int }

func take(x int) { calls += x }

func send(ch chan int, v int) { ch <- v }

func mkCh(v int) chan int {
	ch := make(chan int, 1)
	ch <- v
	return ch
}

// B14.2
func recvOfRecv() int {
	chch := make(chan chan int, 1)
	ch := make(chan int, 1)
	ch <- 3
	chch <- ch
	return <-<-chch // 3
}

func recvField() int {
	ch := make(chan pt, 1)
	ch <- pt{4, 5}
	return (<-ch).x*10 + 5 // 45
}

func recvDeref() int {
	x := 6
	pch := make(chan *int, 1)
	pch <- &x
	return *<-pch // 6
}

func recvCompare() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	r := 0
	if <-ch == 1 {
		r = 1
	}
	if <-ch != 1 {
		r += 10
	}
	return r // 11
}

func recvLen() int {
	chs := make(chan []int, 1)
	chs <- []int{1, 2, 3}
	return len(<-chs) // 3
}

func recvParenChan() int {
	ch := make(chan int, 1)
	ch <- 7
	return <-(ch) // 7
}

func recvCallChan() int {
	return <-mkCh(8) // 8
}

// B14.3
func recvSwitchTag() int {
	ch := make(chan int, 1)
	ch <- 2
	r := 0
	switch <-ch {
	case 1:
		r = 1
	case 2:
		r = 2
	}
	return r // 2
}

func recvIfCond() int {
	ch := make(chan bool, 1)
	ch <- true
	r := 0
	if <-ch {
		r = 1
	}
	return r // 1
}

func recvForCond() int {
	ch := make(chan bool, 3)
	ch <- true
	ch <- true
	ch <- false
	n := 0
	for <-ch {
		n++
	}
	return n // 2
}

func recvReturn() int {
	ch := make(chan int, 1)
	ch <- 9
	return <-ch // 9
}

func recvDeferArg() int {
	calls = 0
	ch := make(chan int, 2)
	ch <- 10
	ch <- 20
	func() {
		defer take(<-ch) // 10 received at the defer statement
		calls += <-ch    // 20
	}()
	return calls // 30
}

func recvGoArg() int {
	ch := make(chan int, 1)
	ch <- 11
	out := make(chan int)
	go send(out, <-ch)
	return <-out // 11
}

func recvCaseExpr() int {
	ch := make(chan int, 1)
	ch <- 12
	x := 12
	r := 0
	switch x {
	case <-ch:
		r = 1
	}
	return r // 1
}

func recvMapKey() int {
	ch := make(chan string, 1)
	ch <- "a"
	m := map[string]int{"a": 13}
	return m[<-ch] // 13
}

func recvComplitElem() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 4
	p := pt{<-ch, <-ch}
	s := []int{<-mkCh(5)}
	return p.x*100 + p.y*10 + s[0] // 145
}

// B14.6
func recvInClosure() int {
	ch := make(chan int, 1)
	ch <- 15
	f := func() int { return <-ch + 1 }
	return f() // 16
}

func main() {
	println(recvOfRecv(), recvField(), recvDeref(), recvCompare(), recvLen(), recvParenChan(), recvCallChan(),
		recvSwitchTag(), recvIfCond(), recvForCond(), recvReturn(), recvDeferArg(), recvGoArg(), recvCaseExpr(),
		recvMapKey(), recvComplitElem(), recvInClosure())
}
