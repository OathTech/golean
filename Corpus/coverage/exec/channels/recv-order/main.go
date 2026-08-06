package main

// Audit pins (channels-arc-s1 audit S2/S9): spec §Order of evaluation —
// "all function calls, method calls, receive operations, and binary
// logical operations are evaluated in lexical left-to-right order" — so
// an inline len(ch) lexically LEFT of a receive reads the pre-receive
// length in every operand-list position, not just binary operands.
// Buffer holds {5, 6}: len is 2 before the receive, the receive yields
// 5 — every subject observes 205 (or the pair (2, 5)).

func orderTwo(a, b int) int { return a*100 + b }

func recvOrderCallArg() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	return orderTwo(len(ch), <-ch)
}

func recvOrderReturnList() (int, int) {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	return len(ch), <-ch
}

func recvOrderCompositeLit() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	xs := []int{len(ch), <-ch}
	return xs[0]*100 + xs[1]
}

func recvOrderMultiAssign() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	a, b := len(ch), <-ch
	return a*100 + b
}

func recvOrderBinary() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	return len(ch)*100 + <-ch
}

func main() {
	recvOrderCallArg()
}

// Delta-review pins (audit-response delta D2): the ordered len/cap
// evaluation must hold in STATEMENT-emission positions too — for-init,
// for-cond (re-evaluated per iteration), else-if chains, and switch
// case expressions.

func recvOrderForInit() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	for v := len(ch)*100 + <-ch; ; {
		return v
	}
}

func recvOrderForCond() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	n := 0
	for len(ch)*100+<-ch == 205 {
		n++
		if n == 2 {
			break
		}
	}
	return n
}

func recvOrderElseIf() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	if false {
		return 9
	} else if len(ch)*100+<-ch == 205 {
		return 2
	}
	return 3
}

func recvOrderSwitchCase() int {
	ch := make(chan int, 3)
	ch <- 5
	ch <- 6
	switch 205 {
	case len(ch)*100 + <-ch:
		return 1
	}
	return 2
}

// Convergence-round pin (BUG-026 claim correction): the len/cap
// receive-ordering hoist is only order-transparent when its OPERAND
// cannot panic — hoisting drags the operand's panic ahead of
// spec-unordered panics to its left. gc realizes left-to-right here:
// the type-assertion panic fires, not the index panic, and a DEAD
// receive elsewhere in the function must not change that.
func recvOrderDeadRecvLenOperand(j int) int {
	var iv interface{} = "s"
	b := make([][]int, 0)
	if j < -100 {
		ch := make(chan int, 1)
		ch <- 1
		return <-ch
	}
	return iv.(int) + len(b[j])
}
