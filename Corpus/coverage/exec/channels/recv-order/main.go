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
