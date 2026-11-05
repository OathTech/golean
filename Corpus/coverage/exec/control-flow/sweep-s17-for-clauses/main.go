package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (lowering coverage
// holes: statement and expression forms; plan §4; the matrix on BUG-172's
// line): the three-clause `for` at every clause shape spec#For_statements
// admits — empty parts in every combination, an init or post that is an
// IncDec, a send, a receive, a call, a compound assignment, a tuple define
// or a parallel assignment, and a condition that is a receive, a func
// literal call, a type assertion or a map read. Expected = gc go1.26.5.

var calls int

func bump() { calls++ }

func two() (int, int) { return 1, 4 }

func next(i int) int { return i + 1 }

func lt(a, b int) bool { return a < b }

// A19.2
func allEmpty() int {
	i := 0
	for ; ; {
		i++
		if i == 3 {
			break
		}
	}
	return i // 3
}

func condOnlySemis() int {
	i := 0
	for ; i < 3; {
		i++
	}
	return i // 3
}

func noCond() int {
	for i := 0; ; i++ {
		if i == 4 {
			return i // 4
		}
	}
}

func initLessPost() int {
	i := 0
	for ; ; i++ {
		if i == 2 {
			break
		}
	}
	return i // 2
}

func noPost() int {
	for i := 0; i < 3; {
		i++
		if i == 3 {
			return i // 3
		}
	}
	return -1
}

func assignInit() int {
	var i int
	for i = 1; i < 4; i++ {
	}
	return i // 4
}

// A19.3
func initIncdec() int {
	i, n := 0, 0
	for i++; i < 3; i++ {
		n++
	}
	return i*10 + n // 32
}

func initSend() int {
	ch := make(chan int, 1)
	x := 0
	for ch <- 7; len(ch) > 0; {
		x = <-ch
	}
	return x // 7
}

func initRecv() int {
	ch := make(chan int, 1)
	ch <- 9
	i := 0
	for <-ch; i < 2; i++ {
	}
	return i*10 + len(ch) // 20
}

func initCall() int {
	calls = 0
	i := 0
	for bump(); i < 3; i++ {
	}
	return calls*10 + i // 13
}

func initCompound() int {
	i, n := 1, 0
	for i += 2; i < 10; i += 3 {
		n++
	}
	return i*10 + n // 123
}

func initTupleCall() int {
	n := 0
	for a, b := two(); a < b; a++ {
		n++
	}
	return n // 3
}

func initTwoVars() int {
	n := 0
	for i, j := 0, 10; i < j; i, j = i+1, j-1 {
		n++
	}
	return n // 5
}

// A19.4
func postSend() int {
	ch := make(chan int, 10)
	for i := 0; i < 3; ch <- i {
		i++
	}
	sum := 0
	for len(ch) > 0 {
		sum += <-ch
	}
	return sum // 1+2+3 = 6
}

func postRecv() int {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	i := 0
	for ; len(ch) > 0; <-ch {
		i++
	}
	return i // 3
}

func postCall() int {
	calls = 0
	for i := 0; i < 3; bump() {
		i++
	}
	return calls // 3
}

func postMultiAssign() int {
	n := 0
	for i, j := 0, 10; i < j; i, j = i+2, j-1 {
		n++
	}
	return n // (0,10) (2,9) (4,8) (6,7) -> 4
}

func postCompound() int {
	n := 0
	for i := 0; i < 10; i += 3 {
		n++
	}
	return n // 4
}

func postCallAssign() int {
	n := 0
	for i := 0; i < 3; i = next(i) {
		n++
	}
	return n // 3
}

// A19.5
func condRecv() int {
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

func condFunclit() int {
	i, n := 0, 0
	for func() bool { i++; return i < 4 }() {
		n++
	}
	return n // 3
}

func condAssert() int {
	var x any = true
	n := 0
	for x.(bool) {
		n++
		x = false
	}
	return n // 1
}

func condMapRead() int {
	m := map[int]bool{0: true, 1: true}
	i := 0
	for m[i] {
		i++
	}
	return i // 2
}

// A19.10
func loopG[T int | int64](n T) T {
	var s T
	for i := T(0); i < n; i++ {
		s += i
	}
	return s
}

func forInGeneric() int {
	return int(loopG(5)) + int(loopG(int64(3))) // 10 + 3 = 13
}

// A19.11
func condTrueLiteral() int {
	i := 0
	for true {
		i++
		if i == 3 {
			break
		}
	}
	return i // 3
}

func condFalseLiteral() int {
	i := 0
	for false {
		i++
	}
	return i // 0
}

func main() {
	println(allEmpty(), condOnlySemis(), noCond(), initLessPost(), noPost(), assignInit(),
		initIncdec(), initSend(), initRecv(), initCall(), initCompound(), initTupleCall(), initTwoVars(),
		postSend(), postRecv(), postCall(), postMultiAssign(), postCompound(), postCallAssign(),
		condRecv(), condFunclit(), condAssert(), condMapRead(), forInGeneric(), condTrueLiteral(), condFalseLiteral())
}
