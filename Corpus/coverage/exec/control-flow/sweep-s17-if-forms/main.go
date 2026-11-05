package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-024's line): if statements at the init-statement and condition
// shapes the corpus did not hold — an init that is an IncDec, a send, a
// receive, a call, a compound or parallel assignment, or a call-assign; a
// condition that is a receive, an assertion, a func literal call, a map
// read, an index, a conversion or a method call on a literal; empty
// branches; constant conditions; an if in a generic body.
// Expected = gc go1.26.5.

var calls int

func bump() { calls++ }

func next(i int) int { return i + 1 }

type tok struct{}

func (tok) ok() bool { return true }

type flag bool

// A15.2
func initIncdec() int {
	i, r := 0, 0
	if i++; i == 1 {
		r = 1
	}
	return r*10 + i // 11
}

func initSend() int {
	ch := make(chan int, 1)
	r := 0
	if ch <- 2; len(ch) == 1 {
		r = <-ch
	}
	return r // 2
}

func initRecv() int {
	ch := make(chan int, 1)
	ch <- 3
	r := 0
	if <-ch; len(ch) == 0 {
		r = 1
	}
	return r // 1
}

func initCall() int {
	calls = 0
	r := 0
	if bump(); calls == 1 {
		r = 7
	}
	return r // 7
}

func initCompound() int {
	i, r := 1, 0
	if i += 2; i == 3 {
		r = 1
	}
	return r*10 + i // 13
}

func initMultiAssign() int {
	var a, b int
	r := 0
	if a, b = 1, 2; a < b {
		r = a + b
	}
	return r // 3
}

func initCallAssign() int {
	var x int
	r := 0
	if x = next(1); x == 2 {
		r = x
	}
	return r // 2
}

// A15.3
func condRecv() int {
	ch := make(chan bool, 1)
	ch <- true
	r := 0
	if <-ch {
		r = 1
	}
	return r // 1
}

func condAssert() int {
	var x any = true
	r := 0
	if x.(bool) {
		r = 1
	}
	return r // 1
}

func condFunclit() int {
	r := 0
	if func() bool { return true }() {
		r = 1
	}
	return r // 1
}

func condMapRead() int {
	m := map[string]bool{"a": true}
	r := 0
	if m["a"] {
		r = 1
	}
	if m["b"] {
		r += 10
	}
	return r // 1
}

func condIndex() int {
	bs := []bool{false, true}
	r := 0
	if bs[1] {
		r = 1
	}
	return r // 1
}

func condConversion() int {
	var f flag = true
	r := 0
	if bool(f) {
		r = 1
	}
	return r // 1
}

func condMethodCall() int {
	r := 0
	if (tok{}).ok() {
		r = 1
	}
	return r // 1
}

// A15.4
func emptyThen(x int) int {
	if x > 0 {
	}
	return x + 1
}

func emptyElse(x int) int {
	r := 0
	if x > 0 {
		r = 1
	} else {
	}
	return r
}

func noFinalElse(x int) int {
	r := 0
	if x == 0 {
		r = 1
	} else if x == 1 {
		r = 2
	}
	return r
}

// A15.5
func constFalseCond() int {
	r := 0
	if false {
		r = 1
	}
	return r // 0
}

func constTrueCond() int {
	r := 0
	if true {
		r = 1
	} else {
		r = 2
	}
	return r // 1
}

// A15.7
func absG[T int | float64](x T) T {
	if x < 0 {
		return -x
	}
	return x
}

func ifInGeneric() int {
	return absG(-3) + int(absG(2.5)*2) // 3 + 5 = 8
}

func main() {
	println(initIncdec(), initSend(), initRecv(), initCall(), initCompound(), initMultiAssign(), initCallAssign(),
		condRecv(), condAssert(), condFunclit(), condMapRead(), condIndex(), condConversion(), condMethodCall(),
		emptyThen(1), emptyElse(1), emptyElse(0), noFinalElse(0), noFinalElse(1), noFinalElse(2),
		constFalseCond(), constTrueCond(), ifInGeneric())
}
