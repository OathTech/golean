package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the blank identifier
// binds nothing but its initializer runs (spec#Blank_identifier) — `var _ =
// f()` in a function body, blank parameters, a blank named result under a
// bare and an explicit return, an all-blank range clause, receive forms with
// a blank value or ok, a select case assigning to blank, a blank receiver;
// and a variable used only inside a never-called closure (a legal use).
// Expected = gc go1.26.5.

var calls = 0

func bump() int { calls++; return calls }

type R struct{ v int }

func (_ R) M() int { return 42 }

// K2
func varBlankEvaluates() int {
	var _ = bump()
	var _ int = bump()
	return calls // 2
}

func takesBlank(_ int, y int, _ string) int { return y * 3 }

// K5
func blankParams() int { return takesBlank(1, 2, "x") } // 6

// K6
func blankResultBare() (_ int, n int) {
	n = 4
	return // 0, 4
}

func blankResultExplicit() (_ int, n int) {
	return 9, 8
}

// K7
func rangeAllBlank() int {
	c := 0
	for _, _ = range []int{1, 2, 3} {
		c++
	}
	return c // 3
}

// K10
func recvBlanks() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	_, ok := <-ch
	v, _ := <-ch
	if ok {
		return v * 10 // 20
	}
	return -1
}

// K11
func selectBlankRecv() int {
	ch := make(chan int, 1)
	ch <- 3
	select {
	case _ = <-ch:
		return 1
	}
}

// K14
func blankReceiver() int { return R{1}.M() } // 42

// L3: x++ counts as a use for gc (the negative cell of the matrix turned out legal).
func incdecIsUse() int {
	x := 0
	x++
	return 1
}

// L9: a for-clause variable only incremented is legal too.
func forInitIncrOnly() int {
	for i := 0; ; i++ {
		break
	}
	return 1
}

// L5
func usedOnlyInClosure() int {
	x := 1
	f := func() int { return x }
	_ = f
	return 2
}

func main() {
	println(varBlankEvaluates(), blankParams(), rangeAllBlank(), recvBlanks(), selectBlankRecv(), blankReceiver(),
		usedOnlyInClosure(), incdecIsUse(), forInitIncrOnly())
	println(blankResultBare())
	println(blankResultExplicit())
}
