package main

// S6 sweep, group T: `return e1, .., en` assigns to the result variables LIKE
// AN ASSIGNMENT (spec#Return_statements): every operand evaluates, left to
// right, before any result is stored — a later operand's panic leaves every
// result at its prior value, visible to a deferred closure (BUG-075's
// shape at the other routes: named results observed in the defer, three
// results, a forwarded call, an interface result slot, a closure, a generic).

func tWit(n int) int { println("wit", n); return n }
func tBoom() int     { panic("boom") }

// T.2: named results observed INSIDE the deferred closure after operand 2's
// nil dereference: both still zero.
func t2Named() (a bool, b int) {
	defer func() {
		recover()
		println("a", a, "b", b)
	}()
	var p *int
	return true, *p
}

func tNamedObservedInDefer() int {
	a, b := t2Named()
	if a {
		return 1
	}
	return b
}

// T.3: operand 1's call runs, operand 2's call panics — no result stored.
func t3() (a int, b int) {
	defer func() { recover() }()
	return tWit(1), tBoom()
}

func tCallEffectsThenPanic() int {
	a, b := t3()
	return a*10 + b
}

// T.4: three named results, the MIDDLE operand panics — none stored.
func t4() (a int, b int, c int) {
	defer func() {
		recover()
		println("abc", a, b, c)
	}()
	var p *int
	return 1, *p, 3
}

func tThreeMiddlePanic() int {
	a, b, c := t4()
	return a*100 + b*10 + c
}

// T.5: `return f()` tuple-forwarded into named results, then the deferred
// closure modifies them.
func tPair() (int, int) { return 3, 4 }
func t5() (a, b int) {
	defer func() { a *= 10 }()
	return tPair()
}

func tForwardThenDefer() int {
	a, b := t5()
	return a*10 + b
}

// T.8: an interface-typed result slot (the boxing wrap on the temp) beside a
// panicking operand: the slot stays nil.
func t8() (any, int) {
	defer func() { recover() }()
	var p *int
	return 1, *p
}

func tIfaceResultUnset() int {
	r, n := t8()
	if r == nil {
		return 10 + n
	}
	return 99
}

// T.9: a function literal with named results.
func tClosureNamedResults() int {
	f := func() (a bool, b int) {
		defer func() { recover() }()
		var p *int
		return true, *p
	}
	a, b := f()
	if a {
		return 1
	}
	return b
}

// T.10: a generic function.
func tGen[T any](v T, p *int) (a T, b int) {
	defer func() { recover() }()
	return v, *p
}

func tGenericTwoPhase() int {
	a, b := tGen(7, nil)
	return a*10 + b
}

// T.11: the results are stored before the deferred closure mutates the local
// they came from.
func t11() (int, int) {
	i := 1
	defer func() { i = 9 }()
	return i, i
}

func tResultsSnapshotBeforeDefer() int {
	a, b := t11()
	return a*10 + b
}

// T.12: a receive as operand 1 (an ordered event) and a panicking call as
// operand 2: the channel is drained, no result stored.
func t12(ch chan int) (a int, b int) {
	defer func() { recover() }()
	return <-ch, tBoom()
}

func tRecvThenCallPanic() int {
	ch := make(chan int, 1)
	ch <- 7
	a, b := t12(ch)
	return a*100 + b*10 + len(ch)
}

// T.13: named results already holding values, operand 2 panics — the prior
// values survive (the two-phase store never began).
func t13() (a int, b int) {
	a, b = 5, 6
	defer func() { recover() }()
	var p *int
	return 1, *p
}

func tPriorNamedValuesSurvive() int {
	a, b := t13()
	return a*10 + b
}

func main() {
	tNamedObservedInDefer()
}
