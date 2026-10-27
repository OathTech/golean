package main

// Defect-neighbourhood campaign, shape S7 (ordered events reordered by the hoist),
// lane sweep/s7-hoist-order, 2026-10-27: plan docs/2026-10-27_defect-neighbourhood-campaign.md
// §4 ([USER]-approved 2026-10-27); the matrix is on the member entries' Neighbourhood lines
// in docs/BUGS.md (BUG-113/062/058/026/023/145/144). spec#Order_of_evaluation: function
// calls, method calls, receive operations and binary logical operations are evaluated in
// lexical left-to-right order. Each subject returns its event log (a closure appends the
// name of each event as it runs); where a receive is in play its VALUE attests its order
// against a call that non-blockingly swaps the buffered element ("r1" if the receive came
// first, "after" if the call did).
//
// STATEMENT HEADERS: if / for / switch conditions, else-if chains and for-post statements
// (BUG-144, BUG-058, BUG-026's positions) with receives, calls and short-circuits — a chain
// stops at the first match, a post runs after each body, case expressions go top to bottom,
// an init runs before its condition, inside a generic body, a func literal and a goto body.
// All born green.

func genIf[T any](_ T) string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return false }
	if a() && b() {
		log += "then "
	} else {
		log += "else "
	}
	return log
}

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	return s
}

var glog = ""

func ga() bool { glog += "a "; return false }

func gb() bool { glog += "b "; return true }

func gc() bool { glog += "c "; return true }

func f1() string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return false }
	if a() && b() {
		log += "then "
	} else {
		log += "else "
	}
	return log
}

func f2() string {
	log := ""
	ch := make(chan int, 2)
	ch <- 1
	f := func() bool {
		log += "f "
		select {
		case <-ch:
			ch <- 2
		default:
		}
		return true
	}
	if <-ch == 1 && f() {
		log += "then "
	} else {
		log += "else "
	}
	return log
}

func f4() string {
	log := ""
	n := 0
	a := func() bool { log += "a "; n++; return n < 3 }
	b := func() bool { log += "b "; return true }
	for a() && b() {
		log += "body "
	}
	return log
}

func f5() string {
	log := ""
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 0
	f := func() bool { log += "f "; return true }
	for <-ch > 0 && f() {
		log += "body "
	}
	return log
}

func f6() string {
	log := ""
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 0
	f := func(i int) bool { log += "f(" + itoa(i) + ") "; return i > 0 }
	for i := <-ch; f(i); i = <-ch {
		log += "body "
	}
	return log
}

func f7() string {
	log := ""
	ch := make(chan int, 1)
	ch <- 2
	f := func() int { log += "f "; return 1 }
	g := func() int { log += "g "; return 2 }
	h := func() int { log += "h "; return 3 }
	switch <-ch {
	case f():
		log += "F "
	case g():
		log += "G "
	case h():
		log += "H "
	}
	return log
}

func f8() string {
	log := ""
	ch := make(chan int, 1)
	ch <- 2
	f := func() int { log += "f "; return 2 }
	g := func() int { log += "g "; return 2 }
	switch {
	case <-ch == 1:
		log += "R "
	case f() == 2:
		log += "F "
	case g() == 2:
		log += "G "
	}
	return log
}

func f10() string {
	log := ""
	ch := make(chan int, 1)
	ch <- 5
	f := func(x int) int { log += "f(" + itoa(x) + ") "; return x }
	g := func() int { log += "g "; return 5 }
	switch x := <-ch; f(x) {
	case g():
		log += "G "
	default:
		log += "D "
	}
	return log
}

func f13() string {
	log := ""
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	if <-ch == 2 {
		log += "A "
	} else if <-ch == 2 {
		log += "B "
	} else if <-ch == 2 {
		log += "C "
	}
	return log + itoa(len(ch))
}

func f14() string {
	log := ""
	a := func() bool { log += "a "; return false }
	b := func() bool { log += "b "; return true }
	c := func() bool { log += "c "; return true }
	d := func() bool { log += "d "; return true }
	if a() {
		log += "A "
	} else if b() && c() {
		log += "BC "
	} else if d() {
		log += "D "
	}
	return log
}

func f15() string {
	log := ""
	a := func() bool { log += "a "; return false }
	d := func() int { log += "d "; return 1 }
	e := func() int { log += "e "; return 2 }
	if a() {
		log += "A "
	} else if x := d(); x > 0 {
		log += "D" + itoa(x) + " "
	} else if y := e(); y > 0 {
		log += "E" + itoa(y) + " "
	}
	return log
}

func f16() string {
	log := ""
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 0
	i := 7
	for ; i > 0; i = <-ch {
		log += "body(" + itoa(i) + ") "
	}
	return log
}

func f19g() string { return genIf(0) }

func f19l() string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return false }
	return func() string {
		if a() && b() {
			log += "then "
		} else {
			log += "else "
		}
		return log
	}()
}

func f21() string {
	log := ""
	a := func() bool { log += "a "; return false }
	b := func() bool { log += "b "; return false }
	if x := a(); b() || x {
		log += "then "
	} else {
		log += "else "
	}
	return log
}

func f22() string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return false }
	c := func() bool { log += "c "; return true }
	switch {
	case a() && b():
		log += "AB "
	case c():
		log += "C "
	}
	return log
}

func f23() string {
	log := ""
	cond := func(i int) bool { log += "cond(" + itoa(i) + ") "; return i < 2 }
	more := func() bool { log += "more "; return true }
	next := func(i int) int { log += "next "; return i + 1 }
	for i := 0; cond(i) && more(); i = next(i) {
		log += "body "
	}
	return log
}

func f26g() string {
	glog = ""
	i := 0
loop:
	if ga() {
		glog += "A "
	} else if gb() {
		glog += "B "
	} else if gc() {
		glog += "C "
	}
	i++
	if i < 2 {
		goto loop
	}
	return glog
}

func p1() string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return true }
	c := func() int { log += "c "; return 10 }
	x := func() int {
		if a() && b() {
			return 1
		}
		return 0
	}() + c()
	return log + itoa(x)
}

func p2() string {
	log := ""
	a := func() bool { log += "a "; return false }
	b := func() bool { log += "b "; return true }
	c := func() bool { log += "c "; return true }
	d := func() bool { log += "d "; return true }
	if a() {
		log += "A "
	} else if func() bool { return b() && c() }() {
		log += "BC "
	} else if d() {
		log += "D "
	}
	return log
}

func p3() string {
	log := ""
	ch := make(chan int, 1)
	ch <- 3
	f := func() int { log += "f "; return 3 }
	switch f() {
	case <-ch:
		log += "R "
	default:
		log += "D "
	}
	return log
}

func f13s() string {
	ch := make(chan int, 3)
	ch <- 1
	ch <- 2
	ch <- 3
	out := ""
	switch 2 {
	case <-ch:
		out = "A"
	case <-ch:
		out = "B"
	case <-ch:
		out = "C"
	}
	return out + itoa(len(ch))
}

func main() {
	f1()
	f2()
	f4()
	f5()
	f6()
	f7()
	f8()
	f10()
	f13()
	f14()
	f15()
	f16()
	f19g()
	f19l()
	f21()
	f22()
	f23()
	f26g()
	p1()
	p2()
	p3()
	f13s()
}
