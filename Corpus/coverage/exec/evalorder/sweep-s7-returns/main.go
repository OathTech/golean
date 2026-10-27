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
// RETURN OPERANDS: two calls, a receive before and after a call, a call plus a receive in one
// operand, a call then a panicking call, and a binary logical operation before a later call
// in a top-level function's return (the same return inside a func literal is the red row
// evalorder/sweep-s7-logical-in-closures/or-in-closure-return, BUG-276). All born green.

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

var left = false

func show(x bool, n int) string {
	if x {
		return "true " + itoa(n)
	}
	return "false " + itoa(n)
}

func b3top() (bool, int) {
	b := false
	change := func() int { b = true; return 0 }
	return left || b, change()
}

func b1() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	g := func() (string, string) { return a(), b() }
	x, y := g()
	return log + x + y
}

func b2() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	a := func() string {
		log += "a "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "A"
	}
	g := func() (string, string) { return <-ch, a() }
	x, y := g()
	return log + x + y
}

func b2r() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	a := func() string {
		log += "a "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "A"
	}
	g := func() (string, string) { return a(), <-ch }
	x, y := g()
	return log + x + y
}

func b4() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	a := func() string {
		log += "a "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "A"
	}
	g := func() string { return a() + <-ch }
	v := g()
	return log + v
}

func b6() (log string) {
	defer func() {
		if r := recover(); r != nil {
			log += "recovered:" + r.(string)
		}
	}()
	a := func() string { log += "a "; return "A" }
	boom := func() string { log += "boom "; panic("boom") }
	g := func() (string, string) { return a(), boom() }
	x, y := g()
	return log + x + y
}

func b3t() string { x, n := b3top(); return show(x, n) }

func main() {
	b1()
	b2()
	b2r()
	b4()
	b6()
	b3t()
}
