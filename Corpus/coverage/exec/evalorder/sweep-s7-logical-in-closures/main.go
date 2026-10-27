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
// BUG-276 (found by this sweep, born RED/differential): BUG-113's wrong order — a binary logical
// operation evaluated AFTER a lexically later call that mutates its right operand — in EVERY
// func-literal body. The unseq classifier declines a lifted body's sweep (`captured variable
// read through its pointer parameter (lifted body)`, `call through a captured func variable
// (lifted body)`), so the sweep takes the legacy ANF hoist, which lifts the later call to a
// temp BEFORE the statement and leaves the `||`/`&&` inline: the machine reads the post-call
// operand (true), gc reads it before the call (false). The same statement at the top level of
// a function is green (evalorder/sweep-s7-binary-operands, -returns).

var left = false

func show(x bool, n int) string {
	if x {
		return "true " + itoa(n)
	}
	return "false " + itoa(n)
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

func d22dInner() (out string) {
	b := false
	change := func() int { b = true; return 0 }
	defer func() { out = show(left || b, change()) }()
	return ""
}

func d22() string {
	b := false
	change := func() int { b = true; return 0 }
	return func() string { return show(left || b, change()) }()
}

func d22s() string {
	xs := []bool{false}
	b := false
	change := func() int { b = true; return 0 }
	return func() string { return show(xs[0] || b, change()) }()
}

func d22a() string {
	l := true
	b := false
	change := func() int { b = true; return 0 }
	return func() string { return show(l && b, change()) }()
}

func d22c() string {
	out := ""
	b := false
	change := func() int { b = true; return 0 }
	sink := func(x bool, n int) { out = show(x, n) }
	func() { sink(left || b, change()) }()
	return out
}

func d22v() string {
	b := false
	change := func() int { b = true; return 0 }
	g := func() string { return show(left || b, change()) }
	return g()
}

func d22d() string { return d22dInner() }

func d18l() string {
	str := "zzz"
	b := false
	change := func() int { b = true; return 0 }
	return func() string { return show(str[0] == 'a' || b, change()) }()
}

func d26l() string {
	ch := make(chan int, 1)
	ch <- 7
	return func() string { return show(left || len(ch) > 0, <-ch) }()
}

func b3() string {
	b := false
	change := func() int { b = true; return 0 }
	g := func() (bool, int) { return left || b, change() }
	x, y := g()
	if x {
		return "true " + itoa(y)
	}
	return "false " + itoa(y)
}

func main() {
	d22()
	d22s()
	d22a()
	d22c()
	d22v()
	d22d()
	d18l()
	d26l()
	b3()
}
