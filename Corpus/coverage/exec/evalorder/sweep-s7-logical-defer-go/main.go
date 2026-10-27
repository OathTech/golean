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
// BUG-278 (found by this sweep, born RED/differential): BUG-113's wrong order — a binary logical
// operation evaluated AFTER a lexically later call that mutates its right operand — at the
// arguments of a `defer` and of a `go` statement (spec: the function value and parameters
// are evaluated as usual). The unseq classifier admits neither statement form (`statement
// form outside the pilot grammar`), so the legacy ANF hoist lifts the later call to a temp
// before the statement and the `||` reads the post-call operand: the machine true, gc false.

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

func h7() string {
	out := ""
	b := false
	change := func() int { b = true; return 0 }
	f := func(x bool, n int) { out = show(x, n) }
	func() {
		defer f(left || b, change())
	}()
	return out
}

func h8() string {
	out := ""
	done := make(chan int)
	b := false
	change := func() int { b = true; return 0 }
	f := func(x bool, n int) { out = show(x, n); done <- 1 }
	go f(left || b, change())
	<-done
	return out
}

func main() {
	h7()
	h8()
}
