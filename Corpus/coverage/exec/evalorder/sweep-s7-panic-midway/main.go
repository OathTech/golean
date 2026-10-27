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
// A PANIC IN THE MIDDLE of an ordered sequence — which events ran before it: in a keyed literal,
// a binary chain, an if condition's `&&`, after a receive, a runtime panic (nil map write)
// inside an ordered call, and at a defer statement's arguments (the deferred call never
// registers). All born green.

type V struct {
	x string
	y string
	z string
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

func k2() (out string) {
	log := ""
	defer func() {
		if r := recover(); r != nil {
			out = log + "recovered:" + r.(string)
		}
	}()
	a := func() string { log += "a "; return "A" }
	boom := func() string { log += "boom "; panic("boom") }
	c := func() string { log += "c "; return "C" }
	v := V{x: a(), y: boom(), z: c()}
	return log + v.x
}

func k3() (out string) {
	log := ""
	defer func() {
		if r := recover(); r != nil {
			out = log + "recovered:" + r.(string)
		}
	}()
	a := func() string { log += "a "; return "A" }
	boom := func() string { log += "boom "; panic("boom") }
	c := func() string { log += "c "; return "C" }
	r := a() + boom() + c()
	return log + r
}

func k5() (out string) {
	log := ""
	defer func() {
		if r := recover(); r != nil {
			out = log + "recovered:" + r.(string)
		}
	}()
	a := func() bool { log += "a "; return true }
	boom := func() bool { log += "boom "; panic("boom") }
	if a() && boom() {
		log += "then "
	}
	return log
}

func k6() (out string) {
	log := ""
	defer func() {
		if r := recover(); r != nil {
			out = log + "recovered:" + r.(string)
		}
	}()
	ch := make(chan string, 2)
	ch <- "r1"
	boom := func() string {
		log += "boom(" + itoa(len(ch)) + ") "
		panic("boom")
	}
	f := func(x, y string) { log += "f " }
	f(<-ch, boom())
	return log
}

func k7() (out string) {
	log := ""
	defer func() {
		if r := recover(); r != nil {
			out = log + "recovered"
		}
	}()
	a := func() string { log += "a "; return "A" }
	nilmap := func() string {
		log += "nilmap "
		var m map[string]int
		m["x"] = 1
		return "N"
	}
	c := func() string { log += "c "; return "C" }
	f := func(x, y, z string) { log += "f " }
	f(a(), nilmap(), c())
	return log
}

func k8() (out string) {
	log := ""
	defer func() {
		if r := recover(); r != nil {
			out = log + "recovered:" + r.(string)
		}
	}()
	a := func() string { log += "a "; return "A" }
	boom := func() string { log += "boom "; panic("boom") }
	f := func(x, y string) { log += "f(" + x + "," + y + ") " }
	func() {
		defer f(a(), boom())
		log += "body "
	}()
	return log
}

func main() {
	k2()
	k3()
	k5()
	k6()
	k7()
	k8()
}
