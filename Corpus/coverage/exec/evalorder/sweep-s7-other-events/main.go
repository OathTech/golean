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
// OTHER ORDERED-EVENT KINDS beside a later call: a receive from a called channel, an assertion
// of a call, a string conversion of a call, len and cap of a call, an immediately invoked
// literal, append of a call with a spread call, min of calls, recover beside a call, a method
// value and a method expression over a called receiver, two interface dispatches, a promoted
// and a generic method, two receives in arguments and in a binary, len beside a receive and
// beside a call inside a func literal (BUG-023/BUG-062 in a lifted body), and a
// package-level initializer's call arguments. All born green.

type R struct{ log *string }

func (r R) M() string { *r.log += "M "; return "m" }

func (r R) A() string { *r.log += "A "; return "a" }

func (r R) B() string { *r.log += "B "; return "b" }

type I interface {
	A() string
	B() string
}

type E struct{ R }

type G[T any] struct{ log *string }

func (g G[T]) M() string { *g.log += "GM "; return "gm" }

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

func n12Inner() (out string) {
	log := ""
	f := func() int { log += "f "; return 1 }
	sink := func(r any, n int) {
		if r == nil {
			log += "sink(nil) "
		} else {
			log += "sink(" + r.(string) + ") "
		}
	}
	defer func() {
		sink(recover(), f())
		out = log
	}()
	panic("p")
}

var pkgLog = ""

func pa() string { pkgLog += "a "; return "A" }

func pb() string { pkgLog += "b "; return "B" }

func pf(x, y string) string { pkgLog += "f(" + x + "," + y + ") "; return x + y }

var pkgA = pf(pa(), pb())

func n1() string {
	log := ""
	ch := make(chan string, 1)
	ch <- "r1"
	chf := func() chan string { log += "chf "; return ch }
	g := func() string {
		log += "g "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "G"
	}
	sink := func(x, y string) { log += "sink(" + x + "," + y + ") " }
	sink(<-chf(), g())
	return log
}

func n2() string {
	log := ""
	getI := func() any { log += "getI "; return 7 }
	g := func() int { log += "g "; return 1 }
	sink := func(x, y int) { log += "sink " }
	sink(getI().(int), g())
	return log
}

func n4() string {
	log := ""
	bs := func() []byte { log += "bs "; return []byte("ab") }
	h := func() string { log += "h "; return "H" }
	v := string(bs()) + h()
	return log + v
}

func n5() string {
	log := ""
	f := func() []int { log += "f "; return []int{1, 2} }
	g := func() int { log += "g "; return 1 }
	sink := func(x, y int) { log += "sink " }
	sink(len(f()), g())
	return log
}

func n6() string {
	log := ""
	mk := func() []int { log += "mk "; return make([]int, 1, 5) }
	g := func() int { log += "g "; return 1 }
	sink := func(x, y int) { log += "sink " }
	sink(cap(mk()), g())
	return log
}

func n7() string {
	log := ""
	f := func() string { log += "f "; return "F" }
	r := func() string { log += "lit "; return "L" }() + f()
	return log + r
}

func n8() string {
	log := ""
	f := func() []string { log += "f "; return []string{"F"} }
	g := func() []string { log += "g "; return []string{"G1", "G2"} }
	s := append(f(), g()...)
	return log + itoa(len(s))
}

func n11() string {
	log := ""
	a := func() int { log += "a "; return 3 }
	b := func() int { log += "b "; return 2 }
	c := func() int { log += "c "; return 10 }
	v := min(a(), b()) + c()
	return log + itoa(v)
}

func n12() string { return n12Inner() }

func n13() string {
	log := ""
	r := func() R { log += "r "; return R{&log} }
	f := func() string { log += "f "; return "F" }
	use := func(mv func() string, y string) { log += "use " + mv() + y + " " }
	use(r().M, f())
	return log
}

func n14() string {
	log := ""
	r := func() R { log += "r "; return R{&log} }
	a := func() string { log += "a "; return "A" }
	sink := func(x, y string) { log += "sink " }
	sink(R.M(r()), a())
	return log
}

func n15() string {
	log := ""
	var i I = R{&log}
	v := i.A() + i.B()
	return v + " " + log
}

func n16() string {
	log := ""
	e := E{R{&log}}
	f := func() string { log += "f "; return "F" }
	v := e.M() + f()
	return v + " " + log
}

func n17() string {
	log := ""
	g := G[int]{&log}
	f := func() string { log += "f "; return "F" }
	v := g.M() + f()
	return v + " " + log
}

func n18() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	ch <- "r2"
	sink := func(x, y string) { log += "sink(" + x + "," + y + ") " }
	sink(<-ch, <-ch)
	return log
}

func n19() string {
	ch := make(chan string, 1)
	ch2 := make(chan string, 1)
	ch <- "r1"
	ch2 <- "r2"
	x := <-ch + <-ch2
	return x
}

func c23l() string {
	ch := make(chan int, 2)
	ch <- 1
	out := ""
	f := func(n int, v int) { out = itoa(n) + "," + itoa(v) }
	func() { f(len(ch), <-ch) }()
	return out
}

func c62l() string {
	ch := make(chan int, 4)
	ch <- 1
	fill := func() int { ch <- 2; ch <- 3; return 0 }
	return func() string { return itoa(len(ch) + fill()) }()
}

func m4() string { return pkgLog + pkgA }

func main() {
	n1()
	n2()
	n4()
	n5()
	n6()
	n7()
	n8()
	n11()
	n12()
	n13()
	n14()
	n15()
	n16()
	n17()
	n18()
	n19()
	c23l()
	c62l()
	m4()
}
