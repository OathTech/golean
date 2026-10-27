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
// CALL ARGUMENTS: every ordered-event pair at the argument position — a receive before a call,
// nested calls, variadic and spread calls, a receiver call before its argument, interface and
// method-value callees, a short-circuit before a call, a panic in the middle, an immediately
// invoked literal, a conversion of a call, a called callee, a literal holding a call, the
// builtins append/copy/delete/println/min with call arguments, and len between two calls.
// All born green (gc = the machine).

type T struct{ x, y string }

type R struct{ log *string }

func (r R) M(a, b string) string { *r.log += "M(" + a + "," + b + ") "; return "m" }

type I interface{ M(a, b string) string }

func itoa(n int) string {
	if n == 0 {
		return "0"
	}
	neg := n < 0
	if neg {
		n = -n
	}
	s := ""
	for n > 0 {
		s = string(rune('0'+n%10)) + s
		n /= 10
	}
	if neg {
		s = "-" + s
	}
	return s
}

func a3() string {
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
	f := func(x, y string) { log += "f(" + x + "," + y + ") " }
	f(<-ch, a())
	return log
}

func a4() string {
	log := ""
	h := func() string { log += "h "; return "H" }
	g := func(x string) string { log += "g(" + x + ") "; return "G" }
	k := func() string { log += "k "; return "K" }
	f := func(x, y string) { log += "f(" + x + "," + y + ") " }
	f(g(h()), k())
	return log
}

func a5() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	c := func() string { log += "c "; return "C" }
	f := func(x string, ys ...string) {
		log += "f(" + x
		for _, y := range ys {
			log += "," + y
		}
		log += ") "
	}
	f(a(), b(), c())
	return log
}

func a5s() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	bs := func() []string { log += "bs "; return []string{"B1", "B2"} }
	f := func(x string, ys ...string) {
		log += "f(" + x
		for _, y := range ys {
			log += "," + y
		}
		log += ") "
	}
	f(a(), bs()...)
	return log
}

func a7() string {
	log := ""
	r := func() R { log += "r "; return R{&log} }
	a := func() string { log += "a "; return "A" }
	r().M(a(), "z")
	return log
}

func a8() string {
	log := ""
	getI := func() I { log += "getI "; return R{&log} }
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	getI().M(a(), b())
	return log
}

func a9() string {
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
	mv := R{&log}.M
	mv(a(), <-ch)
	return log
}

func a10() string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return false }
	c := func() string { log += "c "; return "C" }
	f := func(x bool, y string) {
		log += "f("
		if x {
			log += "t"
		} else {
			log += "f"
		}
		log += "," + y + ") "
	}
	f(a() && b(), c())
	return log
}

func a10o() string {
	log := ""
	a := func() bool { log += "a "; return true }
	b := func() bool { log += "b "; return false }
	c := func() string { log += "c "; return "C" }
	f := func(x bool, y string) {
		log += "f("
		if x {
			log += "t"
		} else {
			log += "f"
		}
		log += "," + y + ") "
	}
	f(a() || b(), c())
	return log
}

func a12() (log string) {
	defer func() {
		if r := recover(); r != nil {
			log += "recovered:" + r.(string)
		}
	}()
	a := func() string { log += "a "; return "A" }
	boom := func() string { log += "boom "; panic("boom") }
	c := func() string { log += "c "; return "C" }
	f := func(x, y, z string) { log += "f " }
	f(a(), boom(), c())
	return log
}

func a13() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	f := func(x, y string) { log += "f(" + x + "," + y + ") " }
	f(func() string { log += "lit "; return "L" }(), a())
	return log
}

func a14() string {
	log := ""
	n := 0
	a := func() int { log += "a "; n++; return n }
	b := func() string { log += "b "; n += 10; return "B" }
	f := func(x int64, y string) { log += "f(" + itoa(int(x)) + "," + y + ") " }
	f(int64(a()), b())
	return log
}

func a15() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	getf := func() func(string) string {
		log += "getf "
		return func(x string) string { log += "fv(" + x + ") "; return x }
	}
	getf()(a())
	return log
}

func a17() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	f := func(t T, y string) { log += "f(" + t.x + "," + y + ") " }
	f(T{x: a()}, b())
	return log
}

func a18append() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	s := []string{"S"}
	s = append(s, a(), b())
	return log + s[0] + s[1] + s[2]
}

func a18copy() string {
	log := ""
	d := func() []string { log += "d "; return make([]string, 2) }
	s := func() []string { log += "s "; return []string{"X", "Y"} }
	n := copy(d(), s())
	return log + itoa(n)
}

func a18delete() string {
	log := ""
	mm := map[string]int{"k": 1}
	m := func() map[string]int { log += "m "; return mm }
	k := func() string { log += "k "; return "k" }
	delete(m(), k())
	return log + itoa(len(mm))
}

func a18print() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	println(a(), b())
	return log
}

func a18min() string {
	log := ""
	a := func() int { log += "a "; return 3 }
	b := func() int { log += "b "; return 2 }
	m := min(a(), b())
	return log + itoa(m)
}

func a19() string {
	log := ""
	ch := make(chan int, 4)
	ch <- 1
	a := func() string { log += "a "; return "A" }
	fill := func() string { log += "fill "; ch <- 2; ch <- 3; return "F" }
	f := func(x string, n int, y string) { log += "f(" + x + "," + itoa(n) + "," + y + ") " }
	f(a(), len(ch), fill())
	return log
}

func main() {
	a3()
	a4()
	a5()
	a5s()
	a7()
	a8()
	a9()
	a10()
	a10o()
	a12()
	a13()
	a14()
	a15()
	a17()
	a18append()
	a18copy()
	a18delete()
	a18print()
	a18min()
	a19()
}
