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
// BUG-280 (found by this sweep, born RED/differential): `make([]T, len(), cap())` with two CALL
// arguments — gc's default build evaluates the CAP call BEFORE the LEN call when the callees
// inline (`b a`), the spec's lexical order and the machine's is `a b`; `-gcflags=all=-N -l`
// and non-inlinable callees give gc the spec order too. The machine (emitMake: len then cap,
// each hoisted at its lexical position) answers the spec; the red rows pin gc's realization at
// every position (define, global target, call argument, var spec, before a later call, string
// elements, before an append, int64 arguments, top-level callees, a return, a generic body,
// before a second make, before a store). The green controls: a chan size and a map hint (one
// argument), arithmetic around the calls, a plain two-argument call, callees sharing a
// counter, non-inlinable callees (a defer inside), make with one call as an argument.

var sink []int

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

var mkLog = ""

func ncA() int {
	defer func() {}()
	mkLog += "a "
	return 2
}

func ncB() int {
	defer func() {}()
	mkLog += "b "
	return 4
}

func tlA() int { mkLog += "a "; return 2 }

func tlB() int { mkLog += "b "; return 4 }

func mk16r() []int {
	a := func() int { mkLog += "a "; return 2 }
	b := func() int { mkLog += "b "; return 4 }
	return make([]int, a(), b())
}

func genMk[T any](_ T) string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	s := make([]T, a(), b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk1() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	s := make([]int, a(), b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk2() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	sink = make([]int, a(), b())
	return log + itoa(len(sink)) + itoa(cap(sink))
}

func mk3() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	use := func(s []int) { log += "use " }
	use(make([]int, a(), b()))
	return log
}

func mk4() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	var s = make([]int, a(), b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk5() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	c := func() int { log += "c "; return 0 }
	s := make([]int, a(), b())
	return log + itoa(len(s)+cap(s)+c())
}

func mk6() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	s := make([]string, a(), b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk7() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	s := make([]int, a(), b())
	s = append(s, 1)
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk11() string {
	log := ""
	a := func() int64 { log += "a "; return 2 }
	b := func() int64 { log += "b "; return 4 }
	s := make([]int, a(), b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk14() string {
	mkLog = ""
	s := make([]int, tlA(), tlB())
	return mkLog + itoa(len(s)) + itoa(cap(s))
}

func mk16() string {
	mkLog = ""
	s := mk16r()
	return mkLog + itoa(len(s)) + itoa(cap(s))
}

func mk17() string { return genMk(0) }

func mk19() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	c := func() int { log += "c "; return 0 }
	s := make([]int, a(), b())
	t := make([]int, c())
	return log + itoa(len(s)+cap(s)+len(t))
}

func mk21() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	s := make([]int, a(), b())
	s[0] = 1
	return log + itoa(len(s)) + itoa(cap(s)) + itoa(s[0])
}

func mk8() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	ch := make(chan int, a()+b())
	return log + itoa(cap(ch))
}

func mk9() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	s := make([]int, 1+a(), 2+b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk10() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	f := func(x, y int) { log += "f " }
	f(a(), b())
	return log
}

func mk12() string {
	log := ""
	n := 0
	a := func() int { log += "a "; n++; return n }
	b := func() int { log += "b "; n += 10; return n }
	s := make([]int, a(), b())
	return log + itoa(len(s)) + itoa(cap(s))
}

func mk13() string {
	mkLog = ""
	s := make([]int, ncA(), ncB())
	return mkLog + itoa(len(s)) + itoa(cap(s))
}

func mk18() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 0 }
	m := make(map[int]int, a()+b())
	return log + itoa(len(m))
}

func mk20() string {
	log := ""
	a := func() int { log += "a "; return 2 }
	b := func() int { log += "b "; return 4 }
	sink := func(x int, s []int) { log += "sink " }
	sink(a(), make([]int, b()))
	return log
}

func main() {
	mk1()
	mk2()
	mk3()
	mk4()
	mk5()
	mk6()
	mk7()
	mk11()
	mk14()
	mk16()
	mk17()
	mk19()
	mk21()
	mk8()
	mk9()
	mk10()
	mk12()
	mk13()
	mk18()
	mk20()
}
