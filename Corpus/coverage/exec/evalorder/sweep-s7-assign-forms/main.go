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
// ASSIGNMENT AND VAR FORMS (the ordered events only; the two phases are S6): tuple assignment
// of two calls and of a receive then a call, a called index target before the called right
// side (spec: f() before g() in `y[f()] = g()`), the compound form, a var spec of two calls, a
// called map key before the value, a called pointer target before the value, two receives, two
// called targets before two called right sides. All born green.

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

func j1() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	var x, y string
	x, y = a(), b()
	return log + x + y
}

func j2() string {
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
	var x, y string
	x, y = <-ch, a()
	return log + x + y
}

func j3() string {
	log := ""
	s := []string{"", ""}
	idx := func() int { log += "idx "; return 1 }
	val := func() string { log += "val "; return "V" }
	s[idx()] = val()
	return log + s[1]
}

func j4() string {
	log := ""
	s := []int{0, 10}
	idx := func() int { log += "idx "; return 1 }
	val := func() int { log += "val "; return 5 }
	s[idx()] += val()
	return log + itoa(s[1])
}

func j5() string {
	log := ""
	f := func() string { log += "f "; return "F" }
	g := func() string { log += "g "; return "G" }
	var a, b = f(), g()
	return log + a + b
}

func j8() string {
	log := ""
	m := map[string]string{}
	k := func() string { log += "k "; return "K" }
	v := func() string { log += "v "; return "V" }
	m[k()] = v()
	return log + m["K"]
}

func j9() string {
	log := ""
	var cell string
	pf := func() *string { log += "pf "; return &cell }
	v := func() string { log += "v "; return "V" }
	*pf() = v()
	return log + cell
}

func j12() string {
	ch := make(chan string, 1)
	ch2 := make(chan string, 1)
	ch <- "r1"
	ch2 <- "r2"
	x, y := <-ch, <-ch2
	return x + y
}

func j14() string {
	log := ""
	xs := []string{"", ""}
	ys := []string{"", ""}
	i := func() int { log += "i "; return 0 }
	j := func() int { log += "j "; return 1 }
	k := func() string { log += "k "; return "K" }
	l := func() string { log += "l "; return "L" }
	xs[i()], ys[j()] = k(), l()
	return log + xs[0] + ys[1]
}

func main() {
	j1()
	j2()
	j3()
	j4()
	j5()
	j8()
	j9()
	j12()
	j14()
}
