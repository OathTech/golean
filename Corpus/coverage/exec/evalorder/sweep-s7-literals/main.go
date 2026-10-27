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
// COMPOSITE LITERALS: the ordered events inside keyed and positional struct literals, arrays,
// slices, slices of structs, nested literals and map literals — a `||` element before a
// mutating call element (lowered as one unseq graph), len before a filling call, a method
// call out of declaration order, a positional receive before a call, map keys and values
// as calls, a receive whose channel is a call result. All born green. The keyed struct
// literal with a plain receive element beside a call element is the red class
// evalorder/sweep-s7-keyed-literal-recv (BUG-279).

type T struct {
	a string
	b string
}

type U struct {
	n int
	z string
}

type L struct {
	a bool
	z int
}

type Inner struct{ y string }

type Outer struct {
	a string
	b Inner
}

type M struct{ log *string }

func (m M) Get() string { *m.log += "M "; return "m" }

var left = false

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

func c3() string {
	b := false
	change := func() int { b = true; return 0 }
	l := L{a: left || b, z: change()}
	if l.a {
		return "true"
	}
	return "false"
}

func c4() string {
	ch := make(chan int, 4)
	ch <- 1
	fill := func() string { ch <- 2; ch <- 3; return "F" }
	u := U{n: len(ch), z: fill()}
	return itoa(u.n) + u.z
}

func c5() string {
	log := ""
	f := func() string { log += "f "; return "F" }
	m := M{&log}
	t := T{b: m.Get(), a: f()}
	return log + t.a + t.b
}

func c6() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	o := Outer{b: Inner{y: a()}, a: b()}
	return log + o.a + o.b.y
}

func c7() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	f := func() string {
		log += "f "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	t := T{<-ch, f()}
	return log + t.a + t.b
}

func c8() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	s := []T{{b: a()}, {a: b()}}
	return log + s[0].b + s[1].a
}

func c9() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	f := func() string {
		log += "f "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	arr := [2]string{<-ch, f()}
	return log + arr[0] + arr[1]
}

func c10() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	f := func() string {
		log += "f "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	s := []string{<-ch, f()}
	return log + s[0] + s[1]
}

func c11() string {
	log := ""
	ka := func() string { log += "ka "; return "KA" }
	va := func() string { log += "va "; return "VA" }
	kb := func() string { log += "kb "; return "KB" }
	vb := func() string { log += "vb "; return "VB" }
	m := map[string]string{ka(): va(), kb(): vb()}
	return log + m["KA"] + m["KB"]
}

func c14() string {
	log := ""
	g := func() string { log += "g "; return "G" }
	t := T{b: func() string { log += "lit "; return "L" }(), a: g()}
	return log + t.a + t.b
}

func c15() string {
	log := ""
	x := true
	f := func() bool { log += "f "; return true }
	g := func() int { log += "g "; return 1 }
	l := L{z: g(), a: x && f()}
	if l.a {
		return log + "true"
	}
	return log + "false"
}

func c17() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	f := func() string {
		log += "f "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	m := map[string]string{<-ch: f()}
	return log + m["r1"] + m["after"]
}

func c8r() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	f := func() string {
		log += "f "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	s := []T{{a: <-ch}, {b: f()}}
	return log + s[0].a + s[1].b
}

func c2c() string {
	ch := make(chan string, 2)
	ch <- "r1"
	chf := func() chan string { return ch }
	f := func() string {
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	t := T{a: <-chf(), b: f()}
	return t.a + t.b
}

func c17v() string {
	ch := make(chan string, 2)
	ch <- "r1"
	f := func() string {
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "F"
	}
	m := map[int]T{1: {a: <-ch}, 2: {b: f()}}
	return m[1].a + m[2].b
}

func main() {
	c3()
	c4()
	c5()
	c6()
	c7()
	c8()
	c9()
	c10()
	c11()
	c14()
	c15()
	c17()
	c8r()
	c2c()
	c17v()
}
