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
// BUG-279 (found by this sweep, born RED/differential): a KEYED struct literal whose element is a
// RECEIVE beside an element holding a CALL evaluates the receive AFTER the call whatever the
// source order. emitStructLit pre-binds the elements `containsCall` finds (CallExprs) to temps
// in source order and emits the rest in declaration order; a receive is a UnaryExpr, so it
// hoists during that second pass — after every call. spec#Order_of_evaluation orders the
// receive and the call lexically; gc receives the element present before the call swaps it
// ("r1"), the machine the swapped one ("after"). Every position of the literal: a define,
// `&T{}`, nested, a method-call sibling, a return, a defer argument, a var spec, a generic body.

type T struct {
	a string
	b string
}

type O struct {
	t T
	z string
}

type M struct{ ch chan string }

func (m M) Get() string {
	select {
	case <-m.ch:
		m.ch <- "after"
	default:
	}
	return "G"
}

type TJ struct{ j, k string }

func genLit[P any](_ P) string {
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
	t := T{a: <-ch, b: f()}
	return log + t.a + t.b
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

func c2a() string {
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
	t := T{a: <-ch, b: f()}
	return log + t.a + t.b
}

func c2b() string {
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
	t := T{b: <-ch, a: f()}
	return log + t.a + t.b
}

func c13() string {
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
	p := &T{a: <-ch, b: f()}
	return log + p.a + p.b
}

func c6r() string {
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
	o := O{t: T{a: <-ch}, z: f()}
	return log + o.t.a + o.z
}

func c2m() string {
	ch := make(chan string, 2)
	ch <- "r1"
	m := M{ch}
	t := T{a: <-ch, b: m.Get()}
	return t.a + t.b
}

func b5() string {
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
	g := func() TJ { return TJ{k: <-ch, j: a()} }
	t := g()
	return log + t.j + t.k
}

func h10() string {
	log := ""
	ch := make(chan string, 2)
	ch <- "r1"
	g := func() string {
		log += "g "
		select {
		case <-ch:
			ch <- "after"
		default:
		}
		return "G"
	}
	f := func(t T) { log += "f(" + t.a + "," + t.b + ") " }
	func() {
		defer f(T{a: <-ch, b: g()})
	}()
	return log
}

func j6() string {
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
	var x = TJ{k: <-ch, j: f()}
	return log + x.j + x.k
}

func m1c() string { return genLit(0) }

func main() {
	c2a()
	c2b()
	c13()
	c6r()
	c2m()
	b5()
	h10()
	j6()
	m1c()
}
