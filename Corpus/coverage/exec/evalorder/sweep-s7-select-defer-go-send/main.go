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
// SELECT, DEFER, GO AND SEND: the select's channel and send-value expressions evaluated once on
// entry in source order (incl. a send value that is a receive and a method-call channel), the
// deferred and spawned call's receiver and arguments evaluated at the statement in order,
// len before a filling call at a defer, a called channel before a called value at a send, a
// call plus a receive as the sent value, a called channel before a logical operand. All born
// green. The `||` beside a later call at a defer/go is the red package
// evalorder/sweep-s7-logical-defer-go (BUG-278).

type R struct{ log *string }

func (r R) M(x string) string { *r.log += "M(" + x + ") "; return "m" }

func (r R) Ch() chan string {
	*r.log += "Ch "
	c := make(chan string, 1)
	c <- "fromCh"
	return c
}

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

func g1() string {
	log := ""
	ca := make(chan string, 1)
	cb := make(chan string, 1)
	chA := func() chan string { log += "chA "; return ca }
	vA := func() string { log += "vA "; return "VA" }
	chB := func() chan string { log += "chB "; return cb }
	select {
	case chA() <- vA():
		log += "sent "
	case <-chB():
		log += "recv "
	}
	return log + <-ca
}

func g2() string {
	log := ""
	ca := make(chan string, 1)
	cb := make(chan string, 1)
	chA := func() chan string { log += "chA "; return ca }
	chB := func() chan string { log += "chB "; return cb }
	vB := func() string { log += "vB "; return "VB" }
	select {
	case <-chA():
		log += "recv "
	case chB() <- vB():
		log += "sent "
	}
	return log + <-cb
}

func g3() string {
	log := ""
	ch := make(chan string, 1)
	other := make(chan string, 1)
	other <- "O"
	select {
	case ch <- <-other:
		log += "sent "
	default:
		log += "default "
	}
	return log + <-ch + itoa(len(other))
}

func g4() string {
	log := ""
	r := R{&log}
	f := func() chan string { log += "f "; return nil }
	select {
	case v := <-r.Ch():
		log += "recv(" + v + ") "
	case <-f():
		log += "nil "
	}
	return log
}

func h1() string {
	log := ""
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	f := func(x, y string) { log += "f(" + x + "," + y + ") " }
	func() {
		defer f(a(), b())
		log += "body "
	}()
	return log
}

func h2() string {
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
	func() {
		defer f(a(), <-ch)
		log += "body "
	}()
	return log
}

func h2r() string {
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
	func() {
		defer f(<-ch, a())
		log += "body "
	}()
	return log
}

func h3() string {
	log := ""
	r := func() R { log += "r "; return R{&log} }
	a := func() string { log += "a "; return "A" }
	func() {
		defer r().M(a())
		log += "body "
	}()
	return log
}

func h4() string {
	log := ""
	done := make(chan int)
	a := func() string { log += "a "; return "A" }
	b := func() string { log += "b "; return "B" }
	f := func(x, y string) { log += "f(" + x + "," + y + ") "; done <- 1 }
	go f(a(), b())
	<-done
	return log
}

func h9() string {
	out := ""
	ch := make(chan int, 4)
	ch <- 1
	fill := func() string { ch <- 2; ch <- 3; return "F" }
	f := func(n int, y string) { out = itoa(n) + y }
	func() {
		defer f(len(ch), fill())
	}()
	return out
}

func i1() string {
	log := ""
	ch := make(chan string, 1)
	chf := func() chan string { log += "chf "; return ch }
	vf := func() string { log += "vf "; return "V" }
	chf() <- vf()
	return log + <-ch
}

func i2() string {
	log := ""
	ch := make(chan string, 1)
	other := make(chan string, 2)
	other <- "r1"
	f := func() string {
		log += "f "
		select {
		case <-other:
			other <- "after"
		default:
		}
		return "F"
	}
	ch <- f() + <-other
	return log + <-ch
}

func i4() string {
	ch := make(chan bool, 1)
	b := false
	chf := func() chan bool { b = true; return ch }
	chf() <- (left || b)
	if <-ch {
		return "true"
	}
	return "false"
}

func main() {
	g1()
	g2()
	g3()
	g4()
	h1()
	h2()
	h2r()
	h3()
	h4()
	h9()
	i1()
	i2()
	i4()
}
