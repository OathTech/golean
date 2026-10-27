package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// CHANNEL TRAFFIC: a send on `chan any` of an untyped constant, nil, a defined
// value, a typed-nil pointer and an interface value (boxed at the send, the
// box read back); a RECEIVE from `chan int` into an interface target by
// assignment, comma-ok assignment, `var` initializer, select receive (both
// forms — the plain `x = <-ci` and `x, ok = <-ci` forms are quarantined by
// name and recorded as coverage gaps, not rowed) and a map element store; a select send; a `chan` of a defined type
// taking an untyped constant; a `chan` of a narrower interface.

type tDef int

type tPt struct{ X int }

type tErr struct{}

func (tErr) Error() string { return "tErr" }

type tR interface{ R() int }

type tBoth struct{ n int }

func (b tBoth) R() int { return b.n }

func sendInt() any {
	ch := make(chan any, 1)
	ch <- 1
	return <-ch
}

func sendFloat() any {
	ch := make(chan any, 1)
	ch <- 2.5
	return <-ch
}

func sendNil() bool {
	ch := make(chan any, 1)
	ch <- nil
	v := <-ch
	return v == nil
}

func sendDefined() any {
	ch := make(chan any, 1)
	ch <- tDef(3)
	return <-ch
}

func sendTypedNilPointer() (bool, bool) {
	ch := make(chan any, 1)
	var p *tPt
	ch <- p
	v := <-ch
	q, ok := v.(*tPt)
	return v != nil, ok && q == nil
}

func sendIface() any {
	ch := make(chan any, 1)
	var e error = tErr{}
	ch <- e
	return <-ch
}




func varInitReceive() any {
	ci := make(chan int, 1)
	ci <- 6
	var x any = <-ci
	return x
}

func selectSend() any {
	ch := make(chan any, 1)
	select {
	case ch <- 1:
	}
	return <-ch
}

func selectRecvAssign() any {
	ci := make(chan int, 1)
	ci <- 7
	var x any
	select {
	case x = <-ci:
	}
	return x
}

func selectRecvCommaOk() (any, bool) {
	ci := make(chan int, 1)
	ci <- 8
	var x any
	var ok bool
	select {
	case x, ok = <-ci:
	}
	return x, ok
}

func sendDefinedConst() any {
	cm := make(chan tDef, 1)
	cm <- 3
	var a any = <-cm
	return a
}

func sendNarrower() int {
	cr := make(chan tR, 1)
	cr <- tBoth{7}
	return (<-cr).R()
}

func recvIntoMapElem() any {
	ci := make(chan int, 1)
	ci <- 9
	m := map[string]any{}
	m["k"] = <-ci
	return m["k"]
}

func main() {
	sendInt()
}
