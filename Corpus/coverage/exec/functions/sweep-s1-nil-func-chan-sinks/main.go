package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// UNTYPED NIL at FUNC- and CHAN-typed slots — the surface BUG-016's fix
// recorded as untested (those slots keep the bare-nil emission): `var` with a
// type, assignment after a value, return, argument, struct field, slice
// element, map value, append element, a send on a chan of chans / funcs,
// defined func / chan types, and the nil channel's behaviour (len, cap, a
// select default, close's panic, a send's deadlock).

type tDefFunc func() int

type tDefChan chan int

type tHolder struct {
	F func() int
	C chan int
}

func mkF() func() int { return nil }

func mkC() chan int { return nil }

func fNil(f func() int) bool { return f == nil }

func cNil(c chan int) bool { return c == nil }

func varFunc() bool {
	var f func() int = nil
	return f == nil
}

func assignFunc() bool {
	f := func() int { return 1 }
	f = nil
	return f == nil
}

func varChan() (bool, int, int) {
	var c chan int = nil
	return c == nil, len(c), cap(c)
}

func assignChan() (bool, int) {
	c := make(chan int, 2)
	c <- 1
	c = nil
	return c == nil, len(c)
}

func returnFunc() bool { return mkF() == nil }

func returnChan() bool { return mkC() == nil }

func argFunc() bool { return fNil(nil) }

func argChan() bool { return cNil(nil) }

func structFields() (bool, bool) {
	h := tHolder{F: nil, C: nil}
	return h.F == nil, h.C == nil
}

func structFieldsPositional() (bool, bool) {
	h := tHolder{nil, nil}
	return h.F == nil, h.C == nil
}

func sliceFuncElem() (bool, int) {
	fs := []func() int{nil, func() int { return 2 }}
	return fs[0] == nil, fs[1]()
}

func mapChanValue() bool {
	m := map[string]chan int{"k": nil}
	return m["k"] == nil
}

func appendNilFunc() (bool, int) {
	var fs []func() int
	fs = append(fs, nil)
	return fs[0] == nil, len(fs)
}

func appendNilChan() (bool, int) {
	cs := []chan int{make(chan int)}
	cs = append(cs, nil)
	return cs[1] == nil, len(cs)
}

func sendNilChan() bool {
	chch := make(chan chan int, 1)
	chch <- nil
	return (<-chch) == nil
}

func sendNilFunc() bool {
	chf := make(chan func() int, 1)
	chf <- nil
	return (<-chf) == nil
}

func selectNilDefault() int {
	var c chan int = nil
	select {
	case v := <-c:
		return v
	default:
		return -1
	}
}

func closeNilLiteral() {
	var c chan int = nil
	close(c)
}

func sendNilLiteralDeadlock() {
	var c chan int = nil
	c <- 1
}

func definedFunc() bool {
	var d tDefFunc = nil
	return d == nil
}

func definedChan() (bool, int) {
	var dc tDefChan = nil
	return dc == nil, len(dc)
}

func mkDF() tDefFunc { return nil }

func dcNil(c tDefChan) bool { return c == nil }

func definedFuncReturn() bool { return mkDF() == nil }

func definedChanArg() (bool, int) {
	c := dcNil(nil)
	cs := []tDefChan{nil}
	return c && cs[0] == nil, len(cs[0])
}

func main() {
	varFunc()
}
