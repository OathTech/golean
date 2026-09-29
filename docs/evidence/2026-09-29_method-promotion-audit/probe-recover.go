package main

import "fmt"

type R interface{ rw() int }

type T struct{}

func (T) rw() int {
	if recover() != nil {
		return 1
	}
	return 0
}

type U struct{ T }          // value embed of T
type SI struct{ R }         // embedded interface
type SP struct{ *T }        // embedded pointer
type SS struct{ SI }        // two-level: value embed of a struct with an embedded interface
type SIU struct{ R }        // holds U (iface then promoted)

// P1: defer through an embedded-interface tail whose value is itself promoted.
func p1() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i R = SIU{U{}}
	defer i.rw()
	panic("boom")
}

// P2: method expression over an iface-tail promoted entry, deferred.
func p2() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	defer SI.rw(SI{T{}})
	panic("boom")
}

// P3: two-level (value hop then iface tail), via interface dispatch, deferred.
func p3() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i R = SS{SI{T{}}}
	defer i.rw()
	panic("boom")
}

// P4: interface method value of a promoted method, deferred.
func p4() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i R = U{}
	f := i.rw
	defer f()
	panic("boom")
}

// P5: pointer method expression over pointer-embed promoted, deferred.
func p5() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	defer (*SP).rw(&SP{&T{}})
	panic("boom")
}

// P6: NOT directly deferred: closure calls the promoted method -> no recover inside rw.
func p6() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i R = U{}
	defer func() { out += i.rw() }()
	panic("boom")
}

// P7: not directly deferred, iface tail.
func p7() (out int) {
	defer func() {
		if recover() != nil {
			out += 100
		}
	}()
	var i R = SI{T{}}
	defer func() { out += i.rw() * 10 }()
	panic("boom")
}

// P8: iface tail with nil field, deferred during a panic; outer recover sees the NEW panic.
func p8() (out string) {
	defer func() {
		r := recover()
		out = fmt.Sprint(r)
	}()
	var i R = SI{}
	defer i.rw()
	panic("first")
}

// P9: iface tail nil field deferred at a normal return, recovered.
func p9() (out string) {
	defer func() {
		r := recover()
		out = fmt.Sprint(r != nil)
	}()
	var i R = SI{}
	defer i.rw()
	return "none"
}

// P10: method expression with iface tail and nil field, direct call, recovered.
func p10() (out string) {
	defer func() {
		out = fmt.Sprint(recover() != nil)
	}()
	SI.rw(SI{})
	return "no"
}

// P11: second recover in the same deferred promoted call returns nil (via iface tail).
type T2 struct{}

func (T2) rw() int {
	a := recover()
	b := recover()
	n := 0
	if a != nil {
		n += 1
	}
	if b != nil {
		n += 10
	}
	return n
}

func p11() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i R = SI{U2{}}
	defer i.rw()
	panic("boom")
}

type U2 struct{ T2 }

// P12: recover-returning value visible: deferred promoted call through method value of iface-tail.
func p12() (out int) {
	defer func() {
		if recover() != nil {
			out = 100
		}
	}()
	var i R = SI{T{}}
	f := i.rw
	defer f()
	panic("boom")
}

func main() {
	fmt.Println(p1(), p2(), p3(), p4(), p5(), p6(), p7())
	fmt.Println(p8())
	fmt.Println(p9(), p10(), p11(), p12())
}
