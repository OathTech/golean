package main

import "fmt"

type R interface{ rw() int }

type T struct{}

func (T) rw() int { return 7 }

type SI struct{ R }

// the new panic replaces "first" as the recover value
func q8() (out int) {
	defer func() {
		r := recover()
		if _, ok := r.(string); ok {
			out = 1
		} else if r != nil {
			out = 2
		}
	}()
	var i R = SI{}
	defer i.rw()
	panic("first")
}

// unrecovered chain: abort output
func q13() int {
	var i R = SI{}
	defer i.rw()
	panic("first")
}

type Box struct{ n int }

type C interface{ get() int }

func (b *Box) get() int {
	if b == nil {
		return -1
	}
	return b.n
}

type W struct{ *Box }
type WV struct{ Box }

// nil embedded *E with pointer receiver via iface dispatch: receiver nil, no panic
func q14() int {
	var c C = W{}
	return c.get()
}

// nil *WV box calling ptr method via value embed: &nil.f panics
func q15() (out int) {
	defer func() {
		if recover() != nil {
			out = 99
		}
	}()
	var p *WV
	var c C = p
	return c.get()
}

// method expression with pointer arg nil over promoted ptr method through value embed: &nil.f panics
func q16() (out int) {
	defer func() {
		if recover() != nil {
			out = 99
		}
	}()
	return (*WV).get(nil)
}

// method expression over promoted ptr method through nil embedded pointer: receiver nil
func q17() int {
	return W.get(W{})
}

type V struct{ n int }

func (v V) val() int { return v.n }

type VI interface{ val() int }
type WP struct{ *V }

// value receiver out of a nil embedded pointer via method expression: panic
func q18() (out int) {
	defer func() {
		if recover() != nil {
			out = 99
		}
	}()
	return WP.val(WP{})
}

// (*WP).val with nil outer pointer: panic
func q19() (out int) {
	defer func() {
		if recover() != nil {
			out = 99
		}
	}()
	return (*WP).val(nil)
}

// go over a method expression with iface tail and nil field: child aborts
func q20() int {
	ch := make(chan int)
	go SI.rw(SI{})
	<-ch
	return 0
}

func main() {
	fmt.Println(q8(), q14(), q15(), q16(), q17(), q18(), q19())
	if len(fmt.Sprint()) > 100 {
		q13()
		q20()
	}
}
