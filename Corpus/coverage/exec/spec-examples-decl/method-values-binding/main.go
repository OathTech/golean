package main

// spec#Method_values block Method_values-2-555de57d: method values bind at
// evaluation — t.Mv (value receiver), pt.Mp (pointer receiver), pt.Mv
// (automatic dereference), t.Mp (automatic address-of for addressable t),
// and makeT().Mv (value method on a non-addressable call result). Their
// types are blocks Method_values-4-d151433c / -7-d9193993. Block
// Method_values-9-a2533909 (methodValueInterface): a method value from an
// INTERFACE value, f := i.M; f(7) acts like i.M(7). The spec's bodiless
// makeT is given a body; bodies return 0 / 1 per the block.

type T struct {
	a int
}

func (tv T) Mv(a int) int          { return 0 } // value receiver
func (tp *T) Mp(f float32) float32 { return 1 } // pointer receiver

func makeT() T { return T{a: 5} } // spec leaves makeT bodiless

var lastM int

type mval struct{}

func (mval) M(a int) { lastM = a }

var myVal = mval{}

func methodValuesBinding() int {
	var t T
	var pt *T = &t
	f1 := t.Mv
	a := f1(7) // 0
	f2 := pt.Mp
	b := int(f2(1.5))                          // 1
	f3 := pt.Mv                                // equivalent to (*pt).Mv
	c := f3(3)                                 // 0
	f4 := t.Mp                                 // equivalent to (&t).Mp
	d := int(f4(2))                            // 1
	e := makeT().Mv(5)                         // 0
	return a*10000 + b*1000 + c*100 + d*10 + e // 1010
}

func methodValueInterface() int {
	var i interface{ M(int) } = myVal
	f := i.M
	f(7)         // like i.M(7)
	return lastM // 7
}
