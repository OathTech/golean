package main

// Embedding a POINTER (*vepMid) puts pointer-receiver methods reached
// through it — including on a DEEPER value field — into the VALUE method
// set of the embedding struct (the pointer hop supplies addressability).
// Declaring such a type must not fail the export, static calls dispatch,
// and a VALUE box satisfies the interface, dispatching through the
// synthesized wrapper. Mutations through the promoted pointer-receiver
// method alias the one heap cell the pointer reaches. (Audit F2,
// 2026-08-05: wrapper synthesis refused this method-set shape and killed
// the whole package export.)

type vepIface interface {
	bump() int
}

type vepBase struct {
	n int
}

func (b *vepBase) bump() int {
	b.n++
	return b.n
}

type vepMid struct {
	vepBase
}

type vepOuter struct {
	*vepMid
}

func vepStaticCall() int {
	o := vepOuter{vepMid: &vepMid{vepBase: vepBase{n: 4}}}
	a := o.bump()
	b := o.bump()
	return a*10 + b
}

func vepValueBoxSatisfies() int {
	o := vepOuter{vepMid: &vepMid{vepBase: vepBase{n: 1}}}
	_, ok := any(o).(vepIface)
	if ok {
		return 1
	}
	return 0
}

func vepDynamicDispatch() int {
	o := vepOuter{vepMid: &vepMid{vepBase: vepBase{n: 7}}}
	var i vepIface = o
	x := i.bump()
	y := o.bump()
	return x*10 + y
}
