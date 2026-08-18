package main

// spec#Selectors block Selectors-2-3fcac2bf: selectors resolve at SHALLOWEST
// depth through embedded fields, with automatic dereference of pointer
// embeddings and of pointer receivers — t.z, t.y (== t.T1.y), t.x
// (== (*t.T0).x), the same through p, q.x (a field selector through the
// named pointer type Q), and the method selectors p.M0/p.M1/p.M2/t.M2. The
// spec's bodiless M0/M1/M2 are realized as recorders; the block's invalid
// selector (q.M0()) is a negative form, noted but not emitted.

type T0 struct {
	x int
}

var mLog string

func (*T0) M0() { mLog += "M0" }

type T1 struct {
	y int
}

func (T1) M1() { mLog += "M1" }

type T2 struct {
	z int
	T1
	*T0
}

func (*T2) M2() { mLog += "M2" }

type Q *T2

func selectorFields() int {
	var t T2 = T2{z: 1, T1: T1{y: 2}, T0: &T0{x: 3}} // t.T0 != nil
	p := &t                                          // p != nil, (*p).T0 != nil
	var q Q = p
	n := t.z*100 + t.y*10 + t.x // 123
	m := p.z*100 + p.y*10 + p.x // 123
	o := q.x                    // (*q).x is a valid FIELD selector through Q
	return n*10000 + m*10 + o   // 1231233
}

func selectorMethods() string {
	mLog = ""
	var t T2 = T2{T0: &T0{}}
	p := &t
	p.M2()
	p.M1()
	p.M0()
	t.M2()      // (&t).M2(): addressable value auto-addressed
	return mLog // "M2M1M0M2"
}
