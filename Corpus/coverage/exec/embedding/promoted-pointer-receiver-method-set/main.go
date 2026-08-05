package main

// Go's method-set asymmetry THROUGH promotion: a pointer-receiver method
// promoted through VALUE embedding is in *Outer's method set but not in
// Outer's — the value box fails the assert, the pointer box passes and
// dispatches. (Spec: struct with embedded field T gets *T's methods only
// on the pointer type.)

type ptrSetIface interface {
	pm() int
}

type ptrSetInner struct {
	n int
}

func (p *ptrSetInner) pm() int {
	return p.n
}

type ptrSetOuter struct {
	ptrSetInner
}

func promotedPointerReceiverValueBox() int {
	var x any = ptrSetOuter{}
	_, ok := x.(ptrSetIface)
	if ok {
		return 1
	}
	return 0
}

func promotedPointerReceiverPointerBox() int {
	o := ptrSetOuter{ptrSetInner: ptrSetInner{n: 3}}
	var x any = &o
	y, ok := x.(ptrSetIface)
	if ok {
		return y.pm()*10 + 1
	}
	return 0
}
