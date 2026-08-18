// spec#Selectors block Selectors-3-361b7011 (also exercises the x.f
// form of block Selectors-1-4580a32c)
// The spec's T0/T1/T2 embedding example, declarations verbatim modulo
// method bodies (the spec declares M0/M1/M2 without bodies; here each
// appends a distinct digit to a trace so the resolved RECEIVER PATH of
// every call in the spec's list is observable). Pins each selector's
// documented resolution: t.z, t.y == t.T1.y, t.x == (*t.T0).x, the
// pointer forms through p, the defined-pointer-type exception q.x ==
// (*(*q).T0).x, and the four method calls incl. auto-address t.M2().
// The invalid line q.M0() from block Selectors-4-c76451a2 is
// negative-lane material and deliberately absent here.
package main

var trace int

type T0 struct {
	x int
}

func (*T0) M0() { trace = trace*10 + 1 }

type T1 struct {
	y int
}

func (T1) M1() { trace = trace*10 + 2 }

type T2 struct {
	z int
	T1
	*T0
}

func (*T2) M2() { trace = trace*10 + 3 }

type Q *T2

func selectorDepth() int {
	var t T2
	t.T0 = &T0{}   // with t.T0 != nil
	t.x = 1        // (*t.T0).x
	t.y = 2        // t.T1.y
	t.z = 3        // t.z
	var p *T2 = &t // with p != nil and (*p).T0 != nil
	var q Q = p
	score := 0
	if t.z == 3 {
		score += 1
	}
	if t.y == 2 {
		score += 2
	}
	if t.x == 1 {
		score += 4
	}
	if p.z == 3 { // (*p).z
		score += 8
	}
	if p.y == 2 { // (*p).T1.y
		score += 16
	}
	if p.x == 1 { // (*(*p).T0).x
		score += 32
	}
	if q.x == 1 { // (*(*q).T0).x — (*q).x is a valid field selector
		score += 64
	}
	trace = 0
	p.M0() // ((*p).T0).M0()      M0 expects *T0 receiver
	p.M1() // ((*p).T1).M1()      M1 expects T1 receiver
	p.M2() // p.M2()              M2 expects *T2 receiver
	t.M2() // (&t).M2()           M2 expects *T2 receiver
	if trace == 1233 {
		score += 128
	}
	return score
}

func main() {
	selectorDepth()
}
