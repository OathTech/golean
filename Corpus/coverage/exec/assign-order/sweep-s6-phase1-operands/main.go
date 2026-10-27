package main

// S6 sweep, group P1: a target's OPERANDS (index operands, the pointer of a
// deref, the implicit pointer of a selector) are evaluated in PHASE 1, before
// any store — so a target whose operand is ALSO an earlier target reads the
// OLD value (spec#Assignment_statements: `i, x[i] = 1, 2` sets x[0]).

type p1T struct{ x int }
type p1M struct{ m map[int]int }

// P1.4: the deref target's pointer operand is the OLD p.
func p1DerefOperand() int {
	a, b := 1, 2
	p := &a
	p, *p = &b, 5 // *old p (a) = 5; p = &b
	return a*100 + b*10 + *p
}

// P1.5: the selector's implicit indirection operand is the OLD p.
func p1FieldOperand() int {
	a := &p1T{x: 1}
	b := &p1T{x: 2}
	p := a
	p, p.x = b, 5 // old p (a).x = 5; p = b
	return a.x*100 + b.x*10 + p.x
}

// P1.6: a chain target's index operand is the OLD i.
func p1ChainOperand() int {
	a := []p1T{{0}, {0}}
	i := 0
	i, a[i].x = 1, 7 // a[0].x = 7; i = 1
	return i*100 + a[0].x*10 + a[1].x
}

// P1.7: a nested array target's two index operands are the OLD i, j.
func p1NestedOperand() int {
	var a [2][2]int
	i, j := 0, 0
	i, j, a[i][j] = 1, 1, 7 // a[0][0] = 7
	return i*1000 + j*100 + a[0][0]*10 + a[1][1]
}

// P1.8: a pointer-to-array target's pointer operand is the OLD bp.
func p1PtrArrayOperand() int {
	var x, y [2]int
	bp := &x
	bp, (*bp)[0] = &y, 5 // x[0] = 5; bp = &y
	return x[0]*100 + y[0]*10 + (*bp)[1]
}

// P1.9: comma-ok type assertion — the ok target's index operand is the OLD i.
func p1AssertDep() int {
	var iv any = 2
	i := 0
	bs := []bool{false, false, false}
	i, bs[i] = iv.(int) // bs[0] = true; i = 2
	n := i * 100
	for j := range bs {
		if bs[j] {
			n += j + 1
		}
	}
	return n
}

// P1.15: the same statement with i and a CAPTURED by a closure (address-taken
// targets lower as pointer targets).
func p1Captured() int {
	i := 0
	a := []int{10, 20, 30}
	f := func() { i, a[i] = 2, 99 }
	f()
	return i*10000 + a[0]*100 + a[1]
}

// P1.16: inside a generic function over []T.
func p1SetIdx[T any](s []T, i int, v T) int {
	i, s[i] = i+1, v
	return i
}

func p1Generic() int {
	s := []int{10, 20, 30}
	n := p1SetIdx(s, 0, 99)
	return n*10000 + s[0]*100 + s[1]
}

// P1.17: a map reached through a pointer's field — the map value and the key
// are the phase-1 operands; the key is the OLD k.
func p1MapViaField() int {
	p := &p1M{m: map[int]int{}}
	k := 0
	k, p.m[k] = 1, 7 // m[0] = 7; k = 1
	return k*100 + p.m[0]*10 + len(p.m)
}

// P1.20: two receives on the right (ordered left to right) and the deref
// target's OLD pointer operand.
func p1TwoReceives() int {
	a, b := 1, 2
	p := &a
	chP := make(chan *int, 1)
	chV := make(chan int, 1)
	chP <- &b
	chV <- 5
	p, *p = <-chP, <-chV // *old p (a) = 5; p = &b
	return a*100 + b*10 + *p
}

var p1Log []int

func p1Wit(n int) int { p1Log = append(p1Log, n); return n }

// P1.21: a call in the index of a SINGLE assignment's target and a call on
// the right are ordered left to right; both are phase 1, the store is phase 2.
func p1CallIndexThenRhs() int {
	p1Log = nil
	a := []int{0, 0}
	a[p1Wit(1)] = p1Wit(7)
	return p1Log[0]*100 + p1Log[1]*10 + a[1]/7
}

// P1.22: a call producing the deref target's pointer, then the right-hand call.
func p1CallDerefThenRhs() int {
	p1Log = nil
	x := 0
	pf := func() *int { p1Wit(1); return &x }
	*pf() = p1Wit(7)
	return p1Log[0]*100 + p1Log[1]*10 + x/7
}

// P1.23: a call in a map target's key, then the right-hand call (map-assign).
func p1CallMapKeyThenRhs() int {
	p1Log = nil
	m := map[int]int{}
	m[p1Wit(1)] = p1Wit(7)
	return p1Log[0]*100 + p1Log[1]*10 + m[1]/7
}

func main() {
	p1DerefOperand()
}
