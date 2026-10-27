package main

// S6 sweep, group P2: a target's OWN check (bounds, nil pointer, nil map)
// fires in PHASE 2, at its store — after the right-hand side evaluated and
// after every earlier target's store landed.

type p2In struct{ x int }
type p2S struct{ q p2In }  // q is a STRUCT field: p.q.x is one address chain
type p2P struct{ q *p2In } // q is a POINTER field: p.q is a value read

func p2Recover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

// P2.4: a nil-map single target against a panicking RHS — the RHS's panic.
func p2NilMapVsRhs() int {
	var m map[int]int
	z := 0
	m[1] = 1 / z
	return 0
}

// P2.5: a nil pointer-to-array element target against a panicking RHS.
func p2NilPtrArrayVsRhs() int {
	var bp *[3]int
	z := 0
	(*bp)[0] = 1 / z
	return 0
}

// P2.6: a chain target (index then field) against a panicking RHS.
func p2ChainVsRhs() int {
	a := []p2In{}
	z := 0
	a[9].x = 1 / z
	return 0
}

func p2Wit(n int) int { println("wit", n); return n }

// P2.11: a NIL MAP as the FIRST target: both right-hand calls run (phase 1)
// before the store's panic.
func p2NilMapFirstRhsEffects() int {
	var m map[int]int
	y := 0
	m[1], y = p2Wit(7), p2Wit(8)
	return y
}

// P2.14: p nil, q a struct field — the whole chain p.q.x is address formation,
// its nil check at the store: x IS stored.
func p2StructFieldChainNilBase() int {
	var p *p2S
	x := 0
	hit := p2Recover(func() { x, p.q.x = 1, 2 })
	return hit*100 + x*5
}

// P2.15: p non-nil, q a POINTER field that is nil — the load of p.q is phase
// 1, the store through nil q is phase 2: x IS stored.
func p2PointerFieldNilAtStore() int {
	p := &p2P{}
	x := 0
	hit := p2Recover(func() { x, p.q.x = 1, 2 })
	return hit*100 + x*5
}

// P2.16: p NIL, q a POINTER field — reading p.q indirects p in phase 1: the
// panic precedes every store, x is NOT stored.
func p2PointerFieldNilBasePhase1() int {
	var p *p2P
	x := 0
	hit := p2Recover(func() { x, p.q.x = 1, 2 })
	return hit*100 + x*5
}

// P2.17: (*pp)[0] with pp a nil *[]int — the deref is a VALUE step (the slice
// header), phase 1: x is NOT stored (plain-path twin of recv-edge's cell).
func p2NilSlicePtrBasePhase1() int {
	var pp *[]int
	x := 0
	hit := p2Recover(func() { x, (*pp)[0] = 1, 2 })
	return hit*100 + x*5
}

// P2.20: comma-ok map read into two deref targets, the second nil: the first
// store lands.
func p2CommaOkDerefSecondNil() int {
	m := map[int]int{1: 7}
	v := 0
	var okp *bool
	hit := p2Recover(func() { *(&v), *okp = m[1] })
	return hit*100 + v
}

// P2.21: comma-ok map read whose FIRST target is out of range: the key call
// ran (phase 1), no store, the ok target untouched.
func p2CommaOkFirstOob() int {
	m := map[int]int{1: 7}
	a := []int{0}
	ok := true
	hit := p2Recover(func() { a[9], ok = m[p2Wit(1)] })
	n := hit * 100
	if ok {
		n += 10
	}
	return n
}

// P2.22: comma-ok map read into a NIL map's element.
func p2CommaOkIntoNilMap() int {
	var m map[int]int
	m2 := map[int]int{1: 7}
	ok := false
	m[1], ok = m2[1]
	if ok {
		return 1
	}
	return 0
}

// P2.23: comma-ok type assertion into a NIL map's element.
func p2AssertIntoNilMap() int {
	var m map[int]int
	var iv any = 5
	ok := false
	m[1], ok = iv.(int)
	if ok {
		return 1
	}
	return 0
}

func p2Pair() (int, int) { println("pair"); return 1, 2 }

// P2.25: a multi-value call into a NIL map's element: the call runs, then the
// store panics.
func p2CallIntoNilMap() int {
	var m map[int]int
	y := 0
	m[1], y = p2Pair()
	return y
}

// P2.27: the second target's bounds check at the store, in a generic function.
func p2GenSecondOob[T any](s []T, v T) (x int) {
	defer func() {
		if recover() != nil {
			x += 100
		}
	}()
	x, s[9] = 1, v
	return
}

func p2GenericSecondOob() int {
	return p2GenSecondOob([]int{0}, 5)
}

// P2.28: both targets out of range — the FIRST store's panic names a's length.
func p2BothOobFirstWins() int {
	a := []int{0}
	b := []int{0, 0}
	a[9], b[9] = 1, 2
	return 0
}

func main() {
	p2NilMapVsRhs()
}
