package main

// Audit probes, Stage E5 family E5d (`&x` as an operand). [AGENT] auditor 2026-09-22.

type PT struct{ p *int }
type S struct{ f int }
type V struct{ n int }

func (v *V) Bump() int { v.n += 10; return 1 }

var g = 1

func use(p *int) int   { *p = 7; return 1 }
func use2(p *int) int  { *p = *p*10 + 3; return 2 }
func readp(p *int) int { return *p }
func readp2(p *int, n int) int { return *p + n }
func sink(b bool, n int) int {
	if b {
		return n
	}
	return -n
}

// COMPUTING positions: every one must REFUSE by name (legacy path, correct answer).
func derefAddrVsCall() int { x := 1; m := func() int { x = 10; return 5 }; return *(&x) + m() }
func addrCmpVsCall() int {
	x, y := 1, 2
	m := func() int { x = 10; y = 20; return 5 }
	return sink(&x == &y, m()) + x
}
func addrElemVsCall() int { a := []int{1, 2}; m := func() int { a[0] = 10; return 5 }; return use(&a[0]) + m() + a[0] }
func addrFieldVsCall() int { s := S{f: 1}; m := func() int { s.f = 10; return 5 }; return use(&s.f) + m() + s.f }
func addrDerefVsCall() int { x := 1; p := &x; m := func() int { x = 10; return 5 }; return use(&*p) + m() + x }
func addrAppendElem() int {
	x := 1
	var ps []*int
	m := func() int { x = 10; return 5 }
	return *append(ps, &x)[0] + m()
}
func addrStoredPlanned() int {
	x := 1
	ps := make([]*int, 2)
	m := func() int { x = 10; return 1 }
	ps[m()] = &x
	return *ps[1]
}

// VALUE positions: admitted; the sets below are the spec's.
func addrMapValue() int { x := 1; m := func() int { x = 10; return 5 }; return *map[int]*int{1: &x}[1] + m() } // {6, 15}
func addrGlobalPayload() int { g = 1; m := func() int { g = 10; return 5 }; return *(&PT{p: &g}).p + m() }  // {6, 15}
func addrArgThenWrite() int { x := 1; gw := func() int { x = 5; return 0 }; return readp(&x) + gw() }         // {1}: readp before gw (E1)
func addrArgCallWritesFirst() int { x := 1; gw := func() int { x = 5; return 0 }; return readp2(&x, gw()) }  // {5}: gw before readp (D)
func addrTwoWritersRead() int { x := 1; return use(&x) + use2(&x) + x }                                        // {4, 10, 76}
func addrPtrRecv() int {
	v := V{n: 1}
	m := func() int { v.n = 100; return 5 }
	return (&v).Bump() + m() + v.n // {7, 17, 106}
}
func addrClosureCaptured() int {
	x := 1
	a := []int{4, 5}
	f := func() int { j := 1; return use(&x) + a[j] } // inside the lifted body: &x of a CAPTURED variable
	r := f()
	return r*10 + x // 67
}
func addrReturnPair() (*int, int) { x := 1; m := func() int { x = 10; return 5 }; return &x, m() + x }
func addrReturnPairDriver() int    { p, y := addrReturnPair(); return *p*100 + y } // {1006, 1015}
func addrNestedLit() int           { x := 1; m := func() int { x = 10; return 5 }; return *[]PT{{p: &x}}[0].p + m() }
func addrParam(x int) int          { return use(&x) + x } // {2, 8}
func addrParamDriver() int         { return addrParam(1) }

// an ADMITTED sweep inside a lifted body carrying `&x` of a CAPTURED variable (the pointer parameter spelling)
func addrClosureAdmitted() int {
	x := 1
	f := func() int { b := []int{4, 5}; j := 1; return use(&x) + b[j] }
	r := f()
	return r*10 + x // 67
}
