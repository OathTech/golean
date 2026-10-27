package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The RECEIVER ADAPTATION of spec#Calls at the operand shapes BUG-048/BUG-143
// did not reach: a pointer method on the addressable paths (a named field, a
// field through a pointer, a pointer-to-array element, a global) and on
// operands that are already pointers (map and slice elements of pointer type,
// a pointer-returning call, `&T{}`, `*p`, explicit `&s`); a value method on the
// NON-addressable operands gc accepts (a map element, a call result, a
// type-asserted value, a composite literal, a channel receive) — the pointer
// method on those is gc's rejection, pinned in the negative corpus.

type cnt struct{ n int }

func (c *cnt) inc()    { c.n++ }
func (c cnt) get() int { return c.n }

type holder struct {
	inner cnt
}

var global cnt

func pointerMethodAddressablePaths() int {
	var h holder
	h.inner.inc() // (&h.inner).inc()
	h.inner.inc()
	ph := &holder{}
	ph.inner.inc() // (&(*ph).inner).inc()
	arr := [2]cnt{}
	pa := &arr
	pa[1].inc() // (&(*pa)[1]).inc()
	pa[1].inc()
	pa[1].inc()
	global.inc()
	global.inc()
	global.inc()
	global.inc()
	return h.inner.n*1000 + ph.inner.n*100 + pa[1].n*10 + global.n
}

func newCnt() *cnt { return &cnt{n: 40} }

func pointerMethodPointerOperands() int {
	mp := map[string]*cnt{"k": {n: 1}}
	mp["k"].inc() // the element IS a pointer: used as is
	sp := []*cnt{{n: 10}}
	sp[0].inc()
	sp[0].inc()
	c := newCnt()
	c.inc()
	lit := &cnt{n: 100}
	lit.inc()
	(&cnt{n: 7}).inc() // a literal's address is addressable
	p := &cnt{n: 200}
	(*p).inc() // (&*p).inc(): the explicit deref form
	var s cnt
	(&s).inc() // the explicit address form
	(&s).inc()
	return mp["k"].n*100000 + sp[0].n*10000 + c.n*100 + (lit.n-100)*10 + p.n - 200 + s.n*1000000
}

func makeCnt() cnt { return cnt{n: 9} }

func valueMethodNonaddressable() int {
	m := map[string]cnt{"k": {n: 3}}
	a := m["k"].get() // a value method on a map element: a copy, fine
	b := makeCnt().get()
	var x any = cnt{n: 5}
	c := x.(cnt).get()
	d := cnt{n: 6}.get()
	ch := make(chan cnt, 1)
	ch <- cnt{n: 8}
	e := (<-ch).get()
	return a*10000 + b*1000 + c*100 + d*10 + e
}

func main() {
	pointerMethodAddressablePaths()
	pointerMethodPointerOperands()
	valueMethodNonaddressable()
}
