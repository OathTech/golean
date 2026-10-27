package main

// Defect-neighbourhood campaign, shape S5 (method sets: records, promotion,
// receiver adaptation, dispatch), lane sweep/s5-method-sets, 2026-10-27: every
// row is an agreement with gc on a route no earlier row held (the matrix is on
// the member entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// METHOD VALUES bound at evaluation time (spec#Method_values): `(&x).Mv` still
// copies the value receiver at the bind; `p.Mv` / `p.Mp` with `p` re-pointed
// afterwards keep the receiver bound then; method values stored in a struct
// field, a map and a slice and called later; the receiver copied at a `go`
// statement; an interface method value bound to the box's dynamic value at
// the bind, not at the call.

type cell struct{ n int }

func (c cell) val() int  { return c.n }
func (c *cell) ptr() int { return c.n }

func addrValueMethodCopies() int {
	x := cell{n: 1}
	f := (&x).val // (*(&x)).val: the receiver is the value, copied now
	x.n = 9
	return f()*10 + x.n
}

func repointedPointerVar() int {
	a := cell{n: 1}
	b := cell{n: 2}
	p := &a
	fv := p.val // (*p).val: a copy of a at the bind
	fp := p.ptr // p itself captured
	p = &b
	a.n = 7 // the copy in fv stays 1; fp still points at a and sees 7
	return fv()*100 + fp()*10 + p.ptr()
}

type callbacks struct {
	f func() int
}

func storedMethodValues() int {
	a := cell{n: 3}
	b := cell{n: 4}
	s := callbacks{f: a.val}
	m := map[string]func() int{"b": b.ptr}
	list := []func() int{a.val, b.val, b.ptr}
	a.n = 30
	b.n = 40
	return s.f()*100000 + m["b"]()*1000 + list[0]()*100 + list[1]()*10 + (list[2]() - 40)
}

func (c cell) report(ch chan int) { ch <- c.n }

func goValueReceiverCopy() int {
	x := cell{n: 5}
	ch := make(chan int)
	go x.report(ch) // x copied when the go statement executes
	x.n = 6
	got := <-ch
	return got*10 + x.n
}

type valuer interface{ val() int }

func ifaceMethodValueReboundBox() int {
	var i valuer = cell{n: 1}
	f := i.val // bound to the dynamic value now
	i = cell{n: 2}
	g := i.val
	i = &cell{n: 3}
	return f()*100 + g()*10 + i.val()
}

func main() {
	addrValueMethodCopies()
	repointedPointerVar()
	storedMethodValues()
	goValueReceiverCopy()
	ifaceMethodValueReboundBox()
}
