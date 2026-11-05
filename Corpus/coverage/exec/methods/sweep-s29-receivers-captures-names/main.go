// Defect-neighbourhood campaign, shape S29 (synthetic-symbol bookkeeping; members
// BUG-031/027, and BUG-302 fixed in train 28), lane sweep/s28-s29-spelling-symbols,
// 2026-11-05 (docs/2026-10-27_defect-neighbourhood-campaign.md §4). The `$recv`
// receiver slot (unnamed, blank, named `recv`, shadowed), the capture pointers `$cap` of
// the binders not yet rowed (a named result, a type-switch binder, a select binder, the
// receiver, a parameter), method values at the other receiver spellings, stencil names at
// the type-argument kinds, and user names that LOOK like the emitter's synthetic names
// (`lit0`, `deferClose0`, `pkginit`, `recv`, `c0`, `res0`, `method`); expected = gc.

package main

type tU struct{ n int }

func (tU) m1() int        { return 1 }
func (_ tU) m2() int      { return 2 }
func (recv tU) m3() int   { return recv.n + 3 }
func (t tU) m4() int {
	{
		t := 5
		return t
	}
}
func (t *tU) m5() int     { return t.n * 10 }
func (t tU) withLit() int { f := func() int { return t.n * 100 }; return f() }

func receiverSlots() int {
	t := tU{7}
	return t.m1() + t.m2()*10 + t.m3()*100 + t.m4()*1000 + t.m5()*10000 + t.withLit()*100000 // 1+20+1000+5000+700000+70000000
}

func captureNamedResult() (r int) {
	f := func() { r = 3 }
	f()
	return
}

func captureBinders(p int) int {
	var x any = 4
	ch := make(chan int, 1)
	ch <- 5
	n := 0
	switch v := x.(type) {
	case int:
		f := func() int { return v * 10 }
		n += f()
	}
	select {
	case v := <-ch:
		f := func() int { return v * 100 }
		n += f()
	}
	g := func() int { return p }
	return n + g() + captureNamedResult()*1000 // 540 + 6 + 3000 = 3546
}

func captureBindersSubject() int { return captureBinders(6) }

type inner struct{ k int }

func (i inner) key() int { return i.k }

type wrap struct{ inner }

type gbox[T any] struct{ v T }

func (b gbox[T]) val() T { return b.v }

func methodValueSpellings() int {
	t := tU{2}
	p := &tU{3}
	w := wrap{inner{4}}
	m1 := (&t).m3
	m2 := p.m3
	m3, m4 := t.m1, p.m5
	m5 := func() func() int { return t.m3 }()
	m6 := w.key
	m7 := w.inner.key
	m8 := gbox[int]{9}.val
	return m1() + m2()*10 + m3()*100 + m4()*1000 + m5()*10000 + m6()*100000 + m7()*1000000 + m8()*10000000 // 5+60+100+30000+50000+400000+4000000+90000000
}

type myI int

func gId[T any](v T) T { return v }

func gLen[T ~[]E, E any](v T) int { return len(v) }

func gEven[T ~int](v T) bool {
	if v == 0 {
		return true
	}
	return gOdd(v - 1)
}

func gOdd[T ~int](v T) bool {
	if v == 0 {
		return false
	}
	return gEven(v - 1)
}

func stencilNameKinds() int {
	a := gId(1)
	b := int(gId(myI(2)))
	c := gLen([]int{1, 2, 3})
	d := gLen([]myI{1, 2, 3, 4})
	p := gId(&tU{5})
	f := gId(func() int { return 6 })
	g := gId(gbox[int]{7})
	h := gId[int](8) + gId(9)
	n := a + b*10 + c*100 + d*1000 + p.n*10000 + f()*100000 + g.v*1000000 + h*10000000
	if gEven(myI(4)) && !gOdd(4) {
		n++
	}
	return n // 1+20+300+4000+50000+600000+7000000+170000000+1
}

func lit0() int        { return 1 }
func deferClose0() int { return 2 }
func pkginit() int     { return 3 }
func recv() int        { return 4 }
func c0() int          { return 5 }
func res0() int        { return 6 }

type method struct{ v int }

var pkginitVar = 7

func syntheticLookalikeNames() int {
	recv := recv()
	res0 := res0() * 10
	lit0 := lit0() * 100
	c0 := c0() * 1000
	m := method{8}
	f := func() int { return lit0 + c0 }
	return recv + res0 + f() + deferClose0()*10000 + pkginit()*100000 + m.v*1000000 + pkginitVar*10000000 // 4+60+5100+20000+300000+8000000+70000000
}

func main() {
	println("receiverSlots", receiverSlots())
	println("captureBindersSubject", captureBindersSubject())
	println("methodValueSpellings", methodValueSpellings())
	println("stencilNameKinds", stencilNameKinds())
	println("syntheticLookalikeNames", syntheticLookalikeNames())
}
