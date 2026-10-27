package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27) — BUG-311: a METHOD VALUE's receiver
// evaluation (spec#Method_values: «the expression x.M is evaluated and saved during the
// evaluation of the method value» — not a call, so unsequenced against a sibling call)
// beside a call that mutates the receiver, at every form the sweep reaches: an argument
// list, a return list, a tuple, a func-typed slice literal, an `any` slice literal, a map
// literal, a struct literal, an indexed literal. The machine realizes ONE order per form
// (an interface method value is hoisted to its lexical position — `$mv` in emit.go's
// interface-method-value arm — so it binds EARLY; a concrete method value binds LATE in
// an argument list / tuple / return list and EARLY inside a literal the legacy hoister
// lifts) and gc the other on five forms: the rows after value-method-value-map-lit are
// born RED on BUG-311's Cases line. value-method-value-map-lit agrees on gc's default
// build (510) while `-gcflags=all=-N -l` gives 110 — the only optimizer-dependent gc
// order this sweep found; recorded in the entry, the row pins the default.

type T2 struct{ n int }

func (t T2) M() int { return t.n }

type PT struct{ n int }

func (p *PT) PM() int { return p.n }

type I2 interface{ M() int }

type W struct {
	f func() int
	k int
}

func sinkF(f func() int, k int) int { return f()*100 + k }

// --- green: the machine's order is gc's ---

func valueMethodValueCallArg() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	return sinkF(v.M, set())
}

func ptrMethodValueCallArg() int {
	a := &PT{1}
	b := &PT{5}
	p := a
	red := func() int { p = b; return 10 }
	return sinkF(p.PM, red())
}

func valueMethodValueReturnList() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	f, k := func() (func() int, int) { return v.M, set() }()
	return f()*100 + k
}

func valueMethodValueStructLit() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	w := W{f: v.M, k: set()}
	return w.f()*100 + w.k
}

func valueMethodValueTuple() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	f, k := v.M, set()
	return f()*100 + k
}

func funcSliceLitWithCallElem() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	l := []func() int{v.M, func() int { return set() }}
	return l[0]()*100 + l[1]()
}

func ifaceMethodValueAnySliceLit() int {
	var i I2 = T2{1}
	set := func() int { i = T2{5}; return 10 }
	l := []any{i.M, set()}
	return l[0].(func() int)()*100 + l[1].(int)
}

func valueMethodValueMapLit() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	m := map[int]any{1: v.M, 2: set()}
	return m[1].(func() int)()*100 + m[2].(int)
}

// --- red (BUG-311): gc realizes the other order ---

func funcSliceLitIndexedByCall() int {
	v := T2{1}
	set := func() int { v.n = 5; return 0 }
	mv := []func() int{v.M, nil}[set()]
	return mv()
}

func ifaceMethodValueCallArg() int {
	var i I2 = T2{1}
	set := func() int { i = T2{5}; return 10 }
	return sinkF(i.M, set())
}

func valueMethodValueAnySliceLit() int {
	v := T2{1}
	set := func() int { v.n = 5; return 10 }
	l := []any{v.M, set()}
	return l[0].(func() int)()*100 + l[1].(int)
}

func ifaceMethodValueReturnList() int {
	var i I2 = T2{1}
	set := func() int { i = T2{5}; return 10 }
	f, k := func() (func() int, int) { return i.M, set() }()
	return f()*100 + k
}

func ifaceMethodValueTuple() int {
	var i I2 = T2{1}
	set := func() int { i = T2{5}; return 10 }
	f, k := i.M, set()
	return f()*100 + k
}
