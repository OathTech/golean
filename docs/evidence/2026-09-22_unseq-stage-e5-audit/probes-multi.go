package main

// Audit probes, Stage E5 family E5b (multi-target assignment). [AGENT] auditor 2026-09-22.

func wit(n int) int { println("wit", n); return n }

var G = 0

// spec#Assignment_statements phase 2: a target's own check is the STORE's — the panic must come AFTER every
// phase-1 event. A member with the panic BEFORE `wit 1` is spec-forbidden.
func oobTargetVsCall() int { xs := []int{1, 2, 3}; y := 0; xs[9], y = 1, wit(1); return y }
func nilMapTargetVsCall() int {
	var m map[int]int
	y := 0
	m[1], y = 1, wit(1)
	return y
}
func nilDerefTargetVsCall() int {
	var p *int
	y := 0
	*p, y = 1, wit(1)
	return y
}
func secondTargetPanics() int {
	xs := []int{1, 2}
	defer func() { println("xs0", xs[0]) }()
	xs[0], xs[9] = 4, wit(5)
	return 0
}
// the spec's own `i, x[i] = 1, 2` (x[i] uses the OLD i), with a call so the sweep is admitted
func specExampleOldIndex() int {
	xs := []int{1, 2, 3}
	i := 0
	f := func() int { return 1 }
	i, xs[i] = f(), 2
	return i*100 + xs[0]*10 + xs[1] // 122
}
func capturedIndexTarget() int {
	xs := []int{1, 2, 3}
	i := 0
	f := func() int { i = 2; return 7 }
	i, xs[i] = 1, f()
	return i*1000 + xs[0]*100 + xs[1]*10 + xs[2] // {1723, 1127}
}
func sameTargetTwice() int { xs := []int{1, 2}; f := func() int { return 5 }; xs[0], xs[0] = f(), 2; return xs[0] } // 2
func plainTargetWrittenByCall() int {
	x := 0
	xs := []int{1}
	f := func() int { x = 5; return 9 }
	x, xs[0] = 1, f()
	return x*10 + xs[0] // 19 (x's store is phase 2, after f)
}
func targetOperandCallsOrder() int {
	xs := make([]int, 3)
	f := func() int { println("f"); return 0 }
	g := func() int { println("g"); return 1 }
	two := func() (int, int) { println("two"); return 7, 8 }
	xs[f()], xs[g()] = two()
	return xs[0]*10 + xs[1] // f g two; 78
}
func targetOperandVsRHSCalls() int {
	xs := make([]int, 3)
	f := func() int { println("f"); return 0 }
	g := func() int { println("g"); return 1 }
	h := func() int { println("h"); return 2 }
	xs[f()], xs[1] = g(), h()
	return xs[0]*10 + xs[1] // f g h; 12
}
func swapVsCall() int {
	x, y := 1, 2
	f := func() int { x = 10; y = 20; return 5 }
	x, y = y, f()
	return x*100 + y // {205, 2005}
}
func blankBesidePlanned() int { xs := []int{1}; _, xs[0] = wit(1), 2; return xs[0] }
func commaOkClosedChan() int {
	ch := make(chan int, 1)
	close(ch)
	xs := []int{0, 0}
	f := func() int { return 1 }
	var ok bool
	xs[f()], ok = <-ch
	if ok {
		return 1
	}
	return xs[1] + 100 // 100
}
func commaOkNilIface() int {
	var iv any
	xs := []int{5, 5}
	f := func() int { return 1 }
	var ok bool
	xs[f()], ok = iv.(int)
	if ok {
		return 1
	}
	return xs[1] + 100 // 100
}
func commaOkMapVsWriter() int {
	m := map[int]int{1: 1}
	xs := []int{0, 0}
	f := func() int { delete(m, 1); return 0 }
	var ok bool
	xs[f()], ok = m[1]
	if ok {
		return xs[0] + 10
	}
	return xs[0] // {11, 0}
}
func globalBesidePlanned() int { xs := []int{0}; f := func() int { return 3 }; G, xs[0] = 1, f(); return G*10 + xs[0] } // 13
func multiCallWritesPlain() int {
	x := 0
	xs := []int{1}
	two := func() (int, int) { x = 5; return 1, 9 }
	x, xs[0] = two()
	return x*10 + xs[0] // 19
}

// map-element targets in a multi-target assignment: the legacy emitter QUARANTINES them («map element as assignment
// target outside a single assignment»); the E5b grammar admits them as planned targets when the sweep is observable.
func nilMapCapturedKeyTarget() int {
	var m map[int]int
	k := 1
	y := 0
	f := func() int { k = 2; return wit(1) }
	m[k], y = 1, f()
	return y
}
func mapCapturedKeyTargetVsWriter() int {
	m := map[int]int{}
	k := 1
	y := 0
	f := func() int { k = 2; return 9 }
	m[k], y = 7, f()
	return m[1]*100 + m[2]*10 + y // {709, 79}
}
func boolMapCommaOk() int {
	mb := map[int]bool{1: true}
	xs := []bool{false, false}
	f := func() int { delete(mb, 1); return 0 }
	var ok bool
	xs[f()], ok = mb[1]
	if xs[0] && ok {
		return 11
	}
	return 0 // {11, 0}
}

func chanBoolCommaOk() int {
	cb := make(chan bool, 1)
	cb <- true
	xs := []bool{false, false}
	f := func() int { return 1 }
	var ok bool
	xs[f()], ok = <-cb
	if xs[1] && ok {
		return 11
	}
	return 0
}

func defineRecvTuple() int {
	ch := make(chan int, 1)
	ch <- 3
	k := 1
	f := func() int { k = 2; return 5 }
	x, y := <-ch, f()+k
	return x*100 + y // {306, 307}
}
