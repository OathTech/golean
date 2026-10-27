package main

// Sweep S8 (lane sweep/s8-unseq, 2026-10-27): positions × representative operand kinds
// (V = a captured local read, I = a slice index with the index mutated, D = a deref with
// the pointer redirected, A = a type assertion with the interface re-boxed, C =
// `[]byte(s)[0]` with s reassigned) beside a sibling call that mutates what the operand
// reads: call arguments, composite-literal elements, index base vs index call, the send
// statement, assignment target operands vs the RHS call, tuple RHS, return lists,
// if/for/switch conditions, the operand RIGHT of the call, defer arguments, var specs, a
// pointer receiver variable vs the argument call, compound loads. Membership rows where
// the grammar admits the sweep; strict rows where the legacy call-first order is gc's.
// The EARLY kinds at the declined positions are the finding rows of
// evalorder/sweep-s8-early-kinds-legacy (BUG-310).

type T struct{ n int }

type R2 struct{ a, b int }

type PA struct{ arr []int }

type G struct{ n int }

func (g *G) Get(k int) int { return g.n*100 + k }

func sink(a, b int) int { return a*100 + b }

func sinkD(r *int, a, b int) { *r = a*100 + b }

// --- call arguments ---

func argLocalVar() int {
	x := 1
	set := func() int { x = 5; return 10 }
	return sink(x, set())
}

func argDeref() int {
	x, y := 1, 5
	p := &x
	red := func() int { p = &y; return 10 }
	return sink(*p, red())
}

func argAssertion() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	return sink(iv.(int), set())
}

func argBytesConv() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return sink(int([]byte(s)[0]), set())
}

func argStringSlice() int {
	str := "ab"
	f := func() int { str = "zz"; return 1 }
	return sink(int(str[1:][0]), f())
}

// --- composite-literal elements ---

func sliceLitDeref() int {
	x, y := 1, 5
	p := &x
	red := func() int { p = &y; return 10 }
	l := []int{*p, red()}
	return l[0]*100 + l[1]
}

func sliceLitAssertion() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	l := []int{iv.(int), set()}
	return l[0]*100 + l[1]
}

func sliceLitBytesConv() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	l := []int{int([]byte(s)[0]), set()}
	return l[0]*100 + l[1]
}

func structLitIndex() int {
	s := []int{1, 5}
	i := 0
	set := func() int { i = 1; return 10 }
	v := R2{a: s[i], b: set()}
	return v.a*100 + v.b
}

func mapLitAssertionKey() int {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	m := map[int]int{iv.(int): set()}
	return m[1]*100 + m[5]
}

func arrayLitLocalVar() int {
	x := 1
	set := func() int { x = 5; return 10 }
	a := [2]int{x, set()}
	return a[0]*100 + a[1]
}

// --- index base vs the index call ---

func indexBaseSlice() int {
	s := []int{1, 2}
	t := []int{5, 6}
	f := func() int { s = t; return 1 }
	return s[f()]
}

func indexBaseMap() int {
	m1 := map[int]int{1: 2}
	m2 := map[int]int{1: 6}
	m := m1
	f := func() int { m = m2; return 1 }
	return m[f()]
}

func indexBasePtrField() int {
	a := &PA{[]int{1, 2}}
	b := &PA{[]int{5, 6}}
	p := a
	f := func() int { p = b; return 1 }
	return p.arr[f()]
}

func indexBaseNested() int {
	s := [][]int{{1, 2}, {5, 6}}
	i := 0
	f := func() int { i = 1; return 1 }
	return s[i][f()]
}

// --- the send statement: the channel operand read vs the value call that rebinds it ---

func sendChanVsValueCall() int {
	ch1 := make(chan int, 1)
	ch2 := make(chan int, 1)
	ch := ch1
	f := func() int { ch = ch2; return 7 }
	ch <- f()
	return len(ch1)*10 + len(ch2)
}

// --- assignment target operands vs the RHS call ---

func targetMapKey() int {
	m := map[int]int{}
	k := 1
	f := func() int { k = 5; return 7 }
	m[k] = f()
	return m[1]*10 + m[5]
}

func targetPtrField() int {
	a := &T{}
	b := &T{}
	p := a
	f := func() int { p = b; return 7 }
	p.n = f()
	return a.n*10 + b.n
}

func targetArrayElem() int {
	arr := [2]int{}
	i := 0
	f := func() int { i = 1; return 7 }
	arr[i] = f()
	return arr[0]*10 + arr[1]
}

func targetAssertionIndex() int {
	x := []int{0, 0, 0, 0, 0, 0}
	var iv any = 1
	f := func() int { iv = 5; return 7 }
	x[iv.(int)] = f()
	return x[1]*10 + x[5]
}

func tupleAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 10 }
	a, b := iv.(int), f()
	return a*100 + b
}

func tupleDeref() int {
	x, y := 1, 5
	p := &x
	f := func() int { p = &y; return 10 }
	a, b := *p, f()
	return a*100 + b
}

// --- return lists ---

func retAssertionInner() (int, int) {
	var iv any = 1
	set := func() int { iv = 5; return 10 }
	return iv.(int), set()
}

func returnAssertion() int {
	a, b := retAssertionInner()
	return a*100 + b
}

func retDerefInner() (int, int) {
	x, y := 1, 5
	p := &x
	red := func() int { p = &y; return 10 }
	return *p, red()
}

func returnDeref() int {
	a, b := retDerefInner()
	return a*100 + b
}

func returnSliceExpr() int {
	a, b := func() (int, int) {
		s := []int{1, 5}
		j := 1
		f := func() int { j = 9; return 10 }
		return s[j:][0], f()
	}()
	return a*100 + b
}

// --- conditions (statement forms the grammar declines: legacy call-first = gc) ---

func ifCondLocalVar() int {
	x := 1
	f := func() int { x = 5; return 3 }
	if x > f() {
		return 1
	}
	return 0
}

func ifCondIndex() int {
	s := []int{1, 5}
	i := 0
	f := func() int { i = 1; return 3 }
	if s[i] > f() {
		return 1
	}
	return 0
}

func forCondLocalVar() int {
	x := 1
	f := func() int { x = 5; return 3 }
	n := 0
	for x < f() {
		n++
		x = 10
	}
	return n
}

func switchTagLocalVar() int {
	x := 1
	f := func() int { x = 5; return 5 }
	switch x {
	case f():
		return 1
	}
	return 0
}

func switchTagAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 5 }
	switch iv.(int) {
	case f():
		return 1
	}
	return 0
}

func switchCaseIndex() int {
	s := []int{1, 5}
	i := 0
	f := func() int { i = 1; return 3 }
	switch {
	case s[i] > f():
		return 1
	}
	return 0
}

// --- the operand RIGHT of the call ---

func rightLocalVar() int {
	x := 1
	f := func() int { x = 5; return 10 }
	return f() + x
}

func rightAssertion() int {
	var iv any = 1
	f := func() int { iv = 5; return 10 }
	return f() + iv.(int)
}

func rightBytesConv() int {
	s := "ab"
	f := func() int { s = "zz"; return 1 }
	return f() + int([]byte(s)[0])
}

// --- defer arguments ---

func deferArgBytesConv() int {
	r := 0
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	func() {
		defer sinkD(&r, int([]byte(s)[0]), set())
	}()
	return r
}

func deferArgLocalVar() int {
	r := 0
	x := 1
	set := func() int { x = 5; return 10 }
	func() {
		defer sinkD(&r, x, set())
	}()
	return r
}

// --- var spec ---

func varSpecLocalVar() int {
	x := 1
	set := func() int { x = 5; return 10 }
	var v = x + set()
	return v
}

// --- the receiver pointer variable vs the argument call that redirects it ---

func receiverVarVsArgCall() int {
	a := &G{1}
	b := &G{5}
	p := a
	red := func() int { p = b; return 10 }
	return p.Get(red())
}

// --- compound loads ---

func compoundLocalVar() int {
	x := 1
	f := func() int { x = 5; return 10 }
	x += f()
	return x
}

func compoundArrayElem() int {
	arr := [2]int{1, 5}
	i := 0
	f := func() int { i = 1; return 10 }
	arr[i] += f()
	return arr[0]*100 + arr[1]
}

func compoundString() string {
	str := "a"
	f := func() string { str = "z"; return "b" }
	str += f()
	return str
}
