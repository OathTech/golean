package main

// Sweep S8 (spec-unsequenced order realized as one member; the defect-neighbourhood
// campaign, docs/2026-10-27_defect-neighbourhood-campaign.md §4, lane sweep/s8-unseq,
// 2026-10-27): operand KIND × a sibling call that mutates what the operand reads, in
// binary position, sequential. spec#Order_of_evaluation orders only calls, receives and
// logical operations against each other, so a non-call operand's read may come before or
// after the sibling call; the machine's `unseq` graph admits both (membership rows, the
// `unseqNext` pick) and gc realizes ONE (late = call-first for a plain read, an index, a
// field, a deref, a numeric conversion, a division, a shift, a string byte read, a map
// read; early = operand-first for a type assertion, a slice expression, a `[]rune`
// conversion). Where the grammar declines the sweep (an array operand, a defined or float
// result type, `len` of a channel or map — an E1 participant, an interface comparison, a
// box) the legacy path realizes call-first alone and gc agrees: strict rows.

type T struct{ n int }

type MyInt int

type R struct{ f int }

func sinkAny(a any, k int) int { return a.(int) + k }

func f1(a int) int { return a + 100 }

func f2(a int) int { return a + 200 }

// --- membership rows: the grammar admits the sweep, both orders are members ---

func localVar() int {
	x := 1
	setX := func() int { x = 100; return 10 }
	return x + setX()
}

func sliceBaseRebound() int {
	s := []int{1, 2}
	t := []int{50, 60}
	rebind := func() int { s = t; return 10 }
	return s[0] + rebind()
}

func mapKeyMutated() int {
	m := map[int]int{1: 1, 2: 2}
	k := 1
	set := func() int { k = 2; return 10 }
	return m[k] + set()
}

func mapRebound() int {
	m1 := map[int]int{1: 1}
	m2 := map[int]int{1: 5}
	m := m1
	reb := func() int { m = m2; return 10 }
	return m[1] + reb()
}

func mapEntryDeleted() int {
	m := map[int]int{1: 1}
	del := func() int { delete(m, 1); return 10 }
	return m[1] + del()
}

func ptrFieldRedirected() int {
	a := &T{1}
	b := &T{5}
	p := a
	red := func() int { p = b; return 10 }
	return p.n + red()
}

func structValueField() int {
	v := T{1}
	set := func() int { v.n = 5; return 10 }
	return v.n + set()
}

func int64Conversion() int64 {
	x := 1
	set := func() int64 { x = 5; return 10 }
	return int64(x) + set()
}

func runesConversion() int {
	s := "ab"
	set := func() int { s = "zz"; return 1 }
	return int([]rune(s)[0]) + set()
}

func division() int {
	d := 2
	set := func() int { d = 4; return 1 }
	return 100/d + set()
}

func modulo() int {
	d := 3
	set := func() int { d = 7; return 1 }
	return 100%d + set()
}

func shift() int {
	sh := 1
	set := func() int { sh = 3; return 1 }
	return 1<<sh + set()
}

func assertionReboxed() int {
	var iv any = 3
	set := func() int { iv = 10; return 1 }
	return iv.(int) + set()
}

func sliceHighBound() int {
	s := []int{1, 2, 3}
	j := 1
	set := func() int { j = 9; return 10 }
	return s[:j][0] + set()
}

func stringReassigned() int {
	str := "ab"
	set := func() int { str = "zz"; return 1 }
	return int(str[0]) + set()
}

func unaryMinus() int {
	x := 1
	set := func() int { x = 100; return 10 }
	return -x + set()
}

func calleeVarVsArgCall() int {
	fn := f1
	set := func() int { fn = f2; return 1 }
	return fn(set())
}

func derefNilAfterCall() int {
	x := 7
	p := &x
	nilp := func() int { p = nil; return 1 }
	return *p + nilp()
}

func nestedIndex() int {
	s := []int{10, 20, 30}
	t := []int{0, 1, 2}
	i := 0
	set := func() int { i = 2; return 1 }
	return s[t[i]] + set()
}

func indexThenField() int {
	a := []R{{1}, {5}}
	i := 0
	set := func() int { i = 1; return 10 }
	return a[i].f + set()
}

// --- strict rows: the grammar declines the sweep, the legacy call-first order is gc's ---

func arrayElem() int {
	arr := [2]int{1, 2}
	i := 0
	set := func() int { i = 1; return 10 }
	return arr[i] + set()
}

func ptrArrayElem() int {
	a1 := [2]int{1, 2}
	a2 := [2]int{5, 6}
	pa := &a1
	red := func() int { pa = &a2; return 10 }
	return pa[0] + red()
}

func definedConversion() MyInt {
	x := 1
	set := func() MyInt { x = 5; return 10 }
	return MyInt(x) + set()
}

func floatConversion() float64 {
	x := 1
	set := func() float64 { x = 5; return 10 }
	return float64(x) + set()
}

func lenChanVsSend() int {
	ch := make(chan int, 3)
	send := func() int { ch <- 1; return 10 }
	return len(ch) + send()
}

func lenMapVsInsert() int {
	m := map[int]int{}
	ins := func() int { m[1] = 1; return 10 }
	return len(m) + ins()
}

func capVsGrow() int {
	s := make([]int, 1, 2)
	grow := func() int { s = make([]int, 1, 4); return 0 }
	return cap(s) + grow()
}

func ifaceCompareValue() bool {
	var iv any = 1
	var jv any = 1
	set := func() int { iv = 2; return 10 }
	return (iv == jv) == (set() > 0)
}

func boxAnyVsWrite() int {
	x := 1
	set := func() int { x = 5; return 10 }
	return sinkAny(any(x), set())
}
