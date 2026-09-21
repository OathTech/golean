package main

type V struct{ n int }

func (v V) Plus(a int) int  { return v.n + a }
func (v *V) Add(a int) int  { return v.n + a }
func (v *V) Bump() int      { v.n++; return v.n }

type U struct{ x int }
type W struct{ u U }

func rec(f func() int) (r int) {
	defer func() {
		if e := recover(); e != nil {
			r = -1
		}
	}()
	return f()
}

// (b1) <-ch + f(), f drains: spec forces the receive first -> 1 + 10 = 11; {11}
func b1RecvThenDrain() int {
	ch := make(chan int, 2)
	ch <- 1
	ch <- 2
	f := func() int { <-ch; return 10 }
	return <-ch + f()
}

// (b2) f() + <-ch, f sends on the empty channel: spec forces f first -> 10 + 5 = 15; {15}
func b2CallThenRecv() int {
	ch := make(chan int, 1)
	f := func() int { ch <- 5; return 10 }
	return f() + <-ch
}

// (b3) <-ch + g with g captured, the receive's sender goroutine writes g: sequential here, g written by f
func b3RecvVsRead() int {
	ch := make(chan int, 1)
	ch <- 1
	g := 1
	f := func() int { g = 5; return 0 }
	return <-ch*100 + g + f()
}

// (c1) value receiver on a pointer operand, the argument's call redirects p: {6, 105}
func c1ValueRecvPtrRedirect() int {
	p := &V{n: 1}
	q := &V{n: 100}
	f := func() int { p = q; return 5 }
	return p.Plus(f())
}

// (c2) nil pointer receiver made non-nil by the argument's call (value method, auto-deref): {panic, 6}
func c2NilRecvMadeNonNil() int {
	var p *V
	f := func() int { p = &V{n: 1}; return 5 }
	return p.Plus(f())
}

// (c3) pointer-receiver method reading the field; nil receiver made non-nil by the argument: {panic, 6}
func c3NilPtrRecvAdd() int {
	var p *V
	f := func() int { p = &V{n: 1}; return 5 }
	return p.Add(f())
}

// (c4) pointer receiver on an addressable variable: the address is frozen, the body reads v.n after f: {15}
func c4AddrRecvForced() int {
	v := V{n: 1}
	f := func() int { v.n = 10; return 5 }
	return v.Add(f())
}

// (d1) string(b) with b private but aliased; m mutates the bytes: spec {ab, zb}
func d1StringOfAliasedBytes() string {
	b := []byte("ab")
	c := b
	m := func() string { c[0] = 'z'; return "" }
	return string(b) + m()
}

// (d2) the same with b captured by m (address-taken): the classifier's occurrence
func d2StringOfCapturedBytes() string {
	b := []byte("ab")
	m := func() string { b[0] = 'z'; return "" }
	return string(b) + m()
}

// (d3) all-forced: x inside f's args, g writes x: {f(1)+g}
func d3AllForced() int {
	x := 1
	f := func(a int) int { return a * 10 }
	g := func() int { x = 7; return 1 }
	return f(x) + g()
}

// (d4) len(s) + f(), f appends to the captured s: gc's len is early -> 1 + 10 = 11
func d4LenVsAppend() int {
	s := []int{1}
	f := func() int { s = append(s, 2, 3); return 10 }
	return len(s) + f()
}

// (d5) BUG-113's shape with a PRIVATE test variable: the guard is spec-ordered before change(): false
func d5GuardPrivateTest() bool {
	x := false
	b := false
	change := func() int { b = true; return 0 }
	sink := func(l bool, c int) bool { return l }
	return sink(x || b, change())
}

// (k1) min(x, 100) + m(), m writes the captured x: gc's min is in the call class (early)
func k1MinVsCall() int {
	x := 1
	m := func() int { x = 50; return 1000 }
	return min(x, 100) + m()
}

// (a5) the spec's own example: x := []int{a, f()} -> [1,2] or [2,2]
func a5SpecSliceLit() int {
	a := 1
	f := func() int { a++; return a }
	x := []int{a, f()}
	return x[0]*10 + x[1]
}

// (a1) nested struct literal payload beside a call: {6, 15}
func a1NestedStructLit() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return W{u: U{x: x}}.u.x + m()
}

// (a2) interface-element slice literal payload: {6, 15}
func a2IfaceSliceLit() int {
	x := 1
	m := func() int { x = 10; return 5 }
	return []any{x}[0].(int) + m()
}

// (a3) cap(make([]int, 1, n)) + m(), m writes the captured n: make E1-ordered -> {1+5}? n=1 -> cap 1
func a3MakeCapVsCall() int {
	n := 1
	m := func() int { n = 3; return 5 }
	return cap(make([]int, 1, n)) + m()
}

// (a6) string([]rune) on aliased runes
func a6StringOfRunes() string {
	r := []rune("ab")
	c := r
	m := func() string { c[0] = 'z'; return "" }
	return string(r) + m()
}

func main() {
	println("b1", b1RecvThenDrain())
	println("b2", b2CallThenRecv())
	println("b3", b3RecvVsRead())
	println("c1", c1ValueRecvPtrRedirect())
	println("c2", rec(c2NilRecvMadeNonNil))
	println("c3", rec(c3NilPtrRecvAdd))
	println("c4", c4AddrRecvForced())
	println("d1", d1StringOfAliasedBytes())
	println("d2", d2StringOfCapturedBytes())
	println("d3", d3AllForced())
	println("d4", d4LenVsAppend())
	println("d5", d5GuardPrivateTest())
	println("k1", k1MinVsCall())
	println("a5", a5SpecSliceLit())
	println("a1", a1NestedStructLit())
	println("a2", a2IfaceSliceLit())
	println("a3", a3MakeCapVsCall())
	println("a6", a6StringOfRunes())
}
