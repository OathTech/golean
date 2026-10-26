package main

// S4 sweep (lane sweep/s4-identity, 2026-10-26): BUG-139's shape — a
// variadic call with NO variadic operands passes `nil`
// (spec#Passing_arguments_to_..._parameters), the explicit empty spread a
// non-nil empty slice — at
// every call route beside variadic/no-args-vs-empty-spread: value and
// pointer receivers, interface dispatch, named / closure / typed function
// values, method values, method expressions, `go` and `defer` statements
// (a named function and a func literal), a generic instantiation, a fixed
// parameter before the pack, tuple forwarding that fills ONLY the fixed
// parameters (the tuple packing site's nil branch), the element kinds
// `...any` / `...string` / `...*int` / `...[]int`, and the pack observed by
// len / cap / append / range. gc agrees on every row (probed both sides
// first; .tmp/probes/va-*). Scores: 1 = nil pack, the empty-spread control
// at the next digit (0: non-nil, as gc).

type box struct{ n int }

func (b box) v(xs ...int) bool   { return xs == nil }
func (b *box) pv(xs ...int) bool { return xs == nil }

type nilCheck interface{ V(xs ...int) bool }
type impl struct{}

func (impl) V(xs ...int) bool { return xs == nil }

func named(xs ...int) bool           { return xs == nil }
func gnil[T any](xs ...T) bool       { return xs == nil }
func fixedThen(head int, xs ...int) bool { return xs == nil }
func twoFixed(a, b int, xs ...int) bool { return xs == nil }
func fixedRes(a int, xs ...int) (bool, int) { return xs == nil, len(xs) }
func one() int        { return 1 }
func two() (int, int) { return 1, 2 }
func anyv(xs ...any) bool  { return xs == nil }
func strv(xs ...string) bool { return xs == nil }
func ptrv(xs ...*int) bool { return xs == nil }
func slv(xs ...[]int) bool { return xs == nil }
func sendNil(ch chan bool, xs ...int) { ch <- xs == nil }

func bit(b bool, w int) int {
	if b {
		return w
	}
	return 0
}

func vaValueReceiver() int {
	b := box{1}
	p := &b
	return bit(b.v(), 1) + bit(b.v([]int{}...), 10) + bit(p.v(), 100) + bit(p.v(nil...), 1000)
}

func vaPointerReceiver() int {
	b := box{1}
	p := &b
	return bit(p.pv(), 1) + bit(p.pv([]int{}...), 10) + bit(b.pv(), 100) + bit(b.pv(1), 1000)
}

func vaIfaceDispatch() int {
	var i nilCheck = impl{}
	return bit(i.V(), 1) + bit(i.V([]int{}...), 10) + bit(i.V(nil...), 100) + bit(i.V(1), 1000)
}

func vaFuncValues() int {
	f := named
	g := func(xs ...int) bool { return xs == nil }
	var h func(...int) bool = named
	return bit(f(), 1) + bit(f([]int{}...), 10) + bit(g(), 100) + bit(g(1), 1000) + bit(h(), 10000)
}

func vaMethodValues() int {
	b := box{1}
	f := b.v
	g := b.pv
	return bit(f(), 1) + bit(f([]int{}...), 10) + bit(g(), 100) + bit(g(1), 1000)
}

func vaMethodExprs() int {
	b := box{1}
	return bit(box.v(b), 1) + bit(box.v(b, []int{}...), 10) + bit((*box).pv(&b), 100) + bit((*box).pv(&b, 1), 1000)
}

func vaGoStmt() int {
	ch := make(chan bool, 1)
	go sendNil(ch)
	s := bit(<-ch, 1)
	go sendNil(ch, []int{}...)
	return s + bit(<-ch, 10)
}

func vaDeferStmt() int {
	s := 0
	rec := func(w int, xs ...int) { s += bit(xs == nil, w) }
	func() {
		defer rec(1)
		defer rec(10, []int{}...)
		defer func(xs ...int) { s += bit(xs == nil, 100) }()
	}()
	return s
}

func vaGeneric() int {
	return bit(gnil[int](), 1) + bit(gnil[int]([]int{}...), 10) + bit(gnil[string](), 100) +
		bit(gnil(1), 1000) + bit(gnil[int](nil...), 10000)
}

func vaFixedPlusZero() int {
	return bit(fixedThen(1), 1) + bit(fixedThen(1, []int{}...), 10) + bit(fixedThen(1, 2), 100) +
		bit(fixedThen(1, nil...), 1000)
}

// Tuple forwarding that fills ONLY the fixed parameters: the pack is nil (gc 11 + 1000 + 0 len).
func vaTupleFixedOnly() int {
	ok, n := fixedRes(one())
	return bit(fixedThen(one()), 1) + bit(twoFixed(two()), 10) + bit(fixedThen(two()), 100) +
		bit(ok, 1000) + n*10000
}

func vaElemKinds() int {
	return bit(anyv(), 1) + bit(strv(), 10) + bit(ptrv(), 100) + bit(slv(), 1000) +
		bit(anyv(nil), 10000) + bit(ptrv(nil), 100000) + bit(slv(nil), 1000000)
}

func obs(xs ...int) int {
	ys := append(xs, 1)
	zs := append(xs)
	n := 0
	for range xs {
		n += 1000
	}
	return bit(xs == nil, 1) + bit(zs == nil, 10) + bit(ys == nil, 100) + len(xs)*10000 +
		cap(xs)*100000 + len(ys)*1000000 + n
}

// The nil pack through len / cap / append / range: nil in, appended non-nil,
// `append(xs)` keeps nil-ness (gc 1000011 / 1000000 / 1000011).
func vaLenCapAppend() int {
	return obs() + obs([]int{}...)*0 + bit(obs([]int{}...) == 1000000, 20000000) + bit(obs(nil...) == 1000011, 40000000)
}

func main() {
	println(vaValueReceiver(), vaPointerReceiver(), vaIfaceDispatch(), vaFuncValues(), vaMethodValues(),
		vaMethodExprs(), vaGoStmt(), vaDeferStmt(), vaGeneric(), vaFixedPlusZero(), vaTupleFixedOnly(),
		vaElemKinds(), vaLenCapAppend())
}
