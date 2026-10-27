// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Composite-literal elements with calls — map keys and values, slice / array / [...]array
// elements, &T{} and the elided &T, nested literals, a map of slice literals, duplicate
// run-time keys (both evaluated, last wins), an indexed slice element, an embedded field,
// in a closure and in a generic function — each operand exactly once.

package main

var cnt int

func f() int { cnt++; return 1 }
func g() int { cnt++; return 2 }
func h() int { cnt++; return 3 }
func k() int { cnt++; return 4 }

type Inner struct{ a int }
type S struct {
	in Inner
	b  int
}
type Outer struct {
	Inner
	c int
}
type P struct{ v int }

func mapLitCalls() int {
	cnt = 0
	m := map[int]int{f(): g(), h(): k()}
	return cnt*100 + len(m)*10 + m[1] + m[3]
}

func sliceLitCalls() int {
	cnt = 0
	s := []int{f(), g()}
	return cnt*100 + s[0]*10 + s[1]
}

func arrayLitCalls() int {
	cnt = 0
	a := [3]int{f(), g(), h()}
	return cnt*100 + a[0] + a[1]*10 + a[2]
}

func ellipsisArrayLitCalls() int {
	cnt = 0
	a := [...]int{f(), g()}
	return cnt*100 + len(a)*10 + a[1]
}

func addrLitCall() int {
	cnt = 0
	p := &P{f()}
	return cnt*100 + p.v
}

func elidedAddrLitCall() int {
	cnt = 0
	ps := []*P{{f()}, {g()}}
	return cnt*100 + ps[0].v*10 + ps[1].v
}

func nestedLitCalls() int {
	cnt = 0
	s := S{Inner{f()}, g()}
	return cnt*100 + s.in.a*10 + s.b
}

func mapOfSliceLitCall() int {
	cnt = 0
	m := map[string][]int{"a": {f(), g()}}
	return cnt*100 + m["a"][0]*10 + m["a"][1]
}

func mapLitDupRuntimeKeys() int {
	cnt = 0
	m := map[int]int{f(): 10, f(): 20}
	return cnt*100 + len(m)*10 + m[1]/10
}

func indexedSliceLitCall() int {
	cnt = 0
	s := []int{2: f()}
	return cnt*100 + len(s)*10 + s[2]
}

func embeddedLitCall() int {
	cnt = 0
	o := Outer{Inner: Inner{f()}, c: g()}
	return cnt*100 + o.a*10 + o.c
}

func closureLit() int {
	cnt = 0
	r := 0
	inner := func() {
		s := []int{f(), g()}
		m := map[int]int{h(): k()}
		r = s[0] + s[1] + m[3]
	}
	inner()
	return cnt*100 + r
}

func litGeneric[T any](a, b func() T) int {
	s := []T{a(), b()}
	m := map[int]T{1: a()}
	_ = m
	return len(s)
}

func genericLit() int {
	cnt = 0
	r := litGeneric(f, g) + litGeneric(func() string { cnt++; return "" }, func() string { cnt++; return "" })
	return cnt*100 + r
}

func main() {
	mapLitCalls()
	sliceLitCalls()
	arrayLitCalls()
	ellipsisArrayLitCalls()
	addrLitCall()
	elidedAddrLitCall()
	nestedLitCalls()
	mapOfSliceLitCall()
	mapLitDupRuntimeKeys()
	indexedSliceLitCall()
	embeddedLitCall()
	closureLit()
	genericLit()
}
