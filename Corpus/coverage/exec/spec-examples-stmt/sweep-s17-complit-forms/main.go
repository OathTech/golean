package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line): composite literals at the nesting and elision shapes
// spec#Composite_literals admits that the corpus did not hold — elided
// element types inside slices, maps (value AND key), pointers, arrays of
// arrays and slices of maps; index continuation after a keyed element;
// `[...]` with keys; func-typed fields; zero-length and empty-struct
// elements; mixed `any` elements; byte / rune / string / bool / float
// elements; and literals as a condition operand, a defer argument and
// inside a closure. Expected = gc go1.26.5.

var calls int

type pt struct{ x, y int }

type inner struct{ v int }

type outer struct {
	in inner
	n  int
}

type withFn struct {
	f func(int) int
	k int
}

func take(p pt) { calls += p.x*10 + p.y }

// B1.2
func elidedStructElems() int {
	ps := []pt{{1, 2}, {3, 4}}
	return ps[0].x*1000 + ps[0].y*100 + ps[1].x*10 + ps[1].y // 1234
}

func elidedNestedSlices() int {
	ss := [][]int{{1}, {2, 3}}
	return len(ss)*100 + ss[1][1]*10 + ss[0][0] // 231
}

func elidedMapValue() int {
	m := map[string]pt{"a": {1, 2}}
	return m["a"].x*10 + m["a"].y // 12
}

func elidedMapKey() int {
	m := map[pt]string{{1, 2}: "a", {3, 4}: "bb"}
	return len(m[pt{1, 2}])*10 + len(m[pt{3, 4}]) // 12
}

func elidedPtrElems() int {
	ps := []*pt{{5, 6}, nil}
	return ps[0].x*10 + ps[0].y + len(ps)*100 // 256
}

func elidedMapPtrValue() int {
	m := map[string]*pt{"a": {7, 8}}
	return m["a"].x*10 + m["a"].y // 78
}

func elidedArrayOfArrays() int {
	aa := [2][2]int{{1}, {2, 3}}
	return aa[0][0]*1000 + aa[0][1]*100 + aa[1][0]*10 + aa[1][1] // 1023
}

func elidedArrayKey() int {
	m := map[[2]int]int{{1, 2}: 3}
	return m[[2]int{1, 2}] // 3
}

func sliceOfMaps() int {
	ms := []map[string]int{{"a": 1}, {"b": 2, "c": 3}}
	return ms[0]["a"]*100 + ms[1]["b"]*10 + ms[1]["c"] // 123
}

func nestedKeyedStruct() int {
	o := outer{in: inner{v: 4}, n: 5}
	return o.in.v*10 + o.n // 45
}

// B1.3
func keyedSliceContinuation() int {
	s := []int{3: 1, 2}
	return len(s)*100 + s[3]*10 + s[4] // 512
}

func keyedEllipsisArray() int {
	a := [...]string{2: "b", "c"}
	return len(a)*100 + len(a[0])*10 + len(a[3]) // 401
}

// B1.4
func structFuncFieldLit() int {
	w := withFn{f: func(x int) int { return x * 2 }, k: 3}
	return w.f(w.k) // 6
}

// B1.6
func zeroLenArrayLit() int {
	a := [0]int{}
	return len(a) // 0
}

func emptyStructElems() int {
	es := []struct{}{{}, {}}
	return len(es) // 2
}

func anyElemsMixed() int {
	xs := []any{1, "ab", nil, true}
	n := 0
	for _, x := range xs {
		switch v := x.(type) {
		case int:
			n += v
		case string:
			n += len(v) * 10
		case nil:
			n += 100
		case bool:
			n += 1000
		}
	}
	return n // 1121
}

// B1.7
func byteRuneElems() int {
	bs := []byte{'a', 98}
	rs := []rune{'x', 'é'}
	return int(bs[0]) + int(bs[1]) + int(rs[0]) + int(rs[1]) // 97+98+120+233 = 548
}

func stringBoolFloatElems() int {
	ss := []string{"a", "bc"}
	bs := [3]bool{true}
	fs := []float64{1.5, 2.5}
	n := len(ss[1])
	if bs[0] && !bs[1] {
		n += 10
	}
	return n + int(fs[0]+fs[1]) // 2 + 10 + 4 = 16
}

// B1.9
func litCompareCond() int {
	p := pt{1, 2}
	r := 0
	if p == (pt{1, 2}) {
		r = 1
	}
	if (pt{}) != p {
		r += 10
	}
	return r // 11
}

func litDeferArg() int {
	calls = 0
	func() { defer take(pt{1, 2}) }()
	return calls // 12
}

func litInClosure() int {
	f := func(a, b int) pt { return pt{a, b} }
	q := f(3, 4)
	return q.x*10 + q.y // 34
}

func main() {
	println(elidedStructElems(), elidedNestedSlices(), elidedMapValue(), elidedMapKey(), elidedPtrElems(),
		elidedMapPtrValue(), elidedArrayOfArrays(), elidedArrayKey(), sliceOfMaps(), nestedKeyedStruct(),
		keyedSliceContinuation(), keyedEllipsisArray(), structFuncFieldLit(), zeroLenArrayLit(), emptyStructElems(),
		anyElemsMixed(), byteRuneElems(), stringBoolFloatElems(), litCompareCond(), litDeferArg(), litInClosure())
}
