package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line): index and slice expressions on operands the corpus
// did not hold — nested slices and maps, call results, slice expressions,
// parenthesised dereferences, string slices, slice and array literals, a
// literal's array field, constant and len-relative indexes, a defined-int
// index; slices of a constant string, of a slice, of a call result, of a
// nested element, of a map element, of a dereference, the tail / empty /
// at-len / three-zero bounds; a two-argument explicit instantiation in
// value position; an index and a slice as a defer argument and in a
// condition. Expected = gc go1.26.5.

var calls int

type di int

type holder struct{ arr [3]int }

func mkSlice() []int { return []int{4, 5, 6} }

func pairG[A any, B any](a A, b B) int { return len([]any{a, b}) }

func takeInt(x int) { calls += x }

func takeSlice(s []int) { calls += len(s) }

// B5.2
func indexNestedSlice() int {
	ss := [][]int{{1, 2}, {3, 4}}
	return ss[1][0]*10 + ss[0][1] // 32
}

func indexNestedMap() int {
	m := map[string]map[int]int{"a": {1: 7}}
	ms := map[string][]int{"b": {8, 9}}
	return m["a"][1]*10 + ms["b"][1] // 79
}

func indexCallResult() int {
	return mkSlice()[1] // 5
}

func indexOfSliceExpr() int {
	s := []int{1, 2, 3, 4}
	return s[1:3][1]*10 + s[2:][0] // 33
}

func indexDerefParen() int {
	a := [2]int{5, 6}
	p := &a
	s := []int{7}
	ps := &s
	return (*p)[1]*10 + (*ps)[0] // 67
}

func indexStringSlice() int {
	s := "hello"
	return int(s[1:][0]) + int(s[1:3][1]) // 'e' + 'l' = 101 + 108 = 209
}

func indexSliceLiteral() int {
	return []int{1, 2, 3}[1] // 2
}

func indexArrayLiteral() int {
	return [3]int{1, 2, 3}[2] // 3
}

func indexLiteralFieldArray() int {
	return holder{arr: [3]int{4, 5, 6}}.arr[0] // 4
}

func indexConstExpr() int {
	a := [4]int{1, 2, 3, 4}
	return a[1+1]*10 + a[len(a)-1] // 34
}

func indexLenMinusOne() int {
	s := []int{1, 2, 3}
	return s[len(s)-1] // 3
}

func indexDefinedInt() int {
	s := []int{1, 2, 3}
	var i di = 2
	return s[i] // 3
}

// B5.3
func instantiationTwoArgsValue() int {
	f := pairG[int, string]
	return f(1, "a") // 2
}

// B6.2
func sliceStringConst() int {
	s := "hello"[1:3]
	return len(s)*100 + int(s[0]) // 200 + 101 = 301
}

func sliceOfSlice() int {
	s := []int{1, 2, 3, 4, 5}
	t := s[1:4][1:]
	return len(t)*10 + t[0] // 23
}

func sliceCallResult() int {
	t := mkSlice()[1:]
	return len(t)*10 + t[0] // 25
}

func sliceNestedElem() int {
	ss := [][]int{{1, 2, 3}}
	t := ss[0][1:]
	return len(t)*10 + t[0] // 22
}

func sliceMapElem() int {
	m := map[string][]int{"a": {1, 2, 3}}
	t := m["a"][:2]
	return len(t)*10 + t[1] // 22
}

func sliceDerefParen() int {
	a := [3]int{1, 2, 3}
	p := &a
	t := (*p)[1:]
	return len(t)*10 + t[0] // 22
}

func sliceTail() int {
	s := "abc"
	return int(s[len(s)-1:][0]) // 99
}

func sliceEmptyPrefix() int {
	s := []int{1, 2}
	return len(s[:0])*10 + cap(s[:0]) // 2
}

func sliceAtLen() int {
	s := []int{1, 2}
	return len(s[len(s):])*10 + cap(s[len(s):]) // 0
}

func sliceThreeZero() int {
	s := []int{1, 2}
	t := s[0:0:0]
	return len(t)*10 + cap(t) // 0
}

// B5.5 / B6.3
func indexDeferArg() int {
	calls = 0
	s := []int{1, 2, 3}
	func() {
		defer takeInt(s[1])
		s[1] = 100 // the deferred argument was evaluated at the defer
	}()
	return calls // 2
}

func indexCond() int {
	s := []int{0, 5}
	r := 0
	if s[1] > s[0] {
		r = 1
	}
	return r // 1
}

func sliceDeferArg() int {
	calls = 0
	s := []int{1, 2, 3}
	func() { defer takeSlice(s[1:]) }()
	return calls // 2
}

func sliceLenCond() int {
	s := []int{1, 2, 3}
	r := 0
	if len(s[1:]) > 1 {
		r = 1
	}
	return r // 1
}

func main() {
	println(indexNestedSlice(), indexNestedMap(), indexCallResult(), indexOfSliceExpr(), indexDerefParen(),
		indexStringSlice(), indexSliceLiteral(), indexArrayLiteral(), indexLiteralFieldArray(), indexConstExpr(),
		indexLenMinusOne(), indexDefinedInt(), instantiationTwoArgsValue(), sliceStringConst(), sliceOfSlice(),
		sliceCallResult(), sliceNestedElem(), sliceMapElem(), sliceDerefParen(), sliceTail(), sliceEmptyPrefix(),
		sliceAtLen(), sliceThreeZero(), indexDeferArg(), indexCond(), sliceDeferArg(), sliceLenCond())
}
