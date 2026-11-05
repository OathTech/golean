package main

import "bytes"

// S23 sweep — resource budgets (docs/defect-shapes.md; the plan
// docs/2026-10-27_defect-neighbourhood-campaign.md §4; lane sweep/s23-budgets,
// 2026-11-05): the `make` door at the element kinds, count forms and routes
// the budget rows of 2026-10-12/13/25 leave out. The three bounds in play
// (GoLean/GoCore/Machine.lean): gc's own makeslice panic first, then the count
// bound sliceCapBudget (2^23 elements), then the footprint bound
// arrayFootprintBudget (2^24 scalar leaves = count × tyLeafCount(elem)); a
// CONSTANT count is judged per declaration by the frontend
// (tools/nativefrontend/budgets.go — the subject quarantines, FAIL/frontend-export)
// and a RUN-TIME count at the make site (FAIL/lean-observation, cause
// unsupported:make-footprint-budget-runtime). gc allocates and answers on every
// row; the over-budget rows are RED BY DESIGN on the Cases lines of BUG-078
// (constant), BUG-131 (run-time) and BUG-090 (the count bound).
//
//   makeConstCapOver            — a constant CAP over the budget (len 0): the
//                                 frontend reads the cap when it is constant.
//   makeConstLenRuntimeCapOver  — a constant len beside a RUN-TIME cap over the
//                                 budget: decodes (the len drives nothing), the
//                                 make site charges the cap.
//   makeStructElemConstOver /   — a defined struct element whose fields SUM to
//   makeStructElemRuntimeOver     1024 leaves, one element past the budget, at
//   makeStructElemRuntimeAt       the constant and the run-time count; the
//                                 run-time count at exactly the budget is admitted.
//   makeNestedElemRuntimeOver   — a nested array element [32][32]byte.
//   makePointerElem             — a pointer element is ONE leaf: 2^15 pointers to
//                                 [1<<16]byte admitted (a [1<<20]byte pointee is
//                                 refused by the per-dimension bound wherever the
//                                 type appears, pointer or not — probed, not rowed).
//   makeLeafElems               — string / any / slice / func elements: one leaf
//                                 each, 2^16 of each admitted.
//   makeBigArrayElemRuntimeOver — a [1<<16]byte element (the per-dimension
//                                 maximum) at 257: one element past the budget.
//   makeArg                     — the count from the entry's --arg-int (32768
//                                 refused, 16 admitted).
//   makeInGoroutine             — the refusal raised in a child goroutine.
//   makeInDeferUnwinding        — the refusal raised in a deferred call during
//                                 unwinding, after recover.
//   makeGenericOver / Under     — through a generic mk[T] at [1024]byte.
//   makeClosure                 — through a closure.
//   makeCountBound              — make([]byte, 2^23 + 1): the count bound,
//                                 cause unsupported:slice-cap-budget (BUG-090).
//   makeImportedElemRuntime /   — a source-through imported struct element
//   makeImportedElemConst         (bytes.Buffer: 3 leaves on both sides) at
//                                 2^23: the frontend and the core count alike.
//   makeZeroSizeElem            — struct{} and [0]int elements at 2^30: gc
//                                 allocates nothing and answers; the model
//                                 would build one node per element and refuses
//                                 at the count bound (an honest gap).

type Pair struct {
	a, b [512]byte
}

func makeConstCapOver() int {
	b := make([][1024]byte, 0, 1<<15)
	return cap(b)
}

func makeConstLenRuntimeCapOver() int {
	n := 1 << 15
	b := make([][1024]byte, 1<<14, n)
	return len(b) + cap(b)
}

func makeStructElemConstOver() int {
	ps := make([]Pair, 1<<14+1)
	ps[0].a[0] = 1
	return len(ps) + int(ps[0].a[0])
}

func makeStructElemRuntimeOver() int {
	n := 1<<14 + 1
	ps := make([]Pair, n)
	ps[0].a[0] = 1
	return len(ps) + int(ps[0].a[0])
}

func makeStructElemRuntimeAt() int {
	n := 1 << 14
	ps := make([]Pair, n)
	ps[0].a[0] = 1
	ps[n-1].b[511] = 2
	return len(ps) + int(ps[0].a[0]) + int(ps[n-1].b[511])
}

func makeNestedElemRuntimeOver() int {
	n := 1<<14 + 1
	g := make([][32][32]byte, n)
	return len(g)
}

func makePointerElem() int {
	n := 1 << 15
	ps := make([]*[1 << 16]byte, n)
	nils := 0
	if ps[7] == nil {
		nils = 1
	}
	return len(ps) + nils
}

func makeLeafElems() int {
	n := 1 << 16
	ss := make([]string, n)
	as := make([]any, n)
	bs := make([][]byte, n)
	fs := make([]func() int, n)
	ss[n-1] = "z"
	return len(ss) + len(as) + len(bs) + len(fs) + len(ss[n-1]) + len(bs[3])
}

func makeBigArrayElemRuntimeOver() int {
	n := 257
	g := make([][1 << 16]byte, n)
	return len(g)
}

func makeArg(n int) int {
	b := make([][1024]byte, n)
	return len(b)
}

func makeInGoroutine() int {
	c := make(chan int)
	go func() {
		n := 1 << 15
		b := make([][1024]byte, n)
		c <- len(b)
	}()
	return <-c
}

func makeInDeferUnwinding() (r int) {
	defer func() {
		e := recover()
		n := 1 << 15
		b := make([][1024]byte, n)
		r = len(b) + len(e.(string))
	}()
	panic("go")
}

func mk[T any](n int) []T { return make([]T, n) }

func makeGenericOver() int {
	n := 1 << 15
	return len(mk[[1024]byte](n))
}

func makeGenericUnder() int {
	n := 16
	b := mk[[1024]byte](n)
	b[15][1023] = 4
	return len(b) + int(b[15][1023])
}

func makeClosure() int {
	n := 1 << 15
	f := func() [][1024]byte { return make([][1024]byte, n) }
	return len(f())
}

func makeCountBound() int {
	n := 1<<23 + 1
	b := make([]byte, n)
	return len(b)
}

func makeImportedElemRuntime() int {
	n := 1 << 23
	bs := make([]bytes.Buffer, n)
	bs[0].WriteByte('a')
	return len(bs) + bs[0].Len()
}

func makeImportedElemConst() int {
	bs := make([]bytes.Buffer, 1<<23)
	bs[0].WriteByte('a')
	return len(bs) + bs[0].Len()
}

func makeZeroSizeElem() int {
	n := 1 << 30
	a := make([]struct{}, n)
	b := make([][0]int, n)
	return len(a) + len(b)
}

func main() {
	println(makeStructElemRuntimeAt(), makePointerElem(), makeLeafElems(), makeArg(16), makeGenericUnder())
}
