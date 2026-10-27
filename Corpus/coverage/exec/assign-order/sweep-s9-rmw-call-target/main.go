// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// Read-modify-write targets (op=, ++/--) whose ADDRESS computation contains a call —
// BUG-140's site (emitReadWriteTargetPhase1 binds an effectful lvalue's address once): a
// call index, a call base, a deref of a call, a field through a call, nested forms, every
// compound operator, a parenthesised target, a package-level slice, in a closure and in a
// generic function. The map-key cell (m[f()] op= v) is maps/compound-assign-eval-once.

package main

var cnt int

func idx() int { cnt++; return 1 }

func val() int { cnt++; return 5 }

type pt struct {
	x   int
	arr [3]int
	n   int
}

var gslice = []int{10, 20, 30}

func sliceCallIndex() int {
	cnt = 0
	s := []int{10, 20, 30}
	s[idx()] += 1
	return cnt*100 + s[1]
}

func sliceCallBase() int {
	cnt = 0
	s := []int{10, 20, 30}
	fs := func() []int { cnt++; return s }
	fs()[1] += 1
	return cnt*100 + s[1]
}

func arrayCallIndex() int {
	cnt = 0
	arr := [3]int{10, 20, 30}
	arr[idx()]++
	return cnt*100 + arr[1]
}


func mapCallBase() int {
	cnt = 0
	m := map[int]int{1: 20}
	fm := func() map[int]int { cnt++; return m }
	fm()[1]++
	return cnt*100 + m[1]
}

func derefCall() int {
	cnt = 0
	x := 20
	pf := func() *int { cnt++; return &x }
	*pf() += 1
	return cnt*100 + x
}

func indexCallThenField() int {
	cnt = 0
	s := []pt{{x: 10}, {x: 20}}
	s[idx()].x += 1
	return cnt*100 + s[1].x
}

func ptrFieldArrayCallIndex() int {
	cnt = 0
	p := &pt{arr: [3]int{10, 20, 30}}
	pf := func() *pt { cnt++; return p }
	pf().arr[idx()] += 1
	return cnt*100 + p.arr[1]
}

func indexCallRhsCall() int {
	cnt = 0
	s := []int{10, 20, 30}
	s[idx()] += val()
	return cnt*100 + s[1]
}

func otherOps() int {
	cnt = 0
	s := []int{7, 20, 30}
	s[idx()] <<= 1 // 40
	s[idx()] /= 4  // 10
	s[idx()] %= 7  // 3
	s[idx()] &^= 1 // 2
	s[idx()]--     // 1
	s[idx()] *= 9  // 9
	return cnt*100 + s[1]
}

func parenTarget() int {
	cnt = 0
	s := []int{10, 20, 30}
	(s[idx()]) += 1
	return cnt*100 + s[1]
}

func ptrArrayCallBaseCallIndex() int {
	cnt = 0
	arr := [3]int{10, 20, 30}
	pa := func() *[3]int { cnt++; return &arr }
	pa()[idx()]++
	return cnt*100 + arr[1]
}

func threeCalls() int {
	cnt = 0
	s := []int{10, 20, 30}
	fs := func() []int { cnt++; return s }
	fs()[idx()] += val()
	return cnt*100 + s[1]
}

func twoDim() int {
	cnt = 0
	s := [][]int{{1, 2}, {10, 20}}
	s[idx()][idx()] += 1
	return cnt*100 + s[1][1]
}

func globalSliceCallIndex() int {
	cnt = 0
	gslice[1] = 20
	gslice[idx()] += 1
	return cnt*100 + gslice[1]
}

func ptrSliceCallIndexField() int {
	cnt = 0
	ps := []*pt{{n: 10}, {n: 20}}
	ps[idx()].n++
	return cnt*100 + ps[1].n
}

type number interface{ ~int | ~int64 }

func rmwGeneric[T number](s []T, d T) T {
	s[idx()] += d
	return s[1]
}

func incGeneric[T number](s []T) T {
	s[idx()]++
	return s[1]
}

func closureRmw() int {
	cnt = 0
	s := []int{10, 20, 30}
	inner := func() {
		s[idx()] += 1
		s[idx()]++
	}
	inner()
	return cnt*100 + s[1]
}

func genericRmw() int {
	cnt = 0
	s := []int{10, 20, 30}
	v := rmwGeneric(s, 1)
	w := incGeneric(s)
	return cnt*100 + v + w - 20
}

func genericRmwInt64() int {
	cnt = 0
	s := []int64{10, 20, 30}
	v := rmwGeneric[int64](s, 1)
	return cnt*100 + int(v)
}

func main() {
	sliceCallIndex()
	sliceCallBase()
	arrayCallIndex()
	mapCallBase()
	derefCall()
	indexCallThenField()
	ptrFieldArrayCallIndex()
	indexCallRhsCall()
	otherOps()
	parenTarget()
	ptrArrayCallBaseCallIndex()
	threeCalls()
	twoDim()
	globalSliceCallIndex()
	ptrSliceCallIndexField()
	closureRmw()
	genericRmw()
	genericRmwInt64()
}
