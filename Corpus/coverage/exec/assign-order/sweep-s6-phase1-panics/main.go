package main

// S6 sweep, group N: a PHASE-1 panic (a target operand's or a right-hand
// operand's, memory-reading so gc holds the store back — L-016) precedes
// every phase-2 store: under recover no target holds its new value.

type nT struct{ f int }

func nRecover(fn func()) (hit int) {
	defer func() {
		if recover() != nil {
			hit = 1
		}
	}()
	fn()
	return 0
}

// N.1: the second TARGET's index operand panics in phase 1 — x unstored.
func nTargetOperandPanic() int {
	x := 0
	a := []int{0}
	b := []int{0}
	hit := nRecover(func() { x, a[b[9]] = 1, 2 })
	return hit*100 + x*5
}

// N.2: a right-hand index read panics — x unstored.
func nRhsIndexPanic() int {
	x := 0
	s := []int{0}
	y := 0
	hit := nRecover(func() { x, y = 1, s[9] })
	return hit*100 + x*5 + y
}

// N.3: a right-hand nil dereference — x unstored (plain locals).
func nRhsNilDeref() int {
	x := 0
	var np *int
	y := 0
	hit := nRecover(func() { x, y = 1, *np })
	return hit*100 + x*5 + y
}

// N.4: a map-element first target against a right-hand index panic — no entry.
func nMapTargetRhsPanic() int {
	m := map[int]int{}
	s := []int{0}
	y := 0
	hit := nRecover(func() { m[1], y = 1, s[9] })
	return hit*100 + len(m)*5 + y
}

// N.5: a deref first target against a right-hand index panic — *p unchanged.
func nDerefTargetRhsPanic() int {
	v := 3
	p := &v
	s := []int{0}
	y := 0
	hit := nRecover(func() { *p, y = 1, s[9] })
	return hit*100 + v + y
}

// N.6: a phase-1 right-hand index panic (length 1) beats the second target's
// phase-2 bounds check (length 2).
func nPhase1BeatsPhase2() int {
	x := 0
	s := []int{0}
	a := []int{0, 0}
	x, a[9] = s[9], 2
	return x
}

// N.7: x captured by the deferred closure (the E5 observation channel), the
// later operand a memory-reading panic: held back on both sides.
func nCapturedRhsIndexPanic() (r int) {
	x := 58
	s := []int{0}
	var y int
	defer func() {
		recover()
		r = x
	}()
	x, y = 29, s[9]
	_ = y
	return 0
}

// N.8: in a generic function.
func nGenRhsPanic[T any](s []T, v T) (x int) {
	defer func() {
		if recover() != nil {
			x += 100
		}
	}()
	var y T
	x, y = 1, s[9]
	_ = y
	return
}

func nGenericRhsIndexPanic() int { return nGenRhsPanic([]int{0}, 5) }

// N.11: a map target's KEY operand panics in phase 1 — x unstored, no entry.
func nMapKeyOperandPanic() int {
	x := 0
	m := map[int]int{}
	k := []int{0}
	hit := nRecover(func() { x, m[k[9]] = 1, 2 })
	return hit*100 + x*5 + len(m)
}

// N.12: pp[9].f with pp a []*T — the element read is a VALUE step (phase 1),
// unlike a []T chain whose index is address formation (phase 2, BUG-033).
func nPtrSliceIndexGetPhase1() int {
	x := 0
	pp := []*nT{}
	hit := nRecover(func() { x, pp[9].f = 1, 2 })
	return hit*100 + x*5
}

func main() {
	nTargetOperandPanic()
}
