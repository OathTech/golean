package main

// S6 sweep, group C: compound assignment and IncDec — `x op= y` is
// `x = x op (y)` with x evaluated once: the READ of x (its bounds / nil
// check) is phase 1, the store is phase 2 (a nil map's store panics after
// its read yielded the zero value). The evaluation COUNT is S9's.

type cT struct{ x int }

func cWit(n int) int { println("wit", n); return n }

// C.1: a nil map's compound store — the read yields zero, the store panics.
func cNilMapCompound() int {
	var m map[int]int
	m[1] += 5
	return 0
}

// C.2: IncDec on a nil map's element.
func cNilMapIncDec() int {
	var m map[int]int
	m[1]++
	return 0
}

// C.3: compound through a nil pointer — the read's nil check.
func cNilDerefCompound() int {
	var p *int
	*p += 1
	return 0
}

// C.4: IncDec on a field through a nil pointer.
func cNilFieldIncDec() int {
	var p *cT
	p.x++
	return 0
}

// C.5: compound on an out-of-range element — the read's bounds check.
func cOobCompound() int {
	a := []int{0}
	a[9] += 1
	return 0
}

// C.6: IncDec on a nil pointer-to-array element.
func cNilPtrArrayIncDec() int {
	var bp *[3]int
	(*bp)[0]++
	return 0
}

// C.13: a nil map's compound store with a right-hand call — the call runs
// (phase 1), then the store panics.
func cNilMapCompoundRhsCall() int {
	var m map[int]int
	m[1] += cWit(5)
	return 0
}

// C.11: compound on an index target in a generic function.
func cGenAdd[T int | float64](s []T, i int, v T) {
	s[i] += v
}

func cGenericCompound() int {
	s := []int{1, 2}
	cGenAdd(s, 1, 5)
	return s[1]
}

// C.12: compound and IncDec on CAPTURED targets inside a closure.
func cCapturedCompound() int {
	x := 1
	a := []int{1}
	f := func() { x += 2; a[0]++ }
	f()
	return x*10 + a[0]
}

// C.14: a chain target's compound (`a[i].x += v`) — index operand once, the
// read's bounds check, the store.
func cChainCompound() int {
	a := []cT{{1}, {2}}
	i := 1
	a[i].x += 5
	return a[0].x*10 + a[1].x
}

func main() {
	cNilMapCompound()
}
