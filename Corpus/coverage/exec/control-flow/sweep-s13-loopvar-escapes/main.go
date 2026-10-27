package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the ways a for-clause
// variable's CELL IDENTITY escapes an iteration beyond BUG-148's three (an
// explicit &i, a pointer-receiver call, slicing an array variable) — a
// pointer-receiver METHOD VALUE, a field's and an element's address, a
// pointer-receiver call on a field, slicing a field array, a capture two
// closures deep — plus the cell identity itself (two iterations' pointers),
// an earlier cell mutated later through its pointer, a struct cell captured
// then mutated, and a pointer-typed loop variable as the no-escape control.
// The trigger is emitFor's findAddrEscape / addrEscapeRoot; the lowering is
// emitForPerIteration's carrier pointer. Expected = gc go1.26.5.

type counter struct{ n int }

func (c *counter) inc() int { c.n++; return c.n }

type inner struct{ n int }

func (p *inner) self() *inner { return p }

type box struct {
	in  inner
	arr [2]int
}

// D14: a pointer-receiver method value bound in the loop and called later.
func methodValuePtrRecv() int {
	var fs []func() int
	for c := (counter{}); c.n < 3; c.n++ {
		fs = append(fs, c.inc)
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 123
}

// D15: the address of a field of a struct loop variable.
func fieldAddr() int {
	var ps []*int
	for c := (counter{}); c.n < 3; c.n++ {
		ps = append(ps, &c.n)
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 12
}

// D16: the address of an element of an array loop variable.
func elemAddr() int {
	var ps []*int
	for a := [2]int{}; a[0] < 3; a[0]++ {
		ps = append(ps, &a[0])
	}
	return *ps[0]*100 + *ps[1]*10 + *ps[2] // 12
}

// D17: a pointer-receiver call on a field of the loop variable.
func nestedFieldPtrRecv() int {
	var ps []*inner
	for b := (box{}); b.in.n < 3; b.in.n++ {
		ps = append(ps, b.in.self())
	}
	return ps[0].n*100 + ps[1].n*10 + ps[2].n // 12
}

// D19: slicing a field array of the loop variable.
func fieldArraySlice() int {
	var ss [][]int
	for b := (box{}); b.arr[0] < 3; b.arr[0]++ {
		ss = append(ss, b.arr[:])
	}
	return ss[0][0]*100 + ss[1][0]*10 + ss[2][0] // 12
}

// D20: a pointer-typed loop variable whose pointee is mutated — no cell escape (control).
func pointerLoopvarControl() int {
	x := 0
	sum := 0
	for p := &x; *p < 3; *p++ {
		sum += *p
	}
	return sum*10 + x // 33
}

// D22: a capture two closures deep.
func nestedClosureCapture() int {
	var fs []func() int
	for i := 0; i < 3; i++ {
		fs = append(fs, func() int { return func() int { return i }() })
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 12
}

// D27: the identity of two iterations' cells.
func cellIdentity() (bool, bool) {
	var ps []*int
	for i := 0; i < 2; i++ {
		ps = append(ps, &i)
		ps = append(ps, &i)
	}
	return ps[0] == ps[1], ps[0] == ps[2] // true, false
}

// D32: an earlier iteration's cell mutated through its pointer in later iterations.
func oldCellMutatedLater() int {
	var p *int
	last := 0
	for i := 0; i < 3; i++ {
		if i == 0 {
			p = &i
		} else {
			*p += 10 // iteration 0's cell: 0 -> 10 -> 20
		}
		last = i
	}
	return *p*10 + last // 202
}

// D33: a struct loop variable captured, then mutated in the same iteration.
func structCapturedThenMutated() int {
	var fs []func() int
	for c := (counter{}); c.n < 30; c.n++ {
		fs = append(fs, func() int { return c.n })
		c.n += 10
	}
	return fs[0]()*100 + fs[1]()*10 + fs[2]() // 10, 21, 32 -> 1242
}

func main() {
	println(methodValuePtrRecv(), fieldAddr(), elemAddr(), nestedFieldPtrRecv(), fieldArraySlice(),
		pointerLoopvarControl(), nestedClosureCapture(), oldCellMutatedLater(), structCapturedThenMutated())
	println(cellIdentity())
}
