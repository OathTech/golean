package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line): address-of and dereference chains the corpus did not
// hold — the address of a field of an element, of a nested field, of a
// field of a slice element, of a pointer-to-array element, of a field's
// array element; `*&x`, `&*&x`; stores through a parenthesised, a double
// and an address-of dereference; a triple dereference; the address of a
// field of a parenthesised dereference and of a parenthesised double
// dereference; address-of in a generic body and as a defer argument.
// Expected = gc go1.26.5.

var calls int

type pt struct{ x, y int }

type outer struct {
	in  pt
	arr [3]int
}

func take(p *int) { calls += *p }

func addrG[T int | int64](v T) T {
	p := &v
	*p += 1
	return *p
}

// B15.2
func addrElemField() int {
	ps := [2]pt{{1, 2}, {3, 4}}
	p := &ps[1].y
	*p = 9
	return ps[1].y*10 + ps[1].x // 93
}

func addrNestedField() int {
	var o outer
	p := &o.in.x
	*p = 5
	return o.in.x // 5
}

func addrSliceElemField() int {
	ss := []pt{{1, 2}}
	p := &ss[0].x
	*p += 10
	return ss[0].x // 11
}

func addrPtrArrayElem() int {
	a := [2]int{1, 2}
	pa := &a
	p := &pa[1]
	*p = 7
	return a[1] // 7
}

func addrFieldArrayElem() int {
	var o outer
	p := &o.arr[2]
	*p = 8
	return o.arr[2] // 8
}

func derefAddr() int {
	x := 3
	return *&x * 10 // 30
}

func addrDerefAddr() int {
	x := 4
	p := &*&x
	*p = 6
	return x // 6
}

func storeViaDerefParen() int {
	x := 0
	p := &x
	(*p) = 5
	return x // 5
}

func storeViaDoubleDeref() int {
	x := 0
	p := &x
	pp := &p
	**pp = 6
	return x // 6
}

func storeViaDerefAddr() int {
	x := 1
	*&x = 7
	return x // 7
}

func tripleDeref() int {
	x := 8
	p := &x
	pp := &p
	ppp := &pp
	***ppp += 1
	return ***ppp + x // 18
}

func addrFieldOfDerefParen() int {
	q := &pt{1, 2}
	p := &(*q).y
	*p = 9
	return q.y // 9
}

func addrParenDoubleDeref() int {
	x := 2
	p := &x
	pp := &p
	r := &(**pp)
	*r = 3
	return x // 3
}

// B15.4
func addrInGeneric() int {
	return int(addrG(1)) + int(addrG(int64(10))) // 2 + 11 = 13
}

func addrDeferArg() int {
	calls = 0
	x := 4
	func() {
		defer take(&x) // the address is evaluated now; the value read at exit
		x = 40
	}()
	return calls // 40
}

func main() {
	println(addrElemField(), addrNestedField(), addrSliceElemField(), addrPtrArrayElem(), addrFieldArrayElem(),
		derefAddr(), addrDerefAddr(), storeViaDerefParen(), storeViaDoubleDeref(), storeViaDerefAddr(), tripleDeref(),
		addrFieldOfDerefParen(), addrParenDoubleDeref(), addrInGeneric(), addrDeferArg())
}
