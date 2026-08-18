package main

// spec#Address_operators block Address_operators-1-7fb9c29a: & applies to
// variables, pointer indirections, slice/array indexing, field selectors, and
// (by exception) composite literals; for a nil pointer x, evaluating *x
// causes a run-time panic, and since "if the evaluation of x would cause a
// run-time panic, then the evaluation of &x does too", &*x panics as well.

type Point struct{ x, y int }

func f(n int) int { return n } // realizes the index call in &a[f(2)]

var pfCell = 40

func pf(n int) *int { return &pfCell } // realizes *pf(x)

// addressForms exercises every legal operand form from the block's first half
// and returns 1 + 30 + 2 + 3 + 40 == 76 through the created pointers.
func addressForms() int {
	x := 1
	a := [4]int{10, 20, 30, 40}
	px := &x           // &x
	pa := &a[f(2)]     // &a[f(2)]
	pp := &Point{2, 3} // &Point{2, 3}
	p := px
	deref := *p    // *p
	call := *pf(x) // *pf(x)
	return deref + *pa + pp.x + pp.y + call
}

// derefNil: spec: *x on nil x causes a run-time panic.
func derefNil() int {
	var x *int = nil
	return *x
}

// addrDerefNil: spec: &*x on nil x causes a run-time panic (the evaluation of
// *x would panic, so &*x does too).
func addrDerefNil() int {
	var x *int = nil
	p := &*x
	_ = p
	return 0
}

// addrDerefNilParen: the parenthesized composition &(*p) shares BUG-056
// exactly (delta-review F-1: the frontend wire for &*p and &(*p) is
// byte-identical — both collapse to q := p; an earlier draft of this
// subject ended `return q.x`, whose trailing deref panicked regardless,
// masking the collapse — the same masked-green pattern BUG-057's rows
// fix). Discriminating shape: the & expression itself must panic.
func addrDerefNilParen() int {
	var p *Point
	q := &(*p)
	_ = q
	return 0
}
