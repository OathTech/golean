package main

// The range-expression non-evaluation special case (spec#For_statements:
// "The range expression x is evaluated once before beginning the loop,
// with one exception: if at most one iteration variable is present and
// len(x) is constant, the range expression is not evaluated." —
// len(x) is constant per spec#Length_and_capacity when x has array or
// pointer-to-array type and contains no channel receives or function
// calls). BUG-076 ($GOROOT/test harvest 2026-09-01,
// fixedbugs/issue72844.go): the lowering evaluated a direct-array
// range expression unconditionally, so `for range *p` with nil p
// panicked where gc iterates the type-derived length.

// issue72844 shape: nil *[4]int, no iteration variables — *p must NOT
// be evaluated; four silent iterations.
func rangeDerefNilNoVar() int {
	var p *[4]int
	n := 0
	for range *p {
		n++
	}
	return n
}

// Key-only form over the same nil deref: still at most one iteration
// variable — not evaluated.
func rangeDerefNilKeyOnly() int {
	var p *[4]int
	s := 0
	for i := range *p {
		s += i
	}
	return s
}

type arrHolder struct{ p *[4]int }

// The pointer-to-array sibling: `for range s.p` with s nil — the
// range expression (a nil-deref-on-evaluate selector chain) contains
// no calls or receives, so it is not evaluated either; the length is
// the pointed-to array type's.
func rangeFieldPtrNilNoVar() int {
	var s *arrHolder
	n := 0
	for range s.p {
		n++
	}
	return n
}

// The boundary's other side (i): TWO iteration variables present
// (blank second still counts) — x IS evaluated, the nil deref panics.
func rangeDerefNilTwoVars() int {
	var p *[4]int
	n := 0
	for i, _ := range *p {
		n += i
	}
	return n
}

var rangeEvalCount int

func mkArr() [3]int {
	rangeEvalCount++
	return [3]int{}
}

// The boundary's other side (ii): a function call in x — len(x) is
// not constant, x evaluates exactly ONCE.
func rangeCallEvaluatedOnce() int {
	rangeEvalCount = 0
	n := 0
	for range mkArr() {
		n++
	}
	return n*10 + rangeEvalCount
}

// ---- Audit fix round 2026-09-01 (NOTE-15): the two hasCallOrRecv arms
// the first pins left unexercised, each with both boundary directions
// where Go can reach them.

// Conversions do NOT count as calls (go/types call.go returns before the
// flag is set on the conversion arm): `*(*[4]int)(sl)` over an EMPTY
// slice contains no call and no receive, so with no iteration variable
// it is NOT evaluated — the slice-to-array-pointer conversion that would
// panic (len 0 < 4) never runs; four silent iterations.
func rangeConversionNoVar() int {
	sl := []int{}
	n := 0
	for range *(*[4]int)(sl) {
		n++
	}
	return n
}

// The same expression with TWO iteration variables IS evaluated: the
// conversion runs and panics on the too-short slice.
func rangeConversionTwoVarsPanic() int {
	sl := []int{}
	n := 0
	for i, _ := range *(*[4]int)(sl) {
		n += i
	}
	return n
}

// A CONSTANT len(...) inside the range expression is not a call
// (call.go's builtin arm sets the flag only for a NON-constant result):
// `ps[len(arr)-4]` over a nil *[2][4]int contains no call and no
// receive, so key-only it is NOT evaluated — the nil deref that indexing
// would perform never happens; the sum of four indices, 6.
func rangeConstLenIndexKeyOnly() int {
	var arr [4]int
	var ps *[2][4]int
	s := 0
	for i := range ps[len(arr)-4] {
		s += i
	}
	return s
}
