package main

// Defect-neighbourhood campaign, shape S1 (implicit conversion omitted at an
// assignable context), lane sweep/s1-implicit-conv, 2026-10-27: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// The PANIC ARGUMENT is an `any` slot (emitPanicStmt's own wrap): an untyped
// constant of each kind, a constant expression and a shift take their default
// type; a typed-nil pointer boxes non-nil; a struct boxes; an interface payload
// keeps its dynamic type — each read back through `recover()`.

type tPt struct{ X, Y int }

type tErr struct{}

func (tErr) Error() string { return "tErr" }

func constInt() (r any) {
	defer func() { r = recover() }()
	panic(3)
}

func constFloat() (r any) {
	defer func() { r = recover() }()
	panic(2.5)
}

func constRune() (r any) {
	defer func() { r = recover() }()
	panic('a')
}

func constBool() (r any) {
	defer func() { r = recover() }()
	panic(true)
}

func pointer() (nonNil bool, isTypedNil bool) {
	defer func() {
		r := recover()
		nonNil = r != nil
		v, ok := r.(*tPt)
		isTypedNil = ok && v == nil
	}()
	var p *tPt
	panic(p)
}

func structPayload() (r any) {
	defer func() { r = recover() }()
	panic(tPt{1, 2})
}

func ifaceToIface() (int, bool) {
	var e error = tErr{}
	score := 0
	same := false
	func() {
		defer func() {
			r := recover()
			switch r.(type) {
			case tErr:
				score += 1
			case error:
				score += 10
			}
			same = r == e
		}()
		panic(e)
	}()
	return score, same
}

func constExpr() (r any) {
	defer func() { r = recover() }()
	const c = 1.5
	panic(c * 2)
}

func shift() (r any) {
	defer func() { r = recover() }()
	s := 2
	panic(1 << s)
}

func main() {
	constInt()
}
