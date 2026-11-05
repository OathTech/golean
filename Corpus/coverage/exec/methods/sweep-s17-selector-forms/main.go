package main

// Sweep lane sweep/s17-forms (2026-11-05), shape S17 (plan §4; the matrix
// on BUG-001's line): selectors on operands the corpus did not hold — a
// field of a call result, of an index, of a map element, of a parenthesised
// dereference, of a type assertion, of a composite literal, of a
// conversion; a method call on a call result, on a conversion, on an
// assertion and on a nested field; a qualified constant of a source-through
// package. (The parenthesised-dereference receiver beside a sibling call is
// BUG-391, rowed in methods/sweep-s17-unseq-deref-receiver.) Expected = gc
// go1.26.5.

import "math"

type pt struct{ x, y int }

func (p pt) sum() int { return p.x + p.y }

func (p *pt) bump() int { p.x++; return p.x }

type wrap struct{ in pt }

type summer interface{ sum() int }

type raw struct{ x, y int }

func mk() pt { return pt{1, 2} }

func mkp() *pt { return &pt{3, 4} }

// B4.2
func qualifiedConst() int {
	return math.MaxInt8 + int(math.MinInt16) // 127 - 32768 = -32641
}

// B4.3
func fieldOfCall() int {
	return mk().x*10 + mkp().y // 14
}

func fieldOfIndex() int {
	ps := []pt{{5, 6}}
	a := [1]pt{{7, 8}}
	return ps[0].x*1000 + ps[0].y*100 + a[0].x*10 + a[0].y // 5678
}

func fieldOfMapElem() int {
	m := map[string]pt{"a": {1, 2}}
	return m["a"].x*10 + m["a"].y // 12
}

func fieldOfDeref() int {
	p := &pt{3, 4}
	return (*p).x*10 + (*p).y // 34
}

func fieldOfAssert() int {
	var i any = pt{5, 6}
	var j any = &pt{7, 8}
	return i.(pt).x*1000 + i.(pt).y*100 + j.(*pt).x*10 + j.(*pt).y // 5678
}

func fieldOfLiteral() int {
	return pt{1, 2}.y*10 + (&pt{3, 4}).x // 23
}

func fieldOfConversion() int {
	r := raw{4, 5}
	return pt(r).x*10 + pt(r).y // 45
}

// B4.5
func methodOnCallResult() int {
	return mk().sum()*10 + mkp().bump() // 30 + 4 = 34
}

func methodOnConversion() int {
	r := raw{1, 2}
	return pt(r).sum() // 3
}

func methodOnAssert() int {
	var i any = pt{2, 3}
	var s summer = pt{4, 5}
	return i.(pt).sum()*10 + s.(pt).sum() // 59
}

// B4.5 control (BUG-391): the deref-paren receiver alone (legacy path)
func derefParenReceiverAlone() int {
	p := &pt{1, 1}
	return (*p).bump() // 2
}

// B4.5 control (BUG-391): the VALUE-receiver twin — `(*p).sum()` beside a
// pointer-receiver call lowers (the `deref` head is admitted); both calls
// are ordered events, so the set is one member
func derefParenValueReceiverBesideCall() int {
	p := &pt{1, 1}
	return (*p).sum()*10 + p.bump() // 22
}

func methodOnField() int {
	w := wrap{in: pt{2, 2}}
	return w.in.sum()*10 + w.in.bump() // 40 + 3 = 43
}

func main() {
	println(qualifiedConst(), fieldOfCall(), fieldOfIndex(), fieldOfMapElem(), fieldOfDeref(), fieldOfAssert(),
		fieldOfLiteral(), fieldOfConversion(), methodOnCallResult(), methodOnConversion(), methodOnAssert(),
		derefParenReceiverAlone(), derefParenValueReceiverBesideCall(), methodOnField())
}
