// Defect-neighbourhood campaign, shape S9 (evaluation count: twice, never, or re-read;
// members BUG-130/082/076/074/066/047/164/140), lane sweep/s9-eval-count, 2026-10-27
// (docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every subject folds a call
// counter into its result, so an operand evaluated twice, never, or re-read after a
// mutation moves the value; expected = gc go1.26.5.
//
// && and || with call operands (emitBinary's short-circuit accumulator): nested mixed
// forms, an if with ||, a len of a call in the right operand, an index with a call in the
// right operand, the return and addressed-target positions, a call argument, in a closure
// and in a generic function — the right operand once when reached, never otherwise.

package main

var cnt int

func t() bool { cnt++; return true }
func fl() bool { cnt++; return false }
func f() int    { cnt++; return 1 }
func fs() []int { cnt++; return []int{1, 2} }

func nestedMixed() int {
	cnt = 0
	r := 0
	if fl() || (t() && t()) {
		r = 1
	}
	if t() || (t() && t()) {
		r += 10
	}
	if fl() || (fl() && t()) {
		r += 100
	}
	return cnt*100 + r
}

func ifOr() int {
	cnt = 0
	r := 0
	if t() || t() {
		r = 1
	}
	if fl() || t() {
		r += 10
	}
	return cnt*100 + r
}

func lenCallInRhs() int {
	cnt = 0
	r := 0
	if t() && len(fs()) > 0 {
		r = 1
	}
	if fl() && len(fs()) > 0 {
		r += 10
	}
	return cnt*100 + r
}

func indexCallInRhs() int {
	cnt = 0
	s := []int{5, 6}
	r := 0
	if t() && s[f()] == 6 {
		r = 1
	}
	if fl() && s[f()] == 6 {
		r += 10
	}
	return cnt*100 + r
}

func returnSc() int {
	cnt = 0
	a := func() bool { return t() && t() }()
	b := func() bool { return fl() && t() }()
	r := 0
	if a {
		r = 1
	}
	if b {
		r += 10
	}
	return cnt*100 + r
}

func indexTargetSc() int {
	cnt = 0
	s := []bool{false, false}
	s[0] = fl() || t()
	s[1] = t() || t()
	r := 0
	if s[0] {
		r = 1
	}
	if s[1] {
		r += 10
	}
	return cnt*100 + r
}

func closureSc() int {
	cnt = 0
	r := 0
	inner := func() {
		if fl() || t() && fl() {
			r = 1
		}
	}
	inner()
	return cnt*100 + r
}

func scGeneric[T comparable](a, b func() T, z T) int {
	if a() == z || b() == z {
		return 1
	}
	return 0
}

func genericSc() int {
	cnt = 0
	r := scGeneric(f, f, 1)
	s := scGeneric(func() string { cnt++; return "a" }, func() string { cnt++; return "b" }, "b")
	return cnt*100 + r*10 + s
}

func callArgSc() int {
	cnt = 0
	id := func(b bool) bool { return b }
	r := 0
	if id(fl() || t()) {
		r = 1
	}
	return cnt*100 + r
}

func main() {
	nestedMixed()
	ifOr()
	lenCallInRhs()
	indexCallInRhs()
	returnSc()
	indexTargetSc()
	closureSc()
	genericSc()
	callArgSc()
}
