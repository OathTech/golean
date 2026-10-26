package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// CHAINED conversions: string through bytes and runes and back (fresh copies
// each way), defined string over defined string, and the struct chain
// C(B(a)) / A(B(c)) with the box's dynamic type at the end of the chain.

type A struct{ X, Y int }
type B struct{ X, Y int }
type C B
type MyStr string
type MyStr2 string

func stringChains() (string, int, bool) {
	s := "héy"
	a := string([]byte(s))
	b := string([]rune(s))
	c := MyStr(string(MyStr2(s)))
	d := []rune(string([]rune(s)))
	e := []byte(string([]byte(s)))
	e[0] = 'x'
	return a + b + string(c), len(d), s == a && s == b && e[0] == 'x'
}

func structChains() int {
	a := A{1, 2}
	c := C(B(a))
	back := A(B(c))
	var i any = C(B(A(B(a))))
	r := 0
	switch i.(type) {
	case A:
		r = 1
	case B:
		r = 2
	case C:
		r = 3
	}
	eq := 0
	if back == a {
		eq = 1
	}
	return r*100 + c.X*10 + eq
}

func main() {}
