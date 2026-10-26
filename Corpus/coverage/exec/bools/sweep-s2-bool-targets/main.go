package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// Bool targets: the emitter STRIPS the conversion node (bool has no kinds), so
// the static-type consequences — the box's dynamic type, map keys, switch,
// chained spellings, the readout's type — must come from go/types at the use sites.

type MyBool bool

func boxedDynamicType() int {
	var b bool = true
	mb := MyBool(b)
	var i any = mb
	r := 0
	switch i.(type) {
	case bool:
		r = 1
	case MyBool:
		r = 2
	}
	return r
}

func compareAndKey() int {
	var b bool = true
	mb := MyBool(b)
	m := map[MyBool]int{true: 1, false: 2}
	r := 0
	if mb == true {
		r += 10
	}
	if bool(mb) {
		r += 100
	}
	r += m[MyBool(b)]
	switch MyBool(!b) {
	case false:
		r += 1000
	case true:
		r += 2000
	}
	return r
}

func chained() int {
	var b bool = false
	x := bool(MyBool(bool(MyBool(b))))
	var i any = MyBool(bool(MyBool(!b)))
	r := 0
	if !x {
		r = 1
	}
	if _, ok := i.(MyBool); ok {
		r += 10
	}
	if _, ok := i.(bool); ok {
		r += 100
	}
	return r
}

func returnedDefinedBool() MyBool {
	var b bool = true
	return MyBool(b)
}

func main() {}
