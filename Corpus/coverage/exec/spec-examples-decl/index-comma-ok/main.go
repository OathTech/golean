package main

// spec#Index_expressions block Index_expressions-2-e0e8e639: a map index in
// a two-value assignment/declaration yields (value, ok) — in all three
// declared forms (assignment, short declaration, var declaration); ok is
// false and v the zero value for a missing key.

func indexCommaOk() int {
	a := map[string]int{"k": 3}
	x := "k"
	var v int
	var ok bool
	v, ok = a[x]
	v2, ok2 := a[x]
	var v3, ok3 = a["missing"]
	n := 0
	if ok {
		n++
	}
	if ok2 {
		n++
	}
	if ok3 || v3 != 0 {
		n = -100
	}
	return v*100 + v2*10 + n // 332
}

// indexCommaOkVarPresent: var-declaration comma-ok on a PRESENT key — the
// P3 audit's unmasking row (BUG-057; the sibling's "missing" key made
// ok=false correct, hiding the flag drop). Expected 91.
func indexCommaOkVarPresent() int {
	a := map[string]int{"here": 9}
	var v, ok = a["here"]
	n := 0
	if ok {
		n = 1
	}
	return v*10 + n
}
