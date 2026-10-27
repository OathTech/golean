package main

// Sweep lane sweep/s13-binding (2026-10-27), shape S13: the select case's
// `:=` binding (selectRecvClause) — captured and mutated by a closure after
// the select, and the two-variable form shadowing outer names with ok used.
// scoping/select-clause-scope holds the plain shadow and the default body's.
// Expected = gc go1.26.5.

// M1
func caseVarCaptured() int {
	ch := make(chan int, 1)
	ch <- 5
	var f func() int
	select {
	case v := <-ch:
		f = func() int { v++; return v }
	}
	return f() + f() // 13
}

// M3
func twoVarShadow() int {
	v, ok := 1, false
	ch := make(chan int, 1)
	ch <- 9
	r := 0
	select {
	case v, ok := <-ch:
		if ok {
			r = v
		}
	}
	if ok {
		return -1
	}
	return r*10 + v // 91
}

func main() { println(caseVarCaptured(), twoVarShadow()) }
